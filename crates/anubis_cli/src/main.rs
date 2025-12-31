//! Anubis Notary CLI
//!
//! A post-quantum CLI for signing, timestamping, licensing, and revenue generation.
//! Uses ML-DSA-87 for signatures, Argon2id for password-based key encryption.
//!
//! # Environment Variables
//!
//! - `ANUBIS_HOME` - Keystore directory (default: `~/.anubis`)
//! - `ANUBIS_PASSWORD` - Password for non-interactive operations (CI/CD)
//! - `ANUBIS_PASSWORD_FILE` - Path to file containing password
//!
//! # Non-Interactive Usage
//!
//! For CI/CD pipelines and scripts, you can provide passwords via:
//! ```bash
//! # Environment variable
//! export ANUBIS_PASSWORD="your-password"
//! anubis-notary sign document.pdf
//!
//! # Password file
//! echo "your-password" > /path/to/password
//! chmod 600 /path/to/password
//! export ANUBIS_PASSWORD_FILE=/path/to/password
//! anubis-notary sign document.pdf
//! ```

use std::io::{self, BufRead, Write};
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use serde::Serialize;
use zeroize::Zeroize;

/// Environment variable for password (non-interactive)
const ENV_ANUBIS_PASSWORD: &str = "ANUBIS_PASSWORD";
/// Environment variable for password file path
const ENV_ANUBIS_PASSWORD_FILE: &str = "ANUBIS_PASSWORD_FILE";

use anubis_core::mldsa::{KeyPair, PublicKey, Signature, SEED_SIZE};
use anubis_core::multisig::{Multisig, Proposal, ProposalType};
use anubis_core::streaming::{StreamingHasher, StreamingSigner, StreamingVerifier, StreamingConfig};
use anubis_io::{hash_directory, hash_file, keystore::Keystore, read_file, write_file_atomic};
use anubis_io::{format_delay, RateLimiter, SystemClock, TimeSource};

/// Anubis Notary - Post-quantum signing and licensing CLI.
#[derive(Parser)]
#[command(name = "anubis-notary")]
#[command(version, about, long_about = None)]
struct Cli {
    /// Output format.
    #[arg(long, global = true)]
    json: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Key management commands.
    Key {
        #[command(subcommand)]
        action: KeyCommands,
    },
    /// Sign a file.
    Sign {
        /// File to sign.
        file: PathBuf,
        /// Output signature file.
        #[arg(long, short)]
        out: Option<PathBuf>,
    },
    /// Verify a signature.
    Verify {
        /// File that was signed.
        file: PathBuf,
        /// Signature file.
        #[arg(long)]
        sig: PathBuf,
    },
    /// Create a receipt for a file or directory.
    Attest {
        /// Path to attest.
        path: PathBuf,
        /// Recurse into directories.
        #[arg(long, short)]
        recursive: bool,
        /// Output receipt file.
        #[arg(long)]
        receipt: PathBuf,
    },
    /// Verify a receipt against a file.
    Check {
        /// Receipt file.
        receipt: PathBuf,
        /// Original file or directory.
        path: PathBuf,
    },
    /// License management commands.
    License {
        #[command(subcommand)]
        action: LicenseCommands,
    },
    /// Anchoring commands (paid feature).
    Anchor {
        #[command(subcommand)]
        action: AnchorCommands,
    },
    /// Multi-signature governance commands.
    Multisig {
        #[command(subcommand)]
        action: MultisigCommands,
    },
    /// Streaming commands for large files.
    Stream {
        #[command(subcommand)]
        action: StreamCommands,
    },
}

#[derive(Subcommand)]
enum KeyCommands {
    /// Initialize a new keystore with a signing key.
    Init {
        /// Keystore path (default: $ANUBIS_HOME or ~/.anubis).
        #[arg(long)]
        keystore: Option<String>,
        /// KDF parameters (e.g., argon2id:m=4G,t=3,p=1).
        #[arg(long, default_value = "argon2id:m=4G,t=3,p=1")]
        kdf: String,
        /// Use low-memory mode (1 GiB instead of 4 GiB Argon2id).
        /// Suitable for systems with limited RAM (< 8 GiB).
        #[arg(long)]
        low_memory: bool,
    },
    /// Show key information.
    Show {
        /// Show only public key.
        #[arg(long)]
        pub_only: bool,
        /// Keystore path.
        #[arg(long)]
        keystore: Option<String>,
    },
    /// Rotate the signing key.
    Rotate {
        /// Keystore path.
        #[arg(long)]
        keystore: Option<String>,
        /// Use low-memory mode (1 GiB instead of 4 GiB Argon2id).
        #[arg(long)]
        low_memory: bool,
    },
    /// Revoke a key (add to revocation list).
    Revoke {
        /// Public key fingerprint (hex-encoded SHA3-256 of public key).
        /// Use "current" to revoke the current key.
        fingerprint: String,
        /// Reason for revocation.
        #[arg(long, default_value = "key compromised")]
        reason: String,
        /// Keystore path.
        #[arg(long)]
        keystore: Option<String>,
    },
    /// List archived and revoked keys.
    List {
        /// Keystore path.
        #[arg(long)]
        keystore: Option<String>,
    },
}

#[derive(Subcommand)]
enum LicenseCommands {
    /// Issue a new license.
    Issue {
        /// Product code.
        #[arg(long)]
        product: String,
        /// User identifier (email or ID).
        #[arg(long)]
        user: String,
        /// Expiration date (YYYY-MM-DD).
        #[arg(long)]
        expiry: String,
        /// Comma-separated feature flags.
        #[arg(long)]
        features: Option<String>,
        /// Output license file.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Verify a license.
    Verify {
        /// License file.
        #[arg(long)]
        license: PathBuf,
    },
    /// List issued licenses.
    List {
        /// Keystore path.
        #[arg(long)]
        keystore: Option<String>,
    },
}

#[derive(Subcommand)]
enum AnchorCommands {
    /// Queue operations.
    Queue {
        #[command(subcommand)]
        action: QueueCommands,
    },
    /// Submit queued receipts for anchoring.
    Submit {
        /// Anchor provider (btc, http-log).
        #[arg(long)]
        provider: String,
        /// HTTP log service URL (required for http-log provider).
        #[arg(long)]
        url: Option<String>,
        /// Batch size.
        #[arg(long, default_value = "512")]
        batch: usize,
        /// Wait for confirmation (seconds, 0 = don't wait).
        #[arg(long, default_value = "0")]
        wait: u64,
    },
    /// Check anchoring status.
    Status {
        /// Anchor ID.
        id: String,
        /// Refresh status from HTTP service.
        #[arg(long)]
        refresh: bool,
    },
}

#[derive(Subcommand)]
enum QueueCommands {
    /// Add a receipt to the queue.
    Add {
        /// Receipt file.
        receipt: PathBuf,
    },
    /// List queued receipts.
    List,
    /// Clear the queue.
    Clear,
}

#[derive(Subcommand)]
enum MultisigCommands {
    /// Initialize a new multisig configuration.
    Init {
        /// Threshold (M of N required signatures).
        #[arg(long, short)]
        threshold: u8,
        /// Public key files to include as signers.
        #[arg(long, short = 'k', required = true)]
        signers: Vec<PathBuf>,
        /// Output configuration file.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Create a new proposal.
    Propose {
        /// Multisig configuration file.
        #[arg(long)]
        config: PathBuf,
        /// Proposal type (key-rotation, threshold-change, add-signer, remove-signer, authorize-action, emergency-pause, resume, custom).
        #[arg(long, short = 't')]
        proposal_type: String,
        /// Proposal data (hex-encoded).
        #[arg(long, short)]
        data: String,
        /// Expiration time (Unix timestamp, 0 = no expiration).
        #[arg(long, default_value = "0")]
        expires: i64,
        /// Output proposal file.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Sign a proposal.
    Sign {
        /// Proposal file.
        #[arg(long)]
        proposal: PathBuf,
        /// Multisig configuration file.
        #[arg(long)]
        config: PathBuf,
        /// Output updated proposal file (default: overwrite input).
        #[arg(long, short)]
        out: Option<PathBuf>,
    },
    /// Execute an approved proposal.
    Execute {
        /// Proposal file.
        #[arg(long)]
        proposal: PathBuf,
        /// Multisig configuration file.
        #[arg(long)]
        config: PathBuf,
    },
    /// Show proposal status.
    Status {
        /// Proposal file.
        #[arg(long)]
        proposal: PathBuf,
        /// Multisig configuration file.
        #[arg(long)]
        config: PathBuf,
    },
    /// List signers in a multisig configuration.
    Signers {
        /// Multisig configuration file.
        #[arg(long)]
        config: PathBuf,
    },
}

#[derive(Subcommand)]
enum StreamCommands {
    /// Sign a large file using streaming (memory-efficient).
    Sign {
        /// File to sign.
        file: PathBuf,
        /// Output signature file.
        #[arg(long, short)]
        out: Option<PathBuf>,
        /// Chunk size in bytes (default: 65536).
        #[arg(long, default_value = "65536")]
        chunk_size: usize,
        /// Show progress.
        #[arg(long)]
        progress: bool,
    },
    /// Verify a large file signature using streaming (memory-efficient).
    Verify {
        /// File that was signed.
        file: PathBuf,
        /// Signature file.
        #[arg(long)]
        sig: PathBuf,
        /// Chunk size in bytes (default: 65536).
        #[arg(long, default_value = "65536")]
        chunk_size: usize,
        /// Show progress.
        #[arg(long)]
        progress: bool,
    },
    /// Hash a large file using streaming.
    Hash {
        /// File to hash.
        file: PathBuf,
        /// Chunk size in bytes (default: 65536).
        #[arg(long, default_value = "65536")]
        chunk_size: usize,
        /// Show progress.
        #[arg(long)]
        progress: bool,
    },
}

/// JSON output wrapper.
#[derive(Serialize)]
struct JsonOutput<T: Serialize> {
    success: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    data: Option<T>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
}

impl<T: Serialize> JsonOutput<T> {
    fn success(data: T) -> Self {
        Self {
            success: true,
            data: Some(data),
            error: None,
        }
    }

    fn error(msg: impl Into<String>) -> Self {
        Self {
            success: false,
            data: None,
            error: Some(msg.into()),
        }
    }
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let result = run_command(&cli);

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            if cli.json {
                let output: JsonOutput<()> = JsonOutput::error(e.to_string());
                match serde_json::to_string_pretty(&output) {
                    Ok(json) => println!("{}", json),
                    Err(json_err) => {
                        // Fallback to plain text if JSON serialization fails
                        eprintln!("Error: {} (JSON serialization failed: {})", e, json_err);
                    }
                }
            } else {
                eprintln!("Error: {}", e);
            }
            ExitCode::FAILURE
        }
    }
}

fn run_command(cli: &Cli) -> Result<(), Box<dyn std::error::Error>> {
    match &cli.command {
        Commands::Key { action } => handle_key(action, cli.json),
        Commands::Sign { file, out } => handle_sign(file, out.as_ref(), cli.json),
        Commands::Verify { file, sig } => handle_verify(file, sig, cli.json),
        Commands::Attest {
            path,
            recursive,
            receipt,
        } => handle_attest(path, *recursive, receipt, cli.json),
        Commands::Check { receipt, path } => handle_check(receipt, path, cli.json),
        Commands::License { action } => handle_license(action, cli.json),
        Commands::Anchor { action } => handle_anchor(action, cli.json),
        Commands::Multisig { action } => handle_multisig(action, cli.json),
        Commands::Stream { action } => handle_stream(action, cli.json),
    }
}

fn handle_key(action: &KeyCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        KeyCommands::Init { keystore, kdf, low_memory } => {
            let path = keystore
                .as_ref()
                .map(|s| expand_path(s))
                .unwrap_or_else(Keystore::default_path);
            let ks = Keystore::open(&path)?;

            // Parse KDF parameters
            if !kdf.starts_with("argon2id:") {
                return Err("KDF must be argon2id".into());
            }

            // Check if key already exists
            if ks.has_key() {
                return Err("Key already exists. Use 'key rotate' to replace.".into());
            }

            // Prompt for password
            if !json {
                eprintln!("Creating new keystore with password-protected key.");
                eprintln!("This will use Argon2id with {} memory for key derivation.",
                    if *low_memory { "1 GiB" } else { "4 GiB" });
                eprintln!();
            }

            let mut password = prompt_new_password()?;

            // Generate seed from system entropy
            let mut seed = generate_seed()?;

            // Generate ML-DSA-87 key pair
            let kp =
                KeyPair::from_seed(&seed).map_err(|e| format!("Key generation failed: {:?}", e))?;

            // Store public key (unencrypted - it's public)
            ks.write_public_key(&kp.public_key().to_bytes())?;

            // Seal and store the seed with password protection
            if !json {
                eprintln!("Encrypting key with Argon2id... (this may take a moment)");
            }

            if *low_memory {
                ks.seal_and_store_key_low_memory(password.as_bytes(), &seed)?;
            } else {
                ks.seal_and_store_key(password.as_bytes(), &seed)?;
            }

            // Zeroize sensitive data
            password.zeroize();
            seed.zeroize();

            // Log memory mode used
            let memory_mode = if *low_memory { "1 GiB (low-memory)" } else { "4 GiB (default)" };

            if json {
                #[derive(Serialize)]
                struct InitResult {
                    keystore: String,
                    public_key: String,
                    created: bool,
                    argon2id_memory: String,
                    password_protected: bool,
                }
                let output = JsonOutput::success(InitResult {
                    keystore: path.display().to_string(),
                    public_key: hex::encode(kp.public_key().to_bytes()),
                    created: true,
                    argon2id_memory: memory_mode.to_string(),
                    password_protected: true,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!();
                println!("Keystore initialized at: {}", path.display());
                println!("Public key: {}", hex::encode(kp.public_key().to_bytes()));
                println!("Argon2id memory: {}", memory_mode);
                println!("Password protection: ENABLED");
                println!();
                println!("IMPORTANT: Remember your password! There is no recovery mechanism.");
            }
            Ok(())
        }
        KeyCommands::Show { pub_only, keystore } => {
            let path = keystore
                .as_ref()
                .map(|s| expand_path(s))
                .unwrap_or_else(Keystore::default_path);
            let ks = Keystore::open(&path)?;

            if ks.has_key() {
                let pubkey = ks.read_public_key()?;
                if json {
                    #[derive(Serialize)]
                    struct ShowResult {
                        has_key: bool,
                        public_key: Option<String>,
                    }
                    let output = JsonOutput::success(ShowResult {
                        has_key: true,
                        public_key: Some(hex::encode(&pubkey)),
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Public key: {}", hex::encode(&pubkey));
                    if !pub_only {
                        println!("(Private key is encrypted in keystore)");
                    }
                }
            } else if json {
                #[derive(Serialize)]
                struct ShowResult {
                    has_key: bool,
                    public_key: Option<String>,
                }
                let output = JsonOutput::success(ShowResult {
                    has_key: false,
                    public_key: None,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("No key found. Run 'anubis-notary key init' first.");
            }
            Ok(())
        }
        KeyCommands::Rotate { keystore, low_memory } => {
            let path = keystore
                .as_ref()
                .map(|s| expand_path(s))
                .unwrap_or_else(Keystore::default_path);
            let ks = Keystore::open(&path)?;

            // Determine memory mode for display
            let memory_mode = if *low_memory { "1 GiB (low-memory)" } else { "4 GiB (default)" };

            // Check if key exists
            if !ks.has_key() {
                return Err("No key found. Run 'anubis-notary key init' first.".into());
            }

            if !json {
                eprintln!("Key rotation will:");
                eprintln!("  1. Authenticate with current password");
                eprintln!("  2. Archive the old key");
                eprintln!("  3. Generate a new key");
                eprintln!("  4. Encrypt with a new password");
                eprintln!();
            }

            // Load the old keypair with password
            let old_kp = load_keypair_with_password(&ks)?;

            // Prompt for new password
            if !json {
                eprintln!();
                eprintln!("Enter a NEW password for the rotated key:");
            }
            let mut new_password = prompt_new_password()?;

            // Generate new keypair
            let mut new_seed = generate_seed()?;
            let new_kp = KeyPair::from_seed(&new_seed)
                .map_err(|e| format!("New key generation failed: {:?}", e))?;

            // Create rotation certificate: sign the new public key with the old key
            // This proves the old key holder authorized the rotation
            let mut rotation_msg = Vec::with_capacity(2048 + 64);
            rotation_msg.extend_from_slice(b"anubis-notary:key-rotation:v1:");
            rotation_msg.extend_from_slice(&old_kp.public_key().to_bytes());
            rotation_msg.extend_from_slice(b":");
            rotation_msg.extend_from_slice(&new_kp.public_key().to_bytes());

            let rotation_sig = old_kp
                .sign(&rotation_msg)
                .map_err(|e| format!("Rotation signing failed: {:?}", e))?;

            // Get current timestamp for archiving
            let clock = SystemClock;
            let timestamp = clock.now();

            // Archive the old key
            let archive_id = ks.archive_current_key(timestamp)?;

            // Store the rotation certificate
            ks.write_rotation_cert(&archive_id, &rotation_sig.to_bytes())?;

            // Write new public key
            ks.write_public_key(&new_kp.public_key().to_bytes())?;

            // Seal and store new key with password
            if !json {
                eprintln!("Encrypting new key with Argon2id... (this may take a moment)");
            }

            if *low_memory {
                ks.seal_and_store_key_low_memory(new_password.as_bytes(), &new_seed)?;
            } else {
                ks.seal_and_store_key(new_password.as_bytes(), &new_seed)?;
            }

            // Zeroize sensitive data
            new_password.zeroize();
            new_seed.zeroize();

            if json {
                #[derive(Serialize)]
                struct RotateResult {
                    old_public_key: String,
                    new_public_key: String,
                    archive_id: String,
                    rotated_at: i64,
                    argon2id_memory: String,
                    password_protected: bool,
                }
                let output = JsonOutput::success(RotateResult {
                    old_public_key: hex::encode(old_kp.public_key().to_bytes()),
                    new_public_key: hex::encode(new_kp.public_key().to_bytes()),
                    archive_id,
                    rotated_at: timestamp,
                    argon2id_memory: memory_mode.to_string(),
                    password_protected: true,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!();
                println!("Key rotated successfully!");
                println!("Old public key: {} (archived)", hex::encode(old_kp.public_key().to_bytes()));
                println!("New public key: {}", hex::encode(new_kp.public_key().to_bytes()));
                println!("Archive ID: {}", archive_id);
                println!("Argon2id memory: {}", memory_mode);
                println!("Password protection: ENABLED");
                println!("Old key archived in: {}", ks.archive_path().display());
                println!();
                println!("Note: Old signatures can still be verified using archived keys.");
            }

            Ok(())
        }
        KeyCommands::Revoke {
            fingerprint,
            reason,
            keystore,
        } => {
            let path = keystore
                .as_ref()
                .map(|s| expand_path(s))
                .unwrap_or_else(Keystore::default_path);
            let ks = Keystore::open(&path)?;

            // Calculate fingerprint
            let fp = if fingerprint == "current" {
                // Revoke current key
                if !ks.has_key() {
                    return Err("No key found.".into());
                }
                let pubkey = ks.read_public_key()?;
                let hash = anubis_core::keccak::sha3::sha3_256(&pubkey);
                hex::encode(hash)
            } else {
                fingerprint.clone()
            };

            // Check fingerprint format (should be 64 hex chars)
            if fp.len() != 64 || !fp.chars().all(|c| c.is_ascii_hexdigit()) {
                return Err("Invalid fingerprint: must be 64 hex characters (SHA3-256)".into());
            }

            let clock = SystemClock;
            let timestamp = clock.now();

            ks.revoke_key(&fp, timestamp, reason)?;

            if json {
                #[derive(Serialize)]
                struct RevokeResult {
                    fingerprint: String,
                    revoked_at: i64,
                    reason: String,
                }
                let output = JsonOutput::success(RevokeResult {
                    fingerprint: fp.clone(),
                    revoked_at: timestamp,
                    reason: reason.clone(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Key revoked:");
                println!("  Fingerprint: {}", fp);
                println!("  Revoked at: {}", timestamp);
                println!("  Reason: {}", reason);
                println!("\nSignatures from this key will now fail verification.");
            }

            Ok(())
        }
        KeyCommands::List { keystore } => {
            let path = keystore
                .as_ref()
                .map(|s| expand_path(s))
                .unwrap_or_else(Keystore::default_path);
            let ks = Keystore::open(&path)?;

            let archived = ks.list_archived_keys()?;
            let revoked = ks.list_revoked()?;

            if json {
                #[derive(Serialize)]
                struct ListResult {
                    current_key: Option<String>,
                    archived_keys: Vec<ArchivedKeyInfo>,
                    revoked_keys: Vec<RevokedKeyInfo>,
                }
                #[derive(Serialize)]
                struct ArchivedKeyInfo {
                    archive_id: String,
                    public_key: Option<String>,
                }
                #[derive(Serialize)]
                struct RevokedKeyInfo {
                    fingerprint: String,
                    revoked_at: i64,
                    reason: String,
                }

                let current_key = if ks.has_key() {
                    let pk = ks.read_public_key()?;
                    Some(hex::encode(&pk))
                } else {
                    None
                };

                let archived_info: Vec<_> = archived
                    .iter()
                    .map(|id| ArchivedKeyInfo {
                        archive_id: id.clone(),
                        public_key: ks.read_archived_public_key(id).ok().map(|pk| hex::encode(&pk)),
                    })
                    .collect();

                let revoked_info: Vec<_> = revoked
                    .iter()
                    .map(|(fp, ts, reason)| RevokedKeyInfo {
                        fingerprint: fp.clone(),
                        revoked_at: *ts,
                        reason: reason.clone(),
                    })
                    .collect();

                let output = JsonOutput::success(ListResult {
                    current_key,
                    archived_keys: archived_info,
                    revoked_keys: revoked_info,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Keystore: {}", path.display());
                println!();

                if ks.has_key() {
                    let pk = ks.read_public_key()?;
                    let fp = hex::encode(anubis_core::keccak::sha3::sha3_256(&pk));
                    println!("Current key:");
                    println!("  Public key: {}", hex::encode(&pk[..32]));
                    println!("  Fingerprint: {}", fp);
                } else {
                    println!("No current key");
                }
                println!();

                if archived.is_empty() {
                    println!("No archived keys");
                } else {
                    println!("Archived keys ({}):", archived.len());
                    for id in &archived {
                        if let Ok(pk) = ks.read_archived_public_key(id) {
                            let fp = hex::encode(anubis_core::keccak::sha3::sha3_256(&pk));
                            println!("  {} (fingerprint: {}...)", id, &fp[..16]);
                        } else {
                            println!("  {} (public key unavailable)", id);
                        }
                    }
                }
                println!();

                if revoked.is_empty() {
                    println!("No revoked keys");
                } else {
                    println!("Revoked keys ({}):", revoked.len());
                    for (fp, ts, reason) in &revoked {
                        println!("  {}... @ {} ({})", &fp[..16], ts, reason);
                    }
                }
            }

            Ok(())
        }
    }
}

fn handle_sign(
    file: &PathBuf,
    out: Option<&PathBuf>,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    // Load the signing key from default keystore
    let ks = Keystore::open(Keystore::default_path())?;
    if !ks.has_key() {
        return Err("No signing key found. Run 'anubis-notary key init' first.".into());
    }

    // SECURITY: Check if the key has been revoked before allowing signing
    let pk_bytes = ks.read_public_key()?;
    let fingerprint = hex::encode(anubis_core::keccak::sha3::sha3_256(&pk_bytes));
    if ks.is_revoked(&fingerprint)? {
        return Err("Cannot sign: key has been revoked. Generate a new key with 'anubis-notary key init'.".into());
    }

    // Load keypair with password authentication
    let kp = load_keypair_with_password(&ks)?;

    // Read and hash the file
    let data = read_file(file)?;
    let hash = anubis_core::keccak::sha3::sha3_256(&data);

    // Create the message to sign (hash of file content with domain separation)
    let mut message_to_sign = Vec::with_capacity(64);
    message_to_sign.extend_from_slice(b"anubis-notary:sign:v1:");
    message_to_sign.extend_from_slice(&hash);

    let signature = kp
        .sign(&message_to_sign)
        .map_err(|e| format!("Signing failed: {:?}", e))?;

    // Write signature file
    let out_path = out.cloned().unwrap_or_else(|| file.with_extension("sig"));

    write_file_atomic(&out_path, &signature.to_bytes())?;

    if json {
        #[derive(Serialize)]
        struct SignResult {
            file: String,
            hash: String,
            signature: String,
            sig_size: usize,
        }
        let output = JsonOutput::success(SignResult {
            file: file.display().to_string(),
            hash: hex::encode(hash),
            signature: out_path.display().to_string(),
            sig_size: signature.to_bytes().len(),
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!("Signed: {}", file.display());
        println!("Hash: {}", hex::encode(hash));
        println!("Signature: {}", out_path.display());
        println!(
            "Signature size: {} bytes (ML-DSA-87)",
            signature.to_bytes().len()
        );
    }

    Ok(())
}

fn handle_verify(
    file: &PathBuf,
    sig: &PathBuf,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    // Load the public key from default keystore
    let ks = Keystore::open(Keystore::default_path())?;
    if !ks.has_key() {
        return Err("No signing key found. Run 'anubis-notary key init' first.".into());
    }

    let pk_bytes = ks.read_public_key()?;
    let pk =
        PublicKey::from_bytes(&pk_bytes).map_err(|e| format!("Invalid public key: {:?}", e))?;

    // Check if key is revoked
    let fingerprint = hex::encode(anubis_core::keccak::sha3::sha3_256(&pk_bytes));
    let revoked = ks.is_revoked(&fingerprint)?;

    // Read and hash the file
    let data = read_file(file)?;
    let hash = anubis_core::keccak::sha3::sha3_256(&data);

    // Reconstruct the message that was signed
    let mut message_to_verify = Vec::with_capacity(64);
    message_to_verify.extend_from_slice(b"anubis-notary:sign:v1:");
    message_to_verify.extend_from_slice(&hash);

    // Read and parse the signature
    let sig_bytes = read_file(sig)?;
    let signature =
        Signature::from_bytes(&sig_bytes).map_err(|e| format!("Invalid signature: {:?}", e))?;

    // Verify the signature
    let crypto_valid = pk.verify(&message_to_verify, &signature);

    // Signature is only valid if cryptographically valid AND not revoked
    let valid = crypto_valid && !revoked;

    if json {
        #[derive(Serialize)]
        struct VerifyResult {
            file: String,
            hash: String,
            signature: String,
            valid: bool,
            crypto_valid: bool,
            revoked: bool,
        }
        let output = JsonOutput::success(VerifyResult {
            file: file.display().to_string(),
            hash: hex::encode(hash),
            signature: sig.display().to_string(),
            valid,
            crypto_valid,
            revoked,
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else if revoked {
        println!("Signature INVALID for: {} (KEY REVOKED)", file.display());
        println!("Hash: {}", hex::encode(hash));
        println!("Note: The signing key has been revoked.");
    } else if crypto_valid {
        println!("Signature VALID for: {}", file.display());
        println!("Hash: {}", hex::encode(hash));
    } else {
        println!("Signature INVALID for: {}", file.display());
    }

    Ok(())
}

fn handle_attest(
    path: &PathBuf,
    recursive: bool,
    receipt_path: &PathBuf,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::keccak::sha3::sha3_256;
    use anubis_core::receipt::Receipt;

    // Load the signing key from default keystore
    let ks = Keystore::open(Keystore::default_path())?;
    if !ks.has_key() {
        return Err("No signing key found. Run 'anubis-notary key init' first.".into());
    }

    // SECURITY: Check if the key has been revoked before allowing attestation
    let pk_bytes = ks.read_public_key()?;
    let fingerprint = hex::encode(sha3_256(&pk_bytes));
    if ks.is_revoked(&fingerprint)? {
        return Err("Cannot attest: key has been revoked. Generate a new key with 'anubis-notary key init'.".into());
    }

    // Load keypair with password authentication
    let kp = load_keypair_with_password(&ks)?;

    let clock = SystemClock;
    let now = clock.now();

    let digest = if path.is_file() {
        hash_file(path)?
    } else if path.is_dir() && recursive {
        // Hash all files and combine
        let entries = hash_directory(path)?;
        let mut combined = Vec::new();
        for (rel_path, hash) in &entries {
            combined.extend_from_slice(rel_path.to_string_lossy().as_bytes());
            combined.extend_from_slice(hash);
        }
        sha3_256(&combined)
    } else {
        return Err("Path must be a file, or use --recursive for directories".into());
    };

    // Create the receipt
    let receipt = Receipt::new(digest, now);

    // Encode the signable portion (everything except the signature)
    let mut signable_buf = [0u8; 4096];
    let signable_len = receipt
        .encode_signable(&mut signable_buf)
        .map_err(|e| format!("Failed to encode signable receipt: {:?}", e))?;

    // Sign the signable portion with domain separation
    let mut message_to_sign = Vec::with_capacity(signable_len + 32);
    message_to_sign.extend_from_slice(b"anubis-notary:attest:v1:");
    message_to_sign.extend_from_slice(&signable_buf[..signable_len]);

    let signature = kp
        .sign(&message_to_sign)
        .map_err(|e| format!("Signing failed: {:?}", e))?;

    // Add signature to receipt
    let receipt = receipt
        .with_signature(&signature.to_bytes())
        .map_err(|e| format!("Failed to add signature: {:?}", e))?;

    // Encode the full signed receipt
    let mut buf = [0u8; 8192];
    let len = receipt.encode(&mut buf).map_err(|e| format!("{:?}", e))?;

    write_file_atomic(receipt_path, &buf[..len])?;

    if json {
        #[derive(Serialize)]
        struct AttestResult {
            path: String,
            digest: String,
            created: i64,
            receipt: String,
            signed: bool,
            sig_size: usize,
        }
        let output = JsonOutput::success(AttestResult {
            path: path.display().to_string(),
            digest: hex::encode(digest),
            created: now,
            receipt: receipt_path.display().to_string(),
            signed: true,
            sig_size: receipt.sig_len,
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!("Attested: {}", path.display());
        println!("Digest: {}", hex::encode(digest));
        println!("Created: {}", now);
        println!("Receipt: {}", receipt_path.display());
        println!("Signed: {} bytes (ML-DSA-87)", receipt.sig_len);
    }

    Ok(())
}

fn handle_check(
    receipt_path: &PathBuf,
    path: &PathBuf,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::mldsa::{PublicKey, Signature};
    use anubis_core::receipt::Receipt;

    let receipt_data = read_file(receipt_path)?;
    let receipt = Receipt::decode(&receipt_data).map_err(|e| format!("{:?}", e))?;

    // SECURITY: Load public key to verify signature
    let ks = Keystore::open(Keystore::default_path())?;
    if !ks.has_key() {
        return Err("No public key found. Cannot verify receipt signature.".into());
    }

    let pk_bytes = ks.read_public_key()?;
    let pk = PublicKey::from_bytes(&pk_bytes)
        .map_err(|e| format!("Invalid public key: {:?}", e))?;

    // Check if key is revoked
    let fingerprint = hex::encode(anubis_core::keccak::sha3::sha3_256(&pk_bytes));
    let key_revoked = ks.is_revoked(&fingerprint)?;

    // Verify the signature on the receipt
    let mut signable_buf = [0u8; 4096];
    let signable_len = receipt
        .encode_signable(&mut signable_buf)
        .map_err(|e| format!("Failed to encode signable portion: {:?}", e))?;

    let mut message_to_verify = Vec::with_capacity(signable_len + 32);
    message_to_verify.extend_from_slice(b"anubis-notary:attest:v1:");
    message_to_verify.extend_from_slice(&signable_buf[..signable_len]);

    let signature = Signature::from_bytes(&receipt.signature[..receipt.sig_len])
        .map_err(|e| format!("Invalid signature in receipt: {:?}", e))?;

    let sig_valid = pk.verify(&message_to_verify, &signature);

    // Compute current hash of the file/directory
    let current_hash = if path.is_file() {
        hash_file(path)?
    } else if path.is_dir() {
        let entries = hash_directory(path)?;
        let mut combined = Vec::new();
        for (rel_path, hash) in &entries {
            combined.extend_from_slice(rel_path.to_string_lossy().as_bytes());
            combined.extend_from_slice(hash.as_ref());
        }
        anubis_core::keccak::sha3::sha3_256(&combined)
    } else {
        return Err("Path must be a file or directory".into());
    };

    let digest_valid = current_hash == receipt.digest;

    // Receipt is only valid if BOTH signature is valid AND digest matches AND key not revoked
    let valid = sig_valid && digest_valid && !key_revoked;

    if json {
        #[derive(Serialize)]
        struct CheckResult {
            receipt: String,
            path: String,
            expected_digest: String,
            actual_digest: String,
            digest_valid: bool,
            signature_valid: bool,
            key_revoked: bool,
            valid: bool,
            created: i64,
        }
        let output = JsonOutput::success(CheckResult {
            receipt: receipt_path.display().to_string(),
            path: path.display().to_string(),
            expected_digest: hex::encode(receipt.digest),
            actual_digest: hex::encode(current_hash),
            digest_valid,
            signature_valid: sig_valid,
            key_revoked,
            valid,
            created: receipt.created,
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else if valid {
        println!("Receipt VALID");
        println!("  Path: {}", path.display());
        println!("  Digest: {}", hex::encode(current_hash));
        println!("  Signature: verified (ML-DSA-87)");
        println!("  Created: {}", receipt.created);
    } else {
        println!("Receipt INVALID");
        if !digest_valid {
            println!("  Digest mismatch:");
            println!("    Expected: {}", hex::encode(receipt.digest));
            println!("    Actual: {}", hex::encode(current_hash));
        }
        if !sig_valid {
            println!("  Signature verification FAILED");
        }
        if key_revoked {
            println!("  Signing key has been REVOKED");
        }
    }

    Ok(())
}

fn handle_license(action: &LicenseCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::license::License;

    match action {
        LicenseCommands::Issue {
            product,
            user,
            expiry,
            features,
            out,
        } => {
            // Load the signing key from default keystore
            let ks = Keystore::open(Keystore::default_path())?;
            if !ks.has_key() {
                return Err("No signing key found. Run 'anubis-notary key init' first.".into());
            }

            // SECURITY: Check if the key has been revoked before allowing signing
            let pk_bytes = ks.read_public_key()?;
            let fingerprint = hex::encode(anubis_core::keccak::sha3::sha3_256(&pk_bytes));
            if ks.is_revoked(&fingerprint)? {
                return Err("Cannot issue license: key has been revoked. Generate a new key with 'anubis-notary key init'.".into());
            }

            // Load keypair with password authentication
            let kp = load_keypair_with_password(&ks)?;

            // Parse expiry date
            let exp_timestamp = parse_date(expiry)?;

            let mut license =
                License::new(user, product, exp_timestamp).map_err(|e| format!("{:?}", e))?;

            // Add features
            if let Some(feat_str) = features {
                for feat in feat_str.split(',') {
                    let feat = feat.trim();
                    if !feat.is_empty() {
                        license.add_feature(feat).map_err(|e| format!("{:?}", e))?;
                    }
                }
            }

            // Encode the signable portion
            let mut signable_buf = [0u8; 4096];
            let signable_len = license
                .encode_signable(&mut signable_buf)
                .map_err(|e| format!("{:?}", e))?;

            // Create the message to sign with domain separation
            let mut message_to_sign = Vec::with_capacity(signable_len + 32);
            message_to_sign.extend_from_slice(b"anubis-notary:license:v1:");
            message_to_sign.extend_from_slice(&signable_buf[..signable_len]);

            // Sign with ML-DSA-87
            let signature = kp
                .sign(&message_to_sign)
                .map_err(|e| format!("Signing failed: {:?}", e))?;

            // Set the signature on the license
            license
                .set_signature(&signature.to_bytes())
                .map_err(|e| format!("{:?}", e))?;

            // Encode the full license
            let mut buf = [0u8; 8192];
            let len = license.encode(&mut buf).map_err(|e| format!("{:?}", e))?;

            write_file_atomic(out, &buf[..len])?;

            // Store license record in keystore
            let clock = SystemClock;
            let timestamp = clock.now();
            let metadata = serde_json::json!({
                "product": product,
                "user": user,
                "expiry": exp_timestamp,
                "issued_at": timestamp,
                "features": license.features().iter().map(|f| f.as_str()).collect::<Vec<_>>(),
                "output_path": out.display().to_string(),
            });
            let license_id = ks.store_license(&buf[..len], metadata.to_string().as_bytes())?;

            if json {
                #[derive(Serialize)]
                struct IssueResult {
                    license_id: String,
                    product: String,
                    user: String,
                    expiry: i64,
                    features: Vec<String>,
                    license_file: String,
                    signature_size: usize,
                }
                let output = JsonOutput::success(IssueResult {
                    license_id,
                    product: product.clone(),
                    user: user.clone(),
                    expiry: exp_timestamp,
                    features: license
                        .features()
                        .iter()
                        .map(|f| f.as_str().to_string())
                        .collect(),
                    license_file: out.display().to_string(),
                    signature_size: signature.to_bytes().len(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("License issued:");
                println!("  License ID: {}", license_id);
                println!("  Product: {}", product);
                println!("  User: {}", user);
                println!("  Expiry: {}", expiry);
                println!("  File: {}", out.display());
                println!(
                    "  Signature: {} bytes (ML-DSA-87)",
                    signature.to_bytes().len()
                );
            }

            Ok(())
        }
        LicenseCommands::Verify { license: lic_path } => {
            // Load the public key from default keystore
            let ks = Keystore::open(Keystore::default_path())?;
            if !ks.has_key() {
                return Err("No signing key found. Run 'anubis-notary key init' first.".into());
            }

            let pk_bytes = ks.read_public_key()?;
            let pk = PublicKey::from_bytes(&pk_bytes)
                .map_err(|e| format!("Invalid public key: {:?}", e))?;

            let data = read_file(lic_path)?;
            let license = License::decode(&data).map_err(|e| format!("{:?}", e))?;

            // Re-encode the signable portion
            let mut signable_buf = [0u8; 4096];
            let signable_len = license
                .encode_signable(&mut signable_buf)
                .map_err(|e| format!("{:?}", e))?;

            // Reconstruct the message that was signed
            let mut message_to_verify = Vec::with_capacity(signable_len + 32);
            message_to_verify.extend_from_slice(b"anubis-notary:license:v1:");
            message_to_verify.extend_from_slice(&signable_buf[..signable_len]);

            // Parse the signature
            let sig_bytes = license.signature();
            let signature = Signature::from_bytes(sig_bytes)
                .map_err(|e| format!("Invalid signature: {:?}", e))?;

            // Verify the signature
            let sig_valid = pk.verify(&message_to_verify, &signature);

            let clock = SystemClock;
            let now = clock.now();
            let expired = license.is_expired(now);

            // License is valid if signature is valid and not expired
            let valid = sig_valid && !expired;

            if json {
                #[derive(Serialize)]
                struct VerifyResult {
                    valid: bool,
                    signature_valid: bool,
                    expired: bool,
                    product: String,
                    user: String,
                    expiry: i64,
                    features: Vec<String>,
                }
                let output = JsonOutput::success(VerifyResult {
                    valid,
                    signature_valid: sig_valid,
                    expired,
                    product: license.product().to_string(),
                    user: license.subject().to_string(),
                    expiry: license.expiration,
                    features: license
                        .features()
                        .iter()
                        .map(|f| f.as_str().to_string())
                        .collect(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("License verification:");
                println!(
                    "  Status: {}",
                    if valid {
                        "VALID"
                    } else if !sig_valid {
                        "INVALID SIGNATURE"
                    } else {
                        "EXPIRED"
                    }
                );
                println!("  Signature: {}", if sig_valid { "valid" } else { "INVALID" });
                println!("  Product: {}", license.product());
                println!("  User: {}", license.subject());
                println!(
                    "  Expiry: {} ({})",
                    license.expiration,
                    if expired { "EXPIRED" } else { "valid" }
                );
                println!(
                    "  Features: {:?}",
                    license
                        .features()
                        .iter()
                        .map(|f| f.as_str())
                        .collect::<Vec<_>>()
                );
            }

            Ok(())
        }
        LicenseCommands::List { keystore } => {
            let path = keystore
                .as_ref()
                .map(|s| expand_path(s))
                .unwrap_or_else(Keystore::default_path);
            let ks = Keystore::open(&path)?;

            let license_ids = ks.list_licenses()?;

            if json {
                #[derive(Serialize)]
                struct LicenseInfo {
                    id: String,
                    product: Option<String>,
                    user: Option<String>,
                    expiry: Option<i64>,
                    issued_at: Option<i64>,
                }

                let mut licenses = Vec::new();
                for id in &license_ids {
                    if let Ok(meta_bytes) = ks.get_license_metadata(id) {
                        if let Ok(meta) = serde_json::from_slice::<serde_json::Value>(&meta_bytes) {
                            licenses.push(LicenseInfo {
                                id: id.clone(),
                                product: meta.get("product").and_then(|v| v.as_str()).map(String::from),
                                user: meta.get("user").and_then(|v| v.as_str()).map(String::from),
                                expiry: meta.get("expiry").and_then(|v| v.as_i64()),
                                issued_at: meta.get("issued_at").and_then(|v| v.as_i64()),
                            });
                        } else {
                            licenses.push(LicenseInfo {
                                id: id.clone(),
                                product: None,
                                user: None,
                                expiry: None,
                                issued_at: None,
                            });
                        }
                    }
                }

                #[derive(Serialize)]
                struct ListResult {
                    count: usize,
                    licenses: Vec<LicenseInfo>,
                }
                let output = JsonOutput::success(ListResult {
                    count: license_ids.len(),
                    licenses,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else if license_ids.is_empty() {
                println!("No licenses issued.");
                println!("Use 'license issue' to create a license.");
            } else {
                println!("Issued licenses ({}):", license_ids.len());
                for id in &license_ids {
                    if let Ok(meta_bytes) = ks.get_license_metadata(id) {
                        if let Ok(meta) = serde_json::from_slice::<serde_json::Value>(&meta_bytes) {
                            let product = meta.get("product").and_then(|v| v.as_str()).unwrap_or("?");
                            let user = meta.get("user").and_then(|v| v.as_str()).unwrap_or("?");
                            let expiry = meta.get("expiry").and_then(|v| v.as_i64()).unwrap_or(0);
                            println!("  {} - {} ({}) expires {}", id, product, user, expiry);
                        } else {
                            println!("  {} - (metadata unavailable)", id);
                        }
                    } else {
                        println!("  {} - (metadata unavailable)", id);
                    }
                }
            }

            Ok(())
        }
    }
}

fn handle_anchor(action: &AnchorCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::merkle::MerkleTree;
    use anubis_core::receipt::Receipt;

    let ks = Keystore::open(Keystore::default_path())?;

    match action {
        AnchorCommands::Queue { action } => match action {
            QueueCommands::Add { receipt } => {
                // Verify the receipt is valid first
                let receipt_data = read_file(receipt)?;
                let parsed = Receipt::decode(&receipt_data)
                    .map_err(|e| format!("Invalid receipt: {:?}", e))?;

                // Add to queue
                let queue_id = ks.queue_receipt(receipt)?;

                if json {
                    #[derive(Serialize)]
                    struct QueueAddResult {
                        receipt: String,
                        queue_id: String,
                        digest: String,
                    }
                    let output = JsonOutput::success(QueueAddResult {
                        receipt: receipt.display().to_string(),
                        queue_id: queue_id.clone(),
                        digest: hex::encode(parsed.digest),
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Receipt queued for anchoring:");
                    println!("  File: {}", receipt.display());
                    println!("  Queue ID: {}", queue_id);
                    println!("  Digest: {}", hex::encode(parsed.digest));
                }
            }
            QueueCommands::List => {
                let queued = ks.list_queue()?;

                if json {
                    #[derive(Serialize)]
                    struct QueueListResult {
                        count: usize,
                        entries: Vec<QueueEntry>,
                    }
                    #[derive(Serialize)]
                    struct QueueEntry {
                        id: String,
                        original_path: String,
                    }

                    let mut entries = Vec::new();
                    for id in &queued {
                        if let Ok((path, _)) = ks.get_queued_receipt(id) {
                            entries.push(QueueEntry {
                                id: id.clone(),
                                original_path: path,
                            });
                        }
                    }

                    let output = JsonOutput::success(QueueListResult {
                        count: queued.len(),
                        entries,
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else if queued.is_empty() {
                    println!("Anchor queue is empty.");
                    println!("Use 'anchor queue add <receipt>' to add receipts.");
                } else {
                    println!("Anchor queue ({} receipts):", queued.len());
                    for id in &queued {
                        if let Ok((path, _)) = ks.get_queued_receipt(id) {
                            println!("  {}... ({})", &id[..16], path);
                        } else {
                            println!("  {}...", &id[..16]);
                        }
                    }
                }
            }
            QueueCommands::Clear => {
                let count = ks.clear_queue()?;

                if json {
                    #[derive(Serialize)]
                    struct QueueClearResult {
                        cleared: usize,
                    }
                    let output = JsonOutput::success(QueueClearResult { cleared: count });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Cleared {} receipts from anchor queue.", count);
                }
            }
        },
        AnchorCommands::Submit { provider, url, batch, wait } => {
            use anubis_io::anchor::AnchorClient;
            use anubis_core::merkle::MAX_LEAVES;

            let queued = ks.list_queue()?;

            if queued.is_empty() {
                return Err("Anchor queue is empty. Add receipts first.".into());
            }

            // Validate http-log requires URL
            if provider == "http-log" && url.is_none() {
                return Err("http-log provider requires --url parameter".into());
            }

            // Validate batch size against MAX_LEAVES limit
            if *batch > MAX_LEAVES {
                return Err(format!(
                    "Batch size {} exceeds maximum of {} leaves per Merkle tree",
                    batch, MAX_LEAVES
                ).into());
            }

            // Limit batch size to available receipts
            let batch_size = (*batch).min(queued.len());
            let batch_ids: Vec<_> = queued.into_iter().take(batch_size).collect();

            // Build Merkle tree from receipt digests
            let mut tree = MerkleTree::new();
            let mut receipt_digests = Vec::new();

            for id in &batch_ids {
                let (_, receipt_data) = ks.get_queued_receipt(id)?;
                let receipt = Receipt::decode(&receipt_data)
                    .map_err(|e| format!("Failed to decode receipt {}: {:?}", id, e))?;
                tree.add_leaf(&receipt.digest)
                    .map_err(|e| format!("Failed to add leaf: {:?}", e))?;
                receipt_digests.push(hex::encode(receipt.digest));
            }

            let merkle_root = tree.compute_root()
                .map_err(|e| format!("Failed to compute Merkle root: {:?}", e))?;

            // Get timestamp
            let clock = SystemClock;
            let timestamp = clock.now();

            // Submit to external service if http-log
            let (anchor_id, status, entry_id, proof) = if provider == "http-log" {
                let service_url = url.as_ref().unwrap();
                let client = AnchorClient::new(service_url)
                    .map_err(|e| format!("Failed to create anchor client: {}", e))?;

                let response = if *wait > 0 {
                    client.submit_and_wait(&merkle_root, timestamp, *wait, 5)
                        .map_err(|e| format!("Failed to submit anchor: {}", e))?
                } else {
                    client.submit(&merkle_root, timestamp)
                        .map_err(|e| format!("Failed to submit anchor: {}", e))?
                };

                (
                    response.anchor_id,
                    response.status.to_string(),
                    response.entry_id,
                    response.proof,
                )
            } else {
                // For other providers (btc), just store locally
                (hex::encode(merkle_root), "submitted".to_string(), None, None)
            };

            // Create anchor record (JSON format for readability)
            let anchor_record = serde_json::json!({
                "version": 1,
                "anchor_id": anchor_id,
                "merkle_root": hex::encode(merkle_root),
                "provider": provider,
                "url": url,
                "timestamp": timestamp,
                "batch_size": batch_ids.len(),
                "receipt_ids": batch_ids,
                "receipt_digests": receipt_digests,
                "status": status,
                "entry_id": entry_id,
                "proof": proof
            });

            // Store anchor record
            ks.store_anchor(&anchor_id, anchor_record.to_string().as_bytes())?;

            // Remove submitted receipts from queue
            for id in &batch_ids {
                ks.remove_from_queue(id)?;
            }

            if json {
                #[derive(Serialize)]
                struct SubmitResult {
                    anchor_id: String,
                    merkle_root: String,
                    provider: String,
                    batch_size: usize,
                    timestamp: i64,
                    status: String,
                    entry_id: Option<u64>,
                }
                let output = JsonOutput::success(SubmitResult {
                    anchor_id: anchor_id.clone(),
                    merkle_root: hex::encode(merkle_root),
                    provider: provider.clone(),
                    batch_size: batch_ids.len(),
                    timestamp,
                    status: status.clone(),
                    entry_id,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Anchor submitted successfully!");
                println!("  Anchor ID: {}", anchor_id);
                println!("  Merkle Root: {}", hex::encode(merkle_root));
                println!("  Provider: {}", provider);
                if let Some(u) = url {
                    println!("  Service URL: {}", u);
                }
                println!("  Batch Size: {} receipts", batch_ids.len());
                println!("  Timestamp: {}", timestamp);
                println!("  Status: {}", status);
                if let Some(eid) = entry_id {
                    println!("  Entry ID: {}", eid);
                }
                println!();
                println!("Use 'anchor status {}' to check anchoring status.", &anchor_id[..16.min(anchor_id.len())]);
            }
        }
        AnchorCommands::Status { id, refresh } => {
            use anubis_io::anchor::AnchorClient;

            // Try to find anchor by ID prefix
            let anchors = ks.list_anchors()?;
            let matching: Vec<_> = anchors.iter()
                .filter(|a| a.starts_with(id))
                .collect();

            if matching.is_empty() {
                return Err(format!("No anchor found matching: {}", id).into());
            }
            if matching.len() > 1 {
                return Err(format!("Ambiguous anchor ID. Matches: {:?}", matching).into());
            }

            let anchor_id = matching[0];
            let anchor_data = ks.get_anchor(anchor_id)?;
            let mut anchor: serde_json::Value = serde_json::from_slice(&anchor_data)?;

            // Refresh from HTTP service if requested
            if *refresh {
                let provider = anchor.get("provider")
                    .and_then(|v| v.as_str())
                    .unwrap_or("");
                let url = anchor.get("url")
                    .and_then(|v| v.as_str());

                if provider == "http-log" {
                    if let Some(service_url) = url {
                        let client = AnchorClient::new(service_url)
                            .map_err(|e| format!("Failed to create anchor client: {}", e))?;

                        let response = client.status(anchor_id)
                            .map_err(|e| format!("Failed to query anchor status: {}", e))?;

                        // Update the stored anchor record
                        anchor["status"] = serde_json::json!(response.status.to_string());
                        if let Some(entry_id) = response.entry_id {
                            anchor["entry_id"] = serde_json::json!(entry_id);
                        }
                        if let Some(proof) = &response.proof {
                            anchor["proof"] = serde_json::json!(proof);
                        }

                        // Save updated record
                        ks.store_anchor(anchor_id, anchor.to_string().as_bytes())?;

                        if !json {
                            println!("(Refreshed from service)");
                        }
                    } else {
                        return Err("Cannot refresh: no URL stored for this anchor".into());
                    }
                } else {
                    return Err(format!("Cannot refresh: provider '{}' does not support refresh", provider).into());
                }
            }

            if json {
                let output = JsonOutput::success(&anchor);
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Anchor Status:");
                println!("  Anchor ID: {}", anchor_id);
                if let Some(root) = anchor.get("merkle_root") {
                    println!("  Merkle Root: {}", root.as_str().unwrap_or("unknown"));
                }
                if let Some(provider) = anchor.get("provider") {
                    println!("  Provider: {}", provider.as_str().unwrap_or("unknown"));
                }
                if let Some(url) = anchor.get("url").and_then(|v| v.as_str()) {
                    println!("  Service URL: {}", url);
                }
                if let Some(ts) = anchor.get("timestamp") {
                    println!("  Timestamp: {}", ts.as_i64().unwrap_or(0));
                }
                if let Some(batch) = anchor.get("batch_size") {
                    println!("  Batch Size: {}", batch.as_i64().unwrap_or(0));
                }
                if let Some(status) = anchor.get("status") {
                    println!("  Status: {}", status.as_str().unwrap_or("unknown"));
                }
                if let Some(entry_id) = anchor.get("entry_id").and_then(|v| v.as_u64()) {
                    println!("  Entry ID: {}", entry_id);
                }
                if anchor.get("proof").and_then(|v| v.as_str()).is_some() {
                    println!("  Proof: (available)");
                }
                if let Some(digests) = anchor.get("receipt_digests").and_then(|v| v.as_array()) {
                    println!("  Receipts ({}):", digests.len());
                    for digest in digests.iter().take(5) {
                        if let Some(d) = digest.as_str() {
                            println!("    {}...", &d[..16.min(d.len())]);
                        }
                    }
                    if digests.len() > 5 {
                        println!("    ... and {} more", digests.len() - 5);
                    }
                }
            }
        }
    }
    Ok(())
}

fn handle_multisig(action: &MultisigCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        MultisigCommands::Init { threshold, signers, out } => {
            if signers.is_empty() {
                return Err("At least one signer is required".into());
            }

            if *threshold == 0 {
                return Err("Threshold must be at least 1".into());
            }

            if *threshold as usize > signers.len() {
                return Err(format!(
                    "Threshold {} exceeds number of signers {}",
                    threshold,
                    signers.len()
                ).into());
            }

            // Load public keys from files
            let mut signer_pks = Vec::new();
            let mut signer_info = Vec::new();

            for signer_path in signers {
                let pk_bytes = read_file(signer_path)?;
                let pk = PublicKey::from_bytes(&pk_bytes)
                    .map_err(|e| format!("Invalid public key in {}: {:?}", signer_path.display(), e))?;

                let fingerprint = hex::encode(anubis_core::keccak::sha3::sha3_256(&pk_bytes));
                signer_pks.push(pk);
                signer_info.push((signer_path.display().to_string(), fingerprint));
            }

            let multisig = Multisig::new(*threshold, signer_pks).map_err(|e| format!("{:?}", e))?;

            // Serialize the configuration
            let config = serde_json::json!({
                "version": 1,
                "threshold": multisig.threshold,
                "signers": (0..multisig.signer_count())
                    .filter_map(|i| multisig.get_signer(i).map(|pk| hex::encode(pk.to_bytes())))
                    .collect::<Vec<_>>(),
            });

            write_file_atomic(out, serde_json::to_string_pretty(&config)?.as_bytes())?;

            if json {
                #[derive(Serialize)]
                struct InitResult {
                    config_file: String,
                    threshold: u8,
                    signer_count: usize,
                    signers: Vec<SignerInfo>,
                }
                #[derive(Serialize)]
                struct SignerInfo {
                    file: String,
                    fingerprint: String,
                }

                let output = JsonOutput::success(InitResult {
                    config_file: out.display().to_string(),
                    threshold: *threshold,
                    signer_count: signers.len(),
                    signers: signer_info.iter().map(|(f, fp)| SignerInfo {
                        file: f.clone(),
                        fingerprint: fp.clone(),
                    }).collect(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Multisig configuration created:");
                println!("  Config file: {}", out.display());
                println!("  Threshold: {} of {}", threshold, signers.len());
                println!("  Signers:");
                for (file, fp) in &signer_info {
                    println!("    {} ({}...)", file, &fp[..16]);
                }
            }
            Ok(())
        }
        MultisigCommands::Propose { config, proposal_type, data, expires, out } => {
            let config_data = read_file(config)?;
            let config_json: serde_json::Value = serde_json::from_slice(&config_data)?;

            // Parse signers from config
            let signers = config_json.get("signers")
                .and_then(|v| v.as_array())
                .ok_or("Invalid config: missing signers")?;

            let threshold = config_json.get("threshold")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid config: missing threshold")? as u8;

            let mut signer_pks = Vec::new();
            for signer_hex in signers {
                let pk_bytes = hex::decode(signer_hex.as_str().ok_or("Invalid signer")?)
                    .map_err(|e| format!("Invalid signer hex: {}", e))?;
                let pk = PublicKey::from_bytes(&pk_bytes)
                    .map_err(|e| format!("Invalid public key: {:?}", e))?;
                signer_pks.push(pk);
            }
            let multisig = Multisig::new(threshold, signer_pks).map_err(|e| format!("{:?}", e))?;

            // Parse proposal type - use AuthorizeAction for all custom data types
            let data_bytes = hex::decode(data)
                .map_err(|e| format!("Invalid data hex: {}", e))?;

            let ptype = match proposal_type.to_lowercase().as_str() {
                "key-rotation" => ProposalType::KeyRotation {
                    signer_index: 0,
                    new_key_hash: [0u8; 32],
                },
                "threshold-change" => ProposalType::ThresholdChange {
                    new_threshold: threshold,
                },
                "add-signer" => ProposalType::AddSigner {
                    new_signer_hash: [0u8; 32],
                },
                "remove-signer" => ProposalType::RemoveSigner {
                    signer_index: 0,
                },
                "authorize-action" => ProposalType::AuthorizeAction {
                    action_type: "custom".to_string(),
                    payload: data_bytes.clone(),
                },
                "emergency-pause" => ProposalType::EmergencyPause,
                "resume" => ProposalType::Resume,
                "custom" => ProposalType::Custom {
                    action_id: [0u8; 32],
                    params: data_bytes.clone(),
                },
                _ => return Err(format!("Unknown proposal type: {}", proposal_type).into()),
            };

            // Create proposal using Proposal::new
            let clock = SystemClock;
            let now = clock.now() as u64;
            let expires_at = if *expires > 0 { *expires as u64 } else { 0 };

            let proposal = Proposal::new(
                ptype,
                proposal_type, // Use proposal type string as description
                &multisig,
                now, // Use timestamp as nonce
                now,
                expires_at,
            ).map_err(|e| format!("{:?}", e))?;

            // Serialize proposal
            let proposal_json = serde_json::json!({
                "version": 1,
                "id": hex::encode(proposal.id),
                "nonce": proposal.nonce,
                "proposal_type": format!("{:?}", proposal.proposal_type),
                "description": proposal.description,
                "multisig_hash": hex::encode(proposal.multisig_hash),
                "data": hex::encode(&data_bytes),
                "expires": proposal.expires_at,
                "created": proposal.created_at,
                "status": format!("{:?}", proposal.status),
                "threshold": proposal.threshold,
                "signatures": Vec::<String>::new(),
                "signed_by": Vec::<usize>::new(),
            });

            write_file_atomic(out, serde_json::to_string_pretty(&proposal_json)?.as_bytes())?;

            if json {
                #[derive(Serialize)]
                struct ProposeResult {
                    proposal_file: String,
                    proposal_id: String,
                    nonce: u64,
                    proposal_type: String,
                    data_size: usize,
                    expires: u64,
                }
                let output = JsonOutput::success(ProposeResult {
                    proposal_file: out.display().to_string(),
                    proposal_id: hex::encode(proposal.id),
                    nonce: proposal.nonce,
                    proposal_type: format!("{:?}", proposal.proposal_type),
                    data_size: data_bytes.len(),
                    expires: proposal.expires_at,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Proposal created:");
                println!("  File: {}", out.display());
                println!("  ID: {}", hex::encode(proposal.id));
                println!("  Nonce: {}", proposal.nonce);
                println!("  Type: {:?}", proposal.proposal_type);
                println!("  Data size: {} bytes", data_bytes.len());
                if proposal.expires_at > 0 {
                    println!("  Expires: {}", proposal.expires_at);
                }
                println!();
                println!("Use 'multisig sign' to add signatures to this proposal.");
            }
            Ok(())
        }
        MultisigCommands::Sign { proposal, config, out } => {
            let config_data = read_file(config)?;
            let config_json: serde_json::Value = serde_json::from_slice(&config_data)?;

            // Parse signers from config
            let signers = config_json.get("signers")
                .and_then(|v| v.as_array())
                .ok_or("Invalid config: missing signers")?;

            let threshold = config_json.get("threshold")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid config: missing threshold")? as u8;

            // Build multisig
            let mut signer_pks = Vec::new();
            for signer_hex in signers {
                let pk_bytes = hex::decode(signer_hex.as_str().ok_or("Invalid signer")?)
                    .map_err(|e| format!("Invalid signer hex: {}", e))?;
                let pk = PublicKey::from_bytes(&pk_bytes)
                    .map_err(|e| format!("Invalid public key: {:?}", e))?;
                signer_pks.push(pk);
            }

            // Load keypair
            let ks = Keystore::open(Keystore::default_path())?;
            if !ks.has_key() {
                return Err("No signing key found. Run 'anubis-notary key init' first.".into());
            }

            // SECURITY: Check if the key has been revoked before allowing signing
            let pk_bytes = ks.read_public_key()?;
            let fingerprint = hex::encode(anubis_core::keccak::sha3::sha3_256(&pk_bytes));
            if ks.is_revoked(&fingerprint)? {
                return Err("Cannot sign: key has been revoked. Generate a new key with 'anubis-notary key init'.".into());
            }

            let kp = load_keypair_with_password(&ks)?;

            // Find signer index
            let my_pk = kp.public_key();
            let signer_idx = signer_pks.iter().position(|pk| pk.to_bytes() == my_pk.to_bytes())
                .ok_or("Your key is not a signer in this multisig")?;

            // Load proposal
            let proposal_data = read_file(proposal)?;
            let mut proposal_json: serde_json::Value = serde_json::from_slice(&proposal_data)?;

            // Get proposal ID and multisig hash
            let proposal_id = proposal_json.get("id").and_then(|v| v.as_str()).ok_or("Invalid proposal: missing id")?;
            let multisig_hash = proposal_json.get("multisig_hash").and_then(|v| v.as_str()).ok_or("Invalid proposal: missing multisig_hash")?;
            let nonce = proposal_json.get("nonce").and_then(|v| v.as_u64()).ok_or("Invalid proposal: missing nonce")?;

            // Create message to sign (using proposal signing payload format)
            let mut message = Vec::new();
            message.extend_from_slice(b"ANUBIS-MULTISIG-PROPOSAL-V1:");
            message.extend_from_slice(&hex::decode(proposal_id)?);
            message.extend_from_slice(&hex::decode(multisig_hash)?);
            message.extend_from_slice(&nonce.to_le_bytes());

            // Sign
            let signature = kp.sign(&message).map_err(|e| format!("Signing failed: {:?}", e))?;

            // Update proposal with signature
            {
                let signatures = proposal_json.get_mut("signatures")
                    .and_then(|v| v.as_array_mut())
                    .ok_or("Invalid proposal: missing signatures")?;

                // Ensure array is large enough
                while signatures.len() <= signer_idx {
                    signatures.push(serde_json::Value::Null);
                }
                signatures[signer_idx] = serde_json::json!(hex::encode(signature.to_bytes()));
            }

            // Update signed_by
            {
                let signed_by = proposal_json.get_mut("signed_by")
                    .and_then(|v| v.as_array_mut())
                    .ok_or("Invalid proposal: missing signed_by")?;
                if !signed_by.iter().any(|v| v.as_u64() == Some(signer_idx as u64)) {
                    signed_by.push(serde_json::json!(signer_idx));
                }
            }

            // Count signatures
            let sig_count = proposal_json.get("signatures")
                .and_then(|v| v.as_array())
                .map(|arr| arr.iter().filter(|s| !s.is_null()).count())
                .unwrap_or(0);

            // Update status if threshold met
            if sig_count >= threshold as usize {
                proposal_json["status"] = serde_json::json!("Approved");
            }

            // Write updated proposal
            let out_path = out.as_ref().unwrap_or(proposal);
            write_file_atomic(out_path, serde_json::to_string_pretty(&proposal_json)?.as_bytes())?;

            if json {
                #[derive(Serialize)]
                struct SignResult {
                    proposal_file: String,
                    signer_index: usize,
                    signatures_collected: usize,
                    threshold: u8,
                    approved: bool,
                }
                let output = JsonOutput::success(SignResult {
                    proposal_file: out_path.display().to_string(),
                    signer_index: signer_idx,
                    signatures_collected: sig_count,
                    threshold,
                    approved: sig_count >= threshold as usize,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Proposal signed:");
                println!("  File: {}", out_path.display());
                println!("  Signer index: {}", signer_idx);
                println!("  Signatures: {} of {} required", sig_count, threshold);
                if sig_count >= threshold as usize {
                    println!("  Status: APPROVED (threshold met)");
                    println!();
                    println!("Use 'multisig execute' to execute this proposal.");
                } else {
                    println!("  Status: Pending ({} more signatures needed)", threshold as usize - sig_count);
                }
            }
            Ok(())
        }
        MultisigCommands::Execute { proposal, config } => {
            use anubis_core::mldsa::Signature;

            let config_data = read_file(config)?;
            let config_json: serde_json::Value = serde_json::from_slice(&config_data)?;

            let threshold = config_json.get("threshold")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid config: missing threshold")? as u8;

            // SECURITY: Parse signer public keys for verification
            let signers = config_json.get("signers")
                .and_then(|v| v.as_array())
                .ok_or("Invalid config: missing signers")?;

            let mut signer_pks = Vec::new();
            for signer_hex in signers {
                let pk_bytes = hex::decode(signer_hex.as_str().ok_or("Invalid signer")?)
                    .map_err(|e| format!("Invalid signer hex: {}", e))?;
                let pk = PublicKey::from_bytes(&pk_bytes)
                    .map_err(|e| format!("Invalid public key: {:?}", e))?;
                signer_pks.push(pk);
            }

            let proposal_data = read_file(proposal)?;
            let proposal_json: serde_json::Value = serde_json::from_slice(&proposal_data)?;

            // Get proposal fields needed for verification
            let proposal_id = proposal_json.get("id")
                .and_then(|v| v.as_str())
                .ok_or("Invalid proposal: missing id")?;
            let multisig_hash = proposal_json.get("multisig_hash")
                .and_then(|v| v.as_str())
                .ok_or("Invalid proposal: missing multisig_hash")?;
            let nonce = proposal_json.get("nonce")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid proposal: missing nonce")?;

            // Reconstruct the message that was signed
            let mut message = Vec::new();
            message.extend_from_slice(b"ANUBIS-MULTISIG-PROPOSAL-V1:");
            message.extend_from_slice(&hex::decode(proposal_id)
                .map_err(|e| format!("Invalid proposal id: {}", e))?);
            message.extend_from_slice(&hex::decode(multisig_hash)
                .map_err(|e| format!("Invalid multisig_hash: {}", e))?);
            message.extend_from_slice(&nonce.to_le_bytes());

            let signatures = proposal_json.get("signatures")
                .and_then(|v| v.as_array())
                .ok_or("Invalid proposal: missing signatures")?;

            // SECURITY: Cryptographically verify each signature
            let mut verified_count = 0;
            let mut verification_errors = Vec::new();

            for (idx, sig_value) in signatures.iter().enumerate() {
                if sig_value.is_null() {
                    continue;
                }

                let sig_hex = sig_value.as_str().ok_or("Invalid signature format")?;
                let sig_bytes = hex::decode(sig_hex)
                    .map_err(|e| format!("Invalid signature hex at index {}: {}", idx, e))?;

                if idx >= signer_pks.len() {
                    verification_errors.push(format!("Signature at index {} has no corresponding signer", idx));
                    continue;
                }

                let signature = match Signature::from_bytes(&sig_bytes) {
                    Ok(s) => s,
                    Err(e) => {
                        verification_errors.push(format!("Invalid signature at index {}: {:?}", idx, e));
                        continue;
                    }
                };

                if signer_pks[idx].verify(&message, &signature) {
                    verified_count += 1;
                } else {
                    verification_errors.push(format!("Signature verification FAILED for signer {}", idx));
                }
            }

            // Check threshold with VERIFIED signatures only
            if verified_count < threshold as usize {
                let mut err_msg = format!(
                    "Insufficient valid signatures: {} verified of {} required",
                    verified_count, threshold
                );
                if !verification_errors.is_empty() {
                    err_msg.push_str("\nVerification errors:");
                    for err in &verification_errors {
                        err_msg.push_str(&format!("\n  - {}", err));
                    }
                }
                return Err(err_msg.into());
            }

            // Check expiration
            if let Some(expires) = proposal_json.get("expires").and_then(|v| v.as_u64()) {
                if expires > 0 {
                    let clock = SystemClock;
                    let now = clock.now() as u64;
                    if now > expires {
                        return Err("Proposal has expired".into());
                    }
                }
            }

            let proposal_type = proposal_json.get("proposal_type")
                .and_then(|v| v.as_str())
                .ok_or("Invalid proposal: missing proposal_type")?;

            let data_hex = proposal_json.get("data")
                .and_then(|v| v.as_str())
                .unwrap_or("");

            if json {
                #[derive(Serialize)]
                struct ExecuteResult {
                    proposal_type: String,
                    data: String,
                    verified_signatures: usize,
                    threshold: u8,
                    executed: bool,
                }
                let output = JsonOutput::success(ExecuteResult {
                    proposal_type: proposal_type.to_string(),
                    data: data_hex.to_string(),
                    verified_signatures: verified_count,
                    threshold,
                    executed: true,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Proposal executed:");
                println!("  Type: {}", proposal_type);
                println!("  Data: {} bytes", data_hex.len() / 2);
                println!("  Verified signatures: {} of {} (threshold: {})", verified_count, signer_pks.len(), threshold);
                if !verification_errors.is_empty() {
                    println!("  Warnings:");
                    for err in &verification_errors {
                        println!("    - {}", err);
                    }
                }
                println!();
                println!("Note: This CLI demonstrates the multisig flow.");
                println!("Actual execution logic depends on the proposal type.");
            }
            Ok(())
        }
        MultisigCommands::Status { proposal, config } => {
            let config_data = read_file(config)?;
            let config_json: serde_json::Value = serde_json::from_slice(&config_data)?;

            let threshold = config_json.get("threshold")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid config: missing threshold")? as u8;

            let signers = config_json.get("signers")
                .and_then(|v| v.as_array())
                .ok_or("Invalid config: missing signers")?;

            let proposal_data = read_file(proposal)?;
            let proposal_json: serde_json::Value = serde_json::from_slice(&proposal_data)?;

            let nonce = proposal_json.get("nonce").and_then(|v| v.as_u64()).unwrap_or(0);
            let proposal_type = proposal_json.get("proposal_type")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown");
            let status = proposal_json.get("status")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown");
            let expires = proposal_json.get("expires").and_then(|v| v.as_u64());
            let created = proposal_json.get("created").and_then(|v| v.as_u64()).unwrap_or(0);

            let signatures = proposal_json.get("signatures")
                .and_then(|v| v.as_array())
                .map(|a| a.iter().filter(|s| !s.is_null()).count())
                .unwrap_or(0);

            let signed_by = proposal_json.get("signed_by")
                .and_then(|v| v.as_array())
                .map(|a| a.iter().filter_map(|v| v.as_u64()).collect::<Vec<_>>())
                .unwrap_or_default();

            // Check if expired
            let is_expired = if let Some(exp) = expires {
                if exp > 0 {
                    let clock = SystemClock;
                    (clock.now() as u64) > exp
                } else {
                    false
                }
            } else {
                false
            };

            if json {
                #[derive(Serialize)]
                struct StatusResult {
                    nonce: u64,
                    proposal_type: String,
                    status: String,
                    signatures_collected: usize,
                    threshold: u8,
                    total_signers: usize,
                    signed_by: Vec<u64>,
                    created: u64,
                    expires: Option<u64>,
                    is_expired: bool,
                    can_execute: bool,
                }
                let output = JsonOutput::success(StatusResult {
                    nonce,
                    proposal_type: proposal_type.to_string(),
                    status: status.to_string(),
                    signatures_collected: signatures,
                    threshold,
                    total_signers: signers.len(),
                    signed_by,
                    created,
                    expires,
                    is_expired,
                    can_execute: signatures >= threshold as usize && !is_expired,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Proposal Status:");
                println!("  Nonce: {}", nonce);
                println!("  Type: {}", proposal_type);
                println!("  Status: {}", status);
                println!("  Signatures: {} of {} (threshold: {})", signatures, signers.len(), threshold);
                println!("  Created: {}", created);
                if let Some(exp) = expires {
                    if exp > 0 {
                        println!("  Expires: {}{}", exp, if is_expired { " (EXPIRED)" } else { "" });
                    }
                }
                println!();
                if signatures >= threshold as usize && !is_expired {
                    println!("  Ready to execute!");
                } else if is_expired {
                    println!("  Proposal has expired.");
                } else {
                    println!("  Needs {} more signature(s).", threshold as usize - signatures);
                }
            }
            Ok(())
        }
        MultisigCommands::Signers { config } => {
            let config_data = read_file(config)?;
            let config_json: serde_json::Value = serde_json::from_slice(&config_data)?;

            let threshold = config_json.get("threshold")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid config: missing threshold")? as u8;

            let signers = config_json.get("signers")
                .and_then(|v| v.as_array())
                .ok_or("Invalid config: missing signers")?;

            if json {
                #[derive(Serialize)]
                struct SignersResult {
                    threshold: u8,
                    total_signers: usize,
                    signers: Vec<SignerInfo>,
                }
                #[derive(Serialize)]
                struct SignerInfo {
                    index: usize,
                    public_key: String,
                    fingerprint: String,
                }

                let signers_info: Vec<SignerInfo> = signers.iter().enumerate()
                    .filter_map(|(i, s)| {
                        let pk_hex = s.as_str()?;
                        let pk_bytes = hex::decode(pk_hex).ok()?;
                        let fp = hex::encode(anubis_core::keccak::sha3::sha3_256(&pk_bytes));
                        Some(SignerInfo {
                            index: i,
                            public_key: pk_hex.to_string(),
                            fingerprint: fp,
                        })
                    })
                    .collect();

                let output = JsonOutput::success(SignersResult {
                    threshold,
                    total_signers: signers.len(),
                    signers: signers_info,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Multisig Configuration:");
                println!("  Threshold: {} of {}", threshold, signers.len());
                println!("  Signers:");
                for (i, signer) in signers.iter().enumerate() {
                    if let Some(pk_hex) = signer.as_str() {
                        if let Ok(pk_bytes) = hex::decode(pk_hex) {
                            let fp = hex::encode(anubis_core::keccak::sha3::sha3_256(&pk_bytes));
                            println!("    [{}] {}...", i, &fp[..32]);
                        }
                    }
                }
            }
            Ok(())
        }
    }
}

fn handle_stream(action: &StreamCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        StreamCommands::Sign { file, out, chunk_size, progress } => {
            use std::fs::File;
            use std::io::BufReader;

            // Load the signing key from default keystore
            let ks = Keystore::open(Keystore::default_path())?;
            if !ks.has_key() {
                return Err("No signing key found. Run 'anubis-notary key init' first.".into());
            }

            // Load keypair with password authentication
            let kp = load_keypair_with_password(&ks)?;

            // Get file size for progress
            let metadata = std::fs::metadata(file)?;
            let file_size = metadata.len();

            // Open file for streaming
            let f = File::open(file)?;
            let mut reader = BufReader::new(f);

            // Create streaming signer with custom chunk size
            let config = StreamingConfig::with_chunk_size(*chunk_size)
                .map_err(|e| format!("{}", e))?;
            let mut signer = StreamingSigner::with_config(&kp, config.clone());
            // Also run hasher in parallel to get the hash for display
            let mut hasher = StreamingHasher::with_config(config);

            // Process file with optional progress
            let mut bytes_read = 0u64;
            let mut buffer = vec![0u8; *chunk_size];

            loop {
                use std::io::Read;
                let n = reader.read(&mut buffer)?;
                if n == 0 {
                    break;
                }
                signer.update(&buffer[..n]).map_err(|e| format!("{}", e))?;
                hasher.update(&buffer[..n]).map_err(|e| format!("{}", e))?;
                bytes_read += n as u64;

                if *progress && !json {
                    let pct = (bytes_read as f64 / file_size as f64 * 100.0) as u32;
                    eprint!("\rProcessing: {}% ({}/{} bytes)", pct, bytes_read, file_size);
                    io::stderr().flush()?;
                }
            }

            if *progress && !json {
                eprintln!();
            }

            // Finalize and get signature
            let signature = signer.finalize().map_err(|e| format!("{}", e))?;
            let hash = hasher.finalize().map_err(|e| format!("{}", e))?;

            // Write signature file
            let out_path = out.clone().unwrap_or_else(|| file.with_extension("sig"));
            write_file_atomic(&out_path, &signature.to_bytes())?;

            if json {
                #[derive(Serialize)]
                struct SignResult {
                    file: String,
                    hash: String,
                    signature: String,
                    file_size: u64,
                    chunk_size: usize,
                    sig_size: usize,
                }
                let output = JsonOutput::success(SignResult {
                    file: file.display().to_string(),
                    hash: hex::encode(hash),
                    signature: out_path.display().to_string(),
                    file_size,
                    chunk_size: *chunk_size,
                    sig_size: signature.to_bytes().len(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Stream-signed: {}", file.display());
                println!("File size: {} bytes", file_size);
                println!("Hash: {}", hex::encode(hash));
                println!("Signature: {}", out_path.display());
                println!("Signature size: {} bytes (ML-DSA-87)", signature.to_bytes().len());
            }
            Ok(())
        }
        StreamCommands::Verify { file, sig, chunk_size, progress } => {
            use std::fs::File;
            use std::io::BufReader;

            // Load the public key from default keystore
            let ks = Keystore::open(Keystore::default_path())?;
            if !ks.has_key() {
                return Err("No signing key found. Run 'anubis-notary key init' first.".into());
            }

            let pk_bytes = ks.read_public_key()?;
            let pk = PublicKey::from_bytes(&pk_bytes)
                .map_err(|e| format!("Invalid public key: {:?}", e))?;

            // Read signature
            let sig_bytes = read_file(sig)?;
            let signature = Signature::from_bytes(&sig_bytes)
                .map_err(|e| format!("Invalid signature: {:?}", e))?;

            // Get file size for progress
            let metadata = std::fs::metadata(file)?;
            let file_size = metadata.len();

            // Open file for streaming
            let f = File::open(file)?;
            let mut reader = BufReader::new(f);

            // Create streaming verifier with custom chunk size
            let config = StreamingConfig::with_chunk_size(*chunk_size)
                .map_err(|e| format!("{}", e))?;
            let mut verifier = StreamingVerifier::with_config(&pk, &signature, config.clone());
            // Also run hasher in parallel to get the hash for display
            let mut hasher = StreamingHasher::with_config(config);

            // Process file with optional progress
            let mut bytes_read = 0u64;
            let mut buffer = vec![0u8; *chunk_size];

            loop {
                use std::io::Read;
                let n = reader.read(&mut buffer)?;
                if n == 0 {
                    break;
                }
                verifier.update(&buffer[..n]).map_err(|e| format!("{}", e))?;
                hasher.update(&buffer[..n]).map_err(|e| format!("{}", e))?;
                bytes_read += n as u64;

                if *progress && !json {
                    let pct = (bytes_read as f64 / file_size as f64 * 100.0) as u32;
                    eprint!("\rVerifying: {}% ({}/{} bytes)", pct, bytes_read, file_size);
                    io::stderr().flush()?;
                }
            }

            if *progress && !json {
                eprintln!();
            }

            // Finalize and verify
            let valid = verifier.finalize().map_err(|e| format!("{}", e))?;
            let hash = hasher.finalize().map_err(|e| format!("{}", e))?;

            if json {
                #[derive(Serialize)]
                struct VerifyResult {
                    file: String,
                    hash: String,
                    signature: String,
                    file_size: u64,
                    chunk_size: usize,
                    valid: bool,
                }
                let output = JsonOutput::success(VerifyResult {
                    file: file.display().to_string(),
                    hash: hex::encode(hash),
                    signature: sig.display().to_string(),
                    file_size,
                    chunk_size: *chunk_size,
                    valid,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else if valid {
                println!("Signature VALID for: {}", file.display());
                println!("File size: {} bytes", file_size);
                println!("Hash: {}", hex::encode(hash));
            } else {
                println!("Signature INVALID for: {}", file.display());
            }
            Ok(())
        }
        StreamCommands::Hash { file, chunk_size, progress } => {
            use std::fs::File;
            use std::io::BufReader;

            // Get file size for progress
            let metadata = std::fs::metadata(file)?;
            let file_size = metadata.len();

            // Open file for streaming
            let f = File::open(file)?;
            let mut reader = BufReader::new(f);

            // Create streaming hasher with custom chunk size
            let config = StreamingConfig::with_chunk_size(*chunk_size)
                .map_err(|e| format!("{}", e))?;
            let mut hasher = StreamingHasher::with_config(config);

            // Process file with optional progress
            let mut bytes_read = 0u64;
            let mut buffer = vec![0u8; *chunk_size];

            loop {
                use std::io::Read;
                let n = reader.read(&mut buffer)?;
                if n == 0 {
                    break;
                }
                hasher.update(&buffer[..n]).map_err(|e| format!("{}", e))?;
                bytes_read += n as u64;

                if *progress && !json {
                    let pct = (bytes_read as f64 / file_size as f64 * 100.0) as u32;
                    eprint!("\rHashing: {}% ({}/{} bytes)", pct, bytes_read, file_size);
                    io::stderr().flush()?;
                }
            }

            if *progress && !json {
                eprintln!();
            }

            // Finalize and get hash
            let hash = hasher.finalize().map_err(|e| format!("{}", e))?;

            if json {
                #[derive(Serialize)]
                struct HashResult {
                    file: String,
                    hash: String,
                    file_size: u64,
                    chunk_size: usize,
                    chunk_count: usize,
                }
                let output = JsonOutput::success(HashResult {
                    file: file.display().to_string(),
                    hash: hex::encode(hash),
                    file_size,
                    chunk_size: *chunk_size,
                    chunk_count: file_size.div_ceil(*chunk_size as u64) as usize,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Hash: {}", hex::encode(hash));
                println!("File: {}", file.display());
                println!("Size: {} bytes", file_size);
            }
            Ok(())
        }
    }
}

/// Expand ~ in paths.
fn expand_path(path: &str) -> PathBuf {
    if let Some(stripped) = path.strip_prefix("~/") {
        if let Some(home) = std::env::var_os("HOME") {
            return PathBuf::from(home).join(stripped);
        }
    }
    PathBuf::from(path)
}

/// Parse a date string (YYYY-MM-DD) to Unix timestamp.
fn parse_date(date: &str) -> Result<i64, Box<dyn std::error::Error>> {
    let parts: Vec<&str> = date.split('-').collect();
    if parts.len() != 3 {
        return Err("Date must be in YYYY-MM-DD format".into());
    }

    let year: i32 = parts[0].parse()?;
    let month: u32 = parts[1].parse()?;
    let day: u32 = parts[2].parse()?;

    // Simple calculation (not accounting for leap seconds etc.)
    // Days from Unix epoch (1970-01-01)
    let days = days_from_epoch(year, month, day);
    Ok(days * 86400)
}

/// Calculate days from Unix epoch.
fn days_from_epoch(year: i32, month: u32, day: u32) -> i64 {
    // Simplified calculation
    let mut total_days: i64 = 0;

    // Days in years
    for y in 1970..year {
        total_days += if is_leap_year(y) { 366 } else { 365 };
    }

    // Days in months
    let days_in_month = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    for m in 1..month {
        total_days += days_in_month[m as usize] as i64;
        if m == 2 && is_leap_year(year) {
            total_days += 1;
        }
    }

    // Days
    total_days += (day - 1) as i64;

    total_days
}

fn is_leap_year(year: i32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

/// Generate a cryptographic seed from the OS CSPRNG.
///
/// Uses `getrandom` which accesses the operating system's secure random number generator
/// (e.g., /dev/urandom on Linux, CryptGenRandom on Windows).
fn generate_seed() -> Result<[u8; SEED_SIZE], Box<dyn std::error::Error>> {
    let mut seed = [0u8; SEED_SIZE];
    getrandom::getrandom(&mut seed)
        .map_err(|e| format!("Failed to get random bytes from OS: {}", e))?;
    Ok(seed)
}

/// Get password from environment variable or file.
///
/// Checks in order:
/// 1. ANUBIS_PASSWORD environment variable
/// 2. ANUBIS_PASSWORD_FILE environment variable (reads from file)
/// 3. Returns None if neither is set
fn get_password_from_env() -> Result<Option<String>, Box<dyn std::error::Error>> {
    // Check ANUBIS_PASSWORD first
    if let Ok(password) = std::env::var(ENV_ANUBIS_PASSWORD) {
        if !password.is_empty() {
            return Ok(Some(password));
        }
    }

    // Check ANUBIS_PASSWORD_FILE
    if let Ok(path) = std::env::var(ENV_ANUBIS_PASSWORD_FILE) {
        if !path.is_empty() {
            let file = std::fs::File::open(&path)
                .map_err(|e| format!("Failed to open password file '{}': {}", path, e))?;
            let reader = std::io::BufReader::new(file);
            if let Some(Ok(line)) = reader.lines().next() {
                let password = line.trim_end_matches('\n').trim_end_matches('\r').to_string();
                if !password.is_empty() {
                    return Ok(Some(password));
                }
            }
            return Err(format!("Password file '{}' is empty", path).into());
        }
    }

    Ok(None)
}

/// Prompt for a password without echoing to the terminal.
///
/// First checks environment variables, then prompts interactively.
/// Returns the password as a zeroizable string.
fn prompt_password(prompt: &str) -> Result<String, Box<dyn std::error::Error>> {
    // Check environment first
    if let Some(password) = get_password_from_env()? {
        return Ok(password);
    }

    // Interactive prompt
    eprint!("{}", prompt);
    io::stderr().flush()?;
    let password = rpassword::read_password()?;
    Ok(password)
}

/// Prompt for a new password with confirmation.
///
/// In non-interactive mode (env var set), uses the env password without confirmation.
/// In interactive mode, requires the user to enter the password twice.
/// Both password buffers are zeroized after comparison.
fn prompt_new_password() -> Result<String, Box<dyn std::error::Error>> {
    // Check environment first - no confirmation needed for scripted usage
    if let Some(password) = get_password_from_env()? {
        if password.len() < 8 {
            return Err("Password must be at least 8 characters".into());
        }
        return Ok(password);
    }

    // Interactive mode with confirmation
    let mut password1 = prompt_password("Enter password: ")?;
    let mut password2 = prompt_password("Confirm password: ")?;

    if password1 != password2 {
        password1.zeroize();
        password2.zeroize();
        return Err("Passwords do not match".into());
    }

    password2.zeroize();

    if password1.len() < 8 {
        password1.zeroize();
        return Err("Password must be at least 8 characters".into());
    }

    Ok(password1)
}

/// Load the signing keypair from the keystore with password and rate limiting.
///
/// This function:
/// 1. Checks rate limiting and enforces delays after failed attempts
/// 2. Prompts for password
/// 3. Unseals the key using Argon2id + ChaCha20Poly1305
/// 4. Returns the reconstructed KeyPair
fn load_keypair_with_password(ks: &Keystore) -> Result<KeyPair, Box<dyn std::error::Error>> {
    let limiter = ks.rate_limiter();

    // Check rate limit before prompting
    if let Some(wait_duration) = limiter.check_rate_limit() {
        return Err(format!(
            "Too many failed attempts. Please wait {} before trying again.",
            format_delay(wait_duration)
        ).into());
    }

    // Prompt for password
    let mut password = prompt_password("Enter keystore password: ")?;

    // Attempt to unseal
    match ks.unseal_stored_key(password.as_bytes()) {
        Ok(mut seed_bytes) => {
            password.zeroize();
            limiter.record_success()?;

            if seed_bytes.len() != SEED_SIZE {
                // SECURITY: Zeroize seed_bytes before returning error
                seed_bytes.zeroize();
                return Err(format!(
                    "Invalid seed size: expected {}, got {}",
                    SEED_SIZE,
                    seed_bytes.len()
                ).into());
            }

            let mut seed = [0u8; SEED_SIZE];
            seed.copy_from_slice(&seed_bytes);

            // SECURITY: Zeroize the Vec buffer immediately after copying
            seed_bytes.zeroize();

            let kp = KeyPair::from_seed(&seed)
                .map_err(|e| {
                    // Zeroize seed on error path
                    seed.zeroize();
                    format!("Key reconstruction failed: {:?}", e)
                })?;

            // Zeroize seed
            seed.zeroize();

            Ok(kp)
        }
        Err(e) => {
            password.zeroize();

            // Check if this was a decryption failure (wrong password)
            let err_str = e.to_string();
            if err_str.contains("DecryptionFailed") || err_str.contains("unseal failed") {
                let failures = limiter.record_failure()?;
                let delay = RateLimiter::delay_seconds(failures);

                if delay > 0 {
                    Err(format!(
                        "Wrong password ({} failed attempts). Next attempt allowed in {} seconds.",
                        failures, delay
                    ).into())
                } else {
                    Err(format!("Wrong password ({} failed attempts).", failures).into())
                }
            } else {
                Err(e.into())
            }
        }
    }
}
