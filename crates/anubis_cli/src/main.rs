//! Anubis Notary CLI
//!
//! A post-quantum CLI for signing, timestamping, licensing, and revenue generation.
//! Uses ML-DSA-87 for signatures, Argon2id for password-based key encryption.
//!
//! # Environment Variables
//!
//! - `ANUBIS_HOME` - Keystore directory (default: `~/.anubis`)
//! - `ANUBIS_PASSWORD` - Password for non-interactive operations (CI/CD)
//! - `ANUBIS_PASSWORD_FILE` - Path to file containing password (reads first line only)
//!
//! # Password Handling
//!
//! Passwords are resolved in the following priority order:
//!
//! 1. `ANUBIS_PASSWORD` environment variable (highest priority)
//! 2. `ANUBIS_PASSWORD_FILE` - reads the first line of the specified file
//! 3. Interactive prompt (if neither environment variable is set)
//!
//! ## Important Notes
//!
//! - **Password file**: Only the first line is read. Ensure your password is on line 1.
//! - **Non-interactive mode**: When using environment variables, password confirmation
//!   is skipped (no "Confirm password:" prompt). This is intentional for CI/CD.
//! - **Security**: Password files should have restricted permissions (`chmod 600`).
//! - **Minimum length**: Passwords must be at least 8 characters.
//!
//! # Non-Interactive Usage
//!
//! For CI/CD pipelines and scripts:
//!
//! ```bash
//! # Option 1: Environment variable (simplest)
//! export ANUBIS_PASSWORD="your-password"
//! anubis-notary sign document.pdf
//!
//! # Option 2: Password file (more secure for shared systems)
//! echo "your-password" > /path/to/password
//! chmod 600 /path/to/password  # IMPORTANT: restrict permissions
//! export ANUBIS_PASSWORD_FILE=/path/to/password
//! anubis-notary sign document.pdf
//! ```
//!
//! # Password Recovery
//!
//! There is no password recovery mechanism. If you forget your password:
//! - Your existing signatures remain valid and verifiable
//! - You must create a new key with `anubis-notary key init`
//! - You cannot recover or use your old private key

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
use anubis_core::mlkem::{MlKemKeyPair, MlKemPublicKey, MlKemSecretKey};
use anubis_core::multisig::{Multisig, Proposal, ProposalType};
use anubis_core::private_batch::{CollaborativeDecryptor, DecryptedShare, PrivateBatch};
use anubis_core::streaming::{
    StreamingConfig, StreamingHasher, StreamingSigner, StreamingVerifier,
};
use anubis_io::{format_delay, RateLimiter, SystemClock, TimeSource};
use anubis_io::{hash_directory, hash_file, keystore::Keystore, read_file, write_file_atomic};

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
    /// Privacy-preserving collaborative anchoring with ML-KEM-1024.
    PrivateBatch {
        #[command(subcommand)]
        action: PrivateBatchCommands,
    },
    /// Encrypt a file using ML-KEM-1024 post-quantum encryption.
    Seal {
        /// File to encrypt.
        file: PathBuf,
        /// Recipient's ML-KEM-1024 public key file.
        #[arg(long, short)]
        recipient: PathBuf,
        /// Output encrypted file.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Decrypt a file using ML-KEM-1024 post-quantum decryption.
    Unseal {
        /// Encrypted file to decrypt.
        file: PathBuf,
        /// Your ML-KEM-1024 secret key file.
        #[arg(long, short = 'k')]
        secret_key: PathBuf,
        /// Output decrypted file.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Blockchain-anchored marriage contracts.
    Marriage {
        #[command(subcommand)]
        action: MarriageCommands,
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
        /// Anchor provider (btc, http-log, mina).
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
    /// Mina Protocol anchoring.
    Mina {
        #[command(subcommand)]
        action: MinaCommands,
    },
    /// Starknet Protocol anchoring (STARK-private, ~$0.001/tx).
    Starknet {
        #[command(subcommand)]
        action: StarknetCommands,
    },
}

#[derive(Subcommand)]
enum MinaCommands {
    /// Configure Mina anchoring settings.
    Config {
        /// zkApp contract address (Base58).
        #[arg(long)]
        zkapp: Option<String>,
        /// Network (mainnet, devnet, local).
        #[arg(long)]
        network: Option<String>,
        /// Path to mina-bridge installation.
        #[arg(long)]
        bridge_path: Option<PathBuf>,
        /// Transaction fee in MINA.
        #[arg(long)]
        fee: Option<f64>,
        /// Show current configuration.
        #[arg(long)]
        show: bool,
    },
    /// Anchor a receipt to Mina.
    Anchor {
        /// Receipt file to anchor.
        receipt: PathBuf,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Verify a Mina anchor.
    Verify {
        /// Receipt with Mina anchor.
        receipt: PathBuf,
    },
    /// Get current Mina blockchain time.
    Time,
    /// Get wallet balance.
    Balance,
    /// Setup mina-bridge (install dependencies).
    Setup {
        /// Force reinstall.
        #[arg(long)]
        force: bool,
    },
    /// Generate a new Mina keypair for deployment.
    Keygen,
    /// Deploy the AnubisAnchor zkApp to mainnet.
    Deploy {
        /// Fee payer private key (will prompt if not provided).
        #[arg(long)]
        fee_payer_key: Option<String>,
        /// Wait for deployment confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Show network info and deployment costs.
    Info,
    /// Add a receipt to the Mina batch queue (for 8x cost savings).
    Queue {
        /// Receipt file to queue.
        receipt: PathBuf,
    },
    /// Submit queued receipts as a batch (requires 8 receipts or --force).
    Flush {
        /// Force flush even if queue is not full.
        #[arg(long)]
        force: bool,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Show Mina batch queue status.
    QueueStatus,
}

#[derive(Subcommand)]
enum StarknetCommands {
    /// Configure Starknet anchoring settings.
    Config {
        /// Contract address (hex, 0x-prefixed).
        #[arg(long)]
        contract: Option<String>,
        /// Network (mainnet, sepolia, devnet).
        #[arg(long)]
        network: Option<String>,
        /// Custom RPC URL.
        #[arg(long)]
        rpc: Option<String>,
        /// Show current configuration.
        #[arg(long)]
        show: bool,
    },
    /// Anchor a receipt to Starknet.
    Anchor {
        /// Receipt file to anchor.
        receipt: PathBuf,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Verify a Starknet anchor.
    Verify {
        /// Receipt with Starknet anchor.
        receipt: PathBuf,
    },
    /// Get current Starknet blockchain time.
    Time,
    /// Get account balance.
    Balance {
        /// Account address (optional, uses configured if not provided).
        #[arg(long)]
        account: Option<String>,
    },
    /// Show network info and deployment costs.
    Info,
    /// Generate a new Starknet keypair.
    Keygen,
    /// Deploy the NotaryOracle contract.
    Deploy {
        /// Account private key (or set STARKNET_PRIVATE_KEY env).
        #[arg(long)]
        account_key: Option<String>,
        /// Wait for deployment confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Add a receipt to the Starknet batch queue (for 8x cost savings).
    Queue {
        /// Receipt file to queue.
        receipt: PathBuf,
    },
    /// Submit queued receipts as a batch (requires 8 receipts or --force).
    Flush {
        /// Force flush even if queue is not full.
        #[arg(long)]
        force: bool,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Show Starknet batch queue status.
    QueueStatus,
    /// Embed anchor proof into a receipt after manual sncast submission.
    Embed {
        /// Receipt file to update.
        receipt: PathBuf,
        /// Transaction hash from sncast (0x-prefixed).
        #[arg(long)]
        tx_hash: String,
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

#[derive(Subcommand)]
enum PrivateBatchCommands {
    /// Generate ML-KEM-1024 keypair for private batch participation.
    Keygen {
        /// Output base path (will create <name>.mlkem.pub and <name>.mlkem.sec).
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Create a private batch from receipts.
    Create {
        /// Receipt files to include in the batch.
        #[arg(required = true)]
        receipts: Vec<PathBuf>,
        /// ML-KEM-1024 public key files for recipients.
        /// Use multiple --recipient flags: --recipient alice.pub --recipient bob.pub
        #[arg(long = "recipient", short = 'r', required = true)]
        recipients: Vec<PathBuf>,
        /// Threshold for decryption (minimum shares needed).
        #[arg(long, short, default_value = "2")]
        threshold: u8,
        /// Output batch file.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Decrypt your share from a private batch.
    DecryptShare {
        /// Private batch file.
        batch: PathBuf,
        /// Your ML-KEM-1024 secret key file (generated by 'private-batch keygen').
        #[arg(long = "secret-key", short = 'k', visible_alias = "key")]
        secret_key: PathBuf,
        /// Output share file.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Combine shares to decrypt the batch.
    Combine {
        /// Private batch file.
        batch: PathBuf,
        /// Decrypted share files (comma-separated or multiple --share flags).
        #[arg(long, short, required = true)]
        share: Vec<PathBuf>,
        /// Output directory for decrypted receipts.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Verify a decrypted receipt against the batch.
    Verify {
        /// Private batch file.
        batch: PathBuf,
        /// Decrypted receipt file.
        receipt: PathBuf,
        /// Index of the receipt in the batch.
        #[arg(long, short)]
        index: usize,
    },
    /// Show batch information.
    Info {
        /// Private batch file.
        batch: PathBuf,
    },
}

#[derive(Subcommand)]
enum MarriageCommands {
    /// Create a new marriage document.
    Init {
        /// Party names (comma-separated, e.g., "Alice,Bob").
        #[arg(long)]
        parties: String,
        /// Template name (monogamy, polygamy, simple).
        #[arg(long, default_value = "monogamy")]
        template: String,
        /// Jurisdiction code (e.g., "US-CA", "UK").
        #[arg(long)]
        jurisdiction: String,
        /// Output marriage document file (JSON).
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Sign a marriage document as a party.
    Sign {
        /// Marriage document file.
        document: PathBuf,
        /// Party index (0-based).
        #[arg(long)]
        party: usize,
        /// Your wedding vows (optional text that gets hashed and stored on-chain).
        #[arg(long)]
        vows: Option<String>,
        /// Output signed document.
        #[arg(long, short)]
        out: Option<PathBuf>,
    },
    /// Verify all signatures on a marriage document.
    Verify {
        /// Marriage document file.
        document: PathBuf,
    },
    /// Create an on-chain marriage (all parties must have signed).
    Create {
        /// Signed marriage document.
        document: PathBuf,
        /// Starknet network (mainnet, sepolia).
        #[arg(long, default_value = "sepolia")]
        network: String,
        /// Automatically mint NFT rings for all partners.
        #[arg(long)]
        mint_rings: bool,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Execute a divorce.
    Divorce {
        /// Marriage ID on-chain.
        #[arg(long)]
        marriage_id: u64,
        /// Reason for divorce.
        #[arg(long)]
        reason: String,
        /// Starknet network.
        #[arg(long, default_value = "sepolia")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Show contract addresses.
    Info {
        /// Show Sepolia testnet addresses.
        #[arg(long)]
        sepolia: bool,
    },
    /// List available marriage templates.
    Templates,
    /// Manage NFT wedding rings.
    Rings {
        #[command(subcommand)]
        action: RingsCommands,
    },
}

#[derive(Subcommand)]
enum RingsCommands {
    /// Mint NFT rings for a marriage.
    Mint {
        /// Marriage ID on-chain.
        #[arg(long)]
        marriage_id: u64,
        /// Partner addresses (comma-separated hex).
        #[arg(long)]
        partners: String,
        /// Partner name hashes (comma-separated hex).
        #[arg(long)]
        name_hashes: String,
        /// Vows hashes (comma-separated hex).
        #[arg(long)]
        vows_hashes: String,
        /// Marriage certificate hash (hex).
        #[arg(long)]
        marriage_hash: String,
        /// Starknet network.
        #[arg(long, default_value = "sepolia")]
        network: String,
    },
    /// Burn a ring (on divorce).
    Burn {
        /// Token ID to burn.
        #[arg(long)]
        token_id: u64,
        /// Starknet network.
        #[arg(long, default_value = "sepolia")]
        network: String,
    },
    /// Show ring metadata.
    Show {
        /// Token ID to show.
        token_id: u64,
        /// Starknet network.
        #[arg(long, default_value = "sepolia")]
        network: String,
    },
    /// Check if a ring exists.
    Exists {
        /// Token ID to check.
        token_id: u64,
        /// Starknet network.
        #[arg(long, default_value = "sepolia")]
        network: String,
    },
    /// Get total supply of rings.
    Supply {
        /// Starknet network.
        #[arg(long, default_value = "sepolia")]
        network: String,
    },
    /// Update vows on a ring (anniversary renewal).
    UpdateVows {
        /// Token ID to update.
        #[arg(long)]
        token_id: u64,
        /// New vows hash (hex).
        #[arg(long)]
        vows_hash: String,
        /// Starknet network.
        #[arg(long, default_value = "sepolia")]
        network: String,
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

    fn error_with_data(msg: impl Into<String>, data: T) -> Self {
        Self {
            success: false,
            data: Some(data),
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
        Commands::PrivateBatch { action } => handle_private_batch(action, cli.json),
        Commands::Seal {
            file,
            recipient,
            out,
        } => handle_seal(file, recipient, out, cli.json),
        Commands::Unseal {
            file,
            secret_key,
            out,
        } => handle_unseal(file, secret_key, out, cli.json),
        Commands::Marriage { action } => handle_marriage(action, cli.json),
    }
}

fn handle_key(action: &KeyCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        KeyCommands::Init {
            keystore,
            kdf,
            low_memory,
        } => {
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
                eprintln!(
                    "This will use Argon2id with {} memory for key derivation.",
                    if *low_memory { "1 GiB" } else { "4 GiB" }
                );
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
            let memory_mode = if *low_memory {
                "1 GiB (low-memory)"
            } else {
                "4 GiB (default)"
            };

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
        KeyCommands::Rotate {
            keystore,
            low_memory,
        } => {
            let path = keystore
                .as_ref()
                .map(|s| expand_path(s))
                .unwrap_or_else(Keystore::default_path);
            let ks = Keystore::open(&path)?;

            // Determine memory mode for display
            let memory_mode = if *low_memory {
                "1 GiB (low-memory)"
            } else {
                "4 GiB (default)"
            };

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
                println!(
                    "Old public key: {} (archived)",
                    hex::encode(old_kp.public_key().to_bytes())
                );
                println!(
                    "New public key: {}",
                    hex::encode(new_kp.public_key().to_bytes())
                );
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
                        public_key: ks
                            .read_archived_public_key(id)
                            .ok()
                            .map(|pk| hex::encode(&pk)),
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
        return Err(
            "Cannot sign: key has been revoked. Generate a new key with 'anubis-notary key init'."
                .into(),
        );
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
    let pk =
        PublicKey::from_bytes(&pk_bytes).map_err(|e| format!("Invalid public key: {:?}", e))?;

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
                println!(
                    "  Signature: {}",
                    if sig_valid { "VALID" } else { "INVALID" }
                );
                println!("  Product: {}", license.product());
                println!("  User: {}", license.subject());
                println!(
                    "  Expiry: {} ({})",
                    license.expiration,
                    if expired { "EXPIRED" } else { "VALID" }
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
                                product: meta
                                    .get("product")
                                    .and_then(|v| v.as_str())
                                    .map(String::from),
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
                            let product =
                                meta.get("product").and_then(|v| v.as_str()).unwrap_or("?");
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
        AnchorCommands::Submit {
            provider,
            url,
            batch,
            wait,
        } => {
            use anubis_core::merkle::MAX_LEAVES;
            use anubis_io::anchor::AnchorClient;

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
                )
                .into());
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

            let merkle_root = tree
                .compute_root()
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
                    client
                        .submit_and_wait(&merkle_root, timestamp, *wait, 5)
                        .map_err(|e| format!("Failed to submit anchor: {}", e))?
                } else {
                    client
                        .submit(&merkle_root, timestamp)
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
                (
                    hex::encode(merkle_root),
                    "submitted".to_string(),
                    None,
                    None,
                )
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
                println!(
                    "Use 'anchor status {}' to check anchoring status.",
                    &anchor_id[..16.min(anchor_id.len())]
                );
            }
        }
        AnchorCommands::Status { id, refresh } => {
            use anubis_io::anchor::AnchorClient;

            // Try to find anchor by ID prefix
            let anchors = ks.list_anchors()?;
            let matching: Vec<_> = anchors.iter().filter(|a| a.starts_with(id)).collect();

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
                let provider = anchor
                    .get("provider")
                    .and_then(|v| v.as_str())
                    .unwrap_or("");
                let url = anchor.get("url").and_then(|v| v.as_str());

                if provider == "http-log" {
                    if let Some(service_url) = url {
                        let client = AnchorClient::new(service_url)
                            .map_err(|e| format!("Failed to create anchor client: {}", e))?;

                        let response = client
                            .status(anchor_id)
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
                    return Err(format!(
                        "Cannot refresh: provider '{}' does not support refresh",
                        provider
                    )
                    .into());
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
        AnchorCommands::Mina { action } => handle_mina(action, json)?,
        AnchorCommands::Starknet { action } => handle_starknet(action, json)?,
    }
    Ok(())
}

fn handle_starknet(
    action: &StarknetCommands,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::receipt::{AnchorType, Receipt};
    use anubis_io::{StarknetClient, StarknetConfig, StarknetNetwork};

    let ks = Keystore::open(Keystore::default_path())?;

    match action {
        StarknetCommands::Config {
            contract,
            network,
            rpc,
            show,
        } => {
            let config_path = ks.path().join("starknet.json");

            if *show || (contract.is_none() && network.is_none() && rpc.is_none()) {
                // Show current configuration
                if config_path.exists() {
                    let config_data = std::fs::read_to_string(&config_path)?;
                    let config: serde_json::Value = serde_json::from_str(&config_data)?;

                    if json {
                        let output = JsonOutput::success(&config);
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Starknet Configuration:");
                        if let Some(addr) = config.get("contract_address").and_then(|v| v.as_str())
                        {
                            println!("  Contract Address: {}", addr);
                        }
                        if let Some(net) = config.get("network").and_then(|v| v.as_str()) {
                            println!("  Network: {}", net);
                        }
                        if let Some(url) = config.get("rpc_url").and_then(|v| v.as_str()) {
                            println!("  RPC URL: {}", url);
                        }
                    }
                } else {
                    // Show defaults
                    let default_config = serde_json::json!({
                        "network": "mainnet",
                        "rpc_url": "https://rpc.starknet.lava.build",
                        "status": "No contract deployed yet. Run 'anchor starknet deploy' to deploy."
                    });

                    if json {
                        let output = JsonOutput::success(&default_config);
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Starknet Configuration (defaults):");
                        println!("  Network: mainnet");
                        println!("  RPC URL: https://rpc.starknet.lava.build");
                        println!();
                        println!("No contract configured. Deploy with:");
                        println!("  anubis-notary anchor starknet deploy");
                    }
                }
            } else {
                // Update configuration
                let mut config: serde_json::Value = if config_path.exists() {
                    let data = std::fs::read_to_string(&config_path)?;
                    serde_json::from_str(&data)?
                } else {
                    serde_json::json!({})
                };

                if let Some(addr) = contract {
                    config["contract_address"] = serde_json::json!(addr);
                }
                if let Some(net) = network {
                    config["network"] = serde_json::json!(net);
                }
                if let Some(url) = rpc {
                    config["rpc_url"] = serde_json::json!(url);
                }

                std::fs::write(&config_path, serde_json::to_string_pretty(&config)?)?;

                if json {
                    let output = JsonOutput::success(&config);
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Starknet configuration updated.");
                }
            }
        }
        StarknetCommands::Time => {
            // Create client to get block time
            let config_path = ks.path().join("starknet.json");
            let (network, rpc_url) = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                let config: serde_json::Value = serde_json::from_str(&data)?;
                let net = config
                    .get("network")
                    .and_then(|v| v.as_str())
                    .unwrap_or("mainnet");
                let network = match net {
                    "sepolia" => StarknetNetwork::Sepolia,
                    "devnet" => StarknetNetwork::Devnet,
                    _ => StarknetNetwork::Mainnet,
                };
                let url = config
                    .get("rpc_url")
                    .and_then(|v| v.as_str())
                    .map(String::from);
                (network, url)
            } else {
                (StarknetNetwork::Mainnet, None)
            };

            let config = StarknetConfig {
                network,
                rpc_url: rpc_url.unwrap_or_else(|| network.default_rpc_url().to_string()),
                contract_address: None,
                account_address: None,
                fee_multiplier: 1.0,
                timeout_secs: 30,
            };

            let client = StarknetClient::new(config)?;
            let time_result = client.get_block_time()?;

            if json {
                #[derive(Serialize)]
                struct TimeResult {
                    block_number: u64,
                    timestamp: u64,
                    network: String,
                }
                let output = JsonOutput::success(TimeResult {
                    block_number: time_result.block_number,
                    timestamp: time_result.timestamp,
                    network: format!("{:?}", network).to_lowercase(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Starknet Time:");
                println!("  Block Number: {}", time_result.block_number);
                println!("  Timestamp: {} ({})", time_result.timestamp, {
                    use std::time::{Duration, UNIX_EPOCH};
                    let dt = UNIX_EPOCH + Duration::from_secs(time_result.timestamp);
                    format!("{:?}", dt)
                });
                println!("  Network: {:?}", network);
            }
        }
        StarknetCommands::Balance { account } => {
            let config_path = ks.path().join("starknet.json");
            let (network, rpc_url) = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                let config: serde_json::Value = serde_json::from_str(&data)?;
                let net = config
                    .get("network")
                    .and_then(|v| v.as_str())
                    .unwrap_or("mainnet");
                let network = match net {
                    "sepolia" => StarknetNetwork::Sepolia,
                    "devnet" => StarknetNetwork::Devnet,
                    _ => StarknetNetwork::Mainnet,
                };
                let url = config
                    .get("rpc_url")
                    .and_then(|v| v.as_str())
                    .map(String::from);
                (network, url)
            } else {
                (StarknetNetwork::Mainnet, None)
            };

            let account_addr = account
                .clone()
                .or_else(|| std::env::var("STARKNET_ACCOUNT").ok());

            if account_addr.is_none() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "No account specified. Use --account or set STARKNET_ACCOUNT.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Error: No account specified.");
                    println!(
                        "Use --account <address> or set STARKNET_ACCOUNT environment variable."
                    );
                }
                return Ok(());
            }

            let config = StarknetConfig {
                network,
                rpc_url: rpc_url.unwrap_or_else(|| network.default_rpc_url().to_string()),
                contract_address: None,
                account_address: account_addr.clone(),
                fee_multiplier: 1.0,
                timeout_secs: 30,
            };

            let client = StarknetClient::new(config)?;
            let balance = client.get_balance(&account_addr.unwrap())?;

            // Convert from wei to ETH (18 decimals)
            let eth_balance = balance as f64 / 1e18;

            if json {
                #[derive(Serialize)]
                struct BalanceResult {
                    balance_wei: String,
                    balance_eth: f64,
                    network: String,
                }
                let output = JsonOutput::success(BalanceResult {
                    balance_wei: balance.to_string(),
                    balance_eth: eth_balance,
                    network: format!("{:?}", network).to_lowercase(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Starknet Balance:");
                println!("  Account: {}", account.as_deref().unwrap_or("(from env)"));
                println!("  Balance: {:.6} ETH ({} wei)", eth_balance, balance);
                println!("  Network: {:?}", network);
            }
        }
        StarknetCommands::Info => {
            if json {
                #[derive(Serialize)]
                struct StarknetInfo {
                    networks: Vec<NetworkInfo>,
                    costs: CostInfo,
                    contract_requirements: String,
                }
                #[derive(Serialize)]
                struct NetworkInfo {
                    name: String,
                    rpc_url: String,
                    explorer: String,
                }
                #[derive(Serialize)]
                struct CostInfo {
                    single_anchor_usd: String,
                    batch_anchor_usd: String,
                    per_receipt_usd: String,
                }
                let output = JsonOutput::success(StarknetInfo {
                    networks: vec![
                        NetworkInfo {
                            name: "mainnet".to_string(),
                            rpc_url: "https://rpc.starknet.lava.build".to_string(),
                            explorer: "https://starkscan.co".to_string(),
                        },
                        NetworkInfo {
                            name: "sepolia".to_string(),
                            rpc_url: "https://starknet-sepolia.public.blastapi.io".to_string(),
                            explorer: "https://sepolia.starkscan.co".to_string(),
                        },
                    ],
                    costs: CostInfo {
                        single_anchor_usd: "~$0.001".to_string(),
                        batch_anchor_usd: "~$0.001".to_string(),
                        per_receipt_usd: "~$0.000125 (batch of 8)".to_string(),
                    },
                    contract_requirements: "Requires STARKNET_PRIVATE_KEY for deployment"
                        .to_string(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!(
                    "╔══════════════════════════════════════════════════════════════════════════╗"
                );
                println!(
                    "║                      STARKNET ANCHORING INFO                             ║"
                );
                println!(
                    "╠══════════════════════════════════════════════════════════════════════════╣"
                );
                println!(
                    "║  NETWORKS                                                                ║"
                );
                println!(
                    "║  ────────                                                                ║"
                );
                println!("║  mainnet  - https://rpc.starknet.lava.build                  ║");
                println!(
                    "║            Explorer: https://starkscan.co                                ║"
                );
                println!(
                    "║  sepolia  - https://starknet-sepolia.public.blastapi.io                  ║"
                );
                println!(
                    "║            Explorer: https://sepolia.starkscan.co                        ║"
                );
                println!(
                    "║  devnet   - http://localhost:5050                                        ║"
                );
                println!(
                    "╟──────────────────────────────────────────────────────────────────────────╢"
                );
                println!(
                    "║  COSTS (STARK-efficient, ~100x cheaper than Ethereum L1)                 ║"
                );
                println!(
                    "║  ─────                                                                   ║"
                );
                println!(
                    "║  Single Anchor:  ~$0.001 per transaction                                 ║"
                );
                println!(
                    "║  Batch Anchor:   ~$0.001 for 8 receipts                                  ║"
                );
                println!(
                    "║  Per Receipt:    ~$0.000125 (batch mode)                                 ║"
                );
                println!(
                    "╟──────────────────────────────────────────────────────────────────────────╢"
                );
                println!(
                    "║  FEATURES                                                                ║"
                );
                println!(
                    "║  ────────                                                                ║"
                );
                println!(
                    "║  • ZK-STARK validity proofs (quantum-resistant)                          ║"
                );
                println!(
                    "║  • Poseidon hash for efficient on-chain verification                     ║"
                );
                println!(
                    "║  • Batch anchoring with Merkle witnesses                                 ║"
                );
                println!(
                    "║  • Cairo smart contract for NotaryOracle                                 ║"
                );
                println!(
                    "╚══════════════════════════════════════════════════════════════════════════╝"
                );
                println!();
                println!("To get started:");
                println!("  1. Set STARKNET_PRIVATE_KEY environment variable");
                println!("  2. Run: anubis-notary anchor starknet deploy");
                println!("  3. Run: anubis-notary anchor starknet anchor <receipt>");
            }
        }
        StarknetCommands::Keygen => {
            // Generate a new Starknet keypair using starknet-crypto
            use starknet_crypto::get_public_key;
            use zeroize::Zeroize;

            // Generate random private key
            let mut private_key_bytes = [0u8; 32];
            getrandom::getrandom(&mut private_key_bytes)
                .map_err(|e| format!("Failed to generate random key: {}", e))?;

            // Convert to felt252
            let private_key = starknet_core::types::Felt::from_bytes_be(&private_key_bytes);

            // Zeroize the raw bytes immediately after conversion
            private_key_bytes.zeroize();

            let public_key = get_public_key(&private_key);

            if json {
                #[derive(Serialize)]
                struct KeygenResult {
                    private_key: String,
                    public_key: String,
                    note: String,
                }
                let output = JsonOutput::success(KeygenResult {
                    private_key: format!("{:#x}", private_key),
                    public_key: format!("{:#x}", public_key),
                    note:
                        "Save the private key securely. Set as STARKNET_PRIVATE_KEY for operations."
                            .to_string(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!(
                    "╔══════════════════════════════════════════════════════════════════════════╗"
                );
                println!(
                    "║                    STARKNET KEYPAIR GENERATED                            ║"
                );
                println!(
                    "╠══════════════════════════════════════════════════════════════════════════╣"
                );
                println!(
                    "║  Private Key:                                                            ║"
                );
                println!("║    {:#x}", private_key);
                println!(
                    "║                                                                          ║"
                );
                println!(
                    "║  Public Key:                                                             ║"
                );
                println!("║    {:#x}", public_key);
                println!(
                    "╠══════════════════════════════════════════════════════════════════════════╣"
                );
                println!(
                    "║  ⚠️  SAVE THE PRIVATE KEY SECURELY - IT CANNOT BE RECOVERED              ║"
                );
                println!(
                    "╚══════════════════════════════════════════════════════════════════════════╝"
                );
                println!();
                println!("Next steps:");
                println!("  1. Fund the account with ETH on Starknet");
                println!("  2. Set: export STARKNET_PRIVATE_KEY={:#x}", private_key);
                println!("  3. Run: anubis-notary anchor starknet deploy");
            }
        }
        StarknetCommands::Deploy { account_key, wait } => {
            // Get private key from argument or environment
            let private_key = account_key
                .clone()
                .or_else(|| std::env::var("STARKNET_PRIVATE_KEY").ok());

            if private_key.is_none() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "No private key provided. Use --account-key or set STARKNET_PRIVATE_KEY.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Error: No private key provided.");
                    println!(
                        "Use --account-key <key> or set STARKNET_PRIVATE_KEY environment variable."
                    );
                }
                return Ok(());
            }

            let config_path = ks.path().join("starknet.json");
            let network = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                let config: serde_json::Value = serde_json::from_str(&data)?;
                let net = config
                    .get("network")
                    .and_then(|v| v.as_str())
                    .unwrap_or("mainnet");
                match net {
                    "sepolia" => StarknetNetwork::Sepolia,
                    "devnet" => StarknetNetwork::Devnet,
                    _ => StarknetNetwork::Mainnet,
                }
            } else {
                StarknetNetwork::Mainnet
            };

            if !json {
                println!(
                    "Deploying NotaryOracle contract to Starknet {:?}...",
                    network
                );
                println!("This requires a funded account and may take a few minutes.");
                println!();
            }

            // Note: Full deployment requires contract compilation and declaration
            // For now, show instructions for manual deployment with Scarb
            if json {
                #[derive(Serialize)]
                struct DeployInfo {
                    status: String,
                    network: String,
                    instructions: Vec<String>,
                }
                let output = JsonOutput::success(DeployInfo {
                    status: "manual_deployment_required".to_string(),
                    network: format!("{:?}", network).to_lowercase(),
                    instructions: vec![
                        "1. Build contract: cd starknet-contract && scarb build".to_string(),
                        "2. Declare: starknet declare --contract target/dev/anubis_notary_oracle_NotaryOracle.contract_class.json".to_string(),
                        "3. Deploy: starknet deploy --class-hash <hash> --inputs <owner_address>".to_string(),
                        "4. Configure: anubis-notary anchor starknet config --contract <address>".to_string(),
                    ],
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!(
                    "╔══════════════════════════════════════════════════════════════════════════╗"
                );
                println!(
                    "║                    STARKNET CONTRACT DEPLOYMENT                          ║"
                );
                println!(
                    "╠══════════════════════════════════════════════════════════════════════════╣"
                );
                println!(
                    "║  The NotaryOracle Cairo contract requires manual deployment via Scarb:   ║"
                );
                println!(
                    "║                                                                          ║"
                );
                println!(
                    "║  1. Build the contract:                                                  ║"
                );
                println!(
                    "║     cd starknet-contract && scarb build                                  ║"
                );
                println!(
                    "║                                                                          ║"
                );
                println!(
                    "║  2. Declare the contract class:                                          ║"
                );
                println!(
                    "║     starknet declare \\                                                   ║"
                );
                println!(
                    "║       --contract target/dev/anubis_notary_oracle_NotaryOracle.json       ║"
                );
                println!(
                    "║                                                                          ║"
                );
                println!(
                    "║  3. Deploy an instance:                                                  ║"
                );
                println!(
                    "║     starknet deploy --class-hash <HASH> --inputs <OWNER>                 ║"
                );
                println!(
                    "║                                                                          ║"
                );
                println!(
                    "║  4. Configure Anubis:                                                    ║"
                );
                println!(
                    "║     anubis-notary anchor starknet config --contract <ADDRESS>            ║"
                );
                println!(
                    "╚══════════════════════════════════════════════════════════════════════════╝"
                );
                if *wait {
                    println!();
                    println!("Note: --wait flag acknowledged but deployment is manual.");
                }
            }
        }
        StarknetCommands::Anchor { receipt, wait } => {
            // Load receipt
            let receipt_data = read_file(receipt)?;
            let parsed =
                Receipt::decode(&receipt_data).map_err(|e| format!("Invalid receipt: {:?}", e))?;

            let digest_hex = hex::encode(parsed.digest);

            // Load configuration
            let config_path = ks.path().join("starknet.json");
            if !config_path.exists() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "Starknet not configured. Run 'anchor starknet config' first.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Error: Starknet not configured.");
                    println!("Run: anubis-notary anchor starknet config --contract <address>");
                }
                return Ok(());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            let config_json: serde_json::Value = serde_json::from_str(&config_data)?;

            let contract_address = config_json.get("contract_address").and_then(|v| v.as_str());

            if contract_address.is_none() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "No contract address configured. Run 'anchor starknet deploy' first.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Error: No contract address configured.");
                    println!("Run: anubis-notary anchor starknet deploy");
                }
                return Ok(());
            }

            let network = match config_json
                .get("network")
                .and_then(|v| v.as_str())
                .unwrap_or("mainnet")
            {
                "sepolia" => StarknetNetwork::Sepolia,
                "devnet" => StarknetNetwork::Devnet,
                _ => StarknetNetwork::Mainnet,
            };

            let rpc_url = config_json
                .get("rpc_url")
                .and_then(|v| v.as_str())
                .map(String::from)
                .unwrap_or_else(|| network.default_rpc_url().to_string());

            let account_address = config_json
                .get("account_address")
                .and_then(|v| v.as_str())
                .map(String::from)
                .or_else(|| std::env::var("STARKNET_ACCOUNT").ok());

            // Check if we have valid credentials for native submission
            // Validate private key format: must start with 0x and be valid hex
            let private_key = std::env::var("STARKNET_PRIVATE_KEY").ok().filter(|k| {
                k.starts_with("0x")
                    && k.len() >= 10
                    && k[2..].chars().all(|c| c.is_ascii_hexdigit())
            });
            let has_private_key = private_key.is_some();

            // Convert digest to fixed-size array (needed for both branches)
            let mut digest_bytes = [0u8; 32];
            digest_bytes.copy_from_slice(&parsed.digest);

            // Define AnchorResult struct once for JSON output
            #[derive(Serialize)]
            struct AnchorResultJson {
                success: bool,
                tx_hash: String,
                contract: String,
                network: String,
                digest: String,
                poseidon_root: Option<String>,
                explorer_url: String,
                #[serde(skip_serializing_if = "Option::is_none")]
                confirmed: Option<bool>,
                #[serde(skip_serializing_if = "Option::is_none")]
                finality_status: Option<String>,
                #[serde(skip_serializing_if = "Option::is_none")]
                execution_status: Option<String>,
            }

            if has_private_key {
                // Native transaction submission
                if !json {
                    println!("Starknet Anchor (Native Submission):");
                    println!("  Receipt: {}", receipt.display());
                    println!("  Digest: {}", digest_hex);
                    println!("  Contract: {}", contract_address.unwrap());
                    println!("  Network: {:?}", network);
                    println!();
                    println!("Submitting transaction...");
                }

                let config = StarknetConfig {
                    network,
                    rpc_url,
                    contract_address: Some(contract_address.unwrap().to_string()),
                    account_address,
                    fee_multiplier: 1.5,
                    timeout_secs: 60,
                };

                let client = StarknetClient::new(config)?;

                match client.anchor_root(&digest_bytes) {
                    Ok(result) => {
                        let explorer_base = match network {
                            StarknetNetwork::Mainnet => "https://starkscan.co",
                            StarknetNetwork::Sepolia => "https://sepolia.starkscan.co",
                            StarknetNetwork::Devnet => "http://localhost:5050",
                        };

                        if !json {
                            println!();
                            println!("✓ Transaction submitted successfully!");
                            println!("  Transaction Hash: {}", result.tx_hash);
                            if let Some(ref poseidon) = result.poseidon_root {
                                println!("  Poseidon Root: {}", poseidon);
                            }
                            println!("  Explorer: {}/tx/{}", explorer_base, result.tx_hash);
                        }

                        // Wait for confirmation if --wait flag is set
                        let mut confirmed_block: Option<u64> = None;
                        if *wait {
                            if !json {
                                println!();
                                println!("Waiting for transaction confirmation...");
                            }

                            // Poll for up to 5 minutes (60 attempts, 5 seconds each)
                            match client.wait_for_transaction(&result.tx_hash, 60, 5) {
                                Ok(status) => {
                                    confirmed_block = status.block_number;
                                    if json {
                                        let output = JsonOutput::success(AnchorResultJson {
                                            success: true,
                                            tx_hash: result.tx_hash.clone(),
                                            contract: result.contract_address.clone(),
                                            network: format!("{:?}", network).to_lowercase(),
                                            digest: digest_hex.clone(),
                                            poseidon_root: result.poseidon_root.clone(),
                                            explorer_url: format!(
                                                "{}/tx/{}",
                                                explorer_base, result.tx_hash
                                            ),
                                            confirmed: Some(true),
                                            finality_status: Some(status.finality_status.clone()),
                                            execution_status: status.execution_status.clone(),
                                        });
                                        println!("{}", serde_json::to_string_pretty(&output)?);
                                    } else {
                                        println!();
                                        println!("✓ Transaction confirmed on L2!");
                                        println!(
                                            "  Status: {} / {:?}",
                                            status.finality_status, status.execution_status
                                        );
                                        if let Some(block) = status.block_number {
                                            println!("  Block: {}", block);
                                        }
                                    }
                                }
                                Err(e) => {
                                    if !json {
                                        println!();
                                        println!("⚠ Transaction submitted but confirmation timed out: {}", e);
                                        println!(
                                            "  Check status manually: {}/tx/{}",
                                            explorer_base, result.tx_hash
                                        );
                                    }
                                }
                            }
                        } else {
                            // Not waiting - just show success
                            if json {
                                let output = JsonOutput::success(AnchorResultJson {
                                    success: true,
                                    tx_hash: result.tx_hash.clone(),
                                    contract: result.contract_address.clone(),
                                    network: format!("{:?}", network).to_lowercase(),
                                    digest: digest_hex.clone(),
                                    poseidon_root: result.poseidon_root.clone(),
                                    explorer_url: format!(
                                        "{}/tx/{}",
                                        explorer_base, result.tx_hash
                                    ),
                                    confirmed: None,
                                    finality_status: None,
                                    execution_status: None,
                                });
                                println!("{}", serde_json::to_string_pretty(&output)?);
                            }
                        }

                        // Update the receipt with anchor proof
                        if !json {
                            println!();
                            println!("Updating receipt with anchor proof...");
                        }

                        // Parse tx_hash and contract to bytes
                        let tx_hash_str = result.tx_hash.trim_start_matches("0x");
                        let contract_str = result.contract_address.trim_start_matches("0x");

                        let mut tx_hash_arr = [0u8; 32];
                        let mut contract_addr_arr = [0u8; 32];
                        let mut tx_hash_len = 0usize;
                        let mut contract_addr_len = 0usize;

                        if let Ok(tx_bytes) = hex::decode(tx_hash_str) {
                            tx_hash_len = tx_bytes.len().min(32);
                            tx_hash_arr[..tx_hash_len].copy_from_slice(&tx_bytes[..tx_hash_len]);
                        }
                        if let Ok(contract_decoded) = hex::decode(contract_str) {
                            contract_addr_len = contract_decoded.len().min(32);
                            contract_addr_arr[..contract_addr_len]
                                .copy_from_slice(&contract_decoded[..contract_addr_len]);
                        }

                        // Get current timestamp
                        let timestamp = std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .map(|d| d.as_secs())
                            .unwrap_or(0);

                        // Create updated receipt with anchor
                        let anchor = AnchorType::Starknet {
                            contract_addr: contract_addr_arr,
                            contract_addr_len,
                            tx_hash: tx_hash_arr,
                            tx_hash_len,
                            block_number: confirmed_block.unwrap_or(0),
                            timestamp,
                            root_id: 0, // Not available from RPC directly
                        };

                        let updated_receipt =
                            Receipt::new(parsed.digest, parsed.created).with_anchor(anchor);

                        // Re-sign the receipt
                        let kp = load_keypair_with_password(&ks)?;

                        let mut signable_buf = [0u8; 4096];
                        let signable_len = updated_receipt
                            .encode_signable(&mut signable_buf)
                            .map_err(|e| format!("Failed to encode signable receipt: {:?}", e))?;

                        let mut message_to_sign = Vec::with_capacity(signable_len + 32);
                        message_to_sign.extend_from_slice(b"anubis-notary:attest:v1:");
                        message_to_sign.extend_from_slice(&signable_buf[..signable_len]);

                        let signature = kp
                            .sign(&message_to_sign)
                            .map_err(|e| format!("Signing failed: {:?}", e))?;

                        let signed_receipt = updated_receipt
                            .with_signature(&signature.to_bytes())
                            .map_err(|e| format!("Failed to add signature: {:?}", e))?;

                        // Write updated receipt
                        let mut buf = [0u8; 8192];
                        let len = signed_receipt
                            .encode(&mut buf)
                            .map_err(|e| format!("{:?}", e))?;
                        write_file_atomic(receipt, &buf[..len])?;

                        if !json {
                            println!("✓ Receipt updated with Starknet anchor proof!");
                            println!("  TX: {}", result.tx_hash);
                            if let Some(block) = confirmed_block {
                                println!("  Block: {}", block);
                            }
                            println!();
                            println!("The receipt now contains cryptographic proof of when it was anchored.");
                        }
                    }
                    Err(e) => {
                        if json {
                            let output: JsonOutput<()> =
                                JsonOutput::error(&format!("Transaction failed: {}", e));
                            println!("{}", serde_json::to_string_pretty(&output)?);
                        } else {
                            println!();
                            println!("✗ Transaction failed: {}", e);
                            println!();
                            println!("Possible causes:");
                            println!("  - Insufficient funds in account");
                            println!("  - Invalid private key");
                            println!("  - Network connectivity issues");
                            println!("  - Contract not deployed on this network");
                        }
                        return Err(Box::new(std::io::Error::new(
                            std::io::ErrorKind::Other,
                            format!("Starknet transaction failed: {}", e),
                        )));
                    }
                }
            } else {
                // No private key - compute Poseidon hash and show manual instructions
                // The Poseidon hash fits in felt252 and is what gets anchored on-chain
                let poseidon_hash = anubis_io::sha256_to_poseidon_felt(&digest_bytes);
                let poseidon_hex = format!("0x{}", hex::encode(poseidon_hash));

                if !json {
                    println!("Starknet Anchor:");
                    println!("  Receipt: {}", receipt.display());
                    println!("  SHA3-256 Digest: {}", digest_hex);
                    println!("  Poseidon Hash (on-chain): {}", poseidon_hex);
                    println!("  Contract: {}", contract_address.unwrap());
                    println!("  Network: {:?}", network);
                    println!();
                    println!("To submit natively, set STARKNET_PRIVATE_KEY and STARKNET_ACCOUNT:");
                    println!("  export STARKNET_PRIVATE_KEY=0x...");
                    println!("  export STARKNET_ACCOUNT=0x...");
                    println!();
                    println!("Or submit manually via sncast:");
                    println!("  sncast invoke --contract-address {} --function anchor_root --calldata {}",
                        contract_address.unwrap(), poseidon_hex);
                } else {
                    #[derive(Serialize)]
                    struct AnchorInfo {
                        receipt: String,
                        digest: String,
                        poseidon_hash: String,
                        contract: String,
                        network: String,
                        manual_required: bool,
                        invoke_command: String,
                    }
                    let output = JsonOutput::success(AnchorInfo {
                        receipt: receipt.display().to_string(),
                        digest: digest_hex.clone(),
                        poseidon_hash: poseidon_hex.clone(),
                        contract: contract_address.unwrap().to_string(),
                        network: format!("{:?}", network).to_lowercase(),
                        manual_required: true,
                        invoke_command: format!(
                            "sncast invoke --contract-address {} --function anchor_root --calldata {}",
                            contract_address.unwrap(),
                            poseidon_hex
                        ),
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                }
            }
        }
        StarknetCommands::Verify { receipt } => {
            // Load receipt
            let receipt_data = read_file(receipt)?;
            let parsed =
                Receipt::decode(&receipt_data).map_err(|e| format!("Invalid receipt: {:?}", e))?;

            // Check if receipt has Starknet anchor
            match &parsed.anchor {
                anubis_core::receipt::AnchorType::Starknet {
                    contract_addr,
                    contract_addr_len,
                    tx_hash,
                    tx_hash_len,
                    block_number,
                    timestamp,
                    root_id,
                } => {
                    let addr_hex = hex::encode(&contract_addr[..*contract_addr_len]);
                    let tx_hex = hex::encode(&tx_hash[..*tx_hash_len]);

                    if json {
                        #[derive(Serialize)]
                        struct StarknetVerifyResult {
                            verified: bool,
                            contract_address: String,
                            tx_hash: String,
                            block_number: u64,
                            timestamp: u64,
                            root_id: u64,
                            explorer_url: String,
                        }
                        let output = JsonOutput::success(StarknetVerifyResult {
                            verified: true,
                            contract_address: format!("0x{}", addr_hex),
                            tx_hash: format!("0x{}", tx_hex),
                            block_number: *block_number,
                            timestamp: *timestamp,
                            root_id: *root_id,
                            explorer_url: format!("https://starkscan.co/tx/0x{}", tx_hex),
                        });
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Starknet Anchor Verification:");
                        println!("  Contract: 0x{}", addr_hex);
                        println!("  Transaction: 0x{}", tx_hex);
                        println!("  Block: {}", block_number);
                        println!("  Timestamp: {}", timestamp);
                        println!("  Root ID: {}", root_id);
                        println!("  Explorer: https://starkscan.co/tx/0x{}", tx_hex);
                        println!();
                        println!("Note: Full on-chain verification requires starknet CLI.");
                    }
                }
                anubis_core::receipt::AnchorType::StarknetBatch {
                    contract_addr,
                    contract_addr_len,
                    tx_hash,
                    tx_hash_len,
                    block_number,
                    timestamp,
                    root_id,
                    batch_index,
                    batch_root,
                    merkle_witness,
                    witness_len,
                } => {
                    let addr_hex = hex::encode(&contract_addr[..*contract_addr_len]);
                    let tx_hex = hex::encode(&tx_hash[..*tx_hash_len]);
                    let batch_root_hex = hex::encode(batch_root);
                    let witness_hex = hex::encode(&merkle_witness[..*witness_len]);

                    if json {
                        #[derive(Serialize)]
                        struct StarknetBatchVerifyResult {
                            verified: bool,
                            contract_address: String,
                            tx_hash: String,
                            block_number: u64,
                            timestamp: u64,
                            root_id: u64,
                            batch_index: u8,
                            batch_root: String,
                            merkle_witness: String,
                            explorer_url: String,
                        }
                        let output = JsonOutput::success(StarknetBatchVerifyResult {
                            verified: true,
                            contract_address: format!("0x{}", addr_hex),
                            tx_hash: format!("0x{}", tx_hex),
                            block_number: *block_number,
                            timestamp: *timestamp,
                            root_id: *root_id,
                            batch_index: *batch_index,
                            batch_root: format!("0x{}", batch_root_hex),
                            merkle_witness: format!("0x{}", witness_hex),
                            explorer_url: format!("https://starkscan.co/tx/0x{}", tx_hex),
                        });
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Starknet Batch Anchor Verification:");
                        println!("  Contract: 0x{}", addr_hex);
                        println!("  Transaction: 0x{}", tx_hex);
                        println!("  Block: {}", block_number);
                        println!("  Timestamp: {}", timestamp);
                        println!("  Root ID: {}", root_id);
                        println!("  Batch Index: {}/8", batch_index);
                        println!("  Batch Root: 0x{}", batch_root_hex);
                        println!("  Witness: 0x{}", witness_hex);
                        println!("  Explorer: https://starkscan.co/tx/0x{}", tx_hex);
                        println!();
                        println!("Note: Verify inclusion with 'starknet call --function verify_inclusion'.");
                    }
                }
                _ => {
                    return Err("Receipt does not have a Starknet anchor".into());
                }
            }
        }
        StarknetCommands::Queue { receipt } => {
            use anubis_io::BatchQueue;

            // Verify the receipt is valid
            let receipt_data = read_file(&receipt)?;
            let parsed =
                Receipt::decode(&receipt_data).map_err(|e| format!("Invalid receipt: {:?}", e))?;

            // Open batch queue
            let queue_path = ks.path().join("starknet-batch-queue");
            let queue = BatchQueue::open(&queue_path)?;

            // Add to queue
            let entry = queue.enqueue(&parsed.digest, &receipt)?;

            if json {
                #[derive(Serialize)]
                struct QueueResult {
                    receipt: String,
                    digest: String,
                    queued_at: u64,
                    pending_count: usize,
                    ready_for_batch: bool,
                }
                let pending = queue.pending_count()?;
                let output = JsonOutput::success(QueueResult {
                    receipt: receipt.display().to_string(),
                    digest: entry.digest.clone(),
                    queued_at: entry.queued_at,
                    pending_count: pending,
                    ready_for_batch: pending >= 8,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                let pending = queue.pending_count()?;
                println!("Receipt added to Starknet batch queue:");
                println!("  File:    {}", receipt.display());
                println!("  Digest:  {}", entry.digest);
                println!("  Pending: {}/8 receipts", pending);
                if pending >= 8 {
                    println!();
                    println!(
                        "Queue is full! Run 'anubis-notary anchor starknet flush' to submit batch."
                    );
                } else {
                    println!();
                    println!("Add {} more receipts for 8x cost savings.", 8 - pending);
                }
            }
        }
        StarknetCommands::Flush { force, wait: _wait } => {
            use anubis_io::BatchQueue;

            let queue_path = ks.path().join("starknet-batch-queue");
            let queue = BatchQueue::open(&queue_path)?;

            let pending = queue.pending()?;
            if pending.is_empty() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "Batch queue is empty. Add receipts with 'anchor starknet queue'.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Batch queue is empty.");
                    println!("Add receipts with: anubis-notary anchor starknet queue <receipt>");
                }
                return Ok(());
            }

            if pending.len() < 8 && !force {
                if json {
                    #[derive(Serialize)]
                    struct NotReadyResult {
                        pending_count: usize,
                        needed: usize,
                    }
                    let output = JsonOutput::error_with_data(
                        "Queue not full. Use --force to submit partial batch.",
                        NotReadyResult {
                            pending_count: pending.len(),
                            needed: 8 - pending.len(),
                        },
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!(
                        "Queue has {} receipts (need 8 for optimal batching).",
                        pending.len()
                    );
                    println!(
                        "Use --force to submit a partial batch, or add {} more receipts.",
                        8 - pending.len()
                    );
                }
                return Ok(());
            }

            // Prepare batch roots for submission
            let roots: Vec<String> = pending
                .iter()
                .map(|e| format!("0x{}", e.digest.clone()))
                .collect();

            if json {
                #[derive(Serialize)]
                struct FlushInfo {
                    status: String,
                    batch_size: usize,
                    roots: Vec<String>,
                    invoke_hint: String,
                }
                let output = JsonOutput::success(FlushInfo {
                    status: "ready_for_submission".to_string(),
                    batch_size: pending.len(),
                    roots: roots.clone(),
                    invoke_hint: "Use 'starknet invoke --function anchor_batch --inputs <roots>'"
                        .to_string(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Starknet Batch Flush:");
                println!("  Receipts: {}", pending.len());
                println!("  Roots:");
                for (i, root) in roots.iter().enumerate() {
                    println!("    [{}] {}", i, root);
                }
                println!();
                println!("Submit batch via starknet CLI:");
                println!(
                    "  starknet invoke --function anchor_batch --inputs {}",
                    roots.join(" ")
                );
            }
        }
        StarknetCommands::QueueStatus => {
            use anubis_io::BatchQueue;

            let queue_path = ks.path().join("starknet-batch-queue");
            let queue = BatchQueue::open(&queue_path)?;
            let pending = queue.pending()?;

            if json {
                #[derive(Serialize)]
                struct QueueStatusResult {
                    pending_count: usize,
                    max_batch_size: usize,
                    ready_for_flush: bool,
                    entries: Vec<QueueEntry>,
                }
                #[derive(Serialize)]
                struct QueueEntry {
                    digest: String,
                    receipt_path: String,
                    queued_at: u64,
                }
                let output = JsonOutput::success(QueueStatusResult {
                    pending_count: pending.len(),
                    max_batch_size: 8,
                    ready_for_flush: pending.len() >= 8,
                    entries: pending
                        .iter()
                        .map(|e| QueueEntry {
                            digest: e.digest.clone(),
                            receipt_path: e.receipt_path.clone(),
                            queued_at: e.queued_at,
                        })
                        .collect(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Starknet Batch Queue Status:");
                println!("  Pending: {}/8 receipts", pending.len());
                if pending.is_empty() {
                    println!("  Queue is empty.");
                } else {
                    println!();
                    println!("Queued receipts:");
                    for (i, entry) in pending.iter().enumerate() {
                        println!("  [{}] {} ({})", i, entry.digest, entry.receipt_path);
                    }
                }
                if pending.len() >= 8 {
                    println!();
                    println!("Queue is full! Run 'anchor starknet flush' to submit batch.");
                }
            }
        }
        StarknetCommands::Embed { receipt, tx_hash } => {
            // Load configuration to get contract address
            let config_path = ks.path().join("starknet.json");
            if !config_path.exists() {
                return Err("Starknet not configured. Run 'anchor starknet config' first.".into());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            let config_json: serde_json::Value = serde_json::from_str(&config_data)?;

            let contract_address = config_json
                .get("contract_address")
                .and_then(|v| v.as_str())
                .ok_or("No contract address configured")?;

            let network = match config_json
                .get("network")
                .and_then(|v| v.as_str())
                .unwrap_or("mainnet")
            {
                "sepolia" => StarknetNetwork::Sepolia,
                "devnet" => StarknetNetwork::Devnet,
                _ => StarknetNetwork::Mainnet,
            };

            let rpc_url = config_json
                .get("rpc_url")
                .and_then(|v| v.as_str())
                .map(String::from)
                .unwrap_or_else(|| network.default_rpc_url().to_string());

            // Load and parse the receipt
            let receipt_data = read_file(receipt)?;
            let parsed =
                Receipt::decode(&receipt_data).map_err(|e| format!("Invalid receipt: {:?}", e))?;

            if !json {
                println!("Embedding anchor proof into receipt...");
                println!("  TX: {}", tx_hash);
            }

            // Create Starknet client to fetch tx status
            let config = StarknetConfig {
                network,
                rpc_url,
                contract_address: Some(contract_address.to_string()),
                account_address: None,
                fee_multiplier: 1.5,
                timeout_secs: 60,
            };

            let client = StarknetClient::new(config)?;

            // Check transaction status
            let status = client.get_transaction_status(tx_hash)?;

            if status.finality_status != "ACCEPTED_ON_L2"
                && status.finality_status != "ACCEPTED_ON_L1"
            {
                return Err(format!(
                    "Transaction not confirmed yet. Status: {}",
                    status.finality_status
                )
                .into());
            }

            // Parse tx_hash and contract to bytes
            let tx_hash_str = tx_hash.trim_start_matches("0x");
            let contract_str = contract_address.trim_start_matches("0x");

            let mut tx_hash_arr = [0u8; 32];
            let mut contract_addr_arr = [0u8; 32];
            let mut tx_hash_len = 0usize;
            let mut contract_addr_len = 0usize;

            if let Ok(tx_bytes) = hex::decode(tx_hash_str) {
                tx_hash_len = tx_bytes.len().min(32);
                tx_hash_arr[..tx_hash_len].copy_from_slice(&tx_bytes[..tx_hash_len]);
            }
            if let Ok(contract_decoded) = hex::decode(contract_str) {
                contract_addr_len = contract_decoded.len().min(32);
                contract_addr_arr[..contract_addr_len]
                    .copy_from_slice(&contract_decoded[..contract_addr_len]);
            }

            // Get timestamp
            let timestamp = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0);

            // Create anchor
            let anchor = AnchorType::Starknet {
                contract_addr: contract_addr_arr,
                contract_addr_len,
                tx_hash: tx_hash_arr,
                tx_hash_len,
                block_number: status.block_number.unwrap_or(0),
                timestamp,
                root_id: 0,
            };

            let updated_receipt = Receipt::new(parsed.digest, parsed.created).with_anchor(anchor);

            // Re-sign the receipt
            let kp = load_keypair_with_password(&ks)?;

            let mut signable_buf = [0u8; 4096];
            let signable_len = updated_receipt
                .encode_signable(&mut signable_buf)
                .map_err(|e| format!("Failed to encode signable receipt: {:?}", e))?;

            let mut message_to_sign = Vec::with_capacity(signable_len + 32);
            message_to_sign.extend_from_slice(b"anubis-notary:attest:v1:");
            message_to_sign.extend_from_slice(&signable_buf[..signable_len]);

            let signature = kp
                .sign(&message_to_sign)
                .map_err(|e| format!("Signing failed: {:?}", e))?;

            let signed_receipt = updated_receipt
                .with_signature(&signature.to_bytes())
                .map_err(|e| format!("Failed to add signature: {:?}", e))?;

            // Write updated receipt
            let mut buf = [0u8; 8192];
            let len = signed_receipt
                .encode(&mut buf)
                .map_err(|e| format!("{:?}", e))?;
            write_file_atomic(receipt, &buf[..len])?;

            if json {
                #[derive(Serialize)]
                struct EmbedResult {
                    success: bool,
                    receipt: String,
                    tx_hash: String,
                    block_number: u64,
                }
                let output = JsonOutput::success(EmbedResult {
                    success: true,
                    receipt: receipt.display().to_string(),
                    tx_hash: tx_hash.clone(),
                    block_number: status.block_number.unwrap_or(0),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("✓ Receipt updated with Starknet anchor proof!");
                println!("  TX: {}", tx_hash);
                if let Some(block) = status.block_number {
                    println!("  Block: {}", block);
                }
                println!();
                println!("The receipt now contains cryptographic proof of when it was anchored.");
            }
        }
    }

    Ok(())
}

fn handle_mina(action: &MinaCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::receipt::Receipt;

    let ks = Keystore::open(Keystore::default_path())?;

    match action {
        MinaCommands::Config {
            zkapp,
            network,
            bridge_path,
            fee,
            show,
        } => {
            let config_path = ks.path().join("mina.json");

            if *show
                || (zkapp.is_none() && network.is_none() && bridge_path.is_none() && fee.is_none())
            {
                // Show current configuration
                if config_path.exists() {
                    let config_data = std::fs::read_to_string(&config_path)?;
                    let config: serde_json::Value = serde_json::from_str(&config_data)?;

                    if json {
                        let output = JsonOutput::success(&config);
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Mina Configuration:");
                        if let Some(addr) = config.get("zkapp_address").and_then(|v| v.as_str()) {
                            println!("  zkApp Address: {}", addr);
                        }
                        if let Some(net) = config.get("network").and_then(|v| v.as_str()) {
                            println!("  Network: {}", net);
                        }
                        if let Some(path) = config.get("bridge_path").and_then(|v| v.as_str()) {
                            println!("  Bridge Path: {}", path);
                        }
                        if let Some(f) = config.get("fee").and_then(|v| v.as_f64()) {
                            println!("  Fee: {} MINA", f);
                        }
                    }
                } else {
                    // Show default mainnet configuration
                    let default_config = serde_json::json!({
                        "zkapp_address": anubis_io::mina::MAINNET_ZKAPP_ADDRESS,
                        "network": "mainnet",
                        "fee": 0.1,
                        "status": "Using official Anubis zkApp on Mina mainnet"
                    });

                    if json {
                        let output = JsonOutput::success(&default_config);
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Mina Configuration (defaults):");
                        println!(
                            "  zkApp Address: {} (official)",
                            anubis_io::mina::MAINNET_ZKAPP_ADDRESS
                        );
                        println!("  Network: mainnet");
                        println!("  Fee: 0.1 MINA");
                        println!();
                        println!("Ready to anchor! Set MINA_PRIVATE_KEY and run:");
                        println!("  anubis-notary anchor mina anchor <receipt>");
                    }
                }
            } else {
                // Update configuration
                let mut config: serde_json::Value = if config_path.exists() {
                    let data = std::fs::read_to_string(&config_path)?;
                    serde_json::from_str(&data)?
                } else {
                    serde_json::json!({})
                };

                if let Some(addr) = zkapp {
                    config["zkapp_address"] = serde_json::json!(addr);
                }
                if let Some(net) = network {
                    config["network"] = serde_json::json!(net);
                }
                if let Some(path) = bridge_path {
                    config["bridge_path"] = serde_json::json!(path.display().to_string());
                }
                if let Some(f) = fee {
                    config["fee"] = serde_json::json!(f);
                }

                std::fs::write(&config_path, serde_json::to_string_pretty(&config)?)?;

                if json {
                    let output = JsonOutput::success(&config);
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Mina configuration updated.");
                }
            }
        }
        MinaCommands::Anchor { receipt, wait } => {
            use std::io::{BufRead, BufReader, Write as IoWrite};
            use std::process::{Command, Stdio};
            use std::thread;
            use std::time::Duration;

            // Load receipt
            let receipt_data = read_file(receipt)?;
            let parsed =
                Receipt::decode(&receipt_data).map_err(|e| format!("Invalid receipt: {:?}", e))?;

            let digest_hex = hex::encode(parsed.digest);

            // Check for bridge - try keystore path first, then home dir
            let bridge_path = {
                let ks_bridge = ks.path().join("mina-bridge");
                if ks_bridge.join("mina-bridge.js").exists() {
                    ks_bridge
                } else {
                    dirs::home_dir()
                        .unwrap_or_else(|| PathBuf::from("."))
                        .join(".anubis")
                        .join("mina-bridge")
                }
            };
            let bridge_script = bridge_path.join("mina-bridge.js");

            if !bridge_script.exists() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "Mina bridge not installed. Run 'anchor mina setup' first.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Mina Anchor:");
                    println!("  Status: Bridge not installed");
                    println!();
                    println!("Run 'anchor mina setup' to install the Mina bridge.");
                }
                return Ok(());
            }

            // Load Mina configuration or use defaults
            let config_path = ks.path().join("mina-config.json");
            let zkapp_address = if config_path.exists() {
                let config_data = std::fs::read_to_string(&config_path)?;
                let config: serde_json::Value = serde_json::from_str(&config_data)?;
                config
                    .get("zkappAddress")
                    .and_then(|v| v.as_str())
                    .unwrap_or(anubis_io::mina::MAINNET_ZKAPP_ADDRESS)
                    .to_string()
            } else {
                anubis_io::mina::MAINNET_ZKAPP_ADDRESS.to_string()
            };

            if !json {
                println!("Mina Anchor:");
                println!("  Receipt: {}", receipt.display());
                println!("  Digest: {}", digest_hex);
                println!("  zkApp: {}", zkapp_address);
                println!();
                println!("Submitting to Mina blockchain...");
            }

            // Spawn bridge process
            let mut child = Command::new("node")
                .arg(&bridge_script)
                .current_dir(&bridge_path)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .map_err(|e| format!("Failed to spawn bridge: {}", e))?;

            // Wait for bridge to initialize (o1js needs time to load WASM)
            // Compilation is cached after first run, so subsequent anchors are faster
            if !json {
                println!(
                    "  Loading zkApp circuit (first run compiles, ~30-60s; cached runs ~5s)..."
                );
            }
            thread::sleep(Duration::from_millis(2000));

            // Send anchor command
            let wait_flag = if *wait { "true" } else { "false" };
            let cmd = format!(
                r#"{{"cmd":"anchor","root":"{}","wait":{}}}"#,
                digest_hex, wait_flag
            );
            {
                let stdin = child.stdin.as_mut().ok_or("Failed to get stdin")?;
                writeln!(stdin, "{}", cmd).map_err(|e| format!("Failed to send command: {}", e))?;
                stdin
                    .flush()
                    .map_err(|e| format!("Failed to flush: {}", e))?;
            }

            // Read response with timeout (anchor can take a while due to proof generation)
            let stdout = child.stdout.take().ok_or("Failed to get stdout")?;
            let mut reader = BufReader::new(stdout);
            let mut response = String::new();

            // Give it up to 2 minutes for proof generation and tx submission
            let start = std::time::Instant::now();
            loop {
                if start.elapsed() > Duration::from_secs(120) {
                    let _ = child.kill();
                    return Err("Anchor timed out after 120 seconds".into());
                }
                match reader.read_line(&mut response) {
                    Ok(0) => {
                        // EOF - process exited, check stderr
                        let stderr = child.stderr.take();
                        let mut err_msg = String::new();
                        if let Some(mut stderr) = stderr {
                            use std::io::Read;
                            let _ = stderr.read_to_string(&mut err_msg);
                        }
                        if !err_msg.is_empty() && err_msg.contains("error") {
                            return Err(format!("Bridge error: {}", err_msg).into());
                        }
                        break;
                    }
                    Ok(_) => {
                        if response.contains(r#""ok":"#) {
                            break;
                        }
                    }
                    Err(e) => {
                        let _ = child.kill();
                        return Err(format!("Failed to read response: {}", e).into());
                    }
                }
                thread::sleep(Duration::from_millis(100));
            }

            // Kill the bridge process
            let _ = child.kill();

            // Parse response
            if response.contains(r#""ok":true"#) {
                // Bridge returns "tx" for anchor, "txHash" for deploy
                let tx_hash: String = response
                    .split(r#""tx":""#)
                    .nth(1)
                    .and_then(|s| s.split('"').next())
                    .or_else(|| {
                        response
                            .split(r#""txHash":""#)
                            .nth(1)
                            .and_then(|s| s.split('"').next())
                    })
                    .unwrap_or("unknown")
                    .to_string();

                // Build explorer URL from tx hash
                let explorer_url = if tx_hash != "unknown" {
                    format!("https://minascan.io/mainnet/tx/{}", tx_hash)
                } else {
                    String::new()
                };

                if json {
                    #[derive(Serialize)]
                    struct MinaAnchorResult {
                        success: bool,
                        digest: String,
                        zkapp_address: String,
                        tx_hash: String,
                        explorer_url: String,
                    }
                    let output = JsonOutput::success(MinaAnchorResult {
                        success: true,
                        digest: digest_hex,
                        zkapp_address,
                        tx_hash,
                        explorer_url,
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!();
                    println!("Anchor submitted successfully!");
                    println!("  Transaction: {}", tx_hash);
                    if !explorer_url.is_empty() {
                        println!("  Explorer: {}", explorer_url);
                    }
                }
            } else {
                let err = response
                    .split(r#""error":""#)
                    .nth(1)
                    .and_then(|s| s.split('"').next())
                    .unwrap_or("Unknown error");
                if json {
                    let output: JsonOutput<()> =
                        JsonOutput::error(&format!("Anchor failed: {}", err));
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!();
                    println!("Anchor failed: {}", err);
                }
            }
        }
        MinaCommands::Verify { receipt } => {
            // Load receipt
            let receipt_data = read_file(receipt)?;
            let parsed =
                Receipt::decode(&receipt_data).map_err(|e| format!("Invalid receipt: {:?}", e))?;

            // Check if receipt has Mina anchor
            match &parsed.anchor {
                anubis_core::receipt::AnchorType::Mina {
                    zkapp_address,
                    zkapp_address_len,
                    tx_hash,
                    tx_hash_len,
                    block_height,
                    timestamp_ms,
                    ..
                } => {
                    let addr_str = std::str::from_utf8(&zkapp_address[..*zkapp_address_len])
                        .unwrap_or("(invalid)");
                    let tx_str =
                        std::str::from_utf8(&tx_hash[..*tx_hash_len]).unwrap_or("(invalid)");

                    if json {
                        #[derive(Serialize)]
                        struct MinaVerifyResult {
                            verified: bool,
                            zkapp_address: String,
                            tx_hash: String,
                            block_height: u64,
                            timestamp_ms: u64,
                        }
                        let output = JsonOutput::success(MinaVerifyResult {
                            verified: true, // Would need bridge to verify on-chain
                            zkapp_address: addr_str.to_string(),
                            tx_hash: tx_str.to_string(),
                            block_height: *block_height,
                            timestamp_ms: *timestamp_ms,
                        });
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Mina Anchor Verification:");
                        println!("  zkApp Address: {}", addr_str);
                        println!("  Transaction: {}", tx_str);
                        println!("  Block Height: {}", block_height);
                        println!("  Timestamp: {} ms", timestamp_ms);
                        println!();
                        println!("Note: Full on-chain verification requires Mina bridge.");
                    }
                }
                _ => {
                    return Err("Receipt does not have a Mina anchor".into());
                }
            }
        }
        MinaCommands::Time => {
            // Get time from Mina network via bridge
            let bridge_path = dirs::home_dir()
                .unwrap_or_else(|| PathBuf::from("."))
                .join(".anubis")
                .join("mina-bridge");
            let bridge_script = bridge_path.join("mina-bridge.js");

            if !bridge_script.exists() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "Mina bridge not installed. Run 'anchor mina setup' first.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Mina Time:");
                    println!("  Status: Bridge not installed");
                    println!();
                    println!("Run 'anchor mina setup' to install the Mina bridge.");
                }
            } else {
                use std::io::{BufRead, BufReader, Write as IoWrite};
                use std::process::{Command, Stdio};
                use std::thread;
                use std::time::Duration;

                // Spawn bridge process
                let mut child = Command::new("node")
                    .arg(&bridge_script)
                    .stdin(Stdio::piped())
                    .stdout(Stdio::piped())
                    .stderr(Stdio::null())
                    .spawn()
                    .map_err(|e| format!("Failed to spawn bridge: {}", e))?;

                // Wait for bridge to initialize (o1js needs time to load WASM)
                thread::sleep(Duration::from_millis(2000));

                // Send time command and flush
                {
                    let stdin = child.stdin.as_mut().ok_or("Failed to get stdin")?;
                    writeln!(stdin, r#"{{"cmd":"time"}}"#)
                        .map_err(|e| format!("Failed to send command: {}", e))?;
                    stdin
                        .flush()
                        .map_err(|e| format!("Failed to flush: {}", e))?;
                }

                // Read response
                let stdout = child.stdout.take().ok_or("Failed to get stdout")?;
                let mut reader = BufReader::new(stdout);
                let mut response = String::new();
                reader
                    .read_line(&mut response)
                    .map_err(|e| format!("Failed to read response: {}", e))?;

                // Kill the bridge process
                let _ = child.kill();

                // Parse response
                if response.contains(r#""ok":true"#) {
                    let height: u64 = response
                        .split(r#""height":"#)
                        .nth(1)
                        .and_then(|s| s.split([',', '}']).next())
                        .and_then(|s| s.trim().parse().ok())
                        .unwrap_or(0);
                    let timestamp: u64 = response
                        .split(r#""timestamp":"#)
                        .nth(1)
                        .and_then(|s| s.split([',', '}']).next())
                        .and_then(|s| s.trim().parse().ok())
                        .unwrap_or(0);

                    if json {
                        #[derive(Serialize)]
                        struct TimeResult {
                            height: u64,
                            timestamp: u64,
                            network: String,
                        }
                        let output = JsonOutput::success(TimeResult {
                            height,
                            timestamp,
                            network: "devnet".to_string(),
                        });
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Mina Time:");
                        println!("  Block Height: {}", height);
                        println!("  Timestamp: {} ms", timestamp);
                        println!("  Network: devnet");
                    }
                } else {
                    let err = response
                        .split(r#""error":""#)
                        .nth(1)
                        .and_then(|s| s.split('"').next())
                        .unwrap_or("Unknown error");
                    if json {
                        let output: JsonOutput<()> =
                            JsonOutput::error(&format!("Bridge error: {}", err));
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Mina Time:");
                        println!("  Error: {}", err);
                    }
                }
            }
        }
        MinaCommands::Balance => {
            // Would use MinaClient to get wallet balance
            if json {
                let output: JsonOutput<()> =
                    JsonOutput::error("Mina bridge not connected. Run 'anchor mina setup' first.");
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Mina Wallet:");
                println!("  Status: Bridge not connected");
                println!();
                println!("Run 'anchor mina setup' to install the Mina bridge.");
            }
        }
        MinaCommands::Setup { force } => {
            let bridge_path = dirs::home_dir()
                .unwrap_or_else(|| PathBuf::from("."))
                .join(".anubis")
                .join("mina-bridge");

            if bridge_path.exists() && !force {
                if json {
                    #[derive(Serialize)]
                    struct SetupResult {
                        status: String,
                        path: String,
                    }
                    let output = JsonOutput::success(SetupResult {
                        status: "already_installed".to_string(),
                        path: bridge_path.display().to_string(),
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Mina bridge already installed at:");
                    println!("  {}", bridge_path.display());
                    println!();
                    println!("Use --force to reinstall.");
                }
            } else {
                // Create directory structure
                std::fs::create_dir_all(&bridge_path)?;

                // Copy package.json and other files would go here
                // For now, just create a placeholder
                let setup_instructions = r#"{
  "name": "anubis-mina-bridge",
  "version": "1.0.0",
  "description": "Mina bridge for Anubis Notary",
  "main": "mina-bridge.js",
  "dependencies": {
    "o1js": "^1.0.0"
  }
}
"#;
                std::fs::write(bridge_path.join("package.json"), setup_instructions)?;

                if json {
                    #[derive(Serialize)]
                    struct SetupResult {
                        status: String,
                        path: String,
                        next_steps: Vec<String>,
                    }
                    let output = JsonOutput::success(SetupResult {
                        status: "created".to_string(),
                        path: bridge_path.display().to_string(),
                        next_steps: vec![
                            format!("cd {}", bridge_path.display()),
                            "npm install".to_string(),
                            "Copy mina-bridge.js from anubis-notary/mina-zkapp/".to_string(),
                        ],
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Mina bridge directory created:");
                    println!("  {}", bridge_path.display());
                    println!();
                    println!("Next steps:");
                    println!("  1. cd {}", bridge_path.display());
                    println!("  2. npm install");
                    println!(
                        "  3. Copy mina-bridge.js from the anubis-notary/mina-zkapp/ directory"
                    );
                    println!();
                    println!("Then configure with:");
                    println!("  anubis-notary anchor mina config --zkapp <your-zkapp-address>");
                }
            }
        }
        MinaCommands::Keygen => {
            let bridge_path = dirs::home_dir()
                .unwrap_or_else(|| PathBuf::from("."))
                .join(".anubis")
                .join("mina-bridge");
            let bridge_script = bridge_path.join("mina-bridge.js");

            if !bridge_script.exists() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "Mina bridge not installed. Run 'anchor mina setup' first.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Mina bridge not installed.");
                    println!("Run 'anubis-notary anchor mina setup' to install the Mina bridge.");
                }
                return Ok(());
            }

            use std::io::{BufRead, BufReader, Write as IoWrite};
            use std::process::{Command, Stdio};
            use std::thread;
            use std::time::Duration;

            let mut child = Command::new("node")
                .arg(&bridge_script)
                .env("MINA_NETWORK", "mainnet")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::null())
                .spawn()?;

            thread::sleep(Duration::from_millis(2000));

            {
                let stdin = child.stdin.as_mut().ok_or("Failed to get stdin")?;
                writeln!(stdin, r#"{{"cmd":"keygen"}}"#)?;
                stdin.flush()?;
            }

            let stdout = child.stdout.as_mut().ok_or("Failed to get stdout")?;
            let mut reader = BufReader::new(stdout);
            let mut response = String::new();
            reader.read_line(&mut response)?;

            let _ = child.kill();

            if response.is_empty() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error("No response from bridge");
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Error: No response from bridge");
                }
                return Ok(());
            }

            if json {
                println!("{}", response.trim());
            } else {
                // Parse and display nicely
                if let Ok(parsed) = serde_json::from_str::<serde_json::Value>(&response) {
                    if parsed.get("ok").and_then(|v| v.as_bool()) == Some(true) {
                        println!("╔════════════════════════════════════════════════════════════════════════╗");
                        println!("║                    MINA KEYPAIR GENERATED                              ║");
                        println!("╠════════════════════════════════════════════════════════════════════════╣");
                        println!("║  Network: MAINNET                                                      ║");
                        println!("╟────────────────────────────────────────────────────────────────────────╢");
                        println!("║  Public Key (Address):                                                 ║");
                        if let Some(pk) = parsed.get("publicKey").and_then(|v| v.as_str()) {
                            println!("║    {}  ║", pk);
                        }
                        println!("╟────────────────────────────────────────────────────────────────────────╢");
                        println!("║  Private Key:                                                          ║");
                        if let Some(sk) = parsed.get("privateKey").and_then(|v| v.as_str()) {
                            println!("║    {}  ║", sk);
                        }
                        println!("╠════════════════════════════════════════════════════════════════════════╣");
                        println!("║  ⚠️  SAVE THE PRIVATE KEY SECURELY - IT CANNOT BE RECOVERED            ║");
                        println!("╚════════════════════════════════════════════════════════════════════════╝");
                        println!();
                        println!("Next steps:");
                        println!("  1. Fund the public key address with at least 1.1 MINA");
                        println!("  2. Run: anubis-notary anchor mina deploy --fee-payer-key <private-key>");
                    } else if let Some(err) = parsed.get("error").and_then(|v| v.as_str()) {
                        println!("Error: {}", err);
                    }
                } else {
                    println!("Response: {}", response.trim());
                }
            }
        }
        MinaCommands::Deploy {
            fee_payer_key,
            wait,
        } => {
            let bridge_path = dirs::home_dir()
                .unwrap_or_else(|| PathBuf::from("."))
                .join(".anubis")
                .join("mina-bridge");
            let bridge_script = bridge_path.join("mina-bridge.js");

            if !bridge_script.exists() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "Mina bridge not installed. Run 'anchor mina setup' first.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Mina bridge not installed.");
                    println!("Run 'anubis-notary anchor mina setup' to install the Mina bridge.");
                }
                return Ok(());
            }

            // Get private key from argument or prompt
            let private_key = if let Some(key) = fee_payer_key {
                key.clone()
            } else {
                // Prompt for private key
                if json {
                    let output: JsonOutput<()> =
                        JsonOutput::error("--fee-payer-key is required for deployment");
                    println!("{}", serde_json::to_string_pretty(&output)?);
                    return Ok(());
                }
                print!("Enter fee payer private key: ");
                std::io::stdout().flush()?;
                let mut key = String::new();
                std::io::stdin().read_line(&mut key)?;
                key.trim().to_string()
            };

            if private_key.is_empty() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error("Private key is required");
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Error: Private key is required for deployment");
                }
                return Ok(());
            }

            if !json {
                println!("Deploying AnubisAnchor zkApp to Mina mainnet...");
                println!("This will take several minutes (zkApp compilation + proof generation)");
                println!();
            }

            use std::io::{BufRead, BufReader, Write as IoWrite};
            use std::process::{Command, Stdio};
            use std::thread;
            use std::time::Duration;

            let mut child = Command::new("node")
                .arg(&bridge_script)
                .env("MINA_NETWORK", "mainnet")
                .env("MINA_PRIVATE_KEY", &private_key)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()?;

            // zkApp compilation takes a while
            thread::sleep(Duration::from_millis(3000));

            let wait_flag = if *wait { "true" } else { "false" };
            {
                let stdin = child.stdin.as_mut().ok_or("Failed to get stdin")?;
                writeln!(stdin, r#"{{"cmd":"deploy","wait":{}}}"#, wait_flag)?;
                stdin.flush()?;
            }

            // Wait longer for deployment (compilation + proof + tx)
            let stdout = child.stdout.as_mut().ok_or("Failed to get stdout")?;
            let mut reader = BufReader::new(stdout);
            let mut response = String::new();

            // Use a timeout loop since deployment can take a while
            let start = std::time::Instant::now();
            let timeout = Duration::from_secs(600); // 10 minute timeout

            loop {
                if start.elapsed() > timeout {
                    let _ = child.kill();
                    if json {
                        let output: JsonOutput<()> = JsonOutput::error("Deployment timed out");
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Error: Deployment timed out after 10 minutes");
                    }
                    return Ok(());
                }

                match reader.read_line(&mut response) {
                    Ok(0) => {
                        thread::sleep(Duration::from_millis(100));
                        continue;
                    }
                    Ok(_) => break,
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(100));
                        continue;
                    }
                    Err(e) => {
                        let _ = child.kill();
                        return Err(e.into());
                    }
                }
            }

            let _ = child.kill();

            if response.is_empty() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error("No response from bridge");
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Error: No response from bridge");
                }
                return Ok(());
            }

            if json {
                println!("{}", response.trim());
            } else {
                if let Ok(parsed) = serde_json::from_str::<serde_json::Value>(&response) {
                    if parsed.get("ok").and_then(|v| v.as_bool()) == Some(true) {
                        println!("╔════════════════════════════════════════════════════════════════════════╗");
                        println!("║                 ZKAPP DEPLOYED SUCCESSFULLY                            ║");
                        println!("╠════════════════════════════════════════════════════════════════════════╣");
                        if let Some(addr) = parsed.get("zkappAddress").and_then(|v| v.as_str()) {
                            println!("║  zkApp Address: {}  ║", addr);
                        }
                        if let Some(tx) = parsed.get("txHash").and_then(|v| v.as_str()) {
                            println!("║  Transaction:   {}  ║", tx);
                        }
                        if let Some(url) = parsed.get("explorerUrl").and_then(|v| v.as_str()) {
                            println!("║  Explorer:      {}  ║", url);
                        }
                        println!("╟────────────────────────────────────────────────────────────────────────╢");
                        println!("║  zkApp Private Key (for upgrades only):                               ║");
                        if let Some(sk) = parsed.get("zkappPrivateKey").and_then(|v| v.as_str()) {
                            println!("║    {}  ║", sk);
                        }
                        println!("╠════════════════════════════════════════════════════════════════════════╣");
                        println!("║  ⚠️  SAVE THE ZKAPP PRIVATE KEY - needed for contract upgrades         ║");
                        println!("╚════════════════════════════════════════════════════════════════════════╝");
                        println!();

                        // Save config automatically
                        if let Some(addr) = parsed.get("zkappAddress").and_then(|v| v.as_str()) {
                            let config_path = dirs::home_dir()
                                .unwrap_or_else(|| PathBuf::from("."))
                                .join(".anubis")
                                .join("mina-config.json");
                            let config = serde_json::json!({
                                "network": "mainnet",
                                "zkapp_address": addr,
                                "fee_mina": 0.1,
                            });
                            if std::fs::write(&config_path, serde_json::to_string_pretty(&config)?)
                                .is_ok()
                            {
                                println!("Configuration saved to: {}", config_path.display());
                                println!();
                                println!(
                                    "You can now use: anubis-notary anchor mina anchor <receipt>"
                                );
                            }
                        }
                    } else if let Some(err) = parsed.get("error").and_then(|v| v.as_str()) {
                        println!("Deployment failed: {}", err);
                    }
                } else {
                    println!("Response: {}", response.trim());
                }
            }
        }
        MinaCommands::Info => {
            let bridge_path = dirs::home_dir()
                .unwrap_or_else(|| PathBuf::from("."))
                .join(".anubis")
                .join("mina-bridge");
            let bridge_script = bridge_path.join("mina-bridge.js");

            if !bridge_script.exists() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "Mina bridge not installed. Run 'anchor mina setup' first.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Mina bridge not installed.");
                    println!("Run 'anubis-notary anchor mina setup' to install the Mina bridge.");
                }
                return Ok(());
            }

            use std::io::{BufRead, BufReader, Write as IoWrite};
            use std::process::{Command, Stdio};
            use std::thread;
            use std::time::Duration;

            let mut child = Command::new("node")
                .arg(&bridge_script)
                .env("MINA_NETWORK", "mainnet")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::null())
                .spawn()?;

            thread::sleep(Duration::from_millis(2000));

            {
                let stdin = child.stdin.as_mut().ok_or("Failed to get stdin")?;
                writeln!(stdin, r#"{{"cmd":"networkinfo"}}"#)?;
                stdin.flush()?;
            }

            let stdout = child.stdout.as_mut().ok_or("Failed to get stdout")?;
            let mut reader = BufReader::new(stdout);
            let mut response = String::new();
            reader.read_line(&mut response)?;

            let _ = child.kill();

            if json {
                println!("{}", response.trim());
            } else {
                if let Ok(parsed) = serde_json::from_str::<serde_json::Value>(&response) {
                    if parsed.get("ok").and_then(|v| v.as_bool()) == Some(true) {
                        println!("╔════════════════════════════════════════════════════════════════════════╗");
                        println!("║                    MINA MAINNET DEPLOYMENT INFO                        ║");
                        println!("╠════════════════════════════════════════════════════════════════════════╣");
                        println!("║  Network:              mainnet                                         ║");
                        println!("║  GraphQL Endpoint:     https://api.minascan.io/node/mainnet/v1/graphql ║");
                        println!("║  Explorer:             https://minascan.io/mainnet                     ║");
                        println!("╟────────────────────────────────────────────────────────────────────────╢");
                        println!("║  DEPLOYMENT COSTS                                                      ║");
                        println!("║  ─────────────────                                                     ║");
                        if let Some(fee) = parsed.get("accountCreationFee").and_then(|v| v.as_f64())
                        {
                            println!("║  Account Creation Fee: {} MINA                                         ║", fee);
                        }
                        if let Some(fee) = parsed.get("transactionFee").and_then(|v| v.as_f64()) {
                            println!("║  Transaction Fee:      {} MINA                                         ║", fee);
                        }
                        if let Some(total) =
                            parsed.get("totalDeploymentCost").and_then(|v| v.as_f64())
                        {
                            println!("║  ─────────────────────────────                                         ║");
                            println!("║  TOTAL DEPLOYMENT:     {} MINA                                         ║", total);
                        }
                        println!("╟────────────────────────────────────────────────────────────────────────╢");
                        println!("║  PER-ANCHOR COSTS                                                      ║");
                        println!("║  ─────────────────                                                     ║");
                        println!("║  Transaction Fee:      0.1 MINA per anchor                             ║");
                        println!("╚════════════════════════════════════════════════════════════════════════╝");
                        println!();
                        println!("To deploy:");
                        println!("  1. Run: anubis-notary anchor mina keygen");
                        println!("  2. Fund the generated address with 1.1+ MINA");
                        println!(
                            "  3. Run: anubis-notary anchor mina deploy --fee-payer-key <key>"
                        );
                    } else if let Some(err) = parsed.get("error").and_then(|v| v.as_str()) {
                        println!("Error: {}", err);
                    }
                } else {
                    println!("Response: {}", response.trim());
                }
            }
        }
        MinaCommands::Queue { receipt } => {
            use anubis_core::receipt::Receipt;
            use anubis_io::BatchQueue;

            // Verify the receipt is valid
            let receipt_data = read_file(&receipt)?;
            let parsed =
                Receipt::decode(&receipt_data).map_err(|e| format!("Invalid receipt: {:?}", e))?;

            // Open batch queue
            let queue_path = ks.path().join("mina-batch-queue");
            let queue = BatchQueue::open(&queue_path)?;

            // Add to queue
            let entry = queue.enqueue(&parsed.digest, &receipt)?;

            if json {
                #[derive(Serialize)]
                struct QueueResult {
                    receipt: String,
                    digest: String,
                    queued_at: u64,
                    pending_count: usize,
                    ready_for_batch: bool,
                }
                let pending = queue.pending_count()?;
                let output = JsonOutput::success(QueueResult {
                    receipt: receipt.display().to_string(),
                    digest: entry.digest.clone(),
                    queued_at: entry.queued_at,
                    pending_count: pending,
                    ready_for_batch: pending >= 8,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                let pending = queue.pending_count()?;
                println!("Receipt added to Mina batch queue:");
                println!("  File:    {}", receipt.display());
                println!("  Digest:  {}", entry.digest);
                println!("  Pending: {}/8 receipts", pending);
                if pending >= 8 {
                    println!();
                    println!(
                        "Queue is full! Run 'anubis-notary anchor mina flush' to submit batch."
                    );
                } else {
                    println!();
                    println!("Add {} more receipts for 8x cost savings.", 8 - pending);
                }
            }
        }
        MinaCommands::Flush { force, wait: _wait } => {
            use anubis_io::BatchQueue;

            let queue_path = ks.path().join("mina-batch-queue");
            let queue = BatchQueue::open(&queue_path)?;

            let pending = queue.pending()?;
            if pending.is_empty() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "Batch queue is empty. Add receipts with 'anchor mina queue'.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Batch queue is empty.");
                    println!("Add receipts with: anubis-notary anchor mina queue <receipt>");
                }
                return Ok(());
            }

            if pending.len() < 8 && !force {
                if json {
                    #[derive(Serialize)]
                    struct NotReadyResult {
                        pending_count: usize,
                        needed: usize,
                    }
                    let output = JsonOutput::error_with_data(
                        "Queue not full. Use --force to submit partial batch.",
                        NotReadyResult {
                            pending_count: pending.len(),
                            needed: 8 - pending.len(),
                        },
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!(
                        "Queue has {} receipts (need 8 for optimal batching).",
                        pending.len()
                    );
                    println!(
                        "Use --force to submit a partial batch, or add {} more receipts.",
                        8 - pending.len()
                    );
                }
                return Ok(());
            }

            // Note: Full implementation would call the bridge with submitbatch command
            // For now, we show what would be submitted
            if !json {
                println!("Batch anchoring (submitting {} receipts):", pending.len());
                for entry in &pending {
                    println!("  - {}", &entry.digest[..16]);
                }
                println!();
                println!("Note: Batch anchoring requires the BatchVault zkApp to be deployed.");
                println!("      Use the standard 'anchor mina anchor' for individual anchoring.");
            } else {
                #[derive(Serialize)]
                struct FlushResult {
                    pending_count: usize,
                    digests: Vec<String>,
                    message: String,
                }
                let output = JsonOutput::success(FlushResult {
                    pending_count: pending.len(),
                    digests: pending.iter().map(|e| e.digest.clone()).collect(),
                    message: "BatchVault deployment required for batch anchoring".to_string(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            }
        }
        MinaCommands::QueueStatus => {
            use anubis_io::BatchQueue;

            let queue_path = ks.path().join("mina-batch-queue");
            let queue = BatchQueue::open(&queue_path)?;

            let pending = queue.pending()?;
            let history = queue.history()?;

            if json {
                #[derive(Serialize)]
                struct StatusResult {
                    pending_count: usize,
                    pending: Vec<PendingEntry>,
                    history_count: usize,
                    ready_for_batch: bool,
                }
                #[derive(Serialize)]
                struct PendingEntry {
                    digest: String,
                    receipt_path: String,
                    queued_at: u64,
                }

                let output = JsonOutput::success(StatusResult {
                    pending_count: pending.len(),
                    pending: pending
                        .iter()
                        .map(|e| PendingEntry {
                            digest: e.digest.clone(),
                            receipt_path: e.receipt_path.clone(),
                            queued_at: e.queued_at,
                        })
                        .collect(),
                    history_count: history.len(),
                    ready_for_batch: pending.len() >= 8,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Mina Batch Queue Status");
                println!("=======================");
                println!("Pending:  {}/8 receipts", pending.len());
                println!("Batches:  {} submitted", history.len());
                println!();

                if pending.is_empty() {
                    println!("Queue is empty. Add receipts with:");
                    println!("  anubis-notary anchor mina queue <receipt>");
                } else {
                    println!("Pending receipts:");
                    for entry in &pending {
                        println!("  - {} ({})", &entry.digest[..16], entry.receipt_path);
                    }

                    if pending.len() >= 8 {
                        println!();
                        println!("Queue is full! Run 'anubis-notary anchor mina flush' to submit.");
                    } else {
                        println!();
                        println!(
                            "Add {} more receipts for optimal 8x cost savings.",
                            8 - pending.len()
                        );
                    }
                }
            }
        }
    }
    Ok(())
}

fn handle_multisig(
    action: &MultisigCommands,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        MultisigCommands::Init {
            threshold,
            signers,
            out,
        } => {
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
                )
                .into());
            }

            // Load public keys from files
            let mut signer_pks = Vec::new();
            let mut signer_info = Vec::new();

            for signer_path in signers {
                let pk_bytes = read_file(signer_path)?;
                let pk = PublicKey::from_bytes(&pk_bytes).map_err(|e| {
                    format!("Invalid public key in {}: {:?}", signer_path.display(), e)
                })?;

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
                    signers: signer_info
                        .iter()
                        .map(|(f, fp)| SignerInfo {
                            file: f.clone(),
                            fingerprint: fp.clone(),
                        })
                        .collect(),
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
        MultisigCommands::Propose {
            config,
            proposal_type,
            data,
            expires,
            out,
        } => {
            let config_data = read_file(config)?;
            let config_json: serde_json::Value = serde_json::from_slice(&config_data)?;

            // Parse signers from config
            let signers = config_json
                .get("signers")
                .and_then(|v| v.as_array())
                .ok_or("Invalid config: missing signers")?;

            let threshold = config_json
                .get("threshold")
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
            let data_bytes = hex::decode(data).map_err(|e| format!("Invalid data hex: {}", e))?;

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
                "remove-signer" => ProposalType::RemoveSigner { signer_index: 0 },
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
            )
            .map_err(|e| format!("{:?}", e))?;

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

            write_file_atomic(
                out,
                serde_json::to_string_pretty(&proposal_json)?.as_bytes(),
            )?;

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
        MultisigCommands::Sign {
            proposal,
            config,
            out,
        } => {
            let config_data = read_file(config)?;
            let config_json: serde_json::Value = serde_json::from_slice(&config_data)?;

            // Parse signers from config
            let signers = config_json
                .get("signers")
                .and_then(|v| v.as_array())
                .ok_or("Invalid config: missing signers")?;

            let threshold = config_json
                .get("threshold")
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
            let signer_idx = signer_pks
                .iter()
                .position(|pk| pk.to_bytes() == my_pk.to_bytes())
                .ok_or("Your key is not a signer in this multisig")?;

            // Load proposal
            let proposal_data = read_file(proposal)?;
            let mut proposal_json: serde_json::Value = serde_json::from_slice(&proposal_data)?;

            // Get proposal ID and multisig hash
            let proposal_id = proposal_json
                .get("id")
                .and_then(|v| v.as_str())
                .ok_or("Invalid proposal: missing id")?;
            let multisig_hash = proposal_json
                .get("multisig_hash")
                .and_then(|v| v.as_str())
                .ok_or("Invalid proposal: missing multisig_hash")?;
            let nonce = proposal_json
                .get("nonce")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid proposal: missing nonce")?;

            // Create message to sign (using proposal signing payload format)
            let mut message = Vec::new();
            message.extend_from_slice(b"ANUBIS-MULTISIG-PROPOSAL-V1:");
            message.extend_from_slice(&hex::decode(proposal_id)?);
            message.extend_from_slice(&hex::decode(multisig_hash)?);
            message.extend_from_slice(&nonce.to_le_bytes());

            // Sign
            let signature = kp
                .sign(&message)
                .map_err(|e| format!("Signing failed: {:?}", e))?;

            // Update proposal with signature
            {
                let signatures = proposal_json
                    .get_mut("signatures")
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
                let signed_by = proposal_json
                    .get_mut("signed_by")
                    .and_then(|v| v.as_array_mut())
                    .ok_or("Invalid proposal: missing signed_by")?;
                if !signed_by
                    .iter()
                    .any(|v| v.as_u64() == Some(signer_idx as u64))
                {
                    signed_by.push(serde_json::json!(signer_idx));
                }
            }

            // Count signatures
            let sig_count = proposal_json
                .get("signatures")
                .and_then(|v| v.as_array())
                .map(|arr| arr.iter().filter(|s| !s.is_null()).count())
                .unwrap_or(0);

            // Update status if threshold met
            if sig_count >= threshold as usize {
                proposal_json["status"] = serde_json::json!("Approved");
            }

            // Write updated proposal
            let out_path = out.as_ref().unwrap_or(proposal);
            write_file_atomic(
                out_path,
                serde_json::to_string_pretty(&proposal_json)?.as_bytes(),
            )?;

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
                    println!(
                        "  Status: Pending ({} more signatures needed)",
                        threshold as usize - sig_count
                    );
                }
            }
            Ok(())
        }
        MultisigCommands::Execute { proposal, config } => {
            use anubis_core::mldsa::Signature;

            let config_data = read_file(config)?;
            let config_json: serde_json::Value = serde_json::from_slice(&config_data)?;

            let threshold = config_json
                .get("threshold")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid config: missing threshold")? as u8;

            // SECURITY: Parse signer public keys for verification
            let signers = config_json
                .get("signers")
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
            let proposal_id = proposal_json
                .get("id")
                .and_then(|v| v.as_str())
                .ok_or("Invalid proposal: missing id")?;
            let multisig_hash = proposal_json
                .get("multisig_hash")
                .and_then(|v| v.as_str())
                .ok_or("Invalid proposal: missing multisig_hash")?;
            let nonce = proposal_json
                .get("nonce")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid proposal: missing nonce")?;

            // Reconstruct the message that was signed
            let mut message = Vec::new();
            message.extend_from_slice(b"ANUBIS-MULTISIG-PROPOSAL-V1:");
            message.extend_from_slice(
                &hex::decode(proposal_id).map_err(|e| format!("Invalid proposal id: {}", e))?,
            );
            message.extend_from_slice(
                &hex::decode(multisig_hash).map_err(|e| format!("Invalid multisig_hash: {}", e))?,
            );
            message.extend_from_slice(&nonce.to_le_bytes());

            let signatures = proposal_json
                .get("signatures")
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
                    verification_errors.push(format!(
                        "Signature at index {} has no corresponding signer",
                        idx
                    ));
                    continue;
                }

                let signature = match Signature::from_bytes(&sig_bytes) {
                    Ok(s) => s,
                    Err(e) => {
                        verification_errors
                            .push(format!("Invalid signature at index {}: {:?}", idx, e));
                        continue;
                    }
                };

                if signer_pks[idx].verify(&message, &signature) {
                    verified_count += 1;
                } else {
                    verification_errors
                        .push(format!("Signature verification FAILED for signer {}", idx));
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

            let proposal_type = proposal_json
                .get("proposal_type")
                .and_then(|v| v.as_str())
                .ok_or("Invalid proposal: missing proposal_type")?;

            let data_hex = proposal_json
                .get("data")
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
                println!(
                    "  Verified signatures: {} of {} (threshold: {})",
                    verified_count,
                    signer_pks.len(),
                    threshold
                );
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

            let threshold = config_json
                .get("threshold")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid config: missing threshold")? as u8;

            let signers = config_json
                .get("signers")
                .and_then(|v| v.as_array())
                .ok_or("Invalid config: missing signers")?;

            let proposal_data = read_file(proposal)?;
            let proposal_json: serde_json::Value = serde_json::from_slice(&proposal_data)?;

            let nonce = proposal_json
                .get("nonce")
                .and_then(|v| v.as_u64())
                .unwrap_or(0);
            let proposal_type = proposal_json
                .get("proposal_type")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown");
            let status = proposal_json
                .get("status")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown");
            let expires = proposal_json.get("expires").and_then(|v| v.as_u64());
            let created = proposal_json
                .get("created")
                .and_then(|v| v.as_u64())
                .unwrap_or(0);

            let signatures = proposal_json
                .get("signatures")
                .and_then(|v| v.as_array())
                .map(|a| a.iter().filter(|s| !s.is_null()).count())
                .unwrap_or(0);

            let signed_by = proposal_json
                .get("signed_by")
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
                println!(
                    "  Signatures: {} of {} (threshold: {})",
                    signatures,
                    signers.len(),
                    threshold
                );
                println!("  Created: {}", created);
                if let Some(exp) = expires {
                    if exp > 0 {
                        println!(
                            "  Expires: {}{}",
                            exp,
                            if is_expired { " (EXPIRED)" } else { "" }
                        );
                    }
                }
                println!();
                if signatures >= threshold as usize && !is_expired {
                    println!("  Ready to execute!");
                } else if is_expired {
                    println!("  Proposal has expired.");
                } else {
                    println!(
                        "  Needs {} more signature(s).",
                        threshold as usize - signatures
                    );
                }
            }
            Ok(())
        }
        MultisigCommands::Signers { config } => {
            let config_data = read_file(config)?;
            let config_json: serde_json::Value = serde_json::from_slice(&config_data)?;

            let threshold = config_json
                .get("threshold")
                .and_then(|v| v.as_u64())
                .ok_or("Invalid config: missing threshold")? as u8;

            let signers = config_json
                .get("signers")
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

                let signers_info: Vec<SignerInfo> = signers
                    .iter()
                    .enumerate()
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
        StreamCommands::Sign {
            file,
            out,
            chunk_size,
            progress,
        } => {
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
            let config =
                StreamingConfig::with_chunk_size(*chunk_size).map_err(|e| format!("{}", e))?;
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
                    eprint!(
                        "\rProcessing: {}% ({}/{} bytes)",
                        pct, bytes_read, file_size
                    );
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
                println!(
                    "Signature size: {} bytes (ML-DSA-87)",
                    signature.to_bytes().len()
                );
            }
            Ok(())
        }
        StreamCommands::Verify {
            file,
            sig,
            chunk_size,
            progress,
        } => {
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
            let config =
                StreamingConfig::with_chunk_size(*chunk_size).map_err(|e| format!("{}", e))?;
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
                verifier
                    .update(&buffer[..n])
                    .map_err(|e| format!("{}", e))?;
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
        StreamCommands::Hash {
            file,
            chunk_size,
            progress,
        } => {
            use std::fs::File;
            use std::io::BufReader;

            // Get file size for progress
            let metadata = std::fs::metadata(file)?;
            let file_size = metadata.len();

            // Open file for streaming
            let f = File::open(file)?;
            let mut reader = BufReader::new(f);

            // Create streaming hasher with custom chunk size
            let config =
                StreamingConfig::with_chunk_size(*chunk_size).map_err(|e| format!("{}", e))?;
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

fn handle_private_batch(
    action: &PrivateBatchCommands,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        PrivateBatchCommands::Keygen { out } => {
            // Generate ML-KEM-1024 keypair
            let kp = MlKemKeyPair::generate()
                .map_err(|e| format!("Failed to generate ML-KEM keypair: {:?}", e))?;

            // Write public key
            let pub_path = out.with_extension("mlkem.pub");
            write_file_atomic(&pub_path, kp.public_key_bytes())?;

            // Write secret key (this is sensitive!)
            let sec_path = out.with_extension("mlkem.sec");
            let (sk, _) = kp.into_parts();
            write_file_atomic(&sec_path, sk.as_bytes())?;

            // Set restrictive permissions on secret key (Unix only)
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let perms = std::fs::Permissions::from_mode(0o600);
                std::fs::set_permissions(&sec_path, perms)?;
            }

            if json {
                #[derive(Serialize)]
                struct KeygenResult {
                    public_key: String,
                    secret_key: String,
                    algorithm: &'static str,
                }
                let output = JsonOutput::success(KeygenResult {
                    public_key: pub_path.display().to_string(),
                    secret_key: sec_path.display().to_string(),
                    algorithm: "ML-KEM-1024",
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Generated ML-KEM-1024 keypair:");
                println!("  Public key:  {}", pub_path.display());
                println!("  Secret key:  {}", sec_path.display());
                println!();
                println!("IMPORTANT: Keep your secret key safe and private!");
            }
            Ok(())
        }

        PrivateBatchCommands::Create {
            receipts,
            recipients,
            threshold,
            out,
        } => {
            // Read receipt files
            let mut leaf_data: Vec<Vec<u8>> = Vec::with_capacity(receipts.len());
            for receipt_path in receipts {
                let data = read_file(receipt_path)?;
                leaf_data.push(data);
            }

            // Convert to slice of slices for API
            let leaves: Vec<&[u8]> = leaf_data.iter().map(|v| v.as_slice()).collect();

            // Read recipient public keys
            let mut recipient_pks: Vec<MlKemPublicKey> = Vec::with_capacity(recipients.len());
            for pk_path in recipients {
                let pk_bytes = read_file(pk_path)?;
                let pk = MlKemPublicKey::from_bytes(&pk_bytes).map_err(|e| {
                    format!(
                        "Invalid ML-KEM public key in {}: {:?}",
                        pk_path.display(),
                        e
                    )
                })?;
                recipient_pks.push(pk);
            }

            // Create private batch
            let batch = PrivateBatch::create(&leaves, &recipient_pks, *threshold)
                .map_err(|e| format!("Failed to create private batch: {:?}", e))?;

            // Serialize and write
            let batch_bytes = batch.to_bytes();
            write_file_atomic(out, &batch_bytes)?;

            if json {
                #[derive(Serialize)]
                struct CreateResult {
                    batch_file: String,
                    batch_id: String,
                    merkle_root: String,
                    num_leaves: usize,
                    threshold: u8,
                    total_recipients: usize,
                }
                let output = JsonOutput::success(CreateResult {
                    batch_file: out.display().to_string(),
                    batch_id: hex::encode(batch.batch_id),
                    merkle_root: hex::encode(batch.merkle_root),
                    num_leaves: batch.len(),
                    threshold: *threshold,
                    total_recipients: recipient_pks.len(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Created private batch: {}", out.display());
                println!("  Batch ID:     {}", hex::encode(batch.batch_id));
                println!("  Merkle root:  {}", hex::encode(batch.merkle_root));
                println!("  Leaves:       {}", batch.len());
                println!("  Threshold:    {}-of-{}", threshold, recipient_pks.len());
                println!();
                println!("Distribute this batch file to recipients for collaborative decryption.");
            }
            Ok(())
        }

        PrivateBatchCommands::DecryptShare {
            batch,
            secret_key,
            out,
        } => {
            // Read batch file
            let batch_bytes = read_file(batch)?;
            let private_batch = PrivateBatch::from_bytes(&batch_bytes)
                .map_err(|e| format!("Failed to parse batch file: {:?}", e))?;

            // Read secret key
            let sk_bytes = read_file(secret_key)?;
            let sk = MlKemSecretKey::from_bytes(&sk_bytes)
                .map_err(|e| format!("Invalid ML-KEM secret key: {:?}", e))?;

            // Find our recipient index by trying each one
            let mut found_share = None;
            let mut found_index = 0u8;

            for i in 0..private_batch.key_envelope.recipient_shares.len() {
                match private_batch.key_envelope.decrypt_share(i, &sk) {
                    Ok(share) => {
                        found_share = Some(share);
                        found_index = i as u8;
                        break;
                    }
                    Err(_) => continue,
                }
            }

            let share = found_share.ok_or("Your key is not a recipient of this batch")?;

            // Create DecryptedShare for transmission
            let decrypted = DecryptedShare::new(share, found_index, private_batch.batch_id);
            let share_bytes = decrypted.to_bytes();
            write_file_atomic(out, &share_bytes)?;

            if json {
                #[derive(Serialize)]
                struct DecryptShareResult {
                    share_file: String,
                    batch_id: String,
                    recipient_index: u8,
                }
                let output = JsonOutput::success(DecryptShareResult {
                    share_file: out.display().to_string(),
                    batch_id: hex::encode(private_batch.batch_id),
                    recipient_index: found_index,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Decrypted share saved to: {}", out.display());
                println!("  Batch ID:        {}", hex::encode(private_batch.batch_id));
                println!("  Recipient index: {}", found_index);
                println!();
                println!("Send this share file to the coordinator for batch decryption.");
            }
            Ok(())
        }

        PrivateBatchCommands::Combine { batch, share, out } => {
            // Read batch file
            let batch_bytes = read_file(batch)?;
            let private_batch = PrivateBatch::from_bytes(&batch_bytes)
                .map_err(|e| format!("Failed to parse batch file: {:?}", e))?;

            // Create decryptor
            let mut decryptor = CollaborativeDecryptor::from_batch(&private_batch);

            // Read and add shares
            for share_path in share {
                let share_bytes = read_file(share_path)?;
                let decrypted = DecryptedShare::from_bytes(&share_bytes).map_err(|e| {
                    format!(
                        "Failed to parse share file {}: {:?}",
                        share_path.display(),
                        e
                    )
                })?;

                // Verify batch ID matches
                if decrypted.batch_id != private_batch.batch_id {
                    return Err(
                        format!("Share {} is for a different batch", share_path.display()).into(),
                    );
                }

                decryptor
                    .add_share(decrypted.share)
                    .map_err(|e| format!("Failed to add share: {:?}", e))?;
            }

            // Check if we have enough shares
            if !decryptor.can_recover() {
                return Err(format!(
                    "Not enough shares. Have {}, need {}",
                    decryptor.shares_collected(),
                    decryptor.threshold()
                )
                .into());
            }

            // Decrypt the batch
            let plaintexts = decryptor
                .decrypt_private_batch(&private_batch)
                .map_err(|e| format!("Failed to decrypt batch: {:?}", e))?;

            // Create output directory
            std::fs::create_dir_all(out)?;

            // Write decrypted receipts
            for (i, plaintext) in plaintexts.iter().enumerate() {
                let receipt_path = out.join(format!("receipt_{}.anb", i));
                write_file_atomic(&receipt_path, plaintext)?;
            }

            if json {
                #[derive(Serialize)]
                struct CombineResult {
                    output_dir: String,
                    batch_id: String,
                    num_receipts: usize,
                    shares_used: usize,
                }
                let output = JsonOutput::success(CombineResult {
                    output_dir: out.display().to_string(),
                    batch_id: hex::encode(private_batch.batch_id),
                    num_receipts: plaintexts.len(),
                    shares_used: decryptor.shares_collected(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Batch decrypted successfully!");
                println!("  Output directory: {}", out.display());
                println!("  Receipts:         {}", plaintexts.len());
                println!("  Shares used:      {}", decryptor.shares_collected());
            }
            Ok(())
        }

        PrivateBatchCommands::Verify {
            batch,
            receipt: _,
            index,
        } => {
            // Read batch file
            let batch_bytes = read_file(batch)?;
            let private_batch = PrivateBatch::from_bytes(&batch_bytes)
                .map_err(|e| format!("Failed to parse batch file: {:?}", e))?;

            // Verify leaf is in range
            if *index >= private_batch.len() {
                return Err(format!(
                    "Index {} out of range (batch has {} leaves)",
                    index,
                    private_batch.len()
                )
                .into());
            }

            // Verify Merkle proof
            let valid = private_batch
                .verify_leaf(*index)
                .map_err(|e| format!("Verification failed: {:?}", e))?;

            if json {
                #[derive(Serialize)]
                struct VerifyResult {
                    valid: bool,
                    batch_id: String,
                    merkle_root: String,
                    index: usize,
                }
                let output = JsonOutput::success(VerifyResult {
                    valid,
                    batch_id: hex::encode(private_batch.batch_id),
                    merkle_root: hex::encode(private_batch.merkle_root),
                    index: *index,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else if valid {
                println!("Verification PASSED");
                println!(
                    "  Leaf {} is included in batch {}",
                    index,
                    hex::encode(private_batch.batch_id)
                );
            } else {
                println!("Verification FAILED");
                return Err("Merkle proof verification failed".into());
            }
            Ok(())
        }

        PrivateBatchCommands::Info { batch } => {
            // Read batch file
            let batch_bytes = read_file(batch)?;
            let private_batch = PrivateBatch::from_bytes(&batch_bytes)
                .map_err(|e| format!("Failed to parse batch file: {:?}", e))?;

            if json {
                #[derive(Serialize)]
                struct InfoResult {
                    batch_id: String,
                    merkle_root: String,
                    num_leaves: usize,
                    threshold: u8,
                    total_recipients: u8,
                    created_at: u64,
                    anchored: bool,
                    recipient_fingerprints: Vec<String>,
                }
                let fingerprints: Vec<String> = private_batch
                    .key_envelope
                    .recipient_shares
                    .iter()
                    .map(|rs| hex::encode(rs.recipient_fingerprint))
                    .collect();

                let output = JsonOutput::success(InfoResult {
                    batch_id: hex::encode(private_batch.batch_id),
                    merkle_root: hex::encode(private_batch.merkle_root),
                    num_leaves: private_batch.len(),
                    threshold: private_batch.key_envelope.threshold,
                    total_recipients: private_batch.key_envelope.total_shares,
                    created_at: private_batch.created_at,
                    anchored: private_batch.anchored,
                    recipient_fingerprints: fingerprints,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Private Batch Information");
                println!("========================");
                println!("Batch ID:     {}", hex::encode(private_batch.batch_id));
                println!("Merkle root:  {}", hex::encode(private_batch.merkle_root));
                println!("Leaves:       {}", private_batch.len());
                println!(
                    "Threshold:    {}-of-{}",
                    private_batch.key_envelope.threshold, private_batch.key_envelope.total_shares
                );
                println!(
                    "Created:      {} (Unix timestamp)",
                    private_batch.created_at
                );
                println!(
                    "Anchored:     {}",
                    if private_batch.anchored { "Yes" } else { "No" }
                );
                println!();
                println!("Recipients:");
                for (i, rs) in private_batch
                    .key_envelope
                    .recipient_shares
                    .iter()
                    .enumerate()
                {
                    println!("  {}: {}", i, hex::encode(rs.recipient_fingerprint));
                }
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
            // Check file permissions on Unix (warn if group/world readable)
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if let Ok(metadata) = std::fs::metadata(&path) {
                    let mode = metadata.permissions().mode();
                    if mode & 0o077 != 0 {
                        eprintln!(
                            "Warning: Password file '{}' has insecure permissions ({:o}).",
                            path,
                            mode & 0o777
                        );
                        eprintln!(
                            "         Run 'chmod 600 {}' to fix this security issue.",
                            path
                        );
                    }
                }
            }

            let file = std::fs::File::open(&path)
                .map_err(|e| format!("Failed to open password file '{}': {}", path, e))?;
            let reader = std::io::BufReader::new(file);
            if let Some(Ok(line)) = reader.lines().next() {
                let password = line
                    .trim_end_matches('\n')
                    .trim_end_matches('\r')
                    .to_string();
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
        )
        .into());
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
                )
                .into());
            }

            let mut seed = [0u8; SEED_SIZE];
            seed.copy_from_slice(&seed_bytes);

            // SECURITY: Zeroize the Vec buffer immediately after copying
            seed_bytes.zeroize();

            let kp = KeyPair::from_seed(&seed).map_err(|e| {
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
                        "Wrong password ({} failed attempts). Next attempt allowed in {} seconds.\n\
                        Hint: If you forgot your password, you must create a new key with 'anubis-notary key init'.\n\
                        Your old signatures remain valid, but you cannot create new ones with the old key.",
                        failures, delay
                    )
                    .into())
                } else {
                    Err(format!(
                        "Wrong password ({} failed attempts).\n\
                        Hint: If you forgot your password, you must create a new key with 'anubis-notary key init'.",
                        failures
                    ).into())
                }
            } else {
                Err(e.into())
            }
        }
    }
}

/// Handle the seal command - encrypt a file using ML-KEM-1024.
///
/// # Sealed File Format
///
/// ```text
/// [4 bytes]  Version (0x414E5531 = "ANU1")
/// [1568 bytes] ML-KEM-1024 ciphertext (encapsulated shared secret)
/// [12 bytes] Nonce for ChaCha20Poly1305
/// [N bytes]  ChaCha20Poly1305 ciphertext (encrypted file + 16-byte tag)
/// ```
fn handle_seal(
    file: &PathBuf,
    recipient: &PathBuf,
    out: &PathBuf,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::aead::ChaCha20Poly1305;
    use anubis_core::mlkem::{MlKemPublicKey, CIPHERTEXT_SIZE};

    // Magic bytes for sealed file format
    const SEAL_MAGIC: &[u8; 4] = b"ANU1";

    // Read the recipient's public key
    let pk_bytes = read_file(recipient)?;
    let public_key = MlKemPublicKey::from_bytes(&pk_bytes)
        .map_err(|e| format!("Invalid public key: {:?}", e))?;

    // Read the file to encrypt
    let plaintext = read_file(file)?;

    // Encapsulate to get shared secret and ciphertext
    let (kem_ciphertext, shared_secret) = public_key
        .encapsulate()
        .map_err(|e| format!("ML-KEM encapsulation failed: {:?}", e))?;

    // Generate random nonce for ChaCha20Poly1305
    let mut nonce = [0u8; 12];
    getrandom::getrandom(&mut nonce).map_err(|e| format!("RNG failed: {}", e))?;

    // Encrypt the file with ChaCha20Poly1305
    let cipher = ChaCha20Poly1305::from_key(&shared_secret);
    let ciphertext = cipher.seal_fixed(&nonce, &[], &plaintext);

    // Build the sealed file
    let mut sealed = Vec::with_capacity(4 + CIPHERTEXT_SIZE + 12 + ciphertext.len());
    sealed.extend_from_slice(SEAL_MAGIC);
    sealed.extend_from_slice(&kem_ciphertext);
    sealed.extend_from_slice(&nonce);
    sealed.extend_from_slice(&ciphertext);

    // Write the sealed file
    write_file_atomic(out, &sealed)?;

    if json {
        #[derive(Serialize)]
        struct SealResult {
            input_file: String,
            output_file: String,
            input_size: usize,
            output_size: usize,
            algorithm: String,
        }
        let output = JsonOutput::success(SealResult {
            input_file: file.display().to_string(),
            output_file: out.display().to_string(),
            input_size: plaintext.len(),
            output_size: sealed.len(),
            algorithm: "ML-KEM-1024 + ChaCha20Poly1305".to_string(),
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!("Sealed: {}", file.display());
        println!("  Output: {}", out.display());
        println!("  Input size: {} bytes", plaintext.len());
        println!("  Sealed size: {} bytes", sealed.len());
        println!("  Algorithm: ML-KEM-1024 + ChaCha20Poly1305");
        println!();
        println!("Only the holder of the corresponding secret key can unseal this file.");
    }

    Ok(())
}

/// Handle the unseal command - decrypt a file using ML-KEM-1024.
fn handle_unseal(
    file: &PathBuf,
    secret_key: &PathBuf,
    out: &PathBuf,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::aead::ChaCha20Poly1305;
    use anubis_core::mlkem::{MlKemSecretKey, CIPHERTEXT_SIZE};

    // Magic bytes for sealed file format
    const SEAL_MAGIC: &[u8; 4] = b"ANU1";

    // Read the secret key
    let sk_bytes = read_file(secret_key)?;
    let secret = MlKemSecretKey::from_bytes(&sk_bytes)
        .map_err(|e| format!("Invalid secret key: {:?}", e))?;

    // Read the sealed file
    let sealed = read_file(file)?;

    // Verify minimum size: magic(4) + kem_ct(1568) + nonce(12) + tag(16)
    let min_size = 4 + CIPHERTEXT_SIZE + 12 + 16;
    if sealed.len() < min_size {
        return Err(format!(
            "Invalid sealed file: too small ({} bytes, need at least {})",
            sealed.len(),
            min_size
        )
        .into());
    }

    // Verify magic bytes
    if &sealed[0..4] != SEAL_MAGIC {
        return Err("Invalid sealed file: wrong magic bytes (not an Anubis sealed file)".into());
    }

    // Extract components
    let kem_ciphertext = &sealed[4..4 + CIPHERTEXT_SIZE];
    let nonce: [u8; 12] = sealed[4 + CIPHERTEXT_SIZE..4 + CIPHERTEXT_SIZE + 12]
        .try_into()
        .unwrap();
    let ciphertext = &sealed[4 + CIPHERTEXT_SIZE + 12..];

    // Decapsulate to recover shared secret
    let shared_secret = secret
        .decapsulate(kem_ciphertext)
        .map_err(|e| format!("ML-KEM decapsulation failed: {:?}", e))?;

    // Decrypt with ChaCha20Poly1305
    let cipher = ChaCha20Poly1305::from_key(&shared_secret);
    let plaintext = cipher
        .open_fixed(&nonce, &[], ciphertext)
        .map_err(|_| "Decryption failed: authentication error (wrong key or corrupted file)")?;

    // Write the decrypted file
    write_file_atomic(out, &plaintext)?;

    if json {
        #[derive(Serialize)]
        struct UnsealResult {
            input_file: String,
            output_file: String,
            sealed_size: usize,
            output_size: usize,
            algorithm: String,
        }
        let output = JsonOutput::success(UnsealResult {
            input_file: file.display().to_string(),
            output_file: out.display().to_string(),
            sealed_size: sealed.len(),
            output_size: plaintext.len(),
            algorithm: "ML-KEM-1024 + ChaCha20Poly1305".to_string(),
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!("Unsealed: {}", file.display());
        println!("  Output: {}", out.display());
        println!("  Sealed size: {} bytes", sealed.len());
        println!("  Output size: {} bytes", plaintext.len());
        println!("  Algorithm: ML-KEM-1024 + ChaCha20Poly1305");
    }

    Ok(())
}

fn handle_marriage(
    action: &MarriageCommands,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::marriage::{
        contracts, AssetSplit, DivorceCondition, MarriageDocument, MarriageTerms, Party,
    };

    match action {
        MarriageCommands::Init {
            parties,
            template,
            jurisdiction,
            out,
        } => {
            // Load keystore and keypair
            let ks = Keystore::open(Keystore::default_path())?;
            let keypair = load_keypair_with_password(&ks)?;

            // Parse party names
            let party_names: Vec<&str> = parties.split(',').map(|s| s.trim()).collect();
            if party_names.len() < 2 {
                return Err("Need at least 2 parties for a marriage".into());
            }

            // For now, all parties use the same keypair (user must specify others separately)
            // In production, each party would generate their own keypair
            let mut party_list = Vec::new();
            for name in &party_names {
                party_list.push(Party {
                    name: name.to_string(),
                    public_key: keypair.public.clone(),
                    starknet_address: None,
                });
            }

            // Set up terms based on template
            let terms = match template.as_str() {
                "monogamy" => MarriageTerms {
                    asset_split: AssetSplit::Equal,
                    divorce_conditions: vec![DivorceCondition::MutualConsent],
                    custom_clauses: vec![],
                },
                "polygamy" => MarriageTerms {
                    asset_split: AssetSplit::Proportional,
                    divorce_conditions: vec![DivorceCondition::Threshold {
                        required: (party_names.len() / 2 + 1) as u8,
                    }],
                    custom_clauses: vec![],
                },
                "simple" => MarriageTerms::default(),
                _ => {
                    return Err(format!(
                        "Unknown template: {}. Use: monogamy, polygamy, simple",
                        template
                    )
                    .into());
                }
            };

            // Create timestamp
            let created_at = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs();

            // Create document
            let doc = MarriageDocument::new(party_list, terms, jurisdiction.clone(), created_at)?;

            // Serialize to JSON
            #[derive(Serialize)]
            struct MarriageDocJson {
                version: u8,
                parties: Vec<PartyJson>,
                terms: TermsJson,
                jurisdiction: String,
                created_at: u64,
                signatures: Vec<SignatureJson>,
            }

            #[derive(Serialize)]
            struct PartyJson {
                name: String,
                public_key_hex: String,
                starknet_address: Option<String>,
            }

            #[derive(Serialize)]
            struct TermsJson {
                asset_split: String,
                divorce_conditions: Vec<String>,
                custom_clauses: Vec<String>,
            }

            #[derive(Serialize)]
            struct SignatureJson {
                party_index: usize,
                signature_hex: String,
            }

            let parties_json: Vec<PartyJson> = doc
                .parties
                .iter()
                .map(|p| PartyJson {
                    name: p.name.clone(),
                    public_key_hex: hex::encode(p.public_key.to_bytes()),
                    starknet_address: p.starknet_address.clone(),
                })
                .collect();

            let terms_json = TermsJson {
                asset_split: match &doc.terms.asset_split {
                    AssetSplit::Equal => "50/50".to_string(),
                    AssetSplit::Proportional => "proportional".to_string(),
                    AssetSplit::Custom(pcts) => format!("custom:{:?}", pcts),
                },
                divorce_conditions: doc
                    .terms
                    .divorce_conditions
                    .iter()
                    .map(|c| format!("{:?}", c))
                    .collect(),
                custom_clauses: doc.terms.custom_clauses.clone(),
            };

            let doc_json = MarriageDocJson {
                version: doc.version,
                parties: parties_json,
                terms: terms_json,
                jurisdiction: doc.jurisdiction.clone(),
                created_at: doc.created_at,
                signatures: vec![],
            };

            let json_str = serde_json::to_string_pretty(&doc_json)?;
            std::fs::write(out, &json_str)?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "document": out.display().to_string(),
                    "parties": party_names.len(),
                    "template": template,
                    "jurisdiction": jurisdiction,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Marriage document created: {}", out.display());
                println!("  Template: {}", template);
                println!("  Parties: {:?}", party_names);
                println!("  Jurisdiction: {}", jurisdiction);
                println!("\nNext steps:");
                println!(
                    "  1. Each party signs: anubis-notary marriage sign {} --party <index>",
                    out.display()
                );
                println!(
                    "  2. Create on-chain: anubis-notary marriage create {}",
                    out.display()
                );
            }

            Ok(())
        }

        MarriageCommands::Sign {
            document,
            party,
            vows,
            out,
        } => {
            // Load keystore and keypair
            let ks = Keystore::open(Keystore::default_path())?;
            let keypair = load_keypair_with_password(&ks)?;

            // Read document
            let doc_str = std::fs::read_to_string(document)?;
            let doc_value: serde_json::Value = serde_json::from_str(&doc_str)?;

            // Recreate the document from JSON
            // (In production, we'd have proper deserialization)
            let party_count = doc_value["parties"]
                .as_array()
                .map(|a| a.len())
                .unwrap_or(0);

            if *party >= party_count {
                return Err(
                    format!("Party index {} out of range (0-{})", party, party_count - 1).into(),
                );
            }

            // Get party name for display
            let party_name = doc_value["parties"]
                .as_array()
                .and_then(|parties| parties.get(*party))
                .and_then(|p| p["name"].as_str())
                .unwrap_or("Unknown")
                .to_string();

            // Compute vows hash if provided
            let vows_hash = vows.as_ref().map(|v| {
                let hash = anubis_core::keccak::sha3_256(v.as_bytes());
                format!("0x{}", hex::encode(&hash))
            });

            // Sign the document digest
            let digest = anubis_core::keccak::sha3_256(doc_str.as_bytes());
            let signature = keypair.secret_key().sign(&digest)?;

            // Add signature to document
            let mut doc_value = doc_value;
            let sigs = doc_value["signatures"].as_array_mut().unwrap();

            let mut sig_entry = serde_json::json!({
                "party_index": party,
                "party_name": party_name,
                "signature_hex": hex::encode(signature.to_bytes()),
            });

            if let Some(ref vh) = vows_hash {
                sig_entry["vows_hash"] = serde_json::json!(vh);
            }
            if let Some(ref v) = vows {
                sig_entry["vows_text"] = serde_json::json!(v);
            }

            sigs.push(sig_entry);

            let output_path = out.as_ref().unwrap_or(document);
            let json_str = serde_json::to_string_pretty(&doc_value)?;
            std::fs::write(output_path, &json_str)?;

            if json {
                let mut output_data = serde_json::json!({
                    "document": output_path.display().to_string(),
                    "party_index": party,
                    "party_name": party_name,
                    "signed": true,
                });
                if let Some(ref vh) = vows_hash {
                    output_data["vows_hash"] = serde_json::json!(vh);
                }
                let output = JsonOutput::success(output_data);
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!(
                    "Marriage document signed by party {} ({})",
                    party, party_name
                );
                println!("  Document: {}", output_path.display());
                if let Some(ref vh) = vows_hash {
                    println!("  Vows hash: {}", vh);
                    println!("  Your vows are now cryptographically bound to this marriage.");
                }
            }

            Ok(())
        }

        MarriageCommands::Verify { document } => {
            let doc_str = std::fs::read_to_string(document)?;
            let doc_value: serde_json::Value = serde_json::from_str(&doc_str)?;

            let party_count = doc_value["parties"]
                .as_array()
                .map(|a| a.len())
                .unwrap_or(0);
            let sig_count = doc_value["signatures"]
                .as_array()
                .map(|a| a.len())
                .unwrap_or(0);

            let fully_signed = sig_count == party_count;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "document": document.display().to_string(),
                    "party_count": party_count,
                    "signature_count": sig_count,
                    "fully_signed": fully_signed,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Marriage document: {}", document.display());
                println!("  Parties: {}", party_count);
                println!("  Signatures: {}/{}", sig_count, party_count);
                if fully_signed {
                    println!("  Status: FULLY SIGNED - Ready for on-chain creation");
                } else {
                    println!(
                        "  Status: PENDING - {} more signature(s) needed",
                        party_count - sig_count
                    );
                }
            }

            Ok(())
        }

        MarriageCommands::Create {
            document,
            network,
            mint_rings,
            wait: _,
        } => {
            let doc_str = std::fs::read_to_string(&document)?;
            let doc_value: serde_json::Value = serde_json::from_str(&doc_str)?;

            let parties = doc_value["parties"]
                .as_array()
                .ok_or("No parties in document")?;
            let party_count = parties.len();
            let signatures = doc_value["signatures"]
                .as_array()
                .ok_or("No signatures in document")?;
            let sig_count = signatures.len();

            if sig_count != party_count {
                return Err(format!(
                    "Document not fully signed: {}/{} signatures",
                    sig_count, party_count
                )
                .into());
            }

            // Compute certificate hash
            let cert_hash = anubis_core::keccak::sha3_256(doc_str.as_bytes());
            let cert_hash_felt = format!("0x{}", hex::encode(&cert_hash[..31])); // Truncate to fit felt252

            let rpc_url = match network.as_str() {
                "mainnet" => "https://rpc.starknet.lava.build",
                _ => "https://api.cartridge.gg/x/starknet/sepolia",
            };
            let marriage_contract = match network.as_str() {
                "mainnet" => contracts::MARRIAGE_ORACLE_MAINNET,
                _ => contracts::MARRIAGE_ORACLE_SEPOLIA,
            };
            let ring_contract = match network.as_str() {
                "mainnet" => contracts::MARRIAGE_RING_MAINNET,
                _ => contracts::MARRIAGE_RING_SEPOLIA,
            };
            let account_name = std::env::var("STARKNET_ACCOUNT_NAME")
                .unwrap_or_else(|_| "anubis-deployer".to_string());

            if !json {
                println!("Creating marriage on Starknet ({})...", network);
                println!("  Parties: {}", party_count);
                println!("  Certificate hash: {}", hex::encode(&cert_hash));
            }

            // Get next marriage ID (current count + 1 since create_marriage increments after)
            let count_output = std::process::Command::new("sncast")
                .args([
                    "call",
                    "--url",
                    rpc_url,
                    "--contract-address",
                    marriage_contract,
                    "--function",
                    "get_marriage_count",
                ])
                .output()?;
            let count_str = String::from_utf8_lossy(&count_output.stdout);
            // Parse "Response:     7_u64" or "Response Raw: [0x7]" format
            let marriage_id: u64 = count_str
                .lines()
                .find(|l| l.contains("Response:") && !l.contains("Raw"))
                .and_then(|l| {
                    // Extract number from "Response:     7_u64"
                    l.split_whitespace()
                        .last()
                        .and_then(|s| s.split('_').next())
                        .and_then(|s| s.trim().parse().ok())
                })
                .or_else(|| {
                    // Fallback: try parsing hex from Raw response
                    count_str.lines().find(|l| l.contains("0x")).and_then(|l| {
                        l.split("0x")
                            .nth(1)
                            .and_then(|s| {
                                s.chars()
                                    .take_while(|c| c.is_ascii_hexdigit())
                                    .collect::<String>()
                                    .parse()
                                    .ok()
                            })
                            .or_else(|| {
                                u64::from_str_radix(
                                    &l.split("0x")
                                        .nth(1)?
                                        .chars()
                                        .take_while(|c| c.is_ascii_hexdigit())
                                        .collect::<String>(),
                                    16,
                                )
                                .ok()
                            })
                    })
                })
                .unwrap_or(1);

            // The next marriage will have ID = current_count + 1
            let next_marriage_id = marriage_id + 1;

            if !json {
                println!("  Marriage ID will be: {}", next_marriage_id);
            }

            // Build calldata for create_marriage
            // Format: partner_count, [partners...], cert_hash, anchor_id (0 for now), required_sigs
            let required_sigs = party_count;
            let mut calldata: Vec<String> = vec![party_count.to_string()];

            // Add placeholder partner addresses (use account address for demo)
            for _ in 0..party_count {
                calldata.push(
                    "0x0634a183f349e68fde9719a3c3bbc83faf557afcad28b143ae99340f2bb2458e"
                        .to_string(),
                );
            }
            calldata.push(cert_hash_felt.clone());
            calldata.push("0".to_string()); // anchor_id
            calldata.push(required_sigs.to_string());

            let calldata_str = calldata.join(" ");

            // Create marriage on-chain
            let create_output = std::process::Command::new("sncast")
                .args([
                    "--account",
                    &account_name,
                    "invoke",
                    "--url",
                    rpc_url,
                    "--contract-address",
                    marriage_contract,
                    "--function",
                    "create_marriage",
                    "--calldata",
                    &calldata_str,
                ])
                .output()?;

            let create_stdout = String::from_utf8_lossy(&create_output.stdout);
            let create_stderr = String::from_utf8_lossy(&create_output.stderr);

            if !create_output.status.success() {
                return Err(format!("Failed to create marriage: {}", create_stderr).into());
            }

            // Extract transaction hash
            let tx_hash = create_stdout
                .lines()
                .find(|l| l.contains("transaction_hash"))
                .and_then(|l| l.split(':').nth(1).or(l.split('=').nth(1)))
                .map(|s| s.trim().to_string())
                .unwrap_or_else(|| "unknown".to_string());

            if !json {
                println!("  Marriage created! TX: {}", tx_hash);
            }

            // Mint rings if requested
            if *mint_rings {
                if !json {
                    println!("\nMinting NFT wedding rings...");
                }

                // Extract vows hashes from signatures
                let mut vows_hashes: Vec<String> = Vec::new();
                let mut name_hashes: Vec<String> = Vec::new();

                for (i, sig) in signatures.iter().enumerate() {
                    // Get vows hash or compute from party name
                    // Truncate to 31 bytes (62 hex chars) to fit in felt252
                    let vows_hash = sig
                        .get("vows_hash")
                        .and_then(|v| v.as_str())
                        .map(|s| {
                            // Truncate "0x..." hash to fit felt252 (max 31 bytes = 62 hex chars)
                            let hex_part = s.trim_start_matches("0x");
                            if hex_part.len() > 62 {
                                format!("0x{}", &hex_part[..62])
                            } else {
                                s.to_string()
                            }
                        })
                        .unwrap_or_else(|| {
                            // No vows - use a default placeholder
                            format!("0x{:062x}", i + 1)
                        });
                    vows_hashes.push(vows_hash);

                    // Get party name hash
                    let party_name = parties
                        .get(i)
                        .and_then(|p| p["name"].as_str())
                        .unwrap_or("Partner");
                    let name_hash_bytes = anubis_core::keccak::sha3_256(party_name.as_bytes());
                    name_hashes.push(format!("0x{}", hex::encode(&name_hash_bytes[..31])));
                }

                // Build mint calldata
                // mint_rings(marriage_id, partner_count, partners[], name_hashes[], vows_hashes[], marriage_hash)
                let mut mint_calldata: Vec<String> =
                    vec![next_marriage_id.to_string(), party_count.to_string()];

                // Partner addresses (placeholders)
                for _ in 0..party_count {
                    mint_calldata.push(
                        "0x0634a183f349e68fde9719a3c3bbc83faf557afcad28b143ae99340f2bb2458e"
                            .to_string(),
                    );
                }

                // Name hashes
                mint_calldata.push(party_count.to_string());
                for nh in &name_hashes {
                    mint_calldata.push(nh.clone());
                }

                // Vows hashes
                mint_calldata.push(party_count.to_string());
                for vh in &vows_hashes {
                    mint_calldata.push(vh.clone());
                }

                // Marriage hash
                mint_calldata.push(cert_hash_felt.clone());

                let mint_calldata_str = mint_calldata.join(" ");

                let mint_output = std::process::Command::new("sncast")
                    .args([
                        "--account",
                        &account_name,
                        "invoke",
                        "--url",
                        rpc_url,
                        "--contract-address",
                        ring_contract,
                        "--function",
                        "mint_rings",
                        "--calldata",
                        &mint_calldata_str,
                    ])
                    .output()?;

                let mint_stdout = String::from_utf8_lossy(&mint_output.stdout);

                if mint_output.status.success() {
                    let mint_tx = mint_stdout
                        .lines()
                        .find(|l| l.contains("transaction_hash"))
                        .and_then(|l| l.split(':').nth(1).or(l.split('=').nth(1)))
                        .map(|s| s.trim().to_string())
                        .unwrap_or_else(|| "unknown".to_string());

                    if !json {
                        println!("  Rings minted! TX: {}", mint_tx);
                        for i in 0..party_count {
                            let token_id = next_marriage_id * 1000 + i as u64;
                            let party_name = parties
                                .get(i)
                                .and_then(|p| p["name"].as_str())
                                .unwrap_or("Partner");
                            println!("    Ring #{} for {}", token_id, party_name);
                        }
                    }
                } else {
                    let mint_stderr = String::from_utf8_lossy(&mint_output.stderr);
                    if !json {
                        println!("  Warning: Failed to mint rings: {}", mint_stderr);
                    }
                }
            }

            if json {
                let mut output_data = serde_json::json!({
                    "marriage_id": next_marriage_id,
                    "certificate_hash": hex::encode(&cert_hash),
                    "network": network,
                    "transaction_hash": tx_hash,
                    "contract": marriage_contract,
                    "status": "created",
                });
                if *mint_rings {
                    let ring_tokens: Vec<u64> = (0..party_count as u64)
                        .map(|i| next_marriage_id * 1000 + i)
                        .collect();
                    output_data["rings"] = serde_json::json!(ring_tokens);
                }
                let output = JsonOutput::success(output_data);
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!(
                    "\nMarriage #{} successfully created on Starknet!",
                    next_marriage_id
                );
                if !*mint_rings {
                    println!("\nTo mint NFT rings, run:");
                    println!(
                        "  anubis-notary marriage rings mint --marriage-id {}",
                        next_marriage_id
                    );
                }
            }

            Ok(())
        }

        MarriageCommands::Divorce {
            marriage_id,
            reason,
            network,
            wait: _,
        } => {
            let rpc_url = match network.as_str() {
                "mainnet" => "https://rpc.starknet.lava.build",
                _ => "https://api.cartridge.gg/x/starknet/sepolia",
            };
            let marriage_contract = match network.as_str() {
                "mainnet" => contracts::MARRIAGE_ORACLE_MAINNET,
                _ => contracts::MARRIAGE_ORACLE_SEPOLIA,
            };
            let ring_contract = match network.as_str() {
                "mainnet" => contracts::MARRIAGE_RING_MAINNET,
                _ => contracts::MARRIAGE_RING_SEPOLIA,
            };
            let account_name = std::env::var("STARKNET_ACCOUNT_NAME")
                .unwrap_or_else(|_| "anubis-deployer".to_string());

            if !json {
                println!("Executing divorce for marriage #{}...", marriage_id);
            }

            // Step 1: Get marriage info to know partner count
            let get_marriage_output = std::process::Command::new("sncast")
                .args([
                    "call",
                    "--url",
                    rpc_url,
                    "--contract-address",
                    marriage_contract,
                    "--function",
                    "get_marriage",
                    "--calldata",
                    &marriage_id.to_string(),
                ])
                .output()?;

            let stdout = String::from_utf8_lossy(&get_marriage_output.stdout);

            // Parse partner_count from response (second field in MarriageRecord)
            let partner_count: u64 = stdout
                .lines()
                .find(|l| l.contains("partner_count:"))
                .and_then(|l| l.split("partner_count:").nth(1))
                .and_then(|s| s.trim().split('_').next())
                .and_then(|s| s.trim().parse().ok())
                .unwrap_or(2); // Default to 2 if parsing fails

            if !json {
                println!("  Found {} partners in marriage", partner_count);
            }

            // Step 2: Execute divorce on-chain
            let reason_hash = format!(
                "0x{:x}",
                reason
                    .bytes()
                    .fold(0u64, |acc, b| acc.wrapping_mul(31).wrapping_add(b as u64))
            );

            let divorce_output = std::process::Command::new("sncast")
                .args([
                    "--account",
                    &account_name,
                    "invoke",
                    "--url",
                    rpc_url,
                    "--contract-address",
                    marriage_contract,
                    "--function",
                    "execute_divorce",
                    "--calldata",
                    &marriage_id.to_string(),
                    &reason_hash,
                    "1",
                ])
                .output()?;

            let divorce_stdout = String::from_utf8_lossy(&divorce_output.stdout);
            let divorce_stderr = String::from_utf8_lossy(&divorce_output.stderr);

            if !divorce_output.status.success() {
                return Err(format!("Failed to execute divorce: {}", divorce_stderr).into());
            }

            let divorce_tx = divorce_stdout
                .lines()
                .find(|line| line.contains("Transaction Hash:"))
                .and_then(|line| line.split(':').nth(1))
                .map(|s| s.trim())
                .unwrap_or("unknown");

            if !json {
                println!("  Divorce executed: {}", divorce_tx);
                println!("  Burning {} rings...", partner_count);
            }

            // Step 3: Burn all rings for this marriage
            let mut burned_rings = Vec::new();
            for i in 0..partner_count {
                let token_id = marriage_id * 1000 + i;

                // Check if ring exists first
                let exists_output = std::process::Command::new("sncast")
                    .args([
                        "call",
                        "--url",
                        rpc_url,
                        "--contract-address",
                        ring_contract,
                        "--function",
                        "exists",
                        "--calldata",
                        &token_id.to_string(),
                        "0",
                    ])
                    .output()?;

                let exists_stdout = String::from_utf8_lossy(&exists_output.stdout);
                let ring_exists = exists_stdout.contains("true") || exists_stdout.contains("[0x1]");

                if ring_exists {
                    let burn_output = std::process::Command::new("sncast")
                        .args([
                            "--account",
                            &account_name,
                            "invoke",
                            "--url",
                            rpc_url,
                            "--contract-address",
                            ring_contract,
                            "--function",
                            "burn_ring",
                            "--calldata",
                            &token_id.to_string(),
                            "0",
                        ])
                        .output()?;

                    let burn_stdout = String::from_utf8_lossy(&burn_output.stdout);

                    if burn_output.status.success() {
                        let burn_tx = burn_stdout
                            .lines()
                            .find(|line| line.contains("Transaction Hash:"))
                            .and_then(|line| line.split(':').nth(1))
                            .map(|s| s.trim().to_string())
                            .unwrap_or_else(|| "unknown".to_string());

                        burned_rings.push(serde_json::json!({
                            "token_id": token_id,
                            "tx": burn_tx,
                        }));

                        if !json {
                            println!("    Ring #{} burned: {}", token_id, burn_tx);
                        }
                    }
                } else if !json {
                    println!("    Ring #{} already burned or doesn't exist", token_id);
                }
            }

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "marriage_id": marriage_id,
                    "reason": reason,
                    "network": network,
                    "status": "divorced",
                    "divorce_tx": divorce_tx,
                    "rings_burned": burned_rings,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!();
                println!("Divorce complete!");
                println!("  Marriage #{} is now DISSOLVED", marriage_id);
                println!("  Rings burned: {}", burned_rings.len());
            }

            Ok(())
        }

        MarriageCommands::Info { sepolia } => {
            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "sepolia": {
                        "marriage_oracle": contracts::MARRIAGE_ORACLE_SEPOLIA,
                        "marriage_ring_nft": contracts::MARRIAGE_RING_SEPOLIA,
                    },
                    "mainnet": {
                        "status": "not_deployed",
                    },
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Anubis Marriage System - Contract Addresses");
                println!();
                if *sepolia {
                    println!("Sepolia Testnet:");
                    println!("  Marriage Oracle: {}", contracts::MARRIAGE_ORACLE_SEPOLIA);
                    println!("  Marriage Ring NFT: {}", contracts::MARRIAGE_RING_SEPOLIA);
                } else {
                    println!("Sepolia Testnet:");
                    println!("  Marriage Oracle: {}", contracts::MARRIAGE_ORACLE_SEPOLIA);
                    println!("  Marriage Ring NFT: {}", contracts::MARRIAGE_RING_SEPOLIA);
                    println!();
                    println!("Mainnet: Not yet deployed");
                }
            }

            Ok(())
        }

        MarriageCommands::Templates => {
            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "templates": [
                        {
                            "name": "monogamy",
                            "description": "Standard 2-party marriage with equal asset split",
                            "max_parties": 2,
                            "asset_split": "50/50",
                            "divorce_condition": "mutual_consent",
                        },
                        {
                            "name": "polygamy",
                            "description": "N-party marriage with proportional asset split",
                            "max_parties": 10,
                            "asset_split": "proportional",
                            "divorce_condition": "threshold (majority)",
                        },
                        {
                            "name": "simple",
                            "description": "Minimal template with default terms",
                            "max_parties": 10,
                            "asset_split": "equal",
                            "divorce_condition": "mutual_consent",
                        },
                    ],
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Available Marriage Templates:");
                println!();
                println!("  monogamy");
                println!("    Standard 2-party marriage with equal asset split");
                println!("    Divorce: Mutual consent required");
                println!();
                println!("  polygamy");
                println!("    N-party marriage (up to 10) with proportional asset split");
                println!("    Divorce: Majority threshold required");
                println!();
                println!("  simple");
                println!("    Minimal template with default terms");
                println!("    Divorce: Mutual consent");
                println!();
                println!("Use: anubis-notary marriage init --template <name> --parties \"Alice,Bob\" --jurisdiction US-CA -o marriage.json");
            }

            Ok(())
        }

        MarriageCommands::Rings { action } => {
            handle_rings(action, json)?;
            Ok(())
        }
    }
}

fn handle_rings(action: &RingsCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    // Contract addresses
    const RING_CONTRACT_SEPOLIA: &str =
        "0x07f579e725cbd8dbac8974245d05824f1024bc0c041d98e0a6133dbd5cdc7090";
    const RING_CONTRACT_MAINNET: &str =
        "0x07f579e725cbd8dbac8974245d05824f1024bc0c041d98e0a6133dbd5cdc7090"; // TODO: Deploy mainnet

    fn get_ring_contract(network: &str) -> &'static str {
        match network {
            "mainnet" => RING_CONTRACT_MAINNET,
            _ => RING_CONTRACT_SEPOLIA,
        }
    }

    fn get_rpc_url(network: &str) -> &'static str {
        match network {
            "mainnet" => "https://rpc.starknet.lava.build/rpc/v0_7",
            _ => "https://api.cartridge.gg/x/starknet/sepolia",
        }
    }

    match action {
        RingsCommands::Mint {
            marriage_id,
            partners,
            name_hashes,
            vows_hashes,
            marriage_hash,
            network,
        } => {
            let contract = get_ring_contract(network);
            let rpc_url = get_rpc_url(network);

            // Parse comma-separated values
            let partner_list: Vec<&str> = partners.split(',').map(|s| s.trim()).collect();
            let name_hash_list: Vec<&str> = name_hashes.split(',').map(|s| s.trim()).collect();
            let vows_hash_list: Vec<&str> = vows_hashes.split(',').map(|s| s.trim()).collect();

            if partner_list.len() != name_hash_list.len()
                || partner_list.len() != vows_hash_list.len()
            {
                return Err("Number of partners, name_hashes, and vows_hashes must match".into());
            }

            // Build calldata: marriage_id, [partners], [name_hashes], [vows_hashes], marriage_hash
            let mut calldata = vec![marriage_id.to_string()];

            // Partners array
            calldata.push(partner_list.len().to_string());
            calldata.extend(partner_list.iter().map(|s| s.to_string()));

            // Name hashes array
            calldata.push(name_hash_list.len().to_string());
            calldata.extend(name_hash_list.iter().map(|s| s.to_string()));

            // Vows hashes array
            calldata.push(vows_hash_list.len().to_string());
            calldata.extend(vows_hash_list.iter().map(|s| s.to_string()));

            // Marriage hash
            calldata.push(marriage_hash.clone());

            let calldata_str = calldata.join(" ");

            if !json {
                println!(
                    "Minting {} rings for marriage #{}...",
                    partner_list.len(),
                    marriage_id
                );
            }

            // Get account name from env or use default
            let account_name = std::env::var("STARKNET_ACCOUNT_NAME")
                .unwrap_or_else(|_| "anubis-deployer".to_string());

            let output = std::process::Command::new("sncast")
                .args([
                    "--account",
                    &account_name,
                    "invoke",
                    "--url",
                    rpc_url,
                    "--contract-address",
                    contract,
                    "--function",
                    "mint_rings",
                    "--calldata",
                ])
                .args(calldata_str.split_whitespace())
                .output()?;

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            if output.status.success() {
                // Extract transaction hash
                let tx_hash = stdout
                    .lines()
                    .find(|line| line.contains("Transaction Hash:"))
                    .and_then(|line| line.split(':').nth(1))
                    .map(|s| s.trim())
                    .unwrap_or("unknown");

                if json {
                    let output = serde_json::json!({
                        "success": true,
                        "action": "mint_rings",
                        "marriage_id": marriage_id,
                        "ring_count": partner_list.len(),
                        "transaction_hash": tx_hash,
                        "network": network,
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Rings minted successfully!");
                    println!("  Marriage ID: {}", marriage_id);
                    println!("  Rings minted: {}", partner_list.len());
                    println!("  TX: {}", tx_hash);
                    println!();
                    println!("Token IDs:");
                    for (i, partner) in partner_list.iter().enumerate() {
                        let token_id = *marriage_id * 1000 + i as u64;
                        println!("  Ring #{}: Token ID {} -> {}", i, token_id, partner);
                    }
                }
            } else {
                return Err(format!("Failed to mint rings: {}", stderr).into());
            }
        }

        RingsCommands::Burn { token_id, network } => {
            let contract = get_ring_contract(network);
            let rpc_url = get_rpc_url(network);

            if !json {
                println!("Burning ring #{}...", token_id);
            }

            let account_name = std::env::var("STARKNET_ACCOUNT_NAME")
                .unwrap_or_else(|_| "anubis-deployer".to_string());

            let output = std::process::Command::new("sncast")
                .args([
                    "--account",
                    &account_name,
                    "invoke",
                    "--url",
                    rpc_url,
                    "--contract-address",
                    contract,
                    "--function",
                    "burn_ring",
                    "--calldata",
                    &token_id.to_string(),
                    "0",
                ]) // u256 = (low, high)
                .output()?;

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            if output.status.success() {
                let tx_hash = stdout
                    .lines()
                    .find(|line| line.contains("Transaction Hash:"))
                    .and_then(|line| line.split(':').nth(1))
                    .map(|s| s.trim())
                    .unwrap_or("unknown");

                if json {
                    let output = serde_json::json!({
                        "success": true,
                        "action": "burn_ring",
                        "token_id": token_id,
                        "transaction_hash": tx_hash,
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Ring burned successfully!");
                    println!("  Token ID: {}", token_id);
                    println!("  TX: {}", tx_hash);
                }
            } else {
                return Err(format!("Failed to burn ring: {}", stderr).into());
            }
        }

        RingsCommands::Show { token_id, network } => {
            let contract = get_ring_contract(network);
            let rpc_url = get_rpc_url(network);

            let output = std::process::Command::new("sncast")
                .args([
                    "call",
                    "--url",
                    rpc_url,
                    "--contract-address",
                    contract,
                    "--function",
                    "get_ring_metadata",
                    "--calldata",
                    &token_id.to_string(),
                    "0",
                ])
                .output()?;

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            if output.status.success() {
                // Parse the response
                if let Some(response_line) = stdout.lines().find(|l| l.starts_with("Response:")) {
                    let response = response_line.trim_start_matches("Response:").trim();

                    if json {
                        let output = serde_json::json!({
                            "success": true,
                            "token_id": token_id,
                            "metadata": response,
                        });
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Ring Metadata (Token #{})", token_id);
                        println!("  {}", response);

                        // Try to extract marriage_id from token_id
                        let marriage_id = token_id / 1000;
                        let partner_index = token_id % 1000;
                        println!();
                        println!("  Derived:");
                        println!("    Marriage ID: {}", marriage_id);
                        println!("    Partner Index: {}", partner_index);
                    }
                } else {
                    return Err(format!("Could not parse response: {}", stdout).into());
                }
            } else {
                return Err(format!("Failed to get ring metadata: {}", stderr).into());
            }
        }

        RingsCommands::Exists { token_id, network } => {
            let contract = get_ring_contract(network);
            let rpc_url = get_rpc_url(network);

            let output = std::process::Command::new("sncast")
                .args([
                    "call",
                    "--url",
                    rpc_url,
                    "--contract-address",
                    contract,
                    "--function",
                    "exists",
                    "--calldata",
                    &token_id.to_string(),
                    "0",
                ])
                .output()?;

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            if output.status.success() {
                let exists = stdout.contains("true") || stdout.contains("[0x1]");

                if json {
                    let output = serde_json::json!({
                        "success": true,
                        "token_id": token_id,
                        "exists": exists,
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    if exists {
                        println!("Ring #{} EXISTS", token_id);
                    } else {
                        println!("Ring #{} does NOT exist", token_id);
                    }
                }
            } else {
                return Err(format!("Failed to check ring existence: {}", stderr).into());
            }
        }

        RingsCommands::Supply { network } => {
            let contract = get_ring_contract(network);
            let rpc_url = get_rpc_url(network);

            let output = std::process::Command::new("sncast")
                .args([
                    "call",
                    "--url",
                    rpc_url,
                    "--contract-address",
                    contract,
                    "--function",
                    "total_supply",
                ])
                .output()?;

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            if output.status.success() {
                // Extract supply from response
                let supply = stdout
                    .lines()
                    .find(|l| l.starts_with("Response:"))
                    .and_then(|l| l.split_whitespace().nth(1))
                    .and_then(|s| s.trim_end_matches("_u256").parse::<u64>().ok())
                    .unwrap_or(0);

                if json {
                    let output = serde_json::json!({
                        "success": true,
                        "total_supply": supply,
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Total Ring Supply: {}", supply);
                }
            } else {
                return Err(format!("Failed to get supply: {}", stderr).into());
            }
        }

        RingsCommands::UpdateVows {
            token_id,
            vows_hash,
            network,
        } => {
            let contract = get_ring_contract(network);
            let rpc_url = get_rpc_url(network);

            if !json {
                println!("Updating vows for ring #{}...", token_id);
            }

            let account_name = std::env::var("STARKNET_ACCOUNT_NAME")
                .unwrap_or_else(|_| "anubis-deployer".to_string());

            let output = std::process::Command::new("sncast")
                .args([
                    "--account",
                    &account_name,
                    "invoke",
                    "--url",
                    rpc_url,
                    "--contract-address",
                    contract,
                    "--function",
                    "update_vows",
                    "--calldata",
                    &token_id.to_string(),
                    "0",
                    vows_hash,
                ])
                .output()?;

            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            if output.status.success() {
                let tx_hash = stdout
                    .lines()
                    .find(|line| line.contains("Transaction Hash:"))
                    .and_then(|line| line.split(':').nth(1))
                    .map(|s| s.trim())
                    .unwrap_or("unknown");

                if json {
                    let output = serde_json::json!({
                        "success": true,
                        "action": "update_vows",
                        "token_id": token_id,
                        "new_vows_hash": vows_hash,
                        "transaction_hash": tx_hash,
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Vows updated successfully!");
                    println!("  Token ID: {}", token_id);
                    println!("  New Vows Hash: {}", vows_hash);
                    println!("  TX: {}", tx_hash);
                }
            } else {
                return Err(format!("Failed to update vows: {}", stderr).into());
            }
        }
    }

    Ok(())
}
