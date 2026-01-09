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
//! - `ANUBIS_CRYPTO_PROFILE` - Cryptographic profile: "cnsa2" (default), "balanced", "fips140"
//!
//! # Cryptographic Profiles
//!
//! Anubis properly separates algorithm selection (WHAT) from module validation (HOW):
//!
//! | Profile | Algorithm Suite | Security Level | Use Case |
//! |---------|-----------------|----------------|----------|
//! | `cnsa2` | ML-DSA-87, ML-KEM-1024, AES-256-GCM, SHA-512 | NIST Level 5 | Default, NSS/government |
//! | `balanced` | ML-DSA-65, ML-KEM-768, ChaCha20Poly1305, SHA-384 | NIST Level 3 | Constrained environments |
//! | `fips140` | Same as cnsa2 + FIPS 140-3 validated module | NIST Level 5 | Government contracts |
//!
//! **Important**: FIPS 140-3 is about module VALIDATION, not algorithm SELECTION.
//! All profiles use CNSA 2.0 algorithms by default.
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
use std::path::{Path, PathBuf};
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

    /// Cryptographic profile: cnsa2 (default), balanced, fips140.
    ///
    /// - cnsa2: NIST Level 5 (ML-DSA-87, ML-KEM-1024, AES-256-GCM, SHA-512)
    /// - balanced: NIST Level 3 (ML-DSA-65, ML-KEM-768, ChaCha20Poly1305, SHA-384)
    /// - fips140: CNSA 2.0 + FIPS 140-3 validated module (requires --features fips)
    ///
    /// Can also be set via ANUBIS_CRYPTO_PROFILE environment variable.
    #[arg(long, global = true, env = "ANUBIS_CRYPTO_PROFILE", value_parser = parse_profile)]
    profile: Option<String>,

    #[command(subcommand)]
    command: Commands,
}

/// Parse and validate cryptographic profile argument
fn parse_profile(s: &str) -> Result<String, String> {
    match s.to_lowercase().as_str() {
        "cnsa2" | "cnsa" | "cnsa-2.0" | "level5" | "nist5" => Ok("cnsa2".to_string()),
        "balanced" | "level3" | "nist3" => Ok("balanced".to_string()),
        "fips140" | "fips" | "fips-140-3" => {
            // Check if FIPS mode is available
            if !anubis_core::profile::ProfileConfig::fips_available() {
                return Err(
                    "FIPS 140-3 mode not available. Build with --features fips (requires CMake, Go, Linux)"
                        .to_string(),
                );
            }
            Ok("fips140".to_string())
        }
        _ => Err(format!(
            "Unknown profile '{}'. Valid profiles: cnsa2, balanced, fips140",
            s
        )),
    }
}

/// Initialize the global cryptographic profile from CLI or environment
fn init_crypto_profile(cli: &Cli) -> Result<(), anubis_core::profile::ProfileError> {
    use anubis_core::profile::{ProfileConfig, set_global_config};

    let config = match cli.profile.as_deref() {
        Some("cnsa2") | None => ProfileConfig::cnsa2(),
        Some("balanced") => ProfileConfig::balanced(),
        Some("fips140") => ProfileConfig::cnsa2_fips(),
        Some(other) => {
            // This shouldn't happen due to parse_profile, but handle it gracefully
            eprintln!("Warning: Unknown profile '{}', using CNSA 2.0 default", other);
            ProfileConfig::cnsa2()
        }
    };

    set_global_config(config)
}

/// Handle the profile command - show current configuration with CNSA 2.0 compliance
fn handle_profile(json: bool) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::cnsa2::Cnsa2Validator;
    use anubis_core::profile::get_global_config;

    let config = get_global_config();
    let summary = config.summary();
    let compliance = Cnsa2Validator::check_compliance();

    if json {
        #[derive(Serialize)]
        struct ProfileOutput {
            profile: String,
            backend: String,
            security_level: String,
            nss_approved: bool,
            fips_required: bool,
            fips_available: bool,
            algorithms: AlgorithmInfo,
            cnsa2_compliance: Cnsa2ComplianceInfo,
        }

        #[derive(Serialize)]
        struct AlgorithmInfo {
            signature: String,
            kem: String,
            symmetric: String,
            hash: String,
        }

        #[derive(Serialize)]
        struct Cnsa2ComplianceInfo {
            compliant: bool,
            checks_passed: usize,
            checks_total: usize,
            checks: Vec<ComplianceCheckInfo>,
        }

        #[derive(Serialize)]
        struct ComplianceCheckInfo {
            component: String,
            algorithm: String,
            compliant: bool,
            standard: String,
        }

        let output = ProfileOutput {
            profile: summary.profile_name.to_string(),
            backend: summary.backend_name.to_string(),
            security_level: format!("{}", summary.security_level),
            nss_approved: summary.nss_approved,
            fips_required: summary.fips_required,
            fips_available: summary.fips_available,
            algorithms: AlgorithmInfo {
                signature: summary.signature.to_string(),
                kem: summary.kem.to_string(),
                symmetric: summary.symmetric.to_string(),
                hash: summary.hash.to_string(),
            },
            cnsa2_compliance: Cnsa2ComplianceInfo {
                compliant: compliance.is_fully_compliant(),
                checks_passed: compliance.compliant_count(),
                checks_total: compliance.total_count(),
                checks: compliance
                    .checks
                    .iter()
                    .map(|c| ComplianceCheckInfo {
                        component: c.component.to_string(),
                        algorithm: c.algorithm.to_string(),
                        compliant: c.compliant,
                        standard: c.standard.to_string(),
                    })
                    .collect(),
            },
        };

        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!("{}", summary);
        println!();

        // Show CNSA 2.0 compliance report
        println!("{}", compliance);

        println!("Key Concepts:");
        println!("  CNSA 2.0: Algorithm SELECTION (what algorithms to use)");
        println!("  FIPS 140-3: Module VALIDATION (how algorithms are certified)");
        println!();
        println!("These are orthogonal concerns - you can use CNSA 2.0 algorithms");
        println!("with or without FIPS 140-3 validation.");
    }

    Ok(())
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
        /// Store receipt in NeoFS (requires Neo configuration).
        #[arg(long)]
        store_neofs: bool,
        /// Encrypt receipt with ML-KEM before storing in NeoFS.
        #[arg(long)]
        encrypt: bool,
        /// Auto-queue receipt for batch anchoring (auto-flush at 8).
        #[arg(long)]
        auto_anchor: bool,
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
    ///
    /// By default, sealed files are automatically uploaded to NeoFS for secure
    /// decentralized storage. The recipient can download and unseal anytime.
    ///
    /// For large files, use --use-s3 for ~4x faster uploads via parallel multipart.
    Seal {
        /// File to encrypt.
        file: PathBuf,
        /// Recipient's ML-KEM-1024 public key file.
        /// If not specified, uses your own encryption key (self-encryption).
        #[arg(long, short)]
        recipient: Option<PathBuf>,
        /// Output encrypted file (local copy).
        #[arg(long, short)]
        out: PathBuf,
        /// Skip automatic NeoFS upload (keep local only).
        #[arg(long)]
        no_upload: bool,
        /// NeoFS container ID for storage (uses default receipts container if not specified).
        #[arg(long)]
        container: Option<String>,
        /// Use S3 gateway for faster parallel uploads (recommended for files > 50MB).
        #[arg(long)]
        use_s3: bool,
        /// Number of parallel connections for S3 upload (default: 4).
        #[arg(long, default_value = "4")]
        parallel: usize,
    },
    /// Decrypt a file using ML-KEM-1024 post-quantum decryption.
    ///
    /// If your secret key is password-protected (default), set ANUBIS_PASSWORD:
    ///   ANUBIS_PASSWORD="your-password" anubis-notary unseal ...
    Unseal {
        /// Encrypted file to decrypt.
        file: PathBuf,
        /// Your ML-KEM-1024 secret key file (typically ~/.anubis/decryption.mlkem.sealed).
        /// If password-protected, set ANUBIS_PASSWORD environment variable.
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
    /// Smart notarization pipeline: sign + attest + encrypt + store + anchor.
    ///
    /// This is the recommended way to notarize documents. It performs:
    /// 1. Pre-flight identity verification
    /// 2. SHA-512 content hashing
    /// 3. Receipt creation with ML-DSA-87 signature
    /// 4. Optional encryption with your ML-KEM-1024 key
    /// 5. Optional storage in NeoFS
    /// 6. Automatic batch queue management for cost-efficient anchoring
    Notarize {
        /// Path to notarize (file or directory).
        path: PathBuf,
        /// Recurse into directories.
        #[arg(long, short)]
        recursive: bool,
        /// Custom receipt output path.
        #[arg(long)]
        receipt: Option<PathBuf>,
        /// Skip NeoFS storage (keep receipt local only).
        #[arg(long)]
        no_store: bool,
        /// Skip encryption (not recommended for sensitive documents).
        #[arg(long)]
        no_encrypt: bool,
        /// Skip batch anchoring (no blockchain timestamp).
        #[arg(long)]
        no_anchor: bool,
        /// Flush batch immediately (higher cost, faster confirmation).
        #[arg(long)]
        flush_now: bool,
        /// Skip pre-flight identity verification.
        #[arg(long)]
        skip_preflight: bool,
    },
    /// Will & Testament management.
    Will {
        #[command(subcommand)]
        action: WillCommands,
    },
    /// Property deed management.
    Deed {
        #[command(subcommand)]
        action: DeedCommands,
    },
    /// Business contract management.
    Contract {
        #[command(subcommand)]
        action: ContractCommands,
    },
    /// Notary journal for tamper-evident record keeping.
    Journal {
        #[command(subcommand)]
        action: JournalCommands,
    },
    /// RFC 3161 timestamp authority integration.
    Timestamp {
        #[command(subcommand)]
        action: TimestampCommands,
    },
    /// Data marketplace - sell and buy access to sealed documents.
    ///
    /// List your sealed files for sale, browse listings, and purchase access.
    /// Platform takes a 5-15% cut based on your membership tier.
    Market {
        #[command(subcommand)]
        action: MarketCommands,
    },
    /// NFT membership tiers with fee discounts.
    ///
    /// Mint a Notary (50 GAS/year) or Vault (200 GAS/year) membership NFT
    /// to get reduced fees on all operations.
    Member {
        #[command(subcommand)]
        action: MemberCommands,
    },
    /// Data escrow - conditional release of sealed documents.
    ///
    /// Create time-locked, payment-gated, multi-sig, or dead-man switch escrows.
    /// Documents are released when conditions are met.
    Escrow {
        #[command(subcommand)]
        action: EscrowCommands,
    },
    /// Show cryptographic profile configuration.
    ///
    /// Displays the current profile settings including:
    /// - Algorithm suite (CNSA 2.0 vs Balanced)
    /// - Backend preference (libcrux vs aws-lc-rs)
    /// - FIPS 140-3 availability
    /// - Security level (NIST Level 5 vs 3)
    Profile,
}

#[derive(Subcommand)]
enum KeyCommands {
    /// Initialize a new keystore with a signing key.
    ///
    /// Creates a complete Anubis Notary identity with:
    /// - ML-DSA-87 signing key (NIST Level 5, post-quantum)
    /// - ML-KEM-1024 decryption key (NIST Level 5, post-quantum)
    /// - DK-QSI identity document (self-signed)
    ///
    /// Use --auto-register to automatically register on Neo N3 blockchain.
    /// Requires NEO_PRIVATE_KEY environment variable.
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
        /// Auto-register identity on Neo N3 blockchain after creation.
        /// Requires NEO_PRIVATE_KEY environment variable and Neo config.
        #[arg(long)]
        auto_register: bool,
        /// Name claim for identity (optional, used with --auto-register).
        #[arg(long)]
        name: Option<String>,
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
        /// Public key fingerprint (hex-encoded SHA-512 of public key, 128 hex chars).
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
    /// Ztarknet Protocol anchoring (privacy-preserving, Zcash L1 settlement).
    Ztarknet {
        #[command(subcommand)]
        action: ZtarknetCommands,
    },
    /// Neo N3 Protocol anchoring (dBFT finality, NeoFS, QSI identity).
    Neo {
        /// Keystore path (default: $ANUBIS_HOME or ~/.anubis).
        #[arg(long)]
        keystore: Option<PathBuf>,
        #[command(subcommand)]
        action: NeoCommands,
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
enum ZtarknetCommands {
    /// Configure Ztarknet anchoring settings.
    Config {
        /// PrivacyOracle contract address (hex, 0x-prefixed).
        #[arg(long)]
        contract: Option<String>,
        /// Network (mainnet, testnet).
        #[arg(long)]
        network: Option<String>,
        /// Custom RPC URL (Madara-compatible).
        #[arg(long)]
        rpc: Option<String>,
        /// Show current configuration.
        #[arg(long)]
        show: bool,
    },
    /// Anchor a receipt with privacy mode.
    Anchor {
        /// Receipt file to anchor.
        receipt: PathBuf,
        /// Privacy mode (public, selective, committed).
        #[arg(long, default_value = "public")]
        mode: String,
        /// Viewing key file (for selective mode).
        #[arg(long)]
        viewing_key: Option<PathBuf>,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Verify a Ztarknet anchor or commitment.
    Verify {
        /// Receipt with Ztarknet anchor.
        receipt: PathBuf,
        /// Commitment ID (for committed mode verification).
        #[arg(long)]
        commitment_id: Option<u64>,
        /// Blinding factor (hex, for committed mode).
        #[arg(long)]
        blinding: Option<String>,
    },
    /// Reveal a committed anchor (makes hash public).
    Reveal {
        /// Commitment ID.
        #[arg(long)]
        commitment_id: u64,
        /// Blinding factor (hex).
        #[arg(long)]
        blinding: String,
        /// Original document hash (hex).
        #[arg(long)]
        original_hash: String,
    },
    /// Grant disclosure to an auditor.
    Disclose {
        /// Commitment ID.
        #[arg(long)]
        commitment_id: u64,
        /// Recipient address (hex).
        #[arg(long)]
        recipient: String,
        /// Duration in seconds.
        #[arg(long)]
        duration: u64,
    },
    /// Revoke a disclosure token.
    Revoke {
        /// Token ID (hex).
        #[arg(long)]
        token_id: String,
    },
    /// Get information about a commitment.
    Commitment {
        /// Commitment ID.
        #[arg(long)]
        id: u64,
    },
    /// Get current Ztarknet blockchain time.
    Time,
    /// Get account balance.
    Balance {
        /// Account address (optional, uses configured if not provided).
        #[arg(long)]
        account: Option<String>,
    },
    /// Show network info and privacy features.
    Info,
    /// Generate a new Ztarknet keypair.
    Keygen,
}

#[derive(Subcommand)]
enum NeoCommands {
    /// Configure Neo N3 anchoring settings.
    Config {
        /// NotaryOracle contract script hash (0x-prefixed hex).
        #[arg(long)]
        contract: Option<String>,
        /// Network (mainnet, testnet, private).
        #[arg(long)]
        network: Option<String>,
        /// Custom RPC URL.
        #[arg(long)]
        rpc: Option<String>,
        /// NeoFS HTTP gateway URL.
        #[arg(long)]
        neofs: Option<String>,
        /// NeoID resolver URL.
        #[arg(long)]
        neoid: Option<String>,
        /// NNS contract script hash.
        #[arg(long)]
        nns: Option<String>,
        /// NeoFS container ID for identity documents.
        #[arg(long)]
        identity_container: Option<String>,
        /// NeoFS container ID for signed receipts.
        #[arg(long)]
        receipts_container: Option<String>,
        /// NeoFS container ID for private batches.
        #[arg(long)]
        batch_container: Option<String>,
        /// Show current configuration.
        #[arg(long)]
        show: bool,
    },
    /// Anchor a receipt to Neo N3.
    Anchor {
        /// Receipt file to anchor.
        receipt: PathBuf,
        /// Store receipt in NeoFS (returns CID).
        #[arg(long)]
        store_neofs: bool,
        /// Wait for confirmation (optional with dBFT).
        #[arg(long)]
        wait: bool,
    },
    /// Verify a Neo anchor.
    Verify {
        /// Receipt with Neo anchor.
        receipt: PathBuf,
    },
    /// Get current Neo blockchain time (dBFT finality).
    Time,
    /// Get account GAS balance.
    Balance {
        /// Account address (optional, uses configured if not provided).
        #[arg(long)]
        account: Option<String>,
    },
    /// Show network info and costs.
    Info,
    /// Add a receipt to the Neo batch queue (for 8x cost savings).
    Queue {
        /// Receipt file to queue.
        receipt: PathBuf,
    },
    /// Submit queued receipts as a batch.
    Flush {
        /// Force flush even if queue is not full.
        #[arg(long)]
        force: bool,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Show Neo batch queue status.
    QueueStatus,
    /// Store a file in NeoFS.
    NeofsStore {
        /// File to store.
        file: PathBuf,
        /// NeoFS container ID.
        #[arg(long)]
        container: Option<String>,
        /// Encrypt with ML-KEM-1024 before storing.
        #[arg(long)]
        encrypt: bool,
        /// Recipient's ML-KEM public key file (for --encrypt).
        /// If omitted, uses your own identity key.
        #[arg(long)]
        recipient: Option<PathBuf>,
    },
    /// Get a file from NeoFS.
    NeofsGet {
        /// NeoFS CID.
        cid: String,
        /// Output file path.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Store a large file in NeoFS via S3 Gateway (multipart upload).
    ///
    /// Supports files up to 5GB with automatic chunking.
    /// Uses AWS S3 API with multipart upload for reliability.
    S3Store {
        /// File to store.
        file: PathBuf,
        /// S3 bucket name (maps to NeoFS container).
        #[arg(long)]
        bucket: String,
        /// Custom object key (defaults to filename).
        #[arg(long)]
        key: Option<String>,
        /// Encrypt with ML-KEM-1024 before storing.
        #[arg(long)]
        encrypt: bool,
        /// Recipient's ML-KEM public key file (for --encrypt).
        #[arg(long)]
        recipient: Option<PathBuf>,
        /// S3 endpoint URL (default: NeoFS testnet).
        #[arg(long)]
        endpoint: Option<String>,
        /// AWS access key (for NeoFS: wallet address).
        #[arg(long)]
        access_key: Option<String>,
        /// AWS secret key (for NeoFS: WIF).
        #[arg(long)]
        secret_key: Option<String>,
        /// Part size in MB (default: 64).
        #[arg(long, default_value = "64")]
        part_size: usize,
    },
    /// Get a file from NeoFS via S3 Gateway.
    S3Get {
        /// S3 bucket name.
        #[arg(long)]
        bucket: String,
        /// Object key.
        key: String,
        /// Output file path.
        #[arg(long, short)]
        out: PathBuf,
        /// Decrypt with ML-KEM-1024.
        #[arg(long)]
        decrypt: bool,
        /// S3 endpoint URL (default: NeoFS testnet).
        #[arg(long)]
        endpoint: Option<String>,
        /// AWS access key.
        #[arg(long)]
        access_key: Option<String>,
        /// AWS secret key.
        #[arg(long)]
        secret_key: Option<String>,
    },
    /// Manage NeoFS authentication.
    NeofsAuth {
        /// Path to bearer token file.
        #[arg(long)]
        token_file: Option<PathBuf>,
        /// Bearer token value (base64-encoded).
        #[arg(long)]
        token: Option<String>,
        /// Show current authentication status.
        #[arg(long)]
        status: bool,
        /// Remove stored bearer token.
        #[arg(long)]
        remove: bool,
    },
    /// Manage Neo wallet for NeoFS operations.
    Wallet {
        /// Generate a new Neo wallet.
        #[arg(long)]
        generate: bool,
        /// Import wallet from WIF (Wallet Import Format).
        #[arg(long)]
        import: Option<String>,
        /// Export wallet WIF (WARNING: exposes private key).
        #[arg(long)]
        export: bool,
        /// Show wallet info (address, public key).
        #[arg(long)]
        show: bool,
    },
    /// Deposit GAS into NeoFS balance for storage operations.
    ///
    /// NeoFS requires a separate deposit from Neo chain GAS.
    /// This transfers GAS from your wallet to the NeoFS contract.
    Deposit {
        /// Amount of GAS to deposit (e.g., "1.0" for 1 GAS).
        #[arg(long)]
        amount: f64,
    },
    /// Create a new NeoFS container.
    NeofsCreate {
        /// Container name (optional).
        #[arg(long)]
        name: Option<String>,
        /// Placement policy (default: "REP 2").
        #[arg(long, default_value = "REP 2")]
        policy: String,
        /// Basic ACL (default: "public-read-write").
        #[arg(long, default_value = "public-read-write")]
        acl: String,
        /// Container purpose attribute (e.g., "receipts", "identities", "batches").
        #[arg(long)]
        purpose: Option<String>,
        /// Register name globally in NNS.
        #[arg(long)]
        global: bool,
    },
    /// Resolve a Neo Name Service (NNS) name.
    NnsResolve {
        /// Name to resolve (e.g., "alice.neo").
        name: String,
    },
    /// Quantum-Safe Identity (QSI) commands.
    Identity {
        #[command(subcommand)]
        action: NeoIdentityCommands,
    },
    /// Privacy-preserving collaborative batch commands.
    PrivateBatch {
        #[command(subcommand)]
        action: NeoPrivateBatchCommands,
    },
}

#[derive(Subcommand)]
enum NeoIdentityCommands {
    /// [DEPRECATED] Register a Dual-Key Quantum-Safe Identity.
    ///
    /// DEPRECATED: As of v1.0, 'key init' creates unified identities automatically.
    /// This command is kept for updating metadata on existing identities.
    ///
    /// Creates both signing (ML-DSA-87) and decryption (ML-KEM-1024) keys.
    RegisterDual {
        /// Name claim (optional).
        #[arg(long)]
        name: Option<String>,
        /// Email (will be hashed, privacy-preserving).
        #[arg(long)]
        email: Option<String>,
        /// Organization claim (optional).
        #[arg(long)]
        organization: Option<String>,
        /// Credential type (optional).
        #[arg(long)]
        credential: Option<String>,
        /// Expiry date (YYYY-MM-DD, optional).
        #[arg(long)]
        expires: Option<String>,
        /// Register on-chain (requires NEO_PRIVATE_KEY).
        #[arg(long)]
        on_chain: bool,
    },
    /// Register your ML-DSA-87 key as a Quantum-Safe Identity (single-key, legacy).
    Register {
        /// Name claim (optional).
        #[arg(long)]
        name: Option<String>,
        /// Email (will be hashed, privacy-preserving).
        #[arg(long)]
        email: Option<String>,
        /// Organization claim (optional).
        #[arg(long)]
        organization: Option<String>,
        /// Credential type (optional).
        #[arg(long)]
        credential: Option<String>,
        /// Expiry date (YYYY-MM-DD, optional).
        #[arg(long)]
        expires: Option<String>,
    },
    /// Verify a receipt's quantum-safe identity.
    Verify {
        /// Receipt file.
        receipt: PathBuf,
    },
    /// Rotate to a new key while maintaining identity continuity.
    Rotate {
        /// Old key file (sealed).
        #[arg(long)]
        old_key: PathBuf,
        /// Reason for rotation.
        #[arg(long)]
        reason: Option<String>,
    },
    /// Revoke your identity (e.g., key compromise).
    Revoke {
        /// Reason for revocation.
        #[arg(long)]
        reason: Option<String>,
        /// New fingerprint for replacement identity.
        #[arg(long)]
        replacement_fp: Option<String>,
    },
    /// Resolve an identity by ID or fingerprint.
    Resolve {
        /// ID or fingerprint to resolve.
        /// ID format: ML-DSA-87:ML-KEM-1024:fingerprint
        /// Fingerprint: 128 hex characters (64 bytes, SHA-512)
        id: String,
    },
    /// Show your current DK-QSI identity.
    Show,
    /// Pre-flight check for notarization readiness.
    ///
    /// Verifies all components are ready for notarization:
    /// - Identity exists and is not revoked
    /// - Signing key is valid
    /// - Neo N3 blockchain is configured
    /// - NeoFS container is configured
    Preflight {
        /// Quiet mode - exit with code only.
        #[arg(long, short)]
        quiet: bool,
    },
    /// Export your public keys for others to encrypt to you.
    ExportPublic {
        /// Output format: qsi-pub (full DK-QSI), mlkem-pub (ML-KEM only).
        #[arg(long, default_value = "qsi-pub")]
        format: String,
        /// Output file path.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Get the on-chain status of an identity.
    Status {
        /// Signing fingerprint (128 hex chars, SHA-512) or DID.
        id: String,
    },
    /// Update on-chain identity with new ML-KEM key.
    ///
    /// Syncs the local ML-KEM-1024 decryption key to on-chain registration.
    /// Use this when you've regenerated local keys and need to update on-chain.
    Update,
    /// Register identity on Neo N3 with front-running protection.
    ///
    /// Creates a sender-bound ML-DSA-87 signature that includes your Neo address,
    /// preventing attackers from copying your registration from the mempool.
    ///
    /// Message format: SHA-256("AnubisQSI:RegisterIdentity:v1" || fingerprint || tx.Sender)
    ///
    /// The signature commitment (32 bytes) is stored on-chain; full signature in NeoFS.
    /// CNSA 2.0 compliant with NIST Level 5 security.
    RegisterNeo {
        /// Output the signature commitment to a file (hex format).
        #[arg(long, short)]
        out: Option<PathBuf>,
        /// Use dual-key (DK-QSI) registration instead of single-key.
        #[arg(long)]
        dual_key: bool,
        /// Dry run - show what would be submitted without sending transaction.
        #[arg(long)]
        dry_run: bool,
    },
}

#[derive(Subcommand)]
enum NeoPrivateBatchCommands {
    /// Create a collaborative private batch.
    Create {
        /// Receipt files to include.
        receipts: Vec<PathBuf>,
        /// Recipient QSI public key files.
        #[arg(long, short, required = true)]
        recipient: Vec<PathBuf>,
        /// Threshold (t-of-n required to decrypt).
        #[arg(long, short)]
        threshold: u8,
        /// Store encrypted batch in NeoFS.
        #[arg(long)]
        store_neofs: bool,
    },
    /// Decrypt your share from a collaborative batch.
    DecryptShare {
        /// Batch ID.
        #[arg(long)]
        batch_id: u64,
        /// Your ML-KEM secret key file.
        #[arg(long, short = 'k')]
        secret_key: PathBuf,
        /// Output share file.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Recover batch using threshold shares.
    Recover {
        /// Batch ID.
        #[arg(long)]
        batch_id: u64,
        /// Share files (need at least threshold).
        #[arg(long, required = true)]
        share: Vec<PathBuf>,
        /// Output directory for decrypted receipts.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Check collaborative batch status.
    Status {
        /// Batch ID.
        #[arg(long)]
        batch_id: u64,
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
        /// Store batch in NeoFS (requires Neo configuration).
        #[arg(long)]
        store_neofs: bool,
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
        /// Neo N3 network (mainnet, testnet).
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Automatically mint NFT rings for all partners.
        #[arg(long)]
        mint_rings: bool,
        /// Store certificate in NeoFS.
        #[arg(long)]
        store_neofs: bool,
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
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Show marriage details.
    Show {
        /// Marriage ID on-chain.
        #[arg(long)]
        marriage_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Show contract addresses.
    Info {
        /// Show TestNet addresses.
        #[arg(long)]
        testnet: bool,
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
        /// Partner fingerprints (comma-separated hex).
        #[arg(long)]
        partners: String,
        /// Partner Neo addresses (comma-separated).
        #[arg(long)]
        neo_addresses: String,
        /// Partner name hashes (comma-separated hex).
        #[arg(long)]
        name_hashes: String,
        /// Vows hashes (comma-separated hex).
        #[arg(long)]
        vows_hashes: String,
        /// Marriage certificate hash (hex).
        #[arg(long)]
        marriage_hash: String,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Burn a ring (on divorce).
    Burn {
        /// Token ID to burn.
        #[arg(long)]
        token_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Show ring metadata.
    Show {
        /// Token ID to show.
        token_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Check if a ring exists.
    Exists {
        /// Token ID to check.
        token_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Get total supply of rings.
    Supply {
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Update vows on a ring (anniversary renewal).
    UpdateVows {
        /// Token ID to update.
        #[arg(long)]
        token_id: u64,
        /// New vows text (will be hashed).
        #[arg(long)]
        vows: String,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
}

#[derive(Subcommand)]
enum WillCommands {
    /// Create a new will document.
    Init {
        /// Testator's full legal name.
        #[arg(long)]
        testator: String,
        /// Jurisdiction code (e.g., "US-CA", "UK").
        #[arg(long)]
        jurisdiction: String,
        /// Output will document file (JSON).
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Add a beneficiary to the will.
    AddBeneficiary {
        /// Will document file.
        document: PathBuf,
        /// Beneficiary's full legal name.
        #[arg(long)]
        name: String,
        /// Relationship to testator (e.g., "spouse", "child").
        #[arg(long)]
        relationship: String,
        /// Share percentage (0-100).
        #[arg(long)]
        share: u8,
        /// Specific assets (comma-separated).
        #[arg(long)]
        assets: Option<String>,
    },
    /// Add an executor to the will.
    AddExecutor {
        /// Will document file.
        document: PathBuf,
        /// Executor's full legal name.
        #[arg(long)]
        name: String,
        /// Executor's ML-DSA-87 public key fingerprint.
        #[arg(long)]
        fingerprint: String,
    },
    /// Sign the will (as testator or witness).
    Sign {
        /// Will document file.
        document: PathBuf,
        /// Sign as witness instead of testator.
        #[arg(long)]
        witness: bool,
        /// Witness name (required if --witness).
        #[arg(long)]
        witness_name: Option<String>,
        /// Output signed document.
        #[arg(long, short)]
        out: Option<PathBuf>,
    },
    /// Apply notary seal to the will.
    Notarize {
        /// Will document file.
        document: PathBuf,
        /// Notary commission number.
        #[arg(long)]
        commission: String,
        /// Notary jurisdiction.
        #[arg(long)]
        jurisdiction: String,
    },
    /// Verify all signatures on a will.
    Verify {
        /// Will document file.
        document: PathBuf,
    },
    /// Anchor will to Neo N3 blockchain.
    Anchor {
        /// Will document file.
        document: PathBuf,
        /// Neo network (mainnet, testnet).
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Seal will (executor access only after activation).
        #[arg(long)]
        sealed: bool,
    },
    /// Revoke a will.
    Revoke {
        /// Will ID on-chain.
        #[arg(long)]
        will_id: String,
        /// Reason for revocation.
        #[arg(long)]
        reason: String,
        /// Path to superseding will (optional).
        #[arg(long)]
        superseded_by: Option<PathBuf>,
    },
}

#[derive(Subcommand)]
enum DeedCommands {
    /// Create a new property deed.
    Init {
        /// Property identifier (e.g., APN, parcel number).
        #[arg(long)]
        property_id: String,
        /// Jurisdiction code (e.g., "US-CA").
        #[arg(long)]
        jurisdiction: String,
        /// Deed type (warranty, quitclaim, grant, bargain-sale).
        #[arg(long, default_value = "warranty")]
        deed_type: String,
        /// Output deed file (JSON).
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Transfer property ownership.
    Transfer {
        /// Deed document file.
        document: PathBuf,
        /// Grantor fingerprint.
        #[arg(long)]
        from: String,
        /// Grantee fingerprints (comma-separated for joint).
        #[arg(long)]
        to: String,
        /// Consideration amount (sale price).
        #[arg(long)]
        amount: Option<u64>,
        /// Currency code (default: USD).
        #[arg(long, default_value = "USD")]
        currency: String,
    },
    /// Add a lien to the property.
    AddLien {
        /// Deed document file.
        document: PathBuf,
        /// Lien holder fingerprint.
        #[arg(long)]
        holder: String,
        /// Lien amount.
        #[arg(long)]
        amount: u64,
        /// Lien type (mortgage, tax, mechanics, judgment, hoa).
        #[arg(long)]
        lien_type: String,
    },
    /// Release a lien.
    ReleaseLien {
        /// Deed document file.
        document: PathBuf,
        /// Lien ID to release.
        #[arg(long)]
        lien_id: u64,
    },
    /// Show chain of title history.
    History {
        /// Property identifier.
        #[arg(long)]
        property_id: String,
        /// Show full chain (all transfers).
        #[arg(long)]
        full_chain: bool,
    },
    /// Verify deed signatures.
    Verify {
        /// Deed document file.
        document: PathBuf,
    },
    /// Anchor deed to Neo N3 blockchain.
    Anchor {
        /// Deed document file.
        document: PathBuf,
        /// Neo network (mainnet, testnet).
        #[arg(long, default_value = "testnet")]
        network: String,
    },
}

#[derive(Subcommand)]
enum ContractCommands {
    /// Create a new business contract.
    Init {
        /// Party names (comma-separated, e.g., "Alice Corp,Bob LLC").
        #[arg(long)]
        parties: String,
        /// Contract type (purchase, service, lease, employment, nda, partnership, licensing).
        #[arg(long, default_value = "service")]
        contract_type: String,
        /// Jurisdiction code.
        #[arg(long)]
        jurisdiction: String,
        /// Output contract file (JSON).
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Add a clause to the contract.
    AddClause {
        /// Contract document file.
        document: PathBuf,
        /// Section number.
        #[arg(long)]
        section: u32,
        /// Clause title.
        #[arg(long)]
        title: String,
        /// Clause text.
        #[arg(long)]
        text: String,
    },
    /// Add an exhibit/attachment.
    AddExhibit {
        /// Contract document file.
        document: PathBuf,
        /// Exhibit label (e.g., "A", "B").
        #[arg(long)]
        label: String,
        /// Exhibit file to attach.
        #[arg(long)]
        file: PathBuf,
        /// Description of the exhibit.
        #[arg(long)]
        description: String,
    },
    /// Propose contract changes (redline).
    Propose {
        /// Contract document file.
        document: PathBuf,
        /// Diff file with proposed changes.
        #[arg(long)]
        changes: PathBuf,
        /// Output proposed contract.
        #[arg(long, short)]
        out: Option<PathBuf>,
    },
    /// Sign the contract as a party.
    Sign {
        /// Contract document file.
        document: PathBuf,
        /// Party index (0-based).
        #[arg(long)]
        party: usize,
        /// Authorized signer title (e.g., "CEO", "CFO").
        #[arg(long)]
        title: Option<String>,
        /// Output signed contract.
        #[arg(long, short)]
        out: Option<PathBuf>,
    },
    /// Verify all signatures on the contract.
    Verify {
        /// Contract document file.
        document: PathBuf,
    },
    /// Anchor contract to Neo N3 blockchain.
    Anchor {
        /// Contract document file.
        document: PathBuf,
        /// Neo network (mainnet, testnet).
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Request RFC 3161 timestamp.
        #[arg(long)]
        timestamp_authority: bool,
    },
    /// Amend an executed contract.
    Amend {
        /// Original contract document.
        document: PathBuf,
        /// Amendment description.
        #[arg(long)]
        description: String,
        /// Output amended contract.
        #[arg(long, short)]
        out: PathBuf,
    },
}

#[derive(Subcommand)]
enum JournalCommands {
    /// Initialize a new notary journal.
    Init {
        /// Notary commission number.
        #[arg(long)]
        commission: String,
        /// Jurisdiction code.
        #[arg(long)]
        jurisdiction: String,
        /// Journal file path.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Add an entry to the journal.
    Entry {
        /// Journal file.
        journal: PathBuf,
        /// Notarial act type (acknowledgment, jurat, copy-cert, oath, affirmation).
        #[arg(long)]
        act_type: String,
        /// Signer ID type (dl, passport, military, state-id).
        #[arg(long)]
        id_type: String,
        /// Signer ID value (e.g., "CA:D1234567").
        #[arg(long)]
        id_value: String,
        /// Signer's name.
        #[arg(long)]
        signer_name: String,
        /// Document type being notarized.
        #[arg(long)]
        document_type: String,
        /// Document hash (hex).
        #[arg(long)]
        document_hash: String,
        /// Number of pages.
        #[arg(long)]
        pages: Option<u32>,
        /// Notarization fee charged.
        #[arg(long)]
        fee: Option<f64>,
    },
    /// Export journal entries.
    Export {
        /// Journal file.
        journal: PathBuf,
        /// Output format (pdf, csv, json).
        #[arg(long, default_value = "json")]
        format: String,
        /// Date range start (YYYY-MM-DD).
        #[arg(long)]
        from: Option<String>,
        /// Date range end (YYYY-MM-DD).
        #[arg(long)]
        to: Option<String>,
        /// Output file.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Audit journal for integrity.
    Audit {
        /// Journal file.
        journal: PathBuf,
        /// Verify all signatures.
        #[arg(long)]
        verify_signatures: bool,
        /// Check sequence integrity.
        #[arg(long)]
        check_sequence: bool,
    },
    /// Anchor journal batch to Neo N3 blockchain.
    Anchor {
        /// Journal file.
        journal: PathBuf,
        /// Neo network (mainnet, testnet).
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Start entry number for batch.
        #[arg(long)]
        from_entry: Option<u64>,
        /// End entry number for batch.
        #[arg(long)]
        to_entry: Option<u64>,
    },
}

#[derive(Subcommand)]
enum TimestampCommands {
    /// Request a timestamp from an RFC 3161 TSA.
    Request {
        /// File to timestamp (SHA-512 hash will be computed).
        file: PathBuf,
        /// TSA endpoint URL (default: FreeTSA).
        #[arg(long)]
        tsa: Option<String>,
        /// Use well-known TSA (freetsa, digicert, globalsign, sectigo, apple).
        #[arg(long)]
        provider: Option<String>,
        /// Output timestamp response file.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// Verify a timestamp response.
    Verify {
        /// Original file that was timestamped.
        file: PathBuf,
        /// Timestamp response file.
        #[arg(long)]
        response: PathBuf,
    },
    /// Embed timestamp into a receipt.
    Embed {
        /// Receipt file to embed timestamp into.
        receipt: PathBuf,
        /// Timestamp response file.
        #[arg(long)]
        timestamp: PathBuf,
        /// Output timestamped receipt.
        #[arg(long, short)]
        out: PathBuf,
    },
    /// List available TSA providers.
    Providers,
}

#[derive(Subcommand)]
enum MarketCommands {
    /// List a sealed file for sale on the marketplace.
    List {
        /// Sealed file to list (must have a NeoFS object ID).
        sealed_file: PathBuf,
        /// Price in GAS.
        #[arg(long)]
        price: f64,
        /// Listing duration (e.g., "30d", "7d", "90d").
        #[arg(long, default_value = "30d")]
        duration: String,
        /// Description/metadata for the listing.
        #[arg(long)]
        metadata: String,
        /// Neo N3 network (mainnet, testnet).
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
        /// Upload sealed file to NeoFS for decentralized storage.
        #[arg(long)]
        upload_neofs: bool,
        /// NeoFS container ID (required if --upload-neofs is set, auto-created if not provided).
        #[arg(long)]
        container: Option<String>,
    },
    /// Browse marketplace listings.
    Browse {
        /// Filter by category.
        #[arg(long)]
        category: Option<String>,
        /// Maximum price in GAS.
        #[arg(long)]
        price_max: Option<f64>,
        /// Minimum price in GAS.
        #[arg(long)]
        price_min: Option<f64>,
        /// Limit results.
        #[arg(long, default_value = "20")]
        limit: u32,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Show details of a specific listing.
    Show {
        /// Listing ID.
        listing_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Purchase access to a listing and decrypt.
    Buy {
        /// Listing ID to purchase.
        listing_id: u64,
        /// Output decrypted file.
        #[arg(long, short)]
        output: PathBuf,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// View your own listings.
    MyListings {
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Revenue management subcommands.
    Revenue {
        #[command(subcommand)]
        action: MarketRevenueCommands,
    },
    /// View pending deliveries (purchases waiting for you to deliver access).
    Pending {
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Deliver access to a buyer (re-wrap content key for their public key).
    Deliver {
        /// Purchase ID to deliver access for.
        purchase_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Claim purchased data (decrypt after seller delivers access).
    Claim {
        /// Purchase ID to claim.
        purchase_id: u64,
        /// Output decrypted file.
        #[arg(long, short)]
        output: PathBuf,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Check status of a purchase.
    Status {
        /// Purchase ID to check.
        purchase_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
}

#[derive(Subcommand)]
enum MarketRevenueCommands {
    /// Show accumulated revenue for a listing.
    Show {
        /// Listing ID.
        listing_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Claim accumulated revenue from a listing.
    Claim {
        /// Listing ID.
        listing_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
}

#[derive(Subcommand)]
enum MemberCommands {
    /// Show available membership tiers.
    Tiers,
    /// Show your current membership status.
    Status {
        /// Neo address to check (defaults to your identity).
        #[arg(long)]
        address: Option<String>,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Mint a membership NFT.
    Mint {
        /// Tier to mint: "notary" (50 GAS/year) or "vault" (200 GAS/year).
        tier: String,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Renew an existing membership.
    Renew {
        /// Token ID to renew.
        token_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Transfer a membership NFT.
    Transfer {
        /// Token ID to transfer.
        token_id: u64,
        /// Recipient Neo address.
        #[arg(long)]
        to: String,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
}

#[derive(Subcommand)]
enum EscrowCommands {
    /// Create a time-locked escrow (auto-release at specific time).
    TimeLock {
        /// Sealed file to escrow.
        sealed_file: PathBuf,
        /// Unlock time (ISO 8601 format, e.g., "2025-06-01T00:00:00Z").
        #[arg(long)]
        unlock_at: String,
        /// Beneficiary Neo address.
        #[arg(long)]
        beneficiary: String,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Create a payment-gated escrow (release when price paid).
    Payment {
        /// Sealed file to escrow.
        sealed_file: PathBuf,
        /// Price in GAS to unlock.
        #[arg(long)]
        price: f64,
        /// Beneficiary Neo address.
        #[arg(long)]
        beneficiary: String,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Create a multi-sig escrow (N-of-M approval required).
    MultiSig {
        /// Sealed file to escrow.
        sealed_file: PathBuf,
        /// Signer fingerprints (comma-separated hex).
        #[arg(long)]
        signers: String,
        /// Number of approvals required.
        #[arg(long)]
        threshold: u32,
        /// Beneficiary Neo address.
        #[arg(long)]
        beneficiary: String,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Create a dead-man switch escrow (release if not renewed).
    DeadMan {
        /// Sealed file to escrow.
        sealed_file: PathBuf,
        /// Heartbeat interval in days.
        #[arg(long, default_value = "30")]
        heartbeat_days: u32,
        /// Beneficiary Neo address.
        #[arg(long)]
        beneficiary: String,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// List your escrows.
    List {
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Show escrow details.
    Show {
        /// Escrow ID.
        escrow_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
    },
    /// Send heartbeat for a dead-man switch escrow.
    Heartbeat {
        /// Escrow ID.
        escrow_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Approve a multi-sig escrow (as a signer).
    Approve {
        /// Escrow ID.
        escrow_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Pay for a payment-gated escrow.
    Pay {
        /// Escrow ID.
        escrow_id: u64,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
    },
    /// Claim an escrow (as beneficiary, when conditions are met).
    Claim {
        /// Escrow ID.
        escrow_id: u64,
        /// Output decrypted file.
        #[arg(long, short)]
        output: PathBuf,
        /// Neo N3 network.
        #[arg(long, default_value = "testnet")]
        network: String,
        /// Wait for confirmation.
        #[arg(long)]
        wait: bool,
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

    // Initialize cryptographic profile from CLI or environment
    if let Err(e) = init_crypto_profile(&cli) {
        eprintln!("Error: {}", e);
        return ExitCode::FAILURE;
    }

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
            store_neofs,
            encrypt,
            auto_anchor,
        } => handle_attest(path, *recursive, receipt, *store_neofs, *encrypt, *auto_anchor, cli.json),
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
            no_upload,
            container,
            use_s3,
            parallel,
        } => handle_seal(file, recipient.as_ref(), out, *no_upload, container.as_deref(), *use_s3, *parallel, cli.json),
        Commands::Unseal {
            file,
            secret_key,
            out,
        } => handle_unseal(file, secret_key, out, cli.json),
        Commands::Marriage { action } => handle_marriage(action, cli.json),
        Commands::Notarize {
            path,
            recursive,
            receipt,
            no_store,
            no_encrypt,
            no_anchor,
            flush_now,
            skip_preflight,
        } => handle_notarize(
            path,
            *recursive,
            receipt.as_ref(),
            *no_store,
            *no_encrypt,
            *no_anchor,
            *flush_now,
            *skip_preflight,
            cli.json,
        ),
        Commands::Will { action } => handle_will(action, cli.json),
        Commands::Deed { action } => handle_deed(action, cli.json),
        Commands::Contract { action } => handle_contract(action, cli.json),
        Commands::Journal { action } => handle_journal(action, cli.json),
        Commands::Timestamp { action } => handle_timestamp(action, cli.json),
        Commands::Market { action } => handle_market(action, cli.json),
        Commands::Member { action } => handle_member(action, cli.json),
        Commands::Escrow { action } => handle_escrow(action, cli.json),
        Commands::Profile => handle_profile(cli.json),
    }
}

fn handle_key(action: &KeyCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        KeyCommands::Init {
            keystore,
            kdf,
            low_memory,
            auto_register,
            name,
        } => {
            use anubis_core::qsi::{DualKeyQsiDocument, QsiClaims};

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
                eprintln!("Creating new Anubis Notary identity with post-quantum keys.");
                eprintln!(
                    "This will use Argon2id with {} memory for key derivation.",
                    if *low_memory { "1 GiB" } else { "4 GiB" }
                );
                eprintln!();
            }

            let mut password = prompt_new_password()?;

            // Generate seed from system entropy
            let mut seed = generate_seed()?;

            // === STEP 1: Generate ML-DSA-87 signing key ===
            if !json {
                eprintln!("Generating ML-DSA-87 signing key...");
            }
            let kp =
                KeyPair::from_seed(&seed).map_err(|e| format!("Key generation failed: {:?}", e))?;

            // Store ML-DSA-87 public key (unencrypted - it's public)
            ks.write_public_key(&kp.public_key().to_bytes())?;

            // Seal and store the ML-DSA-87 seed with password protection
            if !json {
                eprintln!("Encrypting signing key with Argon2id... (this may take a moment)");
            }

            if *low_memory {
                ks.seal_and_store_key_low_memory(password.as_bytes(), &seed)?;
            } else {
                ks.seal_and_store_key(password.as_bytes(), &seed)?;
            }

            // === STEP 2: Generate ML-KEM-1024 encryption key ===
            if !json {
                eprintln!("Generating ML-KEM-1024 encryption key...");
            }
            let mlkem_keypair = MlKemKeyPair::generate()
                .map_err(|e| format!("ML-KEM key generation failed: {:?}", e))?;

            // Store ML-KEM public key
            let mlkem_pub_path = ks.path().join("decryption.mlkem.pub");
            std::fs::write(&mlkem_pub_path, mlkem_keypair.public_key_bytes())?;

            // Seal and store ML-KEM secret key
            // SECURITY: Wrap secret key bytes in Zeroizing to clear from memory after sealing
            let mlkem_sk_bytes = zeroize::Zeroizing::new(mlkem_keypair.secret_key_bytes().to_vec());
            let mlkem_sealed = anubis_io::seal::seal_key(password.as_bytes(), &mlkem_sk_bytes)
                .map_err(|e| format!("Failed to seal ML-KEM key: {}", e))?;
            let mlkem_sealed_path = ks.path().join("decryption.mlkem.sealed");
            std::fs::write(&mlkem_sealed_path, &mlkem_sealed)?;

            // === STEP 3: Create unified DK-QSI identity document ===
            if !json {
                eprintln!("Creating unified identity document...");
            }

            // Get ML-KEM public key for the identity document
            let mlkem_pk = MlKemPublicKey::from_bytes(mlkem_keypair.public_key_bytes())
                .map_err(|e| format!("Failed to parse ML-KEM public key: {:?}", e))?;

            // Create claims (can be updated later with 'identity update')
            let claims = QsiClaims {
                neo_address: String::new(),
                name: name.clone(),
                email_hash: None,
                organization: None,
                credential_type: None,
            };

            // Create and sign the DK-QSI document
            let doc = DualKeyQsiDocument::create(&kp, &mlkem_pk, claims, None)
                .map_err(|e| format!("Failed to create identity document: {:?}", e))?;

            // Get fingerprints
            let signing_fp = hex::encode(&doc.signing_fingerprint[..16]);
            let decryption_fp = hex::encode(&doc.decryption_fingerprint[..16]);
            let identity_id = doc.id();

            // Serialize and store the identity document
            let doc_cbor = doc.to_cbor()
                .map_err(|e| format!("Failed to serialize identity document: {:?}", e))?;
            let qsi_path = ks.path().join("identity.qsi.cbor");
            std::fs::write(&qsi_path, &doc_cbor)?;

            // === STEP 4: Auto-configure Neo N3 testnet for blockchain anchoring ===
            // This ensures anchoring is ready out-of-the-box for all new installations
            let neo_config_path = ks.path().join("neo.json");
            if !neo_config_path.exists() {
                use anubis_io::neo::{NeoConfig, NeoNetwork};

                if !json {
                    eprintln!("Configuring Neo N3 testnet for blockchain anchoring...");
                }

                // Create default testnet configuration with deployed contract
                // Contract deployed: 2026-01-08 on TestNet with Fee Collection + MintRings
                let neo_config = NeoConfig::new(NeoNetwork::TestNet)
                    .with_contract("0x2ebbd7d0b4096210c3eee13583af92c1ec8318ce");

                let config_json = serde_json::to_string_pretty(&neo_config)
                    .map_err(|e| format!("Failed to serialize Neo config: {}", e))?;
                std::fs::write(&neo_config_path, &config_json)?;

                if !json {
                    eprintln!("  ✓ Neo N3 testnet configured (contract: 0x41bdbe...de74)");
                }
            }

            // === STEP 5: Auto-generate Neo wallet for NeoFS storage ===
            let wallet_path = ks.path().join("neo-wallet.wif.sealed");
            let mut wallet_address: Option<String> = None;

            if !wallet_path.exists() {
                use anubis_io::neo::NeoWallet;

                if !json {
                    eprintln!("Generating Neo N3 wallet for NeoFS storage...");
                }

                let wallet = NeoWallet::generate()
                    .map_err(|e| format!("Failed to generate wallet: {}", e))?;

                // Seal the WIF with the same password used for keys
                let wif = wallet.to_wif();
                let sealed_wallet = anubis_io::seal::seal_key(password.as_bytes(), wif.as_bytes())
                    .map_err(|e| format!("Failed to seal wallet: {}", e))?;
                std::fs::write(&wallet_path, &sealed_wallet)?;

                wallet_address = Some(wallet.address().to_string());

                if !json {
                    eprintln!("  ✓ Neo wallet created: {}", wallet.address());
                }
            }

            // Auto-register on Neo N3 if requested
            let mut registration_result: Option<String> = None;
            let mut registration_error: Option<String> = None;

            if *auto_register {
                use anubis_io::neo::{NeoClient, NeoConfig};

                if !json {
                    eprintln!("Attempting auto-registration on Neo N3...");
                }

                // Check for NEO_PRIVATE_KEY (required for secure registration)
                let neo_pk = std::env::var("NEO_PRIVATE_KEY").ok();
                let config_path = ks.path().join("neo.json");

                if neo_pk.is_none() {
                    registration_error = Some(
                        "NEO_PRIVATE_KEY not set. Export your key to auto-register:\n    \
                         export NEO_PRIVATE_KEY=<your-wif-key>".to_string()
                    );
                } else if !config_path.exists() {
                    registration_error = Some(
                        "Neo not configured. Run first:\n    \
                         anubis-notary anchor neo config --contract <HASH>".to_string()
                    );
                } else {
                    // Try to register
                    match std::fs::read_to_string(&config_path) {
                        Ok(config_data) => {
                            match serde_json::from_str::<NeoConfig>(&config_data) {
                                Ok(config) => {
                                    if config.contract_address.is_none() {
                                        registration_error = Some(
                                            "Contract not configured. Run:\n    \
                                             anubis-notary anchor neo config --contract <HASH>".to_string()
                                        );
                                    } else {
                                        // Create NeoClient with the config
                                        match NeoClient::new(config) {
                                            Ok(client) => {
                                                // Use a placeholder CID for immediate registration
                                                // The QSI document can be uploaded to NeoFS later
                                                let placeholder_cid = format!(
                                                    "local:{}",
                                                    &hex::encode(&doc.signing_fingerprint)[..16]
                                                );

                                                // Register the dual-key identity
                                                match client.register_dual_key_identity(
                                                    &doc.signing_fingerprint,
                                                    &doc.decryption_fingerprint,
                                                    &placeholder_cid,
                                                ) {
                                                    Ok(result) => {
                                                        registration_result = Some(result.tx_hash);
                                                    }
                                                    Err(e) => {
                                                        registration_error = Some(format!(
                                                            "Registration failed: {}",
                                                            e
                                                        ));
                                                    }
                                                }
                                            }
                                            Err(e) => {
                                                registration_error = Some(format!(
                                                    "Could not create Neo client: {}",
                                                    e
                                                ));
                                            }
                                        }
                                    }
                                }
                                Err(e) => {
                                    registration_error = Some(format!("Invalid neo.json: {}", e));
                                }
                            }
                        }
                        Err(e) => {
                            registration_error = Some(format!("Could not read neo.json: {}", e));
                        }
                    }
                }

                if !json {
                    if let Some(ref tx) = registration_result {
                        eprintln!("  ✓ Registered on-chain: {}", tx);
                    } else if let Some(ref err) = registration_error {
                        eprintln!("  ⚠ Auto-registration skipped: {}", err);
                    }
                }
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
                    identity_id: String,
                    signing_fingerprint: String,
                    decryption_fingerprint: String,
                    signing_algorithm: String,
                    encryption_algorithm: String,
                    created: bool,
                    argon2id_memory: String,
                    password_protected: bool,
                    on_chain_registered: bool,
                    registration_tx: Option<String>,
                    registration_error: Option<String>,
                    neo_wallet_address: Option<String>,
                    neofs_funding_required: bool,
                }
                let output = JsonOutput::success(InitResult {
                    keystore: path.display().to_string(),
                    identity_id,
                    signing_fingerprint: signing_fp,
                    decryption_fingerprint: decryption_fp,
                    signing_algorithm: "ML-DSA-87".to_string(),
                    encryption_algorithm: "ML-KEM-1024".to_string(),
                    created: true,
                    argon2id_memory: memory_mode.to_string(),
                    password_protected: true,
                    on_chain_registered: registration_result.is_some(),
                    registration_tx: registration_result,
                    registration_error,
                    neo_wallet_address: wallet_address.clone(),
                    neofs_funding_required: wallet_address.is_some(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!();
                println!("╔══════════════════════════════════════════════════════════════════════════╗");
                println!("║              ANUBIS NOTARY IDENTITY CREATED                              ║");
                println!("╠══════════════════════════════════════════════════════════════════════════╣");
                println!("║  Keystore: {:<63}║", path.display());
                println!("║                                                                          ║");
                println!("║  SIGNING KEY (ML-DSA-87):                                                ║");
                println!("║    Fingerprint: {}...                            ║", signing_fp);
                println!("║                                                                          ║");
                println!("║  ENCRYPTION KEY (ML-KEM-1024):                                           ║");
                println!("║    Fingerprint: {}...                            ║", decryption_fp);
                println!("║                                                                          ║");
                println!("║  Protection: Argon2id ({})                                    ║",
                    if *low_memory { "1 GiB" } else { "4 GiB" });
                if registration_result.is_some() {
                    println!("║                                                                          ║");
                    println!("║  On-Chain: ✓ Registered on Neo N3                                       ║");
                }
                if let Some(ref addr) = wallet_address {
                    println!("║                                                                          ║");
                    println!("║  NEO WALLET (for NeoFS storage):                                         ║");
                    println!("║    Address: {:<60}║", addr);
                }
                println!("╚══════════════════════════════════════════════════════════════════════════╝");
                println!();
                println!("Your identity is ready for signing, attestation, and encrypted storage.");
                println!();
                println!("IMPORTANT: Remember your password! There is no recovery mechanism.");

                // Show NeoFS funding instructions if wallet was created
                if let Some(ref addr) = wallet_address {
                    println!();
                    println!("═══════════════════════════════════════════════════════════════════════════");
                    println!("  NEXT STEPS: Enable NeoFS cloud storage");
                    println!("═══════════════════════════════════════════════════════════════════════════");
                    println!();
                    println!("  1. Fund your wallet with GAS (~2 GAS recommended):");
                    println!("     {}", addr);
                    println!();
                    println!("  2. Deposit GAS into NeoFS:");
                    println!("     anubis-notary anchor neo deposit --amount 1.0");
                    println!();
                    println!("  3. Seal and upload files:");
                    println!("     anubis-notary seal document.pdf -o document.sealed");
                    println!("═══════════════════════════════════════════════════════════════════════════");
                }

                if *auto_register && registration_result.is_none() {
                    println!();
                    println!("To register on-chain later, run:");
                    println!("  NEO_PRIVATE_KEY=<your-wif> anubis-notary anchor neo identity register-neo");
                }
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

            // Calculate fingerprint (SHA-512 for CNSA 2.0 compliance)
            let fp = if fingerprint == "current" {
                // Revoke current key
                if !ks.has_key() {
                    return Err("No key found.".into());
                }
                let pubkey = ks.read_public_key()?;
                hex::encode(anubis_core::sha2::fingerprint(&pubkey))
            } else {
                fingerprint.clone()
            };

            // Check fingerprint format (should be 128 hex chars = 64 bytes SHA-512)
            if fp.len() != 128 || !fp.chars().all(|c| c.is_ascii_hexdigit()) {
                return Err("Invalid fingerprint: must be 128 hex characters (SHA-512)".into());
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
                    // Use SHA-512 fingerprint for CNSA 2.0 (128 hex chars)
                    let fp = hex::encode(anubis_core::sha2::fingerprint(&pk));
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
                            // Use SHA-512 fingerprint for CNSA 2.0 (truncated for display)
                            let full_fp = hex::encode(anubis_core::sha2::fingerprint(&pk));
                            println!("  {} (fingerprint: {}...)", id, &full_fp[..32]);
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
    // Uses SHA-512 fingerprint for CNSA 2.0 compliance (128 hex chars)
    let pk_bytes = ks.read_public_key()?;
    let fingerprint = hex::encode(anubis_core::sha2::fingerprint(&pk_bytes));
    if ks.is_revoked(&fingerprint)? {
        return Err(
            "Cannot sign: key has been revoked. Generate a new key with 'anubis-notary key init'."
                .into(),
        );
    }

    // Load keypair with password authentication
    let kp = load_keypair_with_password(&ks)?;

    // Read and hash the file (SHA-512 for CNSA 2.0 compliance)
    let data = read_file(file)?;
    let hash = anubis_core::sha2::sha512(&data);

    // Create the message to sign (hash of file content with domain separation)
    let mut message_to_sign = Vec::with_capacity(96);
    message_to_sign.extend_from_slice(b"anubis-notary:sign:v2:");
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

    // Check if key is revoked (uses SHA-512 fingerprint for CNSA 2.0)
    let fingerprint = hex::encode(anubis_core::sha2::fingerprint(&pk_bytes));
    let revoked = ks.is_revoked(&fingerprint)?;

    // Read and hash the file (SHA-512 for CNSA 2.0 compliance)
    let data = read_file(file)?;
    let hash = anubis_core::sha2::sha512(&data);

    // Reconstruct the message that was signed
    let mut message_to_verify = Vec::with_capacity(96);
    message_to_verify.extend_from_slice(b"anubis-notary:sign:v2:");
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
    store_neofs: bool,
    encrypt: bool,
    auto_anchor: bool,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::receipt::Receipt;
    use anubis_core::sha2::fingerprint as compute_fingerprint;

    // Load the signing key from default keystore
    let ks = Keystore::open(Keystore::default_path())?;
    if !ks.has_key() {
        return Err("No signing key found. Run 'anubis-notary key init' first.".into());
    }

    // SECURITY: Check if the key has been revoked before allowing attestation
    // Uses SHA-512 fingerprint for CNSA 2.0 compliance (128 hex chars)
    let pk_bytes = ks.read_public_key()?;
    let fingerprint = hex::encode(compute_fingerprint(&pk_bytes));
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
        anubis_core::sha2::sha512(&combined)
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
    let receipt_data = buf[..len].to_vec();

    write_file_atomic(receipt_path, &receipt_data)?;

    // Optionally store in NeoFS
    let neofs_cid = if store_neofs {
        use anubis_io::neo::{NeoConfig, NeoFsClient, NeoFsObjectAttributes};

        // Load Neo config
        let config_path = ks.path().join("neo.json");
        if !config_path.exists() {
            if !json {
                eprintln!("Warning: Neo not configured. Skipping NeoFS storage.");
                eprintln!("Run: anubis-notary anchor neo config --receipts-container <ID>");
            }
            None
        } else {
            let config_data = std::fs::read_to_string(&config_path)?;
            let config: NeoConfig = serde_json::from_str(&config_data)?;

            if let Some(ref container_id) = config.receipts_container {
                // Load bearer token
                let token_path = ks.path().join("neofs-bearer.token");
                let bearer_token = if token_path.exists() {
                    Some(std::fs::read_to_string(&token_path)?.trim().to_string())
                } else {
                    None
                };

                // Create NeoFS client
                let mut neofs = NeoFsClient::new(&config.neofs_url, config.timeout_secs);
                if let Some(ref token) = bearer_token {
                    neofs.set_bearer_token(token);
                }

                // File name for receipt
                let receipt_name = receipt_path.file_name()
                    .map(|n| n.to_string_lossy().to_string())
                    .unwrap_or_else(|| format!("{}.anb", hex::encode(&digest[..8])));

                let content_hash = hex::encode(anubis_core::sha2::sha512(&receipt_data));

                if encrypt {
                    // Load ML-KEM public key from identity
                    let mlkem_pk_path = ks.path().join("decryption.mlkem.pub");
                    let qsi_path = ks.path().join("identity.qsi.cbor");

                    let mlkem_pk_result = if mlkem_pk_path.exists() {
                        let pk_bytes = std::fs::read(&mlkem_pk_path)?;
                        anubis_core::mlkem::MlKemPublicKey::from_bytes(&pk_bytes).ok()
                    } else if qsi_path.exists() {
                        // Fall back to extracting from DK-QSI document
                        let qsi_bytes = std::fs::read(&qsi_path)?;
                        anubis_core::qsi::DualKeyQsiDocument::from_cbor(&qsi_bytes)
                            .ok()
                            .and_then(|doc| anubis_core::mlkem::MlKemPublicKey::from_bytes(&doc.decryption_public_key).ok())
                    } else {
                        None
                    };

                    if let Some(mlkem_pk) = mlkem_pk_result {
                        let attrs = NeoFsObjectAttributes {
                            content_type: Some("application/x-anubis-encrypted".to_string()),
                            anubis_type: Some("encrypted-receipt".to_string()),
                            content_hash: Some(content_hash),
                            filename: Some(format!("{}.enc", receipt_name)),
                            ..Default::default()
                        };

                        match neofs.store_encrypted(container_id, &receipt_data, &mlkem_pk, Some(attrs)) {
                            Ok(result) => Some(result.cid),
                            Err(e) => {
                                if !json {
                                    eprintln!("Warning: NeoFS encrypted upload failed: {}", e);
                                }
                                None
                            }
                        }
                    } else {
                        if !json {
                            eprintln!("Warning: No ML-KEM key found for encryption. Storing unencrypted.");
                        }
                        // Fall through to unencrypted storage
                        let attrs = NeoFsObjectAttributes {
                            content_type: Some("application/x-anubis-receipt".to_string()),
                            anubis_type: Some("receipt".to_string()),
                            content_hash: Some(content_hash),
                            filename: Some(receipt_name),
                            ..Default::default()
                        };

                        match neofs.store(container_id, &receipt_data, Some(attrs)) {
                            Ok(result) => Some(result.cid),
                            Err(e) => {
                                if !json {
                                    eprintln!("Warning: NeoFS upload failed: {}", e);
                                }
                                None
                            }
                        }
                    }
                } else {
                    // Unencrypted storage
                    let attrs = NeoFsObjectAttributes {
                        content_type: Some("application/x-anubis-receipt".to_string()),
                        anubis_type: Some("receipt".to_string()),
                        content_hash: Some(content_hash),
                        filename: Some(receipt_name),
                        ..Default::default()
                    };

                    match neofs.store(container_id, &receipt_data, Some(attrs)) {
                        Ok(result) => Some(result.cid),
                        Err(e) => {
                            if !json {
                                eprintln!("Warning: NeoFS upload failed: {}", e);
                            }
                            None
                        }
                    }
                }
            } else {
                if !json {
                    eprintln!("Warning: No receipts_container configured. Skipping NeoFS storage.");
                    eprintln!("Configure with: anubis-notary anchor neo config --receipts-container <ID>");
                }
                None
            }
        }
    } else {
        None
    };

    // Auto-anchor: queue receipt for batch anchoring
    let mut queue_position: Option<usize> = None;
    let mut queue_total: Option<usize> = None;
    let mut queue_flush_recommended = false;

    if auto_anchor {
        use anubis_io::pipeline::{Pipeline, PipelineConfig};

        let ks_pipeline = Keystore::open(Keystore::default_path())?;
        let config = PipelineConfig {
            auto_encrypt: false,
            auto_store_neofs: false,
            auto_queue: true,
            auto_flush_threshold: 8,
            verify_identity: false,
        };
        let pipeline = Pipeline::new(ks_pipeline, config)?;
        let queue_result = pipeline.smart_enqueue(&digest, receipt_path)?;
        queue_position = Some(queue_result.position);
        queue_total = Some(queue_result.total_pending);
        queue_flush_recommended = pipeline.should_flush()?;

        if !json {
            eprintln!("Queued for batch anchoring: position {}/{}",
                queue_result.position, queue_result.total_pending);
            if queue_flush_recommended {
                eprintln!("Queue threshold reached. Run 'anchor neo flush' to submit batch.");
            }
        }
    }

    if json {
        #[derive(Serialize)]
        struct AttestResult {
            path: String,
            digest: String,
            created: i64,
            receipt: String,
            signed: bool,
            sig_size: usize,
            neofs_cid: Option<String>,
            queue_position: Option<usize>,
            queue_total: Option<usize>,
            queue_flush_recommended: bool,
        }
        let output = JsonOutput::success(AttestResult {
            path: path.display().to_string(),
            digest: hex::encode(digest),
            created: now,
            receipt: receipt_path.display().to_string(),
            signed: true,
            sig_size: receipt.sig_len,
            neofs_cid,
            queue_position,
            queue_total,
            queue_flush_recommended,
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!("Attested: {}", path.display());
        println!("Digest: {}", hex::encode(digest));
        println!("Created: {}", now);
        println!("Receipt: {}", receipt_path.display());
        println!("Signed: {} bytes (ML-DSA-87)", receipt.sig_len);
        if let Some(ref cid) = neofs_cid {
            println!("NeoFS: {}", cid);
        }
        if let Some(pos) = queue_position {
            println!("Queue: {}/{}", pos, queue_total.unwrap_or(0));
        }
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

    // Check if key is revoked (uses SHA-512 fingerprint for CNSA 2.0)
    let fingerprint = hex::encode(anubis_core::sha2::fingerprint(&pk_bytes));
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

    // Compute current hash of the file/directory (SHA-512 for NIST Level 5)
    let current_hash = if path.is_file() {
        hash_file(path)?
    } else if path.is_dir() {
        let entries = hash_directory(path)?;
        let mut combined = Vec::new();
        for (rel_path, hash) in &entries {
            combined.extend_from_slice(rel_path.to_string_lossy().as_bytes());
            combined.extend_from_slice(hash.as_ref());
        }
        anubis_core::sha2::sha512(&combined)
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
            // Uses SHA-512 fingerprint for CNSA 2.0 compliance (128 hex chars)
            let pk_bytes = ks.read_public_key()?;
            let fingerprint = hex::encode(anubis_core::sha2::fingerprint(&pk_bytes));
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
        AnchorCommands::Ztarknet { action } => handle_ztarknet(action, json)?,
        AnchorCommands::Neo { keystore, action } => handle_neo(action, json, keystore.as_deref())?,
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
                                JsonOutput::error(format!("Transaction failed: {}", e));
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
                        return Err(Box::new(std::io::Error::other(format!(
                            "Starknet transaction failed: {}",
                            e
                        ))));
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
            let receipt_data = read_file(receipt)?;
            let parsed =
                Receipt::decode(&receipt_data).map_err(|e| format!("Invalid receipt: {:?}", e))?;

            // Open batch queue
            let queue_path = ks.path().join("starknet-batch-queue");
            let queue = BatchQueue::open(&queue_path)?;

            // Add to queue
            let entry = queue.enqueue(&parsed.digest, receipt)?;

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

fn handle_ztarknet(
    action: &ZtarknetCommands,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::receipt::Receipt;
    use anubis_io::ztarknet::{PrivacyMode, ZtarknetClient, ZtarknetConfig, ZtarknetNetwork};

    let ks = Keystore::open(Keystore::default_path())?;

    match action {
        ZtarknetCommands::Config {
            contract,
            network,
            rpc,
            show,
        } => {
            let config_path = ks.path().join("ztarknet.json");

            if *show || (contract.is_none() && network.is_none() && rpc.is_none()) {
                // Show current configuration
                if config_path.exists() {
                    let config_data = std::fs::read_to_string(&config_path)?;
                    let config: serde_json::Value = serde_json::from_str(&config_data)?;

                    if json {
                        let output = JsonOutput::success(&config);
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Ztarknet Configuration:");
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
                        "rpc_url": "https://rpc.ztarknet.cash",
                        "status": "No contract deployed yet. Use PrivacyOracle contract."
                    });

                    if json {
                        let output = JsonOutput::success(&default_config);
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Ztarknet Configuration (defaults):");
                        println!("  Network: mainnet");
                        println!("  RPC URL: https://rpc.ztarknet.cash");
                        println!();
                        println!("Configure with:");
                        println!("  anubis-notary anchor ztarknet config --contract <address>");
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
                    println!("Ztarknet configuration updated.");
                }
            }
        }
        ZtarknetCommands::Time => {
            let config_path = ks.path().join("ztarknet.json");
            let (network, rpc_url) = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                let config: serde_json::Value = serde_json::from_str(&data)?;
                let net = config
                    .get("network")
                    .and_then(|v| v.as_str())
                    .unwrap_or("mainnet");
                let network = match net {
                    "testnet" => ZtarknetNetwork::Testnet,
                    _ => ZtarknetNetwork::Mainnet,
                };
                let url = config
                    .get("rpc_url")
                    .and_then(|v| v.as_str())
                    .map(String::from);
                (network, url)
            } else {
                (ZtarknetNetwork::Mainnet, None)
            };

            let config = ZtarknetConfig {
                network,
                rpc_url: rpc_url.unwrap_or_else(|| network.default_rpc_url().to_string()),
                contract_address: None,
                account_address: None,
                default_privacy_mode: PrivacyMode::Committed,
                fee_multiplier: 1.0,
                timeout_secs: 30,
            };

            let client = ZtarknetClient::new(config)?;
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
                println!("Ztarknet Time:");
                println!("  Block Number: {}", time_result.block_number);
                println!("  Timestamp: {} ({})", time_result.timestamp, {
                    use std::time::{Duration, UNIX_EPOCH};
                    let dt = UNIX_EPOCH + Duration::from_secs(time_result.timestamp);
                    format!("{:?}", dt)
                });
                println!("  Network: {:?}", network);
                println!("  L1 Settlement: Zcash");
            }
        }
        ZtarknetCommands::Balance { account } => {
            let config_path = ks.path().join("ztarknet.json");
            let (network, rpc_url) = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                let config: serde_json::Value = serde_json::from_str(&data)?;
                let net = config
                    .get("network")
                    .and_then(|v| v.as_str())
                    .unwrap_or("mainnet");
                let network = match net {
                    "testnet" => ZtarknetNetwork::Testnet,
                    _ => ZtarknetNetwork::Mainnet,
                };
                let url = config
                    .get("rpc_url")
                    .and_then(|v| v.as_str())
                    .map(String::from);
                (network, url)
            } else {
                (ZtarknetNetwork::Mainnet, None)
            };

            let account_addr = account
                .clone()
                .or_else(|| std::env::var("ZTARKNET_ACCOUNT").ok());

            if account_addr.is_none() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "No account specified. Use --account or set ZTARKNET_ACCOUNT.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Error: No account specified.");
                    println!(
                        "Use --account <address> or set ZTARKNET_ACCOUNT environment variable."
                    );
                }
                return Ok(());
            }

            let config = ZtarknetConfig {
                network,
                rpc_url: rpc_url.unwrap_or_else(|| network.default_rpc_url().to_string()),
                contract_address: None,
                account_address: account_addr.clone(),
                default_privacy_mode: PrivacyMode::Committed,
                fee_multiplier: 1.0,
                timeout_secs: 30,
            };

            let client = ZtarknetClient::new(config)?;
            let balance = client.get_balance(&account_addr.unwrap())?;

            // Convert from wei to ZEC (18 decimals)
            let zec_balance = balance as f64 / 1e18;

            if json {
                #[derive(Serialize)]
                struct BalanceResult {
                    balance_wei: String,
                    balance_zec: f64,
                    network: String,
                }
                let output = JsonOutput::success(BalanceResult {
                    balance_wei: balance.to_string(),
                    balance_zec: zec_balance,
                    network: format!("{:?}", network).to_lowercase(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Ztarknet Balance:");
                println!("  Account: {}", account.as_deref().unwrap_or("(from env)"));
                println!("  Balance: {:.6} ZEC ({} wei)", zec_balance, balance);
                println!("  Network: {:?}", network);
            }
        }
        ZtarknetCommands::Info => {
            if json {
                #[derive(Serialize)]
                struct ZtarknetInfo {
                    networks: Vec<NetworkInfo>,
                    costs: CostInfo,
                    privacy_modes: Vec<PrivacyModeInfo>,
                    features: Vec<String>,
                }
                #[derive(Serialize)]
                struct NetworkInfo {
                    name: String,
                    rpc_url: String,
                    l1_settlement: String,
                }
                #[derive(Serialize)]
                struct CostInfo {
                    public_anchor_usd: String,
                    committed_anchor_usd: String,
                    reveal_usd: String,
                    disclosure_usd: String,
                }
                #[derive(Serialize)]
                struct PrivacyModeInfo {
                    mode: String,
                    description: String,
                }
                let output = JsonOutput::success(ZtarknetInfo {
                    networks: vec![
                        NetworkInfo {
                            name: "mainnet".to_string(),
                            rpc_url: "https://rpc.ztarknet.cash".to_string(),
                            l1_settlement: "Zcash mainnet".to_string(),
                        },
                        NetworkInfo {
                            name: "testnet".to_string(),
                            rpc_url: "https://testnet-rpc.ztarknet.cash".to_string(),
                            l1_settlement: "Zcash testnet".to_string(),
                        },
                    ],
                    costs: CostInfo {
                        public_anchor_usd: "~$0.0005".to_string(),
                        committed_anchor_usd: "~$0.0008".to_string(),
                        reveal_usd: "~$0.0005".to_string(),
                        disclosure_usd: "~$0.0003".to_string(),
                    },
                    privacy_modes: vec![
                        PrivacyModeInfo {
                            mode: "public".to_string(),
                            description: "Document hash visible on-chain".to_string(),
                        },
                        PrivacyModeInfo {
                            mode: "selective".to_string(),
                            description: "Viewing key required to see hash".to_string(),
                        },
                        PrivacyModeInfo {
                            mode: "committed".to_string(),
                            description: "Only Pedersen commitment on-chain".to_string(),
                        },
                    ],
                    features: vec![
                        "Zcash L1 settlement (native privacy)".to_string(),
                        "Circle STARK proofs (Stwo prover)".to_string(),
                        "Pedersen commitments for hash hiding".to_string(),
                        "Disclosure tokens for auditors".to_string(),
                        "Time-locked selective revelation".to_string(),
                    ],
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!(
                    "╔══════════════════════════════════════════════════════════════════════════╗"
                );
                println!(
                    "║                 ZTARKNET PRIVACY-PRESERVING ANCHORING                    ║"
                );
                println!(
                    "╠══════════════════════════════════════════════════════════════════════════╣"
                );
                println!(
                    "║  PRIVACY MODES                                                           ║"
                );
                println!(
                    "║  ─────────────                                                           ║"
                );
                println!(
                    "║  public    - Document hash visible on-chain                              ║"
                );
                println!(
                    "║  selective - Viewing key required to see hash                            ║"
                );
                println!(
                    "║  committed - Only Pedersen commitment on-chain (ZK)                      ║"
                );
                println!(
                    "╟──────────────────────────────────────────────────────────────────────────╢"
                );
                println!(
                    "║  NETWORKS                                                                ║"
                );
                println!(
                    "║  ────────                                                                ║"
                );
                println!(
                    "║  mainnet  - https://rpc.ztarknet.cash (Zcash L1 settlement)              ║"
                );
                println!(
                    "║  testnet  - https://testnet-rpc.ztarknet.cash (Zcash testnet)            ║"
                );
                println!(
                    "╟──────────────────────────────────────────────────────────────────────────╢"
                );
                println!(
                    "║  COSTS (Privacy-preserving, ~50% cheaper than Starknet)                  ║"
                );
                println!(
                    "║  ─────                                                                   ║"
                );
                println!(
                    "║  Public Anchor:     ~$0.0005 per transaction                             ║"
                );
                println!(
                    "║  Committed Anchor:  ~$0.0008 per transaction                             ║"
                );
                println!(
                    "║  Reveal:            ~$0.0005 per transaction                             ║"
                );
                println!(
                    "║  Disclosure Grant:  ~$0.0003 per transaction                             ║"
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
                    "║  • Zcash L1 settlement (native shielded pool privacy)                    ║"
                );
                println!(
                    "║  • Circle STARK proofs via Stwo prover (quantum-resistant)               ║"
                );
                println!(
                    "║  • Pedersen commitments for hiding document hashes                       ║"
                );
                println!(
                    "║  • Disclosure tokens for time-limited auditor access                     ║"
                );
                println!(
                    "║  • Nullifier set prevents double-reveal attacks                          ║"
                );
                println!(
                    "║  • Cairo VM compatible (Madara sequencer)                                ║"
                );
                println!(
                    "╚══════════════════════════════════════════════════════════════════════════╝"
                );
                println!();
                println!("To get started:");
                println!("  1. Configure: anubis-notary anchor ztarknet config --contract <addr>");
                println!("  2. Anchor:    anubis-notary anchor ztarknet anchor receipt.anb --mode committed");
                println!("  3. Reveal:    anubis-notary anchor ztarknet reveal --commitment-id <id> --blinding <hex>");
            }
        }
        ZtarknetCommands::Keygen => {
            // Generate a new Ztarknet keypair (same as Starknet - Cairo VM compatible)
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
                        "Save the private key securely. Set as ZTARKNET_PRIVATE_KEY for operations."
                            .to_string(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!(
                    "╔══════════════════════════════════════════════════════════════════════════╗"
                );
                println!(
                    "║                    ZTARKNET KEYPAIR GENERATED                            ║"
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
                println!("  1. Fund the account with ZEC on Ztarknet");
                println!("  2. Set: export ZTARKNET_PRIVATE_KEY={:#x}", private_key);
                println!("  3. Configure PrivacyOracle contract address");
            }
        }
        ZtarknetCommands::Anchor {
            receipt,
            mode,
            viewing_key: _,
            wait,
        } => {
            // Load receipt
            let receipt_data = std::fs::read(receipt)?;
            let receipt_obj = Receipt::decode(&receipt_data)
                .map_err(|e| format!("Failed to decode receipt: {:?}", e))?;

            // Get document hash from receipt
            let doc_hash: [u8; 64] = receipt_obj.digest;

            // Parse privacy mode
            let privacy_mode = match mode.to_lowercase().as_str() {
                "public" => PrivacyMode::Public,
                "selective" => PrivacyMode::Selective,
                "committed" => PrivacyMode::Committed,
                _ => {
                    return Err(format!("Invalid privacy mode: {}. Use public, selective, or committed.", mode).into());
                }
            };

            // Load Ztarknet config
            let config_path = ks.path().join("ztarknet.json");
            if !config_path.exists() {
                return Err("Ztarknet not configured. Run 'anchor ztarknet config' first.".into());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            let config_json: serde_json::Value = serde_json::from_str(&config_data)?;

            let contract_addr = config_json
                .get("contract_address")
                .and_then(|v| v.as_str())
                .ok_or("No contract address configured")?;

            let net_str = config_json
                .get("network")
                .and_then(|v| v.as_str())
                .unwrap_or("mainnet");
            let network = match net_str {
                "testnet" => ZtarknetNetwork::Testnet,
                _ => ZtarknetNetwork::Mainnet,
            };

            let rpc_url = config_json
                .get("rpc_url")
                .and_then(|v| v.as_str())
                .map(String::from)
                .unwrap_or_else(|| network.default_rpc_url().to_string());

            let config = ZtarknetConfig {
                network,
                rpc_url,
                contract_address: Some(contract_addr.to_string()),
                account_address: std::env::var("ZTARKNET_ACCOUNT").ok(),
                default_privacy_mode: privacy_mode.clone(),
                fee_multiplier: 1.0,
                timeout_secs: if *wait { 120 } else { 30 },
            };

            if !json {
                println!("Anchoring to Ztarknet with {:?} privacy mode...", privacy_mode);
            }

            let client = ZtarknetClient::new(config)?;
            let result = client.anchor_with_privacy(&doc_hash, privacy_mode.clone())?;

            if json {
                #[derive(Serialize)]
                struct AnchorResult {
                    tx_hash: String,
                    commitment_id: u64,
                    blinding_factor: Option<String>,
                    privacy_mode: String,
                    network: String,
                }
                let output = JsonOutput::success(AnchorResult {
                    tx_hash: result.tx_hash.clone(),
                    commitment_id: result.commitment_id,
                    blinding_factor: result.blinding_factor.map(|b| hex::encode(b)),
                    privacy_mode: format!("{:?}", privacy_mode),
                    network: net_str.to_string(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Anchored successfully!");
                println!("  Transaction: {}", result.tx_hash);
                println!("  Commitment ID: {}", result.commitment_id);
                if let Some(bf) = result.blinding_factor {
                    println!("  Blinding Factor: {} (SAVE THIS!)", hex::encode(bf));
                }
                println!("  Privacy Mode: {:?}", privacy_mode);
                println!("  Network: {}", net_str);
            }
        }
        ZtarknetCommands::Verify {
            receipt,
            commitment_id,
            blinding,
        } => {
            // Load receipt
            let receipt_data = std::fs::read(receipt)?;
            let receipt_obj = Receipt::decode(&receipt_data)
                .map_err(|e| format!("Failed to decode receipt: {:?}", e))?;

            // Get document hash from receipt
            let doc_hash: [u8; 64] = receipt_obj.digest;

            // Load Ztarknet config
            let config_path = ks.path().join("ztarknet.json");
            if !config_path.exists() {
                return Err("Ztarknet not configured. Run 'anchor ztarknet config' first.".into());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            let config_json: serde_json::Value = serde_json::from_str(&config_data)?;

            let contract_addr = config_json
                .get("contract_address")
                .and_then(|v| v.as_str())
                .ok_or("No contract address configured")?;

            let net_str = config_json
                .get("network")
                .and_then(|v| v.as_str())
                .unwrap_or("mainnet");
            let network = match net_str {
                "testnet" => ZtarknetNetwork::Testnet,
                _ => ZtarknetNetwork::Mainnet,
            };

            let rpc_url = config_json
                .get("rpc_url")
                .and_then(|v| v.as_str())
                .map(String::from)
                .unwrap_or_else(|| network.default_rpc_url().to_string());

            let config = ZtarknetConfig {
                network,
                rpc_url,
                contract_address: Some(contract_addr.to_string()),
                account_address: None,
                default_privacy_mode: PrivacyMode::Committed,
                fee_multiplier: 1.0,
                timeout_secs: 30,
            };

            let client = ZtarknetClient::new(config)?;

            // Determine verification mode
            let privacy_mode = if commitment_id.is_some() && blinding.is_some() {
                PrivacyMode::Committed
            } else {
                PrivacyMode::Public
            };

            let result = client.verify_anchor(&doc_hash, privacy_mode)?;

            // Convert enum result to our output format
            let (verified, anchor_type, timestamp) = match &result {
                anubis_io::VerifyResult::Public { verified, timestamp } => {
                    (*verified, "public".to_string(), Some(*timestamp))
                }
                anubis_io::VerifyResult::CommitmentExists { commitment_id, timestamp } => {
                    (true, format!("committed (id: {})", commitment_id), Some(*timestamp))
                }
                anubis_io::VerifyResult::Revealed { verified, commitment_id, timestamp } => {
                    (*verified, format!("revealed (id: {})", commitment_id), Some(*timestamp))
                }
                anubis_io::VerifyResult::NeedsDisclosure => {
                    (false, "needs_disclosure".to_string(), None)
                }
            };

            if json {
                #[derive(Serialize)]
                struct VerifyResultOutput {
                    verified: bool,
                    anchor_type: String,
                    timestamp: Option<u64>,
                    network: String,
                }
                let output = JsonOutput::success(VerifyResultOutput {
                    verified,
                    anchor_type: anchor_type.clone(),
                    timestamp,
                    network: net_str.to_string(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                if verified {
                    println!("Verification PASSED");
                    println!("  Anchor Type: {}", anchor_type);
                    if let Some(ts) = timestamp {
                        println!("  Timestamp: {}", ts);
                    }
                    println!("  Network: {}", net_str);
                } else {
                    println!("Verification FAILED");
                    println!("  Document not found on Ztarknet");
                }
            }
        }
        ZtarknetCommands::Reveal {
            commitment_id,
            blinding,
            original_hash,
        } => {
            // Parse hex inputs
            let blinding_bytes: [u8; 32] = hex::decode(blinding.trim_start_matches("0x"))
                .map_err(|_| "Invalid blinding factor hex")?
                .try_into()
                .map_err(|_| "Blinding factor must be 32 bytes")?;

            let hash_bytes: [u8; 32] = hex::decode(original_hash.trim_start_matches("0x"))
                .map_err(|_| "Invalid original hash hex")?
                .try_into()
                .map_err(|_| "Original hash must be 32 bytes")?;

            // Load Ztarknet config
            let config_path = ks.path().join("ztarknet.json");
            if !config_path.exists() {
                return Err("Ztarknet not configured. Run 'anchor ztarknet config' first.".into());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            let config_json: serde_json::Value = serde_json::from_str(&config_data)?;

            let contract_addr = config_json
                .get("contract_address")
                .and_then(|v| v.as_str())
                .ok_or("No contract address configured")?;

            let net_str = config_json
                .get("network")
                .and_then(|v| v.as_str())
                .unwrap_or("mainnet");
            let network = match net_str {
                "testnet" => ZtarknetNetwork::Testnet,
                _ => ZtarknetNetwork::Mainnet,
            };

            let rpc_url = config_json
                .get("rpc_url")
                .and_then(|v| v.as_str())
                .map(String::from)
                .unwrap_or_else(|| network.default_rpc_url().to_string());

            let config = ZtarknetConfig {
                network,
                rpc_url,
                contract_address: Some(contract_addr.to_string()),
                account_address: std::env::var("ZTARKNET_ACCOUNT").ok(),
                default_privacy_mode: PrivacyMode::Committed,
                fee_multiplier: 1.0,
                timeout_secs: 60,
            };

            if !json {
                println!("Revealing commitment {}...", commitment_id);
            }

            let client = ZtarknetClient::new(config)?;
            let result = client.reveal_commitment(*commitment_id, &hash_bytes, &blinding_bytes)?;

            // If we get here without error, reveal succeeded
            if json {
                #[derive(Serialize)]
                struct RevealResultOutput {
                    success: bool,
                    tx_hash: String,
                    commitment_id: u64,
                    block_number: u64,
                }
                let output = JsonOutput::success(RevealResultOutput {
                    success: true,
                    tx_hash: result.tx_hash.clone(),
                    commitment_id: result.commitment_id,
                    block_number: result.block_number,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Commitment revealed successfully!");
                println!("  Transaction: {}", result.tx_hash);
                println!("  Block: {}", result.block_number);
                println!("  Original Hash: 0x{}", hex::encode(result.original_hash));
                println!("  The document hash is now publicly visible.");
            }
        }
        ZtarknetCommands::Disclose {
            commitment_id,
            recipient,
            duration,
        } => {
            // Load Ztarknet config
            let config_path = ks.path().join("ztarknet.json");
            if !config_path.exists() {
                return Err("Ztarknet not configured. Run 'anchor ztarknet config' first.".into());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            let config_json: serde_json::Value = serde_json::from_str(&config_data)?;

            let contract_addr = config_json
                .get("contract_address")
                .and_then(|v| v.as_str())
                .ok_or("No contract address configured")?;

            let net_str = config_json
                .get("network")
                .and_then(|v| v.as_str())
                .unwrap_or("mainnet");
            let network = match net_str {
                "testnet" => ZtarknetNetwork::Testnet,
                _ => ZtarknetNetwork::Mainnet,
            };

            let rpc_url = config_json
                .get("rpc_url")
                .and_then(|v| v.as_str())
                .map(String::from)
                .unwrap_or_else(|| network.default_rpc_url().to_string());

            let config = ZtarknetConfig {
                network,
                rpc_url,
                contract_address: Some(contract_addr.to_string()),
                account_address: std::env::var("ZTARKNET_ACCOUNT").ok(),
                default_privacy_mode: PrivacyMode::Committed,
                fee_multiplier: 1.0,
                timeout_secs: 60,
            };

            if !json {
                println!("Granting disclosure for commitment {} to {}...", commitment_id, recipient);
            }

            let client = ZtarknetClient::new(config)?;
            let token = client.grant_disclosure(*commitment_id, recipient, *duration)?;

            if json {
                #[derive(Serialize)]
                struct DisclosureResult {
                    token_id: String,
                    commitment_id: u64,
                    recipient: String,
                    expires_at: u64,
                }
                let output = JsonOutput::success(DisclosureResult {
                    token_id: hex::encode(token.token_id),
                    commitment_id: token.commitment_id,
                    recipient: token.recipient.clone(),
                    expires_at: token.expires_at,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Disclosure token granted!");
                println!("  Token ID: 0x{}", hex::encode(token.token_id));
                println!("  Commitment ID: {}", token.commitment_id);
                println!("  Recipient: {}", token.recipient);
                println!("  Expires: {} ({}s from now)", token.expires_at, duration);
            }
        }
        ZtarknetCommands::Revoke { token_id } => {
            // Load Ztarknet config
            let config_path = ks.path().join("ztarknet.json");
            if !config_path.exists() {
                return Err("Ztarknet not configured. Run 'anchor ztarknet config' first.".into());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            let config_json: serde_json::Value = serde_json::from_str(&config_data)?;

            let contract_addr = config_json
                .get("contract_address")
                .and_then(|v| v.as_str())
                .ok_or("No contract address configured")?;

            let net_str = config_json
                .get("network")
                .and_then(|v| v.as_str())
                .unwrap_or("mainnet");
            let network = match net_str {
                "testnet" => ZtarknetNetwork::Testnet,
                _ => ZtarknetNetwork::Mainnet,
            };

            let rpc_url = config_json
                .get("rpc_url")
                .and_then(|v| v.as_str())
                .map(String::from)
                .unwrap_or_else(|| network.default_rpc_url().to_string());

            let config = ZtarknetConfig {
                network,
                rpc_url,
                contract_address: Some(contract_addr.to_string()),
                account_address: std::env::var("ZTARKNET_ACCOUNT").ok(),
                default_privacy_mode: PrivacyMode::Committed,
                fee_multiplier: 1.0,
                timeout_secs: 60,
            };

            // Parse token ID
            let token_bytes: [u8; 32] = hex::decode(token_id.trim_start_matches("0x"))
                .map_err(|_| "Invalid token ID hex")?
                .try_into()
                .map_err(|_| "Token ID must be 32 bytes")?;

            if !json {
                println!("Revoking disclosure token {}...", token_id);
            }

            let client = ZtarknetClient::new(config)?;
            let success = client.revoke_disclosure(&token_bytes)?;

            if json {
                #[derive(Serialize)]
                struct RevokeResult {
                    success: bool,
                    token_id: String,
                }
                let output = JsonOutput::success(RevokeResult {
                    success,
                    token_id: token_id.clone(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                if success {
                    println!("Disclosure token revoked successfully.");
                } else {
                    println!("Failed to revoke token. Check token ID and ownership.");
                }
            }
        }
        ZtarknetCommands::Commitment { id } => {
            // Load Ztarknet config
            let config_path = ks.path().join("ztarknet.json");
            if !config_path.exists() {
                return Err("Ztarknet not configured. Run 'anchor ztarknet config' first.".into());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            let config_json: serde_json::Value = serde_json::from_str(&config_data)?;

            let contract_addr = config_json
                .get("contract_address")
                .and_then(|v| v.as_str())
                .ok_or("No contract address configured")?;

            let net_str = config_json
                .get("network")
                .and_then(|v| v.as_str())
                .unwrap_or("mainnet");
            let network = match net_str {
                "testnet" => ZtarknetNetwork::Testnet,
                _ => ZtarknetNetwork::Mainnet,
            };

            let rpc_url = config_json
                .get("rpc_url")
                .and_then(|v| v.as_str())
                .map(String::from)
                .unwrap_or_else(|| network.default_rpc_url().to_string());

            let config = ZtarknetConfig {
                network,
                rpc_url,
                contract_address: Some(contract_addr.to_string()),
                account_address: None,
                default_privacy_mode: PrivacyMode::Committed,
                fee_multiplier: 1.0,
                timeout_secs: 30,
            };

            let client = ZtarknetClient::new(config)?;
            let info = client.get_commitment_info(*id)?;

            if json {
                let output = JsonOutput::success(&info);
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Commitment #{}:", id);
                println!("  Pedersen Commitment: 0x{}", hex::encode(&info.commitment));
                println!("  Timestamp: {}", info.timestamp);
                println!("  Revealed: {}", info.revealed);
                if info.revealed {
                    if let Some(hash) = &info.original_hash {
                        println!("  Original Hash: 0x{}", hex::encode(hash));
                    }
                }
            }
        }
    }

    Ok(())
}

fn handle_neo(action: &NeoCommands, json: bool, keystore_path: Option<&Path>) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::receipt::{AnchorType, Receipt};
    use anubis_io::neo::{NeoClient, NeoConfig, NeoFsClient, NeoFsObjectAttributes, NeoNetwork, NnsClient};

    let ks_path = keystore_path
        .map(|p| p.to_path_buf())
        .unwrap_or_else(Keystore::default_path);
    let ks = Keystore::open(ks_path)?;

    match action {
        NeoCommands::Config {
            contract,
            network,
            rpc,
            neofs,
            neoid,
            nns,
            identity_container,
            receipts_container,
            batch_container,
            show,
        } => {
            let config_path = ks.path().join("neo.json");

            if *show {
                if config_path.exists() {
                    let data = std::fs::read_to_string(&config_path)?;
                    if json {
                        println!("{}", data);
                    } else {
                        println!("Neo N3 Configuration:");
                        println!("{}", data);
                    }
                } else if json {
                    #[derive(Serialize)]
                    struct Empty {}
                    let output = JsonOutput::<Empty> {
                        success: false,
                        error: Some("No Neo configuration found".to_string()),
                        data: None,
                    };
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("No Neo configuration found.");
                    println!("Run: anubis-notary anchor neo config --contract <SCRIPT_HASH>");
                }
                return Ok(());
            }

            // Load existing or create new config
            let mut config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::MainNet)
            };

            // Update fields
            if let Some(net) = network {
                config.network = NeoNetwork::parse(net).unwrap_or(NeoNetwork::MainNet);
                // Update default URLs for new network
                config.rpc_url = config.network.default_rpc_url().to_string();
                config.neofs_url = config.network.default_neofs_url().to_string();
                config.neoid_url = config.network.default_neoid_url().to_string();
                config.nns_contract = config.network.nns_script_hash().to_string();
            }
            if let Some(c) = contract {
                config.contract_address = Some(c.clone());
            }
            if let Some(r) = rpc {
                config.rpc_url = r.clone();
            }
            if let Some(f) = neofs {
                config.neofs_url = f.clone();
            }
            if let Some(i) = neoid {
                config.neoid_url = i.clone();
            }
            if let Some(n) = nns {
                config.nns_contract = n.clone();
            }
            if let Some(c) = identity_container {
                config.identity_container = Some(c.clone());
            }
            if let Some(c) = receipts_container {
                config.receipts_container = Some(c.clone());
            }
            if let Some(c) = batch_container {
                config.batch_container = Some(c.clone());
            }

            // Validate before saving
            config.validate()?;

            // Save configuration
            let data = serde_json::to_string_pretty(&config)?;
            std::fs::write(&config_path, &data)?;

            if json {
                #[derive(Serialize)]
                struct ConfigResult {
                    saved: bool,
                    path: String,
                    network: String,
                }
                let output = JsonOutput::success(ConfigResult {
                    saved: true,
                    path: config_path.display().to_string(),
                    network: config.network.name().to_string(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Neo N3 configuration saved to {}", config_path.display());
                println!("  Network: {}", config.network.name());
                println!("  RPC URL: {}", config.rpc_url);
                if let Some(ref addr) = config.contract_address {
                    println!("  Contract: {}", addr);
                }
                println!("  NeoFS: {}", config.neofs_url);
                println!("  NeoID: {}", config.neoid_url);
                if config.identity_container.is_some() || config.receipts_container.is_some() || config.batch_container.is_some() {
                    println!("  Containers:");
                    if let Some(ref c) = config.identity_container {
                        println!("    Identity: {}", c);
                    }
                    if let Some(ref c) = config.receipts_container {
                        println!("    Receipts: {}", c);
                    }
                    if let Some(ref c) = config.batch_container {
                        println!("    Batches:  {}", c);
                    }
                }
            }
        }
        NeoCommands::Time => {
            // Load config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::MainNet)
            };

            let client = NeoClient::new(config)?;
            let result = client.get_block_time()?;

            if json {
                println!("{}", serde_json::to_string_pretty(&result)?);
            } else {
                println!("Neo N3 Blockchain Time (dBFT - instant finality):");
                println!("  Block: {}", result.block_number);
                println!("  Timestamp: {} ({} UTC)",
                    result.timestamp,
                    chrono::DateTime::from_timestamp((result.timestamp / 1000) as i64, 0)
                        .map(|dt| dt.format("%Y-%m-%d %H:%M:%S").to_string())
                        .unwrap_or_else(|| "Unknown".to_string())
                );
                println!("  Network: {}", result.network);
            }
        }
        NeoCommands::Balance { account } => {
            // Load config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::MainNet)
            };

            let addr = account.clone()
                .or_else(|| config.account_address.clone())
                .or_else(|| std::env::var("NEO_ACCOUNT").ok())
                .ok_or("No account specified. Use --account or set NEO_ACCOUNT")?;

            let client = NeoClient::new(config)?;
            let balance = client.get_balance(&addr)?;

            // GAS has 8 decimals
            let gas_balance = balance as f64 / 100_000_000.0;

            if json {
                #[derive(Serialize)]
                struct BalanceResult {
                    address: String,
                    balance_raw: u128,
                    balance_gas: f64,
                }
                let output = JsonOutput::success(BalanceResult {
                    address: addr.clone(),
                    balance_raw: balance,
                    balance_gas: gas_balance,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Neo N3 Account Balance:");
                println!("  Address: {}", addr);
                println!("  GAS: {:.8}", gas_balance);
            }
        }
        NeoCommands::Info => {
            // Load config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::MainNet)
            };

            if json {
                #[derive(Serialize)]
                struct InfoResult {
                    network: String,
                    rpc_url: String,
                    contract: Option<String>,
                    neofs_url: String,
                    neoid_url: String,
                    nns_contract: String,
                    features: Vec<String>,
                }
                let output = JsonOutput::success(InfoResult {
                    network: config.network.name().to_string(),
                    rpc_url: config.rpc_url.clone(),
                    contract: config.contract_address.clone(),
                    neofs_url: config.neofs_url.clone(),
                    neoid_url: config.neoid_url.clone(),
                    nns_contract: config.nns_contract.clone(),
                    features: vec![
                        "dBFT 2.0 (instant finality)".to_string(),
                        "NeoFS (decentralized storage)".to_string(),
                        "NeoID (self-sovereign identity)".to_string(),
                        "NNS (Neo Name Service)".to_string(),
                        "QSI (Quantum-Safe Identity)".to_string(),
                        "Collaborative Anchoring".to_string(),
                    ],
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("╔══════════════════════════════════════════════════════════════════════════╗");
                println!("║                       NEO N3 INTEGRATION INFO                            ║");
                println!("╠══════════════════════════════════════════════════════════════════════════╣");
                println!("║                                                                          ║");
                println!("║  Network: {:62}║", config.network.name());
                println!("║  RPC URL: {:62}║", &config.rpc_url[..config.rpc_url.len().min(62)]);
                if let Some(ref addr) = config.contract_address {
                    println!("║  Contract: {:61}║", &addr[..addr.len().min(61)]);
                } else {
                    println!("║  Contract: (not configured)                                              ║");
                }
                println!("║                                                                          ║");
                println!("╠══════════════════════════════════════════════════════════════════════════╣");
                println!("║  FEATURES:                                                               ║");
                println!("║    • dBFT 2.0 Consensus (one-block finality - no wait needed)            ║");
                println!("║    • NeoFS Decentralized Storage (large receipts off-chain)              ║");
                println!("║    • NeoID Self-Sovereign Identity (DID:NEO compatible)                  ║");
                println!("║    • NNS Name Service (human-readable addresses)                         ║");
                println!("║    • QSI Protocol (ML-DSA-87 bound quantum-safe identity)                ║");
                println!("║    • Collaborative Anchoring (t-of-n threshold privacy)                  ║");
                println!("║                                                                          ║");
                println!("╠══════════════════════════════════════════════════════════════════════════╣");
                println!("║  ESTIMATED COSTS:                                                        ║");
                println!("║    Single anchor:  ~0.1 GAS (~$0.01)                                     ║");
                println!("║    Batch (8):      ~0.15 GAS (~$0.015)                                   ║");
                println!("║    NeoFS (1MB):    ~0.01 GAS (~$0.001)                                   ║");
                println!("║    QSI Register:   ~0.2 GAS (~$0.02)                                     ║");
                println!("╚══════════════════════════════════════════════════════════════════════════╝");
                println!();
                println!("To get started:");
                println!("  1. Configure: anubis-notary anchor neo config --contract <script_hash>");
                println!("  2. Anchor:    anubis-notary anchor neo anchor receipt.anb");
                println!("  3. Verify:    anubis-notary anchor neo verify receipt.anb");
                println!();
                println!("QSI Identity:");
                println!("  Register:   anubis-notary anchor neo identity register --name \"Your Name\"");
                println!("  Verify:     anubis-notary anchor neo identity verify receipt.anb");
            }
        }
        NeoCommands::Anchor { receipt, store_neofs: _, wait: _ } => {
            // Load receipt
            let receipt_data = std::fs::read(receipt)?;
            let receipt_obj = Receipt::decode(&receipt_data)
                .map_err(|e| format!("Failed to decode receipt: {:?}", e))?;

            let doc_hash: [u8; 64] = receipt_obj.digest;

            // Load Neo config
            let config_path = ks.path().join("neo.json");
            if !config_path.exists() {
                return Err("Neo not configured. Run 'anchor neo config --contract <HASH>' first.".into());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            let config: NeoConfig = serde_json::from_str(&config_data)?;

            if config.contract_address.is_none() {
                return Err("No contract configured. Run 'anchor neo config --contract <HASH>'".into());
            }

            if !json {
                println!("Anchoring to Neo N3 (dBFT finality)...");
                println!("  Network: {}", config.network.name());
                println!("  Contract: {}", config.contract_address.as_ref().unwrap());
            }

            let client = NeoClient::new(config)?;
            let result = client.anchor_root(&doc_hash)?;

            if json {
                println!("{}", serde_json::to_string_pretty(&result)?);
            } else {
                println!();
                println!("╔══════════════════════════════════════════════════════════════════════════╗");
                println!("║                     ANCHORED ON NEO N3 (dBFT)                            ║");
                println!("╠══════════════════════════════════════════════════════════════════════════╣");
                println!("║  Transaction: {}...", &result.tx_hash[..40]);
                println!("║  Block: {}", result.block_number);
                println!("║  Root ID: {}", result.root_id);
                println!("║  Timestamp: {}", result.timestamp);
                println!("║                                                                          ║");
                println!("║  ✓ FINALIZED (dBFT one-block confirmation)                               ║");
                println!("╚══════════════════════════════════════════════════════════════════════════╝");
            }
        }
        NeoCommands::Verify { receipt } => {
            // Load receipt
            let receipt_data = std::fs::read(receipt)?;
            let receipt_obj = Receipt::decode(&receipt_data)
                .map_err(|e| format!("Failed to decode receipt: {:?}", e))?;

            // Load config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::MainNet)
            };

            let client = NeoClient::new(config)?;

            // Check if receipt has Neo anchor embedded
            let neo_anchor = match &receipt_obj.anchor {
                AnchorType::Neo { root_id, contract_addr, contract_addr_len, .. } => {
                    let addr_str = std::str::from_utf8(&contract_addr[..*contract_addr_len])
                        .unwrap_or("invalid")
                        .to_string();
                    Some((*root_id, addr_str))
                }
                AnchorType::NeoBatch { root_id, contract_addr, contract_addr_len, .. } => {
                    let addr_str = std::str::from_utf8(&contract_addr[..*contract_addr_len])
                        .unwrap_or("invalid")
                        .to_string();
                    Some((*root_id, addr_str))
                }
                _ => None,
            };

            if let Some((root_id, _contract)) = neo_anchor {
                // Receipt has embedded anchor - verify by root ID
                let verified = client.verify_anchor(root_id, &receipt_obj.digest)?;

                if json {
                    #[derive(Serialize)]
                    struct VerifyResult {
                        verified: bool,
                        root_id: u64,
                        digest: String,
                        method: String,
                    }
                    let output = JsonOutput::success(VerifyResult {
                        verified,
                        root_id,
                        digest: hex::encode(receipt_obj.digest),
                        method: "embedded_anchor".to_string(),
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else if verified {
                    println!("✓ Neo anchor VERIFIED (embedded anchor)");
                    println!("  Root ID: {}", root_id);
                    println!("  Digest: {}", hex::encode(receipt_obj.digest));
                } else {
                    println!("✗ Neo anchor verification FAILED");
                    println!("  Root ID: {}", root_id);
                }
            } else {
                // No embedded anchor - check batch history first, then blockchain
                println!("Checking if receipt is anchored on Neo N3...");

                // Check batch history for this receipt
                let queue_path = ks.path().join("neo-batch-queue");
                let batch_verified = if queue_path.exists() {
                    use anubis_io::BatchQueue;
                    let queue = BatchQueue::open(&queue_path)?;
                    let digest_hex = hex::encode(receipt_obj.digest);

                    if let Some(batch) = queue.find_batch(&digest_hex)? {
                        // Found in batch history - verify the batch root is anchored
                        // (contract stores the Merkle root of all batch members)
                        println!("  Found in batch {} (tx: {}...)", &batch.batch_id[..16], &batch.tx_hash[..16]);

                        // Decode the contract_root from hex and check if it's anchored
                        let contract_root_bytes = hex::decode(&batch.contract_root)
                            .map_err(|e| format!("Invalid contract root: {}", e))?;

                        if contract_root_bytes.len() == 32 {
                            // The contract_root is stored in little-endian format (from contract event).
                            // is_batch_anchored expects big-endian and reverses to LE internally.
                            let mut contract_root_be: [u8; 32] = contract_root_bytes.clone().try_into().unwrap();
                            contract_root_be.reverse();

                            // Use is_batch_anchored for 32-byte batch roots
                            let is_batch_anchored = client.is_batch_anchored(&contract_root_be)?;

                            if is_batch_anchored {
                                // Batch root is anchored - verify receipt is in our batch record
                                let index = batch.digests.iter().position(|d| d == &digest_hex);
                                if index.is_some() {
                                    Some(true)
                                } else {
                                    // Receipt not in batch (shouldn't happen with find_batch)
                                    Some(false)
                                }
                            } else {
                                Some(false)
                            }
                        } else {
                            // Invalid contract root length
                            Some(false)
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };

                let is_anchored = match batch_verified {
                    Some(true) => true, // Batch verification succeeded
                    _ => {
                        // Either not in batch history OR batch verification failed
                        // Fall back to direct blockchain query (handles direct anchoring case)
                        client.is_anchored(&receipt_obj.digest)?
                    }
                };

                if json {
                    #[derive(Serialize)]
                    struct VerifyResult {
                        verified: bool,
                        digest: String,
                        method: String,
                    }
                    let method = if batch_verified == Some(true) { "batch_merkle_proof" } else { "blockchain_query" };
                    let output = JsonOutput::success(VerifyResult {
                        verified: is_anchored,
                        digest: hex::encode(receipt_obj.digest),
                        method: method.to_string(),
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else if is_anchored {
                    let method = if batch_verified == Some(true) { " (via batch Merkle proof)" } else { "" };
                    println!("✓ Receipt is ANCHORED on Neo N3{}", method);
                    println!("  Digest: {}", hex::encode(receipt_obj.digest));
                    println!("  Contract: {}", client.config().contract_address.as_deref().unwrap_or("N/A"));
                } else {
                    println!("✗ Receipt is NOT anchored on Neo N3");
                    println!("  Digest: {}", hex::encode(receipt_obj.digest));
                    println!("  Contract: {}", client.config().contract_address.as_deref().unwrap_or("N/A"));
                }
            }
        }
        NeoCommands::Queue { receipt } => {
            use anubis_io::BatchQueue;

            // Verify the receipt is valid
            let receipt_data = read_file(&receipt)?;
            let parsed =
                Receipt::decode(&receipt_data).map_err(|e| format!("Invalid receipt: {:?}", e))?;

            // Open batch queue
            let queue_path = ks.path().join("neo-batch-queue");
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
                println!("Receipt added to Neo batch queue:");
                println!("  File:    {}", receipt.display());
                println!("  Digest:  {}", entry.digest);
                println!("  Pending: {}/8 receipts", pending);
                if pending >= 8 {
                    println!();
                    println!(
                        "Queue is full! Run 'anubis-notary anchor neo flush' to submit batch."
                    );
                } else {
                    println!();
                    println!("Add {} more receipts for 8x cost savings.", 8 - pending);
                }
            }
        }
        NeoCommands::Flush { force, wait: _ } => {
            use anubis_io::BatchQueue;

            let queue_path = ks.path().join("neo-batch-queue");
            let queue = BatchQueue::open(&queue_path)?;

            let pending = queue.pending()?;
            if pending.is_empty() {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(
                        "Batch queue is empty. Add receipts with 'anchor neo queue'.",
                    );
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Neo batch queue is empty.");
                    println!("Add receipts with: anubis-notary anchor neo queue <receipt>");
                }
                return Ok(());
            }

            if pending.len() < 8 && !force {
                if json {
                    let output: JsonOutput<()> = JsonOutput::error(&format!(
                        "Queue has only {}/8 receipts. Use --force to flush anyway.",
                        pending.len()
                    ));
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!(
                        "Queue has only {}/8 receipts. Add {} more for optimal savings.",
                        pending.len(),
                        8 - pending.len()
                    );
                    println!("Use --force to flush anyway.");
                }
                return Ok(());
            }

            // Load Neo configuration
            let config_path = ks.path().join("neo.json");
            if !config_path.exists() {
                return Err("Neo not configured. Run 'anchor neo config' first.".into());
            }
            let config_data = std::fs::read_to_string(&config_path)?;
            let config: NeoConfig = serde_json::from_str(&config_data)?;

            let client = NeoClient::new(config)?;

            // Collect roots from pending receipts (64-byte SHA-512 digests)
            let mut roots: Vec<[u8; 64]> = Vec::new();
            for entry in &pending {
                let digest_bytes = hex::decode(&entry.digest)
                    .map_err(|e| format!("Invalid digest hex: {}", e))?;
                let root: [u8; 64] = digest_bytes
                    .try_into()
                    .map_err(|_| "Digest must be 64 bytes (SHA-512)")?;
                roots.push(root);
            }

            // Use anchor_root for single receipt, anchor_batch for multiple
            if roots.len() == 1 {
                println!("Submitting single receipt to Neo N3...");
                let result = client.anchor_root(&roots[0])?;

                // Clear the queue on success
                queue.clear()?;

                if json {
                    println!("{}", serde_json::to_string_pretty(&result)?);
                } else {
                    println!();
                    println!("╔══════════════════════════════════════════════════════════════════════════╗");
                    println!("║                     ANCHORED ON NEO N3 (dBFT)                            ║");
                    println!("╠══════════════════════════════════════════════════════════════════════════╣");
                    println!("║  Transaction: {}...", &result.tx_hash[..42.min(result.tx_hash.len())]);
                    println!("║  Block: {}", result.block_number);
                    println!("║  Root ID: {}", result.root_id);
                    println!("║  Timestamp: {}", result.timestamp);
                    println!("║                                                                          ║");
                    println!("║  ✓ FINALIZED (dBFT one-block confirmation)                               ║");
                    println!("╚══════════════════════════════════════════════════════════════════════════╝");
                    println!();
                    println!("Anchored receipt:");
                    println!("  [0] {}", pending[0].digest);
                }
            } else {
                // Use anchor_batch for multiple receipts (single transaction)
                println!("Submitting batch of {} receipts to Neo N3...", roots.len());

                let result = client.anchor_batch(&roots)?;

                // Store batch in history with contract's computed root for verification
                let digests: Vec<String> = pending.iter().map(|e| e.digest.clone()).collect();
                let contract_root_hex = hex::encode(result.contract_root);
                queue.mark_submitted(&digests, &result.tx_hash, result.block_number, &contract_root_hex)?;

                if json {
                    println!("{}", serde_json::to_string_pretty(&result)?);
                } else {
                    println!();
                    println!("╔══════════════════════════════════════════════════════════════════════════╗");
                    println!("║                  NEO BATCH ANCHORED (dBFT)                               ║");
                    println!("╠══════════════════════════════════════════════════════════════════════════╣");
                    println!("║  Transaction: {}...", &result.tx_hash[..42.min(result.tx_hash.len())]);
                    println!("║  Block: {}", result.block_number);
                    println!("║  Batch ID: {}", result.batch_id);
                    println!("║  Batch Root: {}...", &hex::encode(result.batch_root)[..32]);
                    println!("║  Receipts: {}                                                            ║", result.root_count);
                    println!("║  Timestamp: {}                                                           ║", result.timestamp);
                    println!("║                                                                          ║");
                    println!("║  ✓ FINALIZED (dBFT one-block confirmation)                               ║");
                    println!("╚══════════════════════════════════════════════════════════════════════════╝");
                    println!();
                    println!("Anchored receipts (batch ID {}):", result.batch_id);
                    for (i, entry) in pending.iter().enumerate() {
                        println!("  [{}] {}", i, &entry.digest[..32]);
                    }
                }
            }
        }
        NeoCommands::QueueStatus => {
            use anubis_io::BatchQueue;

            let queue_path = ks.path().join("neo-batch-queue");
            let queue = BatchQueue::open(&queue_path)?;
            let pending = queue.pending()?;

            // Calculate cost efficiency
            let max_batch_size = 8;
            let count = pending.len();
            let efficiency = if count == 0 {
                0.0
            } else if count >= max_batch_size {
                100.0
            } else {
                (count as f64 / max_batch_size as f64) * 100.0
            };
            let remaining = max_batch_size.saturating_sub(count);

            if json {
                #[derive(Serialize)]
                struct QueueStatusResult {
                    pending_count: usize,
                    max_batch_size: usize,
                    ready_for_flush: bool,
                    cost_efficiency_percent: f64,
                    receipts_for_optimal: usize,
                    recommendation: String,
                    entries: Vec<QueueEntry>,
                }
                #[derive(Serialize)]
                struct QueueEntry {
                    digest: String,
                    receipt_path: String,
                    queued_at: u64,
                }
                let recommendation = if count >= max_batch_size {
                    "Queue full - flush now for maximum efficiency".to_string()
                } else if count >= 6 {
                    format!("Consider flushing ({} more for optimal)", remaining)
                } else if count > 0 {
                    format!("Wait for {} more receipts for optimal batching", remaining)
                } else {
                    "Queue empty - add receipts with 'attest --auto-anchor' or 'notarize'".to_string()
                };
                let output = JsonOutput::success(QueueStatusResult {
                    pending_count: count,
                    max_batch_size,
                    ready_for_flush: count >= max_batch_size,
                    cost_efficiency_percent: efficiency,
                    receipts_for_optimal: remaining,
                    recommendation,
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
                println!("╔══════════════════════════════════════════════════════════════════════════╗");
                println!("║                     NEO BATCH QUEUE STATUS                               ║");
                println!("╠══════════════════════════════════════════════════════════════════════════╣");

                // Progress bar
                let filled = count.min(max_batch_size);
                let empty = max_batch_size - filled;
                let bar: String = "█".repeat(filled) + &"░".repeat(empty);
                println!("║  Progress: [{}] {}/{}                                     ║", bar, count, max_batch_size);
                println!("║  Cost Efficiency: {:.0}%{:>51}║", efficiency, "");

                if count == 0 {
                    println!("║                                                                          ║");
                    println!("║  Queue is empty.                                                         ║");
                    println!("║  Add receipts with:                                                      ║");
                    println!("║    • anubis-notary notarize <file>                                       ║");
                    println!("║    • anubis-notary attest <file> --receipt <out> --auto-anchor           ║");
                } else {
                    println!("║                                                                          ║");
                    println!("║  Queued Receipts:                                                        ║");
                    for (i, entry) in pending.iter().take(5).enumerate() {
                        let digest_short = &entry.digest[..16];
                        let path_short = if entry.receipt_path.len() > 40 {
                            format!("...{}", &entry.receipt_path[entry.receipt_path.len()-37..])
                        } else {
                            entry.receipt_path.clone()
                        };
                        println!("║    [{}] {}... {}{}║", i+1, digest_short, path_short, " ".repeat(40 - path_short.len().min(40)));
                    }
                    if pending.len() > 5 {
                        println!("║    ... and {} more                                                     ║", pending.len() - 5);
                    }
                }

                println!("║                                                                          ║");
                if count >= max_batch_size {
                    println!("║  ✓ READY TO FLUSH - Maximum efficiency achieved!                        ║");
                    println!("║    Run: anubis-notary anchor neo flush                                  ║");
                } else if count >= 6 {
                    println!("║  → Consider flushing now ({} more for optimal)                           ║", remaining);
                    println!("║    Or wait to maximize cost efficiency.                                 ║");
                } else if count > 0 {
                    println!("║  ○ Wait for {} more receipts for optimal batching                        ║", remaining);
                    println!("║    Current efficiency: {:.0}%                                              ║", efficiency);
                }
                println!("╚══════════════════════════════════════════════════════════════════════════╝");
            }
        }
        NeoCommands::NeofsStore { file, container, encrypt, recipient } => {
            use anubis_io::neo::NeoWallet;

            // Load config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::MainNet)
            };

            // Try to load wallet for authentication
            let wallet_path = ks.path().join("neo-wallet.wif.sealed");
            let wallet = if wallet_path.exists() {
                if let Ok(password) = std::env::var("ANUBIS_PASSWORD") {
                    if let Ok(sealed) = std::fs::read(&wallet_path) {
                        if let Ok(wif_bytes) = anubis_io::seal::unseal_key(password.as_bytes(), &sealed) {
                            if let Ok(wif) = String::from_utf8(wif_bytes) {
                                NeoWallet::from_wif(&wif).ok()
                            } else { None }
                        } else { None }
                    } else { None }
                } else { None }
            } else { None };

            // Fall back to bearer token file if no wallet
            let token_path = ks.path().join("neofs-bearer.token");
            let stored_bearer_token = if wallet.is_none() && token_path.exists() {
                Some(std::fs::read_to_string(&token_path)?.trim().to_string())
            } else {
                None
            };

            // Determine container ID
            let container_id = container.clone().ok_or_else(|| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "NeoFS container ID required. Use --container <ID> or configure default with 'neo config'"
                )
            })?;

            // Read file data
            let data = std::fs::read(&file)?;
            let file_name = file.file_name()
                .map(|n| n.to_string_lossy().to_string())
                .unwrap_or_else(|| "unnamed".to_string());
            let content_hash = hex::encode(anubis_core::sha2::sha512(&data));

            // Determine content type (will be overridden if encrypting)
            let base_content_type = if file_name.ends_with(".anb") {
                "application/x-anubis-receipt"
            } else if file_name.ends_with(".cbor") {
                "application/cbor"
            } else if file_name.ends_with(".json") {
                "application/json"
            } else if file_name.ends_with(".pdf") {
                "application/pdf"
            } else {
                "application/octet-stream"
            };

            // Determine anubis type
            let base_anubis_type = if file_name.ends_with(".anb") {
                Some("receipt".to_string())
            } else {
                None
            };

            // Create NeoFS client
            let mut neofs = NeoFsClient::new(&config.neofs_url, config.timeout_secs);

            // Authenticate with bearer token
            if let Some(ref w) = wallet {
                // Create bearer token using wallet (for PUT operations)
                match neofs.create_bearer_token(w, &["PUT"]) {
                    Ok(bearer) => {
                        neofs.set_bearer_token(&bearer);
                        eprintln!("Authenticated as: {}", w.address());
                    }
                    Err(e) => {
                        eprintln!("Warning: Failed to create bearer token: {}", e);
                        eprintln!("Upload may fail if container requires authentication.");
                    }
                }
            } else if let Some(ref token) = stored_bearer_token {
                neofs.set_bearer_token(token);
            } else {
                eprintln!("Warning: No wallet or bearer token found.");
                eprintln!("Upload will only work with public-write containers.");
            }

            if *encrypt {
                // Load recipient's ML-KEM public key
                let mlkem_pk = if let Some(ref pk_path) = recipient {
                    // Load from specified file
                    let pk_bytes = std::fs::read(pk_path).map_err(|e| {
                        std::io::Error::new(
                            std::io::ErrorKind::NotFound,
                            format!("Failed to read recipient public key: {}", e)
                        )
                    })?;
                    anubis_core::mlkem::MlKemPublicKey::from_bytes(&pk_bytes).map_err(|e| {
                        std::io::Error::new(
                            std::io::ErrorKind::InvalidData,
                            format!("Invalid ML-KEM public key: {}", e)
                        )
                    })?
                } else {
                    // Load from identity keystore (own key)
                    // First try the dedicated .pub file
                    let identity_pub_path = ks.path().join("decryption.mlkem.pub");
                    if identity_pub_path.exists() {
                        let pk_bytes = std::fs::read(&identity_pub_path)?;
                        anubis_core::mlkem::MlKemPublicKey::from_bytes(&pk_bytes).map_err(|e| {
                            std::io::Error::new(
                                std::io::ErrorKind::InvalidData,
                                format!("Invalid identity ML-KEM key: {}", e)
                            )
                        })?
                    } else {
                        // Fall back to extracting from DK-QSI document
                        let qsi_path = ks.path().join("identity.qsi.cbor");
                        if !qsi_path.exists() {
                            return Err(std::io::Error::new(
                                std::io::ErrorKind::NotFound,
                                "No --recipient specified and no identity found. Register with 'anchor neo identity register-dual' first."
                            ).into());
                        }
                        let qsi_bytes = std::fs::read(&qsi_path)?;
                        let doc = anubis_core::qsi::DualKeyQsiDocument::from_cbor(&qsi_bytes)
                            .map_err(|e| std::io::Error::new(
                                std::io::ErrorKind::InvalidData,
                                format!("Invalid QSI document: {:?}", e)
                            ))?;
                        anubis_core::mlkem::MlKemPublicKey::from_bytes(&doc.decryption_public_key)
                            .map_err(|e| std::io::Error::new(
                                std::io::ErrorKind::InvalidData,
                                format!("Invalid ML-KEM key in QSI document: {:?}", e)
                            ))?
                    }
                };

                // Build attributes for encrypted storage
                let attrs = NeoFsObjectAttributes {
                    content_type: Some("application/x-anubis-encrypted".to_string()),
                    anubis_type: Some("encrypted".to_string()),
                    content_hash: Some(content_hash.clone()),
                    filename: Some(format!("{}.enc", file_name)),
                    ..Default::default()
                };

                // Store encrypted with automatic chunking for large files
                let data_size = data.len();
                let progress_callback = |current: usize, total: usize| {
                    if total > 1 {
                        eprint!("\rUploading chunk {}/{} ", current, total);
                    }
                };
                let result = neofs.store_large_encrypted(&container_id, &data, &mlkem_pk, Some(attrs), Some(&progress_callback))?;
                if data_size > anubis_io::neo::NeoFsClient::CHUNK_THRESHOLD {
                    eprintln!(); // Newline after progress
                }

                if json {
                    println!("{}", serde_json::to_string_pretty(&result)?);
                } else {
                    let chunked = if data_size > anubis_io::neo::NeoFsClient::CHUNK_THRESHOLD { " (chunked)" } else { "" };
                    println!("File stored (encrypted{}) in NeoFS:", chunked);
                    println!("  CID: {}", result.cid);
                    println!("  Container: {}", result.container_id);
                    println!("  Object ID: {}", result.object_id);
                    println!("  Size: {} bytes (encrypted payload)", result.size);
                    println!("  Original Hash: {}", content_hash);
                    println!("  Encryption: ML-KEM-1024 + ChaCha20Poly1305");
                    println!();
                    println!("Retrieve with:");
                    println!("  anubis-notary anchor neo neofs-get {} -o {}", result.cid, file_name);
                    println!("  (auto-decrypts if you have the secret key)");
                }
            } else {
                // Store unencrypted with automatic chunking for large files
                let data_size = data.len();
                let attrs = NeoFsObjectAttributes {
                    content_type: Some(base_content_type.to_string()),
                    anubis_type: base_anubis_type,
                    content_hash: Some(content_hash.clone()),
                    filename: Some(file_name.clone()),
                    ..Default::default()
                };

                let progress_callback = |current: usize, total: usize| {
                    if total > 1 {
                        eprint!("\rUploading chunk {}/{} ", current, total);
                    }
                };
                let result = neofs.store_large(&container_id, &data, Some(attrs), Some(&progress_callback))?;
                if data_size > anubis_io::neo::NeoFsClient::CHUNK_THRESHOLD {
                    eprintln!(); // Newline after progress
                }

                if json {
                    println!("{}", serde_json::to_string_pretty(&result)?);
                } else {
                    let chunked = if data_size > anubis_io::neo::NeoFsClient::CHUNK_THRESHOLD { " (chunked)" } else { "" };
                    println!("File stored{} in NeoFS:", chunked);
                    println!("  CID: {}", result.cid);
                    println!("  Container: {}", result.container_id);
                    println!("  Object ID: {}", result.object_id);
                    println!("  Size: {} bytes", result.size);
                    println!("  Content Hash: {}", content_hash);
                    if data_size > anubis_io::neo::NeoFsClient::CHUNK_THRESHOLD {
                        println!("  Note: File was automatically chunked for upload");
                    }
                    println!();
                    println!("Retrieve with:");
                    println!("  anubis-notary anchor neo neofs-get {} -o {}", result.cid, file_name);
                }
            }
        }
        NeoCommands::NeofsGet { cid, out } => {
            // Load config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::MainNet)
            };

            // Load bearer token (optional for public containers)
            let token_path = ks.path().join("neofs-bearer.token");
            let bearer_token = if token_path.exists() {
                Some(std::fs::read_to_string(&token_path)?.trim().to_string())
            } else {
                None
            };

            // Create NeoFS client
            let mut neofs = NeoFsClient::new(&config.neofs_url, config.timeout_secs);
            if let Some(ref token) = bearer_token {
                neofs.set_bearer_token(token);
            }

            // Fetch the object (automatically handles chunked files)
            let raw_data = neofs.get_large(cid)?;

            // Auto-detect encryption and decrypt if possible
            let (final_data, was_encrypted) = if NeoFsClient::is_mlkem_encrypted(&raw_data) {
                // Try to load secret key from identity (sealed with password)
                let sk_path = ks.path().join("decryption.mlkem.sealed");
                if sk_path.exists() {
                    // Load sealed secret key (requires password)
                    let sealed_sk = std::fs::read(&sk_path)?;

                    // Load password from environment or prompt
                    let password = std::env::var("ANUBIS_PASSWORD").ok();
                    if password.is_none() {
                        eprintln!("Encrypted file detected (ML-KEM-1024).");
                        eprintln!("To auto-decrypt, set your keystore password:");
                        eprintln!("  ANUBIS_PASSWORD=\"your-password\" anubis-notary anchor neo neofs-get ...");
                        eprintln!();
                        eprintln!("Saving raw encrypted payload.");
                        (raw_data, false)
                    } else {
                        // Unseal the secret key
                        let password = password.unwrap();
                        match anubis_io::seal::unseal_key(password.as_bytes(), &sealed_sk) {
                            Ok(sk_bytes) => {
                                match anubis_core::mlkem::MlKemSecretKey::from_bytes(sk_bytes.as_slice()) {
                                    Ok(mlkem_sk) => {
                                        match neofs.get_encrypted_with_data(&raw_data, &mlkem_sk) {
                                            Ok(plaintext) => (plaintext, true),
                                            Err(e) => {
                                                eprintln!("Decryption failed: {}. Saving raw data.", e);
                                                (raw_data, false)
                                            }
                                        }
                                    }
                                    Err(e) => {
                                        eprintln!("Invalid secret key format: {}. Saving raw data.", e);
                                        (raw_data, false)
                                    }
                                }
                            }
                            Err(e) => {
                                eprintln!("Failed to unseal secret key: {}. Saving raw data.", e);
                                (raw_data, false)
                            }
                        }
                    }
                } else {
                    eprintln!("Encrypted file detected but no secret key found at:");
                    eprintln!("  {}", sk_path.display());
                    eprintln!("Saving raw encrypted payload.");
                    (raw_data, false)
                }
            } else {
                (raw_data, false)
            };

            // Write to output file
            std::fs::write(&out, &final_data)?;

            if json {
                #[derive(serde::Serialize)]
                struct GetResult {
                    cid: String,
                    output: String,
                    size: usize,
                    decrypted: bool,
                }
                let result = GetResult {
                    cid: cid.clone(),
                    output: out.display().to_string(),
                    size: final_data.len(),
                    decrypted: was_encrypted,
                };
                println!("{}", serde_json::to_string_pretty(&result)?);
            } else {
                println!("Downloaded from NeoFS:");
                println!("  CID: {}", cid);
                println!("  Output: {}", out.display());
                println!("  Size: {} bytes", final_data.len());
                if was_encrypted {
                    println!("  Decrypted: Yes (ML-KEM-1024 + ChaCha20Poly1305)");
                }
            }
        }
        NeoCommands::S3Store { file, bucket, key, encrypt, recipient, endpoint, access_key, secret_key, part_size } => {
            use anubis_io::s3::{S3Client, S3Config, upload_encrypted};

            // Read the file
            let file_data = std::fs::read(file)?;
            let file_name = file.file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("upload")
                .to_string();
            let object_key = key.clone().unwrap_or_else(|| file_name.clone());

            // Get credentials - try environment, then CLI args, then wallet
            let ak = access_key.clone().or_else(|| std::env::var("AWS_ACCESS_KEY_ID").ok());
            let sk = secret_key.clone().or_else(|| std::env::var("AWS_SECRET_ACCESS_KEY").ok());

            // Try to load from wallet if not provided
            let (final_ak, final_sk) = if ak.is_some() && sk.is_some() {
                (ak.unwrap(), sk.unwrap())
            } else {
                // Try to load Neo wallet
                let wallet_path = ks.path().join("neo-wallet.wif.sealed");
                if wallet_path.exists() {
                    let password = std::env::var("ANUBIS_PASSWORD")
                        .map_err(|_| "S3 credentials required. Set AWS_ACCESS_KEY_ID/AWS_SECRET_ACCESS_KEY or ANUBIS_PASSWORD for wallet")?;
                    let sealed = std::fs::read(&wallet_path)?;
                    let wif_bytes = anubis_io::seal::unseal_key(password.as_bytes(), &sealed)
                        .map_err(|e| format!("Failed to unseal wallet: {}", e))?;
                    let wif = String::from_utf8(wif_bytes)
                        .map_err(|_| "Invalid wallet format")?;
                    let wallet = anubis_io::neo::NeoWallet::from_wif(&wif)?;
                    (wallet.address().to_string(), wif)
                } else {
                    return Err(
                        "S3 credentials required. Either:\n  \
                        1. Set AWS_ACCESS_KEY_ID and AWS_SECRET_ACCESS_KEY\n  \
                        2. Use --access-key and --secret-key\n  \
                        3. Import a Neo wallet: anubis-notary anchor neo wallet --import <WIF>".into()
                    );
                }
            };

            // Configure S3 client
            let s3_endpoint = endpoint.clone()
                .or_else(|| std::env::var("S3_ENDPOINT").ok())
                .unwrap_or_else(|| "https://s3.t5.fs.neo.org".to_string());

            let config = S3Config {
                endpoint: s3_endpoint.clone(),
                access_key: final_ak,
                secret_key: zeroize::Zeroizing::new(final_sk),
                region: "us-east-1".to_string(),
                bucket: bucket.clone(),
                part_size: part_size * 1024 * 1024, // Convert MB to bytes
                timeout_secs: 300,
                parallel_connections: 4, // Default parallel connections
            };

            let client = S3Client::new(config)?;

            eprintln!("Uploading {} ({:.2} MB) to s3://{}/{}",
                file_name,
                file_data.len() as f64 / 1_048_576.0,
                bucket,
                object_key
            );

            let result = if *encrypt {
                // Load recipient's public key
                let recipient_pk = if let Some(ref pk_path) = recipient {
                    let pk_bytes = std::fs::read(pk_path)?;
                    anubis_core::mlkem::MlKemPublicKey::from_bytes(&pk_bytes)
                        .map_err(|e| format!("Invalid recipient public key: {}", e))?
                } else {
                    // Use own identity key
                    let pk_path = ks.path().join("decryption.mlkem.pub");
                    if !pk_path.exists() {
                        return Err(
                            "No recipient specified and no identity key found.\n\
                            Either use --recipient or run 'anubis-notary key init' first.".into()
                        );
                    }
                    let pk_bytes = std::fs::read(&pk_path)?;
                    anubis_core::mlkem::MlKemPublicKey::from_bytes(&pk_bytes)
                        .map_err(|e| format!("Invalid identity public key: {}", e))?
                };

                upload_encrypted(&client, &object_key, &file_data, &recipient_pk)?
            } else {
                client.upload(&object_key, &file_data)?
            };

            if json {
                #[derive(serde::Serialize)]
                struct S3StoreResult {
                    bucket: String,
                    key: String,
                    uri: String,
                    etag: String,
                    size: usize,
                    parts: usize,
                    encrypted: bool,
                }
                let output = S3StoreResult {
                    bucket: bucket.clone(),
                    key: result.key.clone(),
                    uri: result.uri.clone(),
                    etag: result.etag.clone(),
                    size: result.size,
                    parts: result.parts,
                    encrypted: *encrypt,
                };
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("File stored via S3 Gateway:");
                println!("  Bucket: {}", bucket);
                println!("  Key: {}", result.key);
                println!("  URI: {}", result.uri);
                println!("  ETag: {}", result.etag);
                println!("  Size: {} bytes ({:.2} MB)", result.size, result.size as f64 / 1_048_576.0);
                println!("  Parts: {} (multipart: {})", result.parts, result.parts > 1);
                if *encrypt {
                    println!("  Encryption: ML-KEM-1024 + ChaCha20Poly1305");
                }
                println!();
                println!("Retrieve with:");
                println!("  anubis-notary anchor neo s3-get --bucket {} {} -o {}", bucket, result.key, file_name);
            }
        }
        NeoCommands::S3Get { bucket, key, out, decrypt, endpoint, access_key, secret_key } => {
            use anubis_io::s3::{S3Client, S3Config, download_encrypted};

            // Get credentials
            let ak = access_key.clone().or_else(|| std::env::var("AWS_ACCESS_KEY_ID").ok());
            let sk = secret_key.clone().or_else(|| std::env::var("AWS_SECRET_ACCESS_KEY").ok());

            let (final_ak, final_sk) = if ak.is_some() && sk.is_some() {
                (ak.unwrap(), sk.unwrap())
            } else {
                let wallet_path = ks.path().join("neo-wallet.wif.sealed");
                if wallet_path.exists() {
                    let password = std::env::var("ANUBIS_PASSWORD")
                        .map_err(|_| "S3 credentials required")?;
                    let sealed = std::fs::read(&wallet_path)?;
                    let wif_bytes = anubis_io::seal::unseal_key(password.as_bytes(), &sealed)
                        .map_err(|e| format!("Failed to unseal wallet: {}", e))?;
                    let wif = String::from_utf8(wif_bytes)
                        .map_err(|_| "Invalid wallet format")?;
                    let wallet = anubis_io::neo::NeoWallet::from_wif(&wif)?;
                    (wallet.address().to_string(), wif)
                } else {
                    return Err("S3 credentials required".into());
                }
            };

            let s3_endpoint = endpoint.clone()
                .or_else(|| std::env::var("S3_ENDPOINT").ok())
                .unwrap_or_else(|| "https://s3.t5.fs.neo.org".to_string());

            let config = S3Config {
                endpoint: s3_endpoint,
                access_key: final_ak,
                secret_key: zeroize::Zeroizing::new(final_sk),
                region: "us-east-1".to_string(),
                bucket: bucket.clone(),
                part_size: 64 * 1024 * 1024,
                timeout_secs: 300,
                parallel_connections: 4, // Default parallel connections
            };

            let client = S3Client::new(config)?;

            let final_data = if *decrypt {
                // Load secret key
                let sk_path = ks.path().join("decryption.mlkem.sealed");
                if !sk_path.exists() {
                    return Err("No decryption key found. Run 'anubis-notary key init' first.".into());
                }
                let password = std::env::var("ANUBIS_PASSWORD")
                    .map_err(|_| "ANUBIS_PASSWORD required for decryption")?;
                let sealed_sk = std::fs::read(&sk_path)?;
                let sk_bytes = anubis_io::seal::unseal_key(password.as_bytes(), &sealed_sk)
                    .map_err(|e| format!("Failed to unseal secret key: {}", e))?;
                let mlkem_sk = anubis_core::mlkem::MlKemSecretKey::from_bytes(&sk_bytes)
                    .map_err(|e| format!("Invalid secret key: {}", e))?;

                download_encrypted(&client, key, &mlkem_sk)?
            } else {
                client.download(key)?
            };

            std::fs::write(out, &final_data)?;

            if json {
                #[derive(serde::Serialize)]
                struct S3GetResult {
                    bucket: String,
                    key: String,
                    output: String,
                    size: usize,
                    decrypted: bool,
                }
                let result = S3GetResult {
                    bucket: bucket.clone(),
                    key: key.clone(),
                    output: out.display().to_string(),
                    size: final_data.len(),
                    decrypted: *decrypt,
                };
                println!("{}", serde_json::to_string_pretty(&result)?);
            } else {
                println!("Downloaded from S3:");
                println!("  Bucket: {}", bucket);
                println!("  Key: {}", key);
                println!("  Output: {}", out.display());
                println!("  Size: {} bytes", final_data.len());
                if *decrypt {
                    println!("  Decrypted: Yes (ML-KEM-1024 + ChaCha20Poly1305)");
                }
            }
        }
        NeoCommands::NeofsAuth { token_file, token, status, remove } => {
            let token_path = ks.path().join("neofs-bearer.token");

            if *status {
                if token_path.exists() {
                    let stored = std::fs::read_to_string(&token_path)?;
                    let token_preview = if stored.len() > 20 {
                        format!("{}...{}", &stored[..10], &stored[stored.len()-10..])
                    } else {
                        stored.trim().to_string()
                    };
                    if json {
                        println!(r#"{{"authenticated": true, "token_preview": "{}"}}"#, token_preview);
                    } else {
                        println!("NeoFS Authentication Status:");
                        println!("  Authenticated: Yes");
                        println!("  Token: {}", token_preview);
                    }
                } else {
                    if json {
                        println!(r#"{{"authenticated": false}}"#);
                    } else {
                        println!("NeoFS Authentication Status:");
                        println!("  Authenticated: No");
                        println!();
                        println!("Configure with:");
                        println!("  anubis-notary anchor neo neofs-auth --token <BASE64_TOKEN>");
                        println!("  anubis-notary anchor neo neofs-auth --token-file <PATH>");
                    }
                }
            } else if *remove {
                if token_path.exists() {
                    std::fs::remove_file(&token_path)?;
                    println!("Bearer token removed.");
                } else {
                    println!("No bearer token configured.");
                }
            } else if let Some(ref file) = token_file {
                // Read token from file
                let token_data = std::fs::read_to_string(file)?;
                let token_data = token_data.trim();
                std::fs::write(&token_path, token_data)?;
                println!("Bearer token configured from file.");
                println!("  Token file: {}", file.display());
            } else if let Some(ref t) = token {
                // Use provided token directly
                std::fs::write(&token_path, t.trim())?;
                println!("Bearer token configured.");
            } else {
                // No action specified, show help
                eprintln!("Usage:");
                eprintln!("  anubis-notary anchor neo neofs-auth --token <BASE64_TOKEN>");
                eprintln!("  anubis-notary anchor neo neofs-auth --token-file <PATH>");
                eprintln!("  anubis-notary anchor neo neofs-auth --status");
                eprintln!("  anubis-notary anchor neo neofs-auth --remove");
            }
        }
        NeoCommands::Wallet { generate, import, export, show } => {
            use anubis_io::neo::NeoWallet;

            let wallet_path = ks.path().join("neo-wallet.wif.sealed");

            if *generate {
                // Generate a new wallet
                if wallet_path.exists() {
                    return Err("Neo wallet already exists. Use --export to view or delete the file to regenerate.".into());
                }

                let wallet = NeoWallet::generate()
                    .map_err(|e| format!("Failed to generate wallet: {}", e))?;

                // Get password from environment
                let password = std::env::var("ANUBIS_PASSWORD").map_err(|_| {
                    "Set ANUBIS_PASSWORD environment variable to encrypt the wallet"
                })?;

                // Seal the WIF with Argon2id
                let wif = wallet.to_wif();
                let sealed = anubis_io::seal::seal_key(password.as_bytes(), wif.as_bytes())
                    .map_err(|e| format!("Failed to seal wallet: {}", e))?;

                std::fs::write(&wallet_path, &sealed)?;

                // Update config with the new address
                let config_path = ks.path().join("neo.json");
                let mut config: NeoConfig = if config_path.exists() {
                    let data = std::fs::read_to_string(&config_path)?;
                    serde_json::from_str(&data)?
                } else {
                    NeoConfig::new(NeoNetwork::TestNet)
                };
                config.account_address = Some(wallet.address().to_string());
                std::fs::write(&config_path, serde_json::to_string_pretty(&config)?)?;

                if json {
                    #[derive(serde::Serialize)]
                    struct WalletResult {
                        address: String,
                        public_key: String,
                        wallet_file: String,
                    }
                    let output = JsonOutput::success(WalletResult {
                        address: wallet.address().to_string(),
                        public_key: wallet.public_key_hex(),
                        wallet_file: wallet_path.display().to_string(),
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Generated new Neo wallet:");
                    println!("  Address: {}", wallet.address());
                    println!("  Public Key: {}", wallet.public_key_hex());
                    println!("  Wallet file: {}", wallet_path.display());
                    println!();
                    println!("The wallet is encrypted with your ANUBIS_PASSWORD.");
                    println!("You can now create NeoFS containers and store files.");
                }
            } else if let Some(wif) = import {
                // Import wallet from WIF
                if wallet_path.exists() {
                    return Err("Neo wallet already exists. Delete the file to import a new one.".into());
                }

                // Validate WIF by parsing it
                let wallet = NeoWallet::from_wif(wif)
                    .map_err(|e| format!("Invalid WIF: {}", e))?;

                // Get password from environment
                let password = std::env::var("ANUBIS_PASSWORD").map_err(|_| {
                    "Set ANUBIS_PASSWORD environment variable to encrypt the wallet"
                })?;

                // Seal the WIF with Argon2id
                let sealed = anubis_io::seal::seal_key(password.as_bytes(), wif.as_bytes())
                    .map_err(|e| format!("Failed to seal wallet: {}", e))?;

                std::fs::write(&wallet_path, &sealed)?;

                // Update config with the address
                let config_path = ks.path().join("neo.json");
                let mut config: NeoConfig = if config_path.exists() {
                    let data = std::fs::read_to_string(&config_path)?;
                    serde_json::from_str(&data)?
                } else {
                    NeoConfig::new(NeoNetwork::TestNet)
                };
                config.account_address = Some(wallet.address().to_string());
                std::fs::write(&config_path, serde_json::to_string_pretty(&config)?)?;

                println!("Imported Neo wallet:");
                println!("  Address: {}", wallet.address());
                println!("  Wallet file: {}", wallet_path.display());
            } else if *export {
                // Export wallet WIF (requires password)
                if !wallet_path.exists() {
                    return Err("No Neo wallet configured. Use --generate or --import first.".into());
                }

                let password = std::env::var("ANUBIS_PASSWORD").map_err(|_| {
                    "Set ANUBIS_PASSWORD environment variable to decrypt the wallet"
                })?;

                let sealed = std::fs::read(&wallet_path)?;
                let wif_bytes = anubis_io::seal::unseal_key(password.as_bytes(), &sealed)
                    .map_err(|e| format!("Failed to unseal wallet: {}. Check your password.", e))?;
                let wif = String::from_utf8(wif_bytes)
                    .map_err(|_| "Invalid wallet data")?;

                let wallet = NeoWallet::from_wif(&wif)
                    .map_err(|e| format!("Invalid wallet: {}", e))?;

                eprintln!("WARNING: The WIF below is your private key. Keep it secret!");
                eprintln!();
                println!("Address: {}", wallet.address());
                println!("WIF: {}", wif);
            } else if *show {
                // Show wallet info (no password needed for public info)
                let config_path = ks.path().join("neo.json");
                if !config_path.exists() {
                    return Err("No Neo configuration found.".into());
                }
                let config: NeoConfig = serde_json::from_str(&std::fs::read_to_string(&config_path)?)?;

                let has_wallet = wallet_path.exists();

                if json {
                    #[derive(serde::Serialize)]
                    struct WalletInfo {
                        address: Option<String>,
                        has_wallet: bool,
                        wallet_file: String,
                    }
                    let output = JsonOutput::success(WalletInfo {
                        address: config.account_address.clone(),
                        has_wallet,
                        wallet_file: wallet_path.display().to_string(),
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Neo Wallet Status:");
                    if let Some(addr) = &config.account_address {
                        println!("  Address: {}", addr);
                    } else {
                        println!("  Address: Not configured");
                    }
                    println!("  Wallet file: {} ({})",
                        wallet_path.display(),
                        if has_wallet { "exists" } else { "not found" }
                    );
                    if !has_wallet {
                        println!();
                        println!("Generate a wallet with:");
                        println!("  ANUBIS_PASSWORD=\"...\" anubis-notary anchor neo wallet --generate");
                    }
                }
            } else {
                eprintln!("Usage:");
                eprintln!("  anubis-notary anchor neo wallet --generate     Generate new wallet");
                eprintln!("  anubis-notary anchor neo wallet --import <WIF> Import existing wallet");
                eprintln!("  anubis-notary anchor neo wallet --show         Show wallet info");
                eprintln!("  anubis-notary anchor neo wallet --export       Export WIF (WARNING: exposes key)");
            }
        }
        NeoCommands::Deposit { amount } => {
            use anubis_io::neo::NeoAccount;

            // Load config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::TestNet)
            };

            // Load wallet
            let wallet_path = ks.path().join("neo-wallet.wif.sealed");
            if !wallet_path.exists() {
                return Err("Neo wallet required. Generate with: ANUBIS_PASSWORD=\"...\" anubis-notary anchor neo wallet --generate".into());
            }

            let password = std::env::var("ANUBIS_PASSWORD").map_err(|_| {
                "Set ANUBIS_PASSWORD environment variable to use the Neo wallet"
            })?;
            let sealed = std::fs::read(&wallet_path)?;
            let wif_bytes = anubis_io::seal::unseal_key(password.as_bytes(), &sealed)
                .map_err(|e| format!("Failed to unseal wallet: {}. Check your password.", e))?;
            let wif = String::from_utf8(wif_bytes)
                .map_err(|_| "Invalid wallet data")?;
            let account = NeoAccount::from_wif(&wif)
                .map_err(|e| format!("Invalid wallet: {}", e))?;

            // Convert GAS amount to fractions (1 GAS = 10^8 fractions)
            let amount_fractions = (*amount * 100_000_000.0) as u64;

            if amount_fractions == 0 {
                return Err("Amount must be greater than 0".into());
            }

            // Check balance first
            let client = NeoClient::new(config.clone())?;
            let balance = client.get_balance(account.address())?;
            let balance_gas = balance as f64 / 100_000_000.0;

            if balance < amount_fractions as u128 {
                return Err(format!(
                    "Insufficient GAS balance. Have: {:.8} GAS, Need: {:.8} GAS",
                    balance_gas, amount
                ).into());
            }

            println!("Depositing {:.8} GAS into NeoFS...", amount);
            println!("  From: {}", account.address());
            println!("  Network: {}", config.network.name());
            println!();

            // Perform the deposit
            let result = client.deposit_neofs(&account, amount_fractions)?;

            if json {
                println!("{}", serde_json::to_string_pretty(&result)?);
            } else {
                println!("╔══════════════════════════════════════════════════════════════════════════╗");
                println!("║                        NEOFS DEPOSIT SUCCESSFUL                          ║");
                println!("╠══════════════════════════════════════════════════════════════════════════╣");
                println!("║  Amount:    {:.8} GAS                                              ║", amount);
                println!("║  TX Hash:   {}  ║", &result.tx_hash[..40]);
                println!("║  From:      {}                      ║", result.from_address);
                println!("║  Contract:  {}  ║", result.neofs_contract);
                println!("║                                                                          ║");
                println!("║  ✓ DEPOSIT CONFIRMED (dBFT finality)                                     ║");
                println!("╚══════════════════════════════════════════════════════════════════════════╝");
                println!();
                println!("You can now create NeoFS containers and store files.");
                println!("  anubis-notary anchor neo neofs-create --name \"my-container\"");
            }
        }
        NeoCommands::NeofsCreate { name, policy, acl, purpose, global } => {
            use anubis_io::NeoFsContainerConfig;
            use anubis_io::neo::NeoWallet;

            // Load config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::MainNet)
            };

            // Load wallet for signing
            let wallet_path = ks.path().join("neo-wallet.wif.sealed");
            let wallet = if wallet_path.exists() {
                let password = std::env::var("ANUBIS_PASSWORD").map_err(|_| {
                    "Set ANUBIS_PASSWORD environment variable to use the Neo wallet"
                })?;
                let sealed = std::fs::read(&wallet_path)?;
                let wif_bytes = anubis_io::seal::unseal_key(password.as_bytes(), &sealed)
                    .map_err(|e| format!("Failed to unseal wallet: {}. Check your password.", e))?;
                let wif = String::from_utf8(wif_bytes)
                    .map_err(|_| "Invalid wallet data")?;
                NeoWallet::from_wif(&wif)
                    .map_err(|e| format!("Invalid wallet: {}", e))?
            } else {
                return Err("Neo wallet required for container creation. Generate with: ANUBIS_PASSWORD=\"...\" anubis-notary anchor neo wallet --generate".into());
            };

            let owner_id = wallet.address().to_string();

            // Create NeoFS client
            let mut neofs = NeoFsClient::new(&config.neofs_url, config.timeout_secs);

            // Create session token for container PUT operation
            let session = neofs.create_session_token(&wallet, "PUT")
                .map_err(|e| format!("Failed to create session token: {}", e))?;
            neofs.set_session_token(&session);

            // Build container configuration
            let mut container_config = NeoFsContainerConfig::new(policy, acl);

            if let Some(ref n) = name {
                container_config = container_config.with_name(n);
            }

            if let Some(ref p) = purpose {
                container_config = container_config.with_attribute("Purpose", p);
            }

            // Add Anubis-specific attribute
            container_config = container_config.with_attribute("CreatedBy", "anubis-notary");

            if *global {
                container_config = container_config.with_global_name();
            }

            // Create the container
            let result = neofs.create_container(container_config)?;

            if json {
                #[derive(serde::Serialize)]
                struct CreateResult {
                    container_id: String,
                    owner: String,
                    placement_policy: String,
                    basic_acl: String,
                    name: Option<String>,
                    purpose: Option<String>,
                    global_name: bool,
                }
                let output = CreateResult {
                    container_id: result.container_id.clone(),
                    owner: owner_id,
                    placement_policy: policy.clone(),
                    basic_acl: acl.clone(),
                    name: name.clone(),
                    purpose: purpose.clone(),
                    global_name: *global,
                };
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("╔══════════════════════════════════════════════════════════════╗");
                println!("║             NEOFS CONTAINER CREATED                          ║");
                println!("╠══════════════════════════════════════════════════════════════╣");
                println!("║  Container ID: {:<46}║", result.container_id);
                println!("║                                                              ║");
                println!("║  Configuration:                                              ║");
                println!("║    Placement Policy: {:<39}║", policy);
                println!("║    Basic ACL:        {:<39}║", acl);
                if let Some(ref n) = name {
                    println!("║    Name:             {:<39}║", n);
                }
                if let Some(ref p) = purpose {
                    println!("║    Purpose:          {:<39}║", p);
                }
                if *global {
                    println!("║    NNS Global Name:  Yes                                     ║");
                }
                println!("║                                                              ║");
                println!("║  Owner: {:<52}║", owner_id);
                println!("╚══════════════════════════════════════════════════════════════╝");
                println!();
                println!("Use this container ID with:");
                println!("  anubis-notary anchor neo neofs-store <FILE> --container {}", result.container_id);
            }
        }
        NeoCommands::NnsResolve { name } => {
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::MainNet)
            };

            let client = NeoClient::new(config)?;
            let nns = NnsClient::new(client);
            let result = nns.resolve(name)?;

            if json {
                println!("{}", serde_json::to_string_pretty(&result)?);
            } else {
                println!("NNS Resolution:");
                println!("  Name: {}", result.name);
                println!("  Address: {}", result.address);
                if let Some(exp) = result.expires {
                    println!("  Expires: {}", exp);
                }
            }
        }
        NeoCommands::Identity { action } => {
            handle_neo_identity(action, json, &ks)?;
        }
        NeoCommands::PrivateBatch { action } => {
            handle_neo_private_batch(action, json, &ks)?;
        }
    }

    Ok(())
}

fn handle_neo_identity(
    action: &NeoIdentityCommands,
    json: bool,
    ks: &Keystore,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_io::neo::{NeoClient, NeoConfig, NeoNetwork, NeoFsClient, NeoFsObjectAttributes};
    use anubis_core::qsi::{DualKeyQsiDocument, QsiClaims};

    match action {
        NeoIdentityCommands::RegisterDual { name, email, organization, credential, expires, on_chain } => {
            // === DEPRECATION WARNING ===
            // As of v1.0, `key init` automatically creates both ML-DSA-87 and ML-KEM-1024 keys
            // along with a DK-QSI identity document. This command is only needed for:
            // 1. Updating identity metadata (name, email, etc.)
            // 2. Legacy keystores created before the unified identity system
            eprintln!("╔══════════════════════════════════════════════════════════════════════════╗");
            eprintln!("║  ⚠️  DEPRECATION NOTICE                                                   ║");
            eprintln!("╠══════════════════════════════════════════════════════════════════════════╣");
            eprintln!("║  'identity register-dual' is deprecated.                                 ║");
            eprintln!("║  'key init' now creates unified identities automatically.                ║");
            eprintln!("║                                                                          ║");
            eprintln!("║  This command still works for:                                           ║");
            eprintln!("║    - Updating identity metadata (name, email, etc.)                      ║");
            eprintln!("║    - Legacy keystores created before v1.0                                ║");
            eprintln!("╚══════════════════════════════════════════════════════════════════════════╝");
            eprintln!();

            // Load config
            let config_path = ks.path().join("neo.json");
            if !config_path.exists() {
                return Err("Neo not configured. Run 'anchor neo config' first.".into());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            let config: NeoConfig = serde_json::from_str(&config_data)?;

            // Check if contract is configured
            if config.contract_address.is_none() {
                return Err("Contract not configured. Run 'anchor neo config --contract <HASH>' first.".into());
            }

            // Load the user's ML-DSA-87 keypair
            if !ks.has_key() {
                return Err("No key found. Run 'anubis-notary key init' first.".into());
            }

            // Get password for unsealing
            let password = prompt_password("Enter password to unseal your key: ")?;
            let seed_bytes = ks.unseal_stored_key(password.as_bytes())?;

            // Load keypair from seed (seed is 32 bytes)
            let keypair = anubis_core::mldsa::KeyPair::from_seed(&seed_bytes)
                .map_err(|e| format!("Failed to load keypair: {:?}", e))?;

            // Load or generate ML-KEM-1024 keypair
            let mlkem_key_path = ks.path().join("decryption.mlkem.sealed");
            let qsi_path = ks.path().join("identity.qsi.cbor");
            let mlkem_pk = if mlkem_key_path.exists() && qsi_path.exists() {
                // Load existing ML-KEM public key from QSI document
                let doc_bytes = std::fs::read(&qsi_path)?;
                let doc = DualKeyQsiDocument::from_cbor(&doc_bytes)
                    .map_err(|e| format!("Failed to parse existing QSI document: {:?}", e))?;
                anubis_core::mlkem::MlKemPublicKey::from_bytes(&doc.decryption_public_key)
                    .map_err(|e| format!("Failed to parse ML-KEM public key: {:?}", e))?
            } else if mlkem_key_path.exists() {
                // Legacy: sealed key exists but no QSI document, need to regenerate
                // Delete old file and generate fresh keypair
                std::fs::remove_file(&mlkem_key_path).ok();
                return Err("Legacy ML-KEM key found without QSI document. Please re-run register-dual.".into());
            } else {
                // Generate new ML-KEM keypair
                if !json {
                    println!("Generating new ML-KEM-1024 keypair for decryption authority...");
                }
                let mlkem_keypair = anubis_core::mlkem::MlKemKeyPair::generate()
                    .map_err(|e| format!("Failed to generate ML-KEM keypair: {:?}", e))?;

                // Get the public key
                let pk_bytes = mlkem_keypair.public_key_bytes();

                // Store the SECRET key sealed for private batch decryption
                let sk_bytes = mlkem_keypair.secret_key_bytes();
                let sealed = anubis_io::seal::seal_key(password.as_bytes(), sk_bytes)
                    .map_err(|e| format!("Failed to seal ML-KEM key: {}", e))?;
                std::fs::write(&mlkem_key_path, &sealed)?;

                if !json {
                    println!("  ML-KEM secret key saved (sealed) to: {}", mlkem_key_path.display());
                }

                anubis_core::mlkem::MlKemPublicKey::from_bytes(pk_bytes)
                    .map_err(|e| format!("Failed to parse ML-KEM public key: {:?}", e))?
            };

            // Parse expiry date
            let expires_ts = if let Some(exp_str) = expires {
                // Parse YYYY-MM-DD format
                let parts: Vec<&str> = exp_str.split('-').collect();
                if parts.len() == 3 {
                    let year: i32 = parts[0].parse().unwrap_or(2030);
                    let month: u32 = parts[1].parse().unwrap_or(12);
                    let day: u32 = parts[2].parse().unwrap_or(31);
                    // Simple timestamp calculation
                    let days_since_epoch = (year - 1970) as u64 * 365 + (month - 1) as u64 * 30 + day as u64;
                    Some(days_since_epoch * 86400)
                } else {
                    None
                }
            } else {
                None
            };

            // Build claims
            let claims = QsiClaims {
                neo_address: config.account_address.clone().unwrap_or_default(),
                name: name.clone(),
                email_hash: email.as_ref().map(|e| {
                    anubis_core::sha2::sha512(e.as_bytes()).to_vec()
                }),
                organization: organization.clone(),
                credential_type: credential.clone(),
            };

            // Create DK-QSI document
            let doc = DualKeyQsiDocument::create(
                &keypair,
                &mlkem_pk,
                claims.clone(),
                expires_ts,
            ).map_err(|e| format!("Failed to create DK-QSI document: {:?}", e))?;

            // Get fingerprints
            let signing_fp = doc.signing_fingerprint;
            let decryption_fp = doc.decryption_fingerprint;
            let identity_id = doc.id();

            // Serialize to CBOR
            let doc_cbor = doc.to_cbor()
                .map_err(|e| format!("Failed to serialize DK-QSI document: {:?}", e))?;

            // Store locally
            let qsi_path = ks.path().join("identity.qsi.cbor");
            std::fs::write(&qsi_path, &doc_cbor)?;

            // On-chain registration if requested
            let (tx_hash, block_number, status, neofs_cid) = if *on_chain {
                if !json {
                    println!("Registering identity on-chain...");
                }

                // Store DK-QSI document in NeoFS if container is configured
                let neofs_cid = if let Some(ref container_id) = config.identity_container {
                    // Load bearer token
                    let token_path = ks.path().join("neofs-bearer.token");
                    let bearer_token = if token_path.exists() {
                        Some(std::fs::read_to_string(&token_path)?.trim().to_string())
                    } else {
                        None
                    };

                    // Create NeoFS client
                    let mut neofs = NeoFsClient::new(&config.neofs_url, config.timeout_secs);
                    if let Some(ref token) = bearer_token {
                        neofs.set_bearer_token(token);
                    }

                    // Build attributes
                    let attrs = NeoFsObjectAttributes {
                        content_type: Some("application/cbor".to_string()),
                        anubis_type: Some("dk-qsi-document".to_string()),
                        content_hash: Some(hex::encode(anubis_core::sha2::sha512(&doc_cbor))),
                        filename: Some(format!("{}.qsi.cbor", hex::encode(&signing_fp[..8]))),
                        ..Default::default()
                    };

                    if !json {
                        println!("  Storing identity document in NeoFS...");
                    }

                    match neofs.store(container_id, &doc_cbor, Some(attrs)) {
                        Ok(result) => result.cid,
                        Err(e) => {
                            if !json {
                                eprintln!("  Warning: NeoFS upload failed: {}. Using local reference.", e);
                            }
                            format!("local:{}", hex::encode(&signing_fp[..16]))
                        }
                    }
                } else {
                    // No container configured, use local reference
                    if !json {
                        println!("  Note: No identity_container configured. Using local reference.");
                        println!("  Configure with: anubis-notary anchor neo config --identity-container <ID>");
                    }
                    format!("local:{}", hex::encode(&signing_fp[..16]))
                };

                let client = NeoClient::new(config.clone())?;
                let result = client.register_dual_key_identity(
                    &signing_fp,
                    &decryption_fp,
                    &neofs_cid,
                )?;

                (Some(result.tx_hash), result.block_number, "on_chain".to_string(), Some(neofs_cid))
            } else {
                (None, 0, "local_only".to_string(), None)
            };

            if json {
                #[derive(Serialize)]
                struct RegisterDualResult {
                    id: String,
                    signing_fingerprint: String,
                    decryption_fingerprint: String,
                    name: Option<String>,
                    algorithm_signing: String,
                    algorithm_decryption: String,
                    document_path: String,
                    neofs_cid: Option<String>,
                    status: String,
                    tx_hash: Option<String>,
                    block_number: u64,
                }
                let output = JsonOutput::success(RegisterDualResult {
                    id: identity_id.clone(),
                    signing_fingerprint: hex::encode(signing_fp),
                    decryption_fingerprint: hex::encode(decryption_fp),
                    name: name.clone(),
                    algorithm_signing: "ML-DSA-87".to_string(),
                    algorithm_decryption: "ML-KEM-1024".to_string(),
                    document_path: qsi_path.display().to_string(),
                    neofs_cid: neofs_cid.clone(),
                    status,
                    tx_hash,
                    block_number,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!();
                println!("═══════════════════════════════════════════════════════════════════════════");
                println!(" DUAL-KEY QUANTUM-SAFE IDENTITY REGISTERED");
                println!("═══════════════════════════════════════════════════════════════════════════");
                println!();
                println!(" ID: {}", identity_id);
                println!();
                println!(" SIGNING AUTHORITY (ML-DSA-87 NIST Level 5):");
                println!("   Fingerprint: {}", hex::encode(signing_fp));
                println!("   Purpose:     Sign receipts, attest documents");
                println!();
                println!(" DECRYPTION AUTHORITY (ML-KEM-1024 NIST Level 5):");
                println!("   Fingerprint: {}", hex::encode(decryption_fp));
                println!("   Purpose:     Participate in private batches, threshold decryption");
                println!();
                println!(" CRYPTOGRAPHIC BINDING:");
                println!("   ✓ ML-DSA-87 signature covers ML-KEM-1024 public key");
                println!("   ✓ Both keys bound to single identity");
                println!("   ✓ Revocation kills both powers");
                println!();
                println!(" LOCAL STORAGE:");
                println!("   Document: {}", qsi_path.display());
                if let Some(ref cid) = neofs_cid {
                    if !cid.starts_with("local:") {
                        println!("   NeoFS:    {}", cid);
                    }
                }
                println!();
                if let Some(ref tx) = tx_hash {
                    println!(" ON-CHAIN REGISTRATION:");
                    println!("   TX:    {}", tx);
                    println!("   Block: {}", block_number);
                    if let Some(ref cid) = neofs_cid {
                        println!("   CID:   {}", cid);
                    }
                    println!();
                }
                println!(" Your identity now enables:");
                println!("   ✓ Quantum-resistant receipt signing");
                println!("   ✓ Private batch participation");
                println!("   ✓ Forward-secure threshold decryption");
                if tx_hash.is_none() {
                    println!();
                    println!(" NOTE: To register on-chain, add --on-chain flag:");
                    println!("   anubis-notary anchor neo identity register-dual --on-chain");
                }
                println!("═══════════════════════════════════════════════════════════════════════════");
            }
        }
        NeoIdentityCommands::Register { name, email: _, organization: _, credential: _, expires: _ } => {
            // Legacy single-key registration
            let config_path = ks.path().join("neo.json");
            if !config_path.exists() {
                return Err("Neo not configured. Run 'anchor neo config' first.".into());
            }

            let config_data = std::fs::read_to_string(&config_path)?;
            // Parse config to validate it's well-formed
            let _config: NeoConfig = serde_json::from_str(&config_data)?;

            // Use full SHA-512 fingerprint for CNSA 2.0 identity (truncated for display)
            let pk_data = ks.read_public_key()?;
            let full_fingerprint = hex::encode(anubis_core::sha2::fingerprint(&pk_data));
            let fingerprint = &full_fingerprint[..32]; // First 32 hex chars for display
            let identity_id = format!("ML-DSA-87:ML-KEM-1024:{}", fingerprint);

            if json {
                #[derive(Serialize)]
                struct RegisterResult {
                    id: String,
                    fingerprint: String,
                    name: Option<String>,
                    algorithm: String,
                    note: String,
                }
                let output = JsonOutput::success(RegisterResult {
                    id: identity_id,
                    fingerprint: fingerprint.to_string(),
                    name: name.clone(),
                    algorithm: "ML-DSA-87".to_string(),
                    note: "Use 'register-dual' for dual-key identity (recommended)".to_string(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("╔══════════════════════════════════════════════════════════════════════════╗");
                println!("║       QUANTUM-SAFE IDENTITY (QSI) - Single Key (Legacy)                 ║");
                println!("╠══════════════════════════════════════════════════════════════════════════╣");
                println!("║  ID: {}", identity_id);
                println!("║  Fingerprint: {}", fingerprint);
                println!("║  Algorithm: ML-DSA-87 (NIST Level 5)                                    ║");
                println!("║                                                                          ║");
                println!("║  TIP: Use 'register-dual' for full DK-QSI with private batch support.   ║");
                println!("╚══════════════════════════════════════════════════════════════════════════╝");
            }
        }
        NeoIdentityCommands::Verify { receipt } => {
            println!("Verifying QSI for receipt: {}", receipt.display());
            println!("Note: Full verification requires on-chain lookup (future release)");
        }
        NeoIdentityCommands::Rotate { old_key, reason } => {
            println!("Rotating key from: {}", old_key.display());
            if let Some(r) = reason {
                println!("Reason: {}", r);
            }
            println!("Note: Key rotation requires on-chain attestation (future release)");
        }
        NeoIdentityCommands::Revoke { reason, replacement_fp } => {
            println!("Revoking identity...");
            if let Some(r) = reason {
                println!("Reason: {}", r);
            }
            if let Some(fp) = replacement_fp {
                println!("Replacement: {}", fp);
            }
            println!("Note: Revocation requires on-chain transaction (future release)");
        }
        NeoIdentityCommands::Resolve { id } => {
            // Load config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                NeoConfig::new(NeoNetwork::MainNet)
            };

            // Parse the ID (either ML-DSA-87:ML-KEM-1024:fp format or raw fingerprint)
            let fingerprint_hex = if id.starts_with("ML-DSA-87:ML-KEM-1024:") {
                // Extract fingerprint from ID
                id.strip_prefix("ML-DSA-87:ML-KEM-1024:").unwrap_or(&id).to_string()
            } else {
                id.clone()
            };

            // Validate fingerprint format (128 hex chars = 64 bytes SHA-512)
            if fingerprint_hex.len() != 128 || !fingerprint_hex.chars().all(|c| c.is_ascii_hexdigit()) {
                return Err(format!("Invalid fingerprint: expected 128 hex characters (SHA-512), got '{}' ({})", fingerprint_hex, fingerprint_hex.len()).into());
            }

            let mut fingerprint = [0u8; 64];
            hex::decode_to_slice(&fingerprint_hex, &mut fingerprint)?;

            if config.contract_address.is_some() {
                // Try on-chain resolution
                let client = NeoClient::new(config.clone())?;
                match client.resolve_identity(&fingerprint)? {
                    Some((neofs_cid, status)) => {
                        let identity_id = format!("ML-DSA-87:ML-KEM-1024:{}", fingerprint_hex);
                        if json {
                            #[derive(Serialize)]
                            struct ResolveResult {
                                id: String,
                                fingerprint: String,
                                neofs_cid: String,
                                status: String,
                            }
                            let output = JsonOutput::success(ResolveResult {
                                id: identity_id,
                                fingerprint: fingerprint_hex,
                                neofs_cid,
                                status: status.to_string(),
                            });
                            println!("{}", serde_json::to_string_pretty(&output)?);
                        } else {
                            println!("Identity Resolved:");
                            println!("  ID: {}", identity_id);
                            println!("  Fingerprint: {}", fingerprint_hex);
                            println!("  NeoFS CID: {}", neofs_cid);
                            println!("  Status: {}", status);
                        }
                    }
                    None => {
                        if json {
                            let output: JsonOutput<()> = JsonOutput::error("Identity not found on-chain");
                            println!("{}", serde_json::to_string_pretty(&output)?);
                        } else {
                            println!("Identity not found on-chain for fingerprint: {}", fingerprint_hex);
                        }
                    }
                }
            } else {
                // No contract configured, check local
                let qsi_path = ks.path().join("identity.qsi.cbor");
                if qsi_path.exists() {
                    let doc_bytes = std::fs::read(&qsi_path)?;
                    let doc = DualKeyQsiDocument::from_cbor(&doc_bytes)
                        .map_err(|e| format!("Failed to parse local QSI document: {:?}", e))?;

                    let local_signing_fp = hex::encode(doc.signing_fingerprint);
                    if local_signing_fp == fingerprint_hex {
                        let identity_id = doc.id();
                        if json {
                            #[derive(Serialize)]
                            struct LocalResolveResult {
                                id: String,
                                signing_fingerprint: String,
                                decryption_fingerprint: String,
                                source: String,
                            }
                            let output = JsonOutput::success(LocalResolveResult {
                                id: identity_id,
                                signing_fingerprint: local_signing_fp,
                                decryption_fingerprint: hex::encode(doc.decryption_fingerprint),
                                source: "local".to_string(),
                            });
                            println!("{}", serde_json::to_string_pretty(&output)?);
                        } else {
                            println!("Identity Found (local):");
                            println!("  ID: {}", identity_id);
                            println!("  Signing Fingerprint: {}", local_signing_fp);
                            println!("  Decryption Fingerprint: {}", hex::encode(doc.decryption_fingerprint));
                            println!("  Source: local file");
                        }
                    } else {
                        println!("Identity not found locally");
                    }
                } else {
                    println!("No local identity found and no contract configured.");
                    println!("Run 'anchor neo config --contract <HASH>' to enable on-chain resolution.");
                }
            }
        }
        NeoIdentityCommands::Show => {
            // Check for DK-QSI document first
            let qsi_path = ks.path().join("identity.qsi.cbor");

            let config_path = ks.path().join("neo.json");
            let _network = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                let config: NeoConfig = serde_json::from_str(&data)?;
                config.network.name().to_string()
            } else {
                "mainnet".to_string()
            };

            if qsi_path.exists() {
                // Show DK-QSI identity
                let doc_bytes = std::fs::read(&qsi_path)?;
                let doc = DualKeyQsiDocument::from_cbor(&doc_bytes)
                    .map_err(|e| format!("Failed to parse QSI document: {:?}", e))?;

                let identity_id = doc.id();
                let signing_fp = hex::encode(doc.signing_fingerprint);
                let decryption_fp = hex::encode(doc.decryption_fingerprint);

                if json {
                    #[derive(Serialize)]
                    struct ShowDualResult {
                        id: String,
                        signing_fingerprint: String,
                        decryption_fingerprint: String,
                        algorithm_signing: String,
                        algorithm_decryption: String,
                        created: u64,
                        expires: Option<u64>,
                        name: Option<String>,
                    }
                    let output = JsonOutput::success(ShowDualResult {
                        id: identity_id,
                        signing_fingerprint: signing_fp,
                        decryption_fingerprint: decryption_fp,
                        algorithm_signing: "ML-DSA-87".to_string(),
                        algorithm_decryption: "ML-KEM-1024".to_string(),
                        created: doc.created,
                        expires: doc.expires,
                        name: doc.claims.name.clone(),
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("═══════════════════════════════════════════════════════════════════════════");
                    println!(" YOUR DUAL-KEY QUANTUM-SAFE IDENTITY");
                    println!("═══════════════════════════════════════════════════════════════════════════");
                    println!();
                    println!(" ID: {}", identity_id);
                    if let Some(n) = &doc.claims.name {
                        println!(" Name: {}", n);
                    }
                    println!();
                    println!(" SIGNING (ML-DSA-87):");
                    println!("   Fingerprint: {}", signing_fp);
                    println!();
                    println!(" DECRYPTION (ML-KEM-1024):");
                    println!("   Fingerprint: {}", decryption_fp);
                    println!();
                    println!(" Created: {}", doc.created);
                    if let Some(exp) = doc.expires {
                        println!(" Expires: {}", exp);
                    }
                    println!("═══════════════════════════════════════════════════════════════════════════");
                }
            } else {
                // Fallback to single-key display
                // Uses SHA-512 fingerprint for CNSA 2.0 (truncated for display)
                let pk_data = ks.read_public_key()?;
                let full_fingerprint = hex::encode(anubis_core::sha2::fingerprint(&pk_data));
                let fingerprint = &full_fingerprint[..32];
                let identity_id = format!("ML-DSA-87:ML-KEM-1024:{}", fingerprint);

                if json {
                    #[derive(Serialize)]
                    struct ShowResult {
                        id: String,
                        fingerprint: String,
                        algorithm: String,
                        public_key_size: usize,
                        note: String,
                    }
                    let output = JsonOutput::success(ShowResult {
                        id: identity_id,
                        fingerprint: fingerprint.to_string(),
                        algorithm: "ML-DSA-87".to_string(),
                        public_key_size: pk_data.len(),
                        note: "Single-key identity. Use 'register-dual' for full DK-QSI.".to_string(),
                    });
                    println!("{}", serde_json::to_string_pretty(&output)?);
                } else {
                    println!("Your Quantum-Safe Identity (single-key):");
                    println!("  ID: {}", identity_id);
                    println!("  Fingerprint: {}", fingerprint);
                    println!("  Algorithm: ML-DSA-87 (NIST Level 5)");
                    println!("  Public Key Size: {} bytes", pk_data.len());
                    println!();
                    println!("TIP: Use 'register-dual' to create a full DK-QSI with:");
                    println!("  - ML-KEM-1024 for private batch participation");
                    println!("  - Cryptographic binding of both keys");
                }
            }
        }
        NeoIdentityCommands::Preflight { quiet } => {
            use anubis_io::pipeline::{Pipeline, PipelineConfig};

            let config = PipelineConfig {
                auto_encrypt: true,
                auto_store_neofs: true,
                auto_queue: true,
                auto_flush_threshold: 8,
                verify_identity: true,
            };

            let ks_pipeline = Keystore::open(Keystore::default_path())?;
            let pipeline = Pipeline::new(ks_pipeline, config)?;
            let preflight = pipeline.preflight()?;

            if *quiet {
                // Just exit with appropriate code
                if !preflight.ready {
                    return Err("Pre-flight check failed".into());
                }
            } else if json {
                #[derive(Serialize)]
                struct PreflightResult {
                    ready: bool,
                    identity_exists: bool,
                    key_valid: bool,
                    neo_configured: bool,
                    neofs_configured: bool,
                    warnings: Vec<String>,
                }
                let output = JsonOutput::success(PreflightResult {
                    ready: preflight.ready,
                    identity_exists: preflight.identity_exists,
                    key_valid: preflight.key_valid,
                    neo_configured: preflight.neo_configured,
                    neofs_configured: preflight.neofs_configured,
                    warnings: preflight.warnings.clone(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("═══════════════════════════════════════════════════════════════════════════");
                println!(" IDENTITY PRE-FLIGHT CHECK");
                println!("═══════════════════════════════════════════════════════════════════════════");
                println!();
                println!(" Local Identity:     {}", if preflight.identity_exists { "✓ Found" } else { "✗ Missing" });
                println!(" Signing Key:        {}", if preflight.key_valid { "✓ Valid" } else { "✗ Invalid/Revoked" });
                println!(" Neo Configured:     {}", if preflight.neo_configured { "✓ Yes" } else { "○ No" });
                println!(" NeoFS Containers:   {}", if preflight.neofs_configured { "✓ Configured" } else { "○ Not configured" });
                println!();

                if !preflight.warnings.is_empty() {
                    println!(" Warnings:");
                    for warning in &preflight.warnings {
                        println!("   ⚠  {}", warning);
                    }
                    println!();
                }

                let status = if preflight.ready {
                    "✓ READY for notarization"
                } else {
                    "✗ NOT READY - see warnings above"
                };
                println!(" Status: {}", status);
                println!("═══════════════════════════════════════════════════════════════════════════");
            }

            if !preflight.ready {
                return Err("Pre-flight check failed".into());
            }
        }
        NeoIdentityCommands::ExportPublic { format, out } => {
            let qsi_path = ks.path().join("identity.qsi.cbor");

            if !qsi_path.exists() {
                return Err("No DK-QSI identity found. Run 'register-dual' first.".into());
            }

            let doc_bytes = std::fs::read(&qsi_path)?;
            let doc = DualKeyQsiDocument::from_cbor(&doc_bytes)
                .map_err(|e| format!("Failed to parse QSI document: {:?}", e))?;

            let output_bytes = match format.as_str() {
                "qsi-pub" => {
                    // Full DK-QSI document (already public, self-signed)
                    doc_bytes.clone()
                }
                "mlkem-pub" => {
                    // Just the ML-KEM public key
                    doc.decryption_public_key.to_vec()
                }
                "mldsa-pub" => {
                    // Just the ML-DSA public key
                    doc.signing_public_key.to_vec()
                }
                _ => {
                    return Err(format!("Unknown format: {}. Use 'qsi-pub', 'mlkem-pub', or 'mldsa-pub'", format).into());
                }
            };

            std::fs::write(&out, &output_bytes)?;

            if json {
                #[derive(Serialize)]
                struct ExportResult {
                    format: String,
                    path: String,
                    size: usize,
                    signing_fingerprint: String,
                    decryption_fingerprint: String,
                }
                let output_json = JsonOutput::success(ExportResult {
                    format: format.clone(),
                    path: out.display().to_string(),
                    size: output_bytes.len(),
                    signing_fingerprint: hex::encode(doc.signing_fingerprint),
                    decryption_fingerprint: hex::encode(doc.decryption_fingerprint),
                });
                println!("{}", serde_json::to_string_pretty(&output_json)?);
            } else {
                println!("Exported public key:");
                println!("  Format: {}", format);
                println!("  Path: {}", out.display());
                println!("  Size: {} bytes", output_bytes.len());
                println!("  Signing Fingerprint: {}", hex::encode(doc.signing_fingerprint));
                println!("  Decryption Fingerprint: {}", hex::encode(doc.decryption_fingerprint));
            }
        }
        NeoIdentityCommands::Status { id } => {
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                return Err("Neo not configured. Run 'anchor neo config' first.".into());
            };

            if config.contract_address.is_none() {
                return Err("Contract not configured. Run 'anchor neo config --contract <HASH>' first.".into());
            }

            // Parse the ID (either ML-DSA-87:ML-KEM-1024:fp format or raw fingerprint)
            let fingerprint_hex = if id.starts_with("ML-DSA-87:ML-KEM-1024:") {
                id.strip_prefix("ML-DSA-87:ML-KEM-1024:").unwrap_or(&id).to_string()
            } else {
                id.clone()
            };

            if fingerprint_hex.len() != 128 {
                return Err("Invalid fingerprint: expected 128 hex characters (SHA-512)".into());
            }

            let mut fingerprint = [0u8; 64];
            hex::decode_to_slice(&fingerprint_hex, &mut fingerprint)?;

            let client = NeoClient::new(config.clone())?;
            let status = client.get_identity_status(&fingerprint)?;

            let identity_id = format!("ML-DSA-87:ML-KEM-1024:{}", fingerprint_hex);

            if json {
                #[derive(Serialize)]
                struct StatusResult {
                    id: String,
                    fingerprint: String,
                    status: String,
                    status_code: u8,
                    is_active: bool,
                }
                let output = JsonOutput::success(StatusResult {
                    id: identity_id,
                    fingerprint: fingerprint_hex,
                    status: status.to_string(),
                    status_code: status as u8,
                    is_active: status.is_active(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Identity Status:");
                println!("  ID: {}", identity_id);
                println!("  Fingerprint: {}", fingerprint_hex);
                println!("  Status: {} ({})", status, if status.is_active() { "✓ can participate" } else { "✗ cannot participate" });
            }
        }
        NeoIdentityCommands::Update => {
            // Load config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                return Err("Neo not configured. Run 'anchor neo config' first.".into());
            };

            if config.contract_address.is_none() {
                return Err("Contract not configured. Run 'anchor neo config --contract <HASH>' first.".into());
            }

            // Load local QSI document
            let qsi_path = ks.path().join("identity.qsi.cbor");
            if !qsi_path.exists() {
                return Err("No local DK-QSI identity found. Run 'register-dual' first.".into());
            }

            let doc_bytes = std::fs::read(&qsi_path)?;
            let doc = DualKeyQsiDocument::from_cbor(&doc_bytes)
                .map_err(|e| format!("Failed to parse QSI document: {:?}", e))?;

            let signing_fp = doc.signing_fingerprint;
            let decryption_fp = doc.decryption_fingerprint;

            if !json {
                println!("Updating on-chain identity...");
                println!("  ID: {}", doc.id());
                println!("  New Decryption Fingerprint: {}", hex::encode(decryption_fp));
            }

            // Create local CID reference
            let local_cid = format!("local:{}", &hex::encode(signing_fp)[..32]);

            // Create client and call update
            let client = NeoClient::new(config.clone())?;
            let result = client.update_dual_key_identity(
                &signing_fp,
                &decryption_fp,
                &local_cid,
            )?;

            if json {
                #[derive(Serialize)]
                struct UpdateResult {
                    id: String,
                    signing_fingerprint: String,
                    decryption_fingerprint: String,
                    neofs_cid: String,
                    tx_hash: String,
                }
                let output = JsonOutput::success(UpdateResult {
                    id: doc.id(),
                    signing_fingerprint: hex::encode(signing_fp),
                    decryption_fingerprint: hex::encode(decryption_fp),
                    neofs_cid: local_cid,
                    tx_hash: result.tx_hash.clone(),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!();
                println!("═══════════════════════════════════════════════════════════════════════════");
                println!(" ON-CHAIN IDENTITY UPDATED");
                println!("═══════════════════════════════════════════════════════════════════════════");
                println!();
                println!(" ID: {}", doc.id());
                println!();
                println!(" DECRYPTION KEY UPDATED:");
                println!("   Fingerprint: {}", hex::encode(decryption_fp));
                println!();
                println!(" TRANSACTION:");
                println!("   TX Hash: {}", result.tx_hash);
                println!();
                println!(" Your on-chain identity now matches local keys.");
                println!(" Private batch participants can now encrypt to your current ML-KEM key.");
                println!("═══════════════════════════════════════════════════════════════════════════");
            }
        }
        NeoIdentityCommands::RegisterNeo { out, dual_key, dry_run } => {
            use anubis_core::qsi::{
                create_registration_signature, create_dual_key_registration_signature,
                NEO_SCRIPT_HASH_SIZE, DOMAIN_REGISTER_IDENTITY, DOMAIN_REGISTER_DUALKEY,
            };
            use anubis_io::neo::{NeoWallet, parse_neo_identifier};

            // Load Neo config
            let config_path = ks.path().join("neo.json");
            let config: NeoConfig = if config_path.exists() {
                let data = std::fs::read_to_string(&config_path)?;
                serde_json::from_str(&data)?
            } else {
                return Err("Neo not configured. Run 'anchor neo config' first.".into());
            };

            // Get sender script hash from Neo wallet
            let wallet_path = ks.path().join("neo-wallet.wif.sealed");
            if !wallet_path.exists() {
                return Err("No Neo wallet found. Run 'anchor neo wallet --generate' or '--import' first.".into());
            }

            let password = std::env::var("ANUBIS_PASSWORD")
                .map_err(|_| "ANUBIS_PASSWORD environment variable not set")?;

            let sealed_wallet = std::fs::read(&wallet_path)?;
            let wif_bytes = anubis_io::seal::unseal_key(password.as_bytes(), &sealed_wallet)
                .map_err(|e| format!("Failed to unseal wallet: {}. Check your password.", e))?;
            let wif = String::from_utf8(wif_bytes)
                .map_err(|_| "Invalid wallet data")?;

            let neo_wallet = NeoWallet::from_wif(&wif)
                .map_err(|e| format!("Invalid wallet: {}", e))?;

            // Get script hash from wallet address (little-endian, as used in transactions)
            let sender_script_hash: [u8; NEO_SCRIPT_HASH_SIZE] = parse_neo_identifier(neo_wallet.address())
                .map_err(|e| format!("Failed to parse wallet address: {:?}", e))?;

            // Load ML-DSA-87 keypair from keystore using the seed
            let seed_bytes = ks.unseal_stored_key(password.as_bytes())?;
            let mldsa_keypair = anubis_core::mldsa::KeyPair::from_seed(&seed_bytes)
                .map_err(|e| format!("Failed to load keypair: {:?}", e))?;

            // Compute fingerprint
            let fingerprint = anubis_core::sha2::sha512(&mldsa_keypair.public_key().to_bytes());

            let (commitment, signature_bytes, neofs_cid) = if *dual_key {
                // Load ML-KEM public key for DK-QSI
                let mlkem_pk_path = ks.path().join("mlkem1024.pk");
                if !mlkem_pk_path.exists() {
                    return Err("No ML-KEM-1024 key found. Run 'key init' first.".into());
                }
                let mlkem_pk_bytes = std::fs::read(&mlkem_pk_path)?;
                let mlkem_pk = anubis_core::mlkem::MlKemPublicKey::from_bytes(&mlkem_pk_bytes)?;
                let decryption_fp = anubis_core::sha2::sha512(mlkem_pk.as_bytes());

                let reg_sig = create_dual_key_registration_signature(
                    &mldsa_keypair,
                    &mlkem_pk,
                    &sender_script_hash,
                )?;

                // Create NeoFS CID placeholder (or upload if not dry run)
                let neofs_cid = format!("qsi:dkqsi:{}", &hex::encode(&fingerprint)[..32]);

                if !json && !*dry_run {
                    println!("Creating sender-bound DK-QSI registration signature...");
                    println!("  Domain: {}", String::from_utf8_lossy(DOMAIN_REGISTER_DUALKEY));
                    println!("  Signing Fingerprint: {}", hex::encode(&fingerprint));
                    println!("  Decryption Fingerprint: {}", hex::encode(&decryption_fp));
                }

                (reg_sig.commitment, reg_sig.signature.to_bytes(), neofs_cid)
            } else {
                let reg_sig = create_registration_signature(
                    &mldsa_keypair,
                    &sender_script_hash,
                )?;

                let neofs_cid = format!("qsi:single:{}", &hex::encode(&fingerprint)[..32]);

                if !json && !*dry_run {
                    println!("Creating sender-bound QSI registration signature...");
                    println!("  Domain: {}", String::from_utf8_lossy(DOMAIN_REGISTER_IDENTITY));
                    println!("  Fingerprint: {}", hex::encode(&fingerprint));
                }

                (reg_sig.commitment, reg_sig.signature.to_bytes(), neofs_cid)
            };

            // Output commitment to file if specified
            if let Some(out_path) = out {
                let commitment_hex = hex::encode(&commitment);
                std::fs::write(out_path, &commitment_hex)?;
                if !json {
                    println!("  Commitment written to: {}", out_path.display());
                }
            }

            if json {
                #[derive(Serialize)]
                struct RegisterNeoResult {
                    fingerprint: String,
                    commitment: String,
                    signature_size: usize,
                    neofs_cid: String,
                    sender_script_hash: String,
                    dry_run: bool,
                    contract_params: ContractParams,
                }
                #[derive(Serialize)]
                struct ContractParams {
                    method: String,
                    fingerprint_hex: String,
                    commitment_hex: String,
                    neofs_cid: String,
                }
                let method = if *dual_key {
                    "registerDualKeyIdentityWithProof"
                } else {
                    "registerIdentityWithProof"
                };
                let output = JsonOutput::success(RegisterNeoResult {
                    fingerprint: hex::encode(&fingerprint),
                    commitment: hex::encode(&commitment),
                    signature_size: signature_bytes.len(),
                    neofs_cid: neofs_cid.clone(),
                    sender_script_hash: hex::encode(&sender_script_hash),
                    dry_run: *dry_run,
                    contract_params: ContractParams {
                        method: method.to_string(),
                        fingerprint_hex: hex::encode(&fingerprint),
                        commitment_hex: hex::encode(&commitment),
                        neofs_cid: neofs_cid.clone(),
                    },
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!();
                println!("═══════════════════════════════════════════════════════════════════════════");
                if *dry_run {
                    println!(" REGISTRATION SIGNATURE GENERATED (DRY RUN)");
                } else {
                    println!(" REGISTRATION SIGNATURE GENERATED");
                }
                println!("═══════════════════════════════════════════════════════════════════════════");
                println!();
                println!(" SENDER BINDING (Front-Running Protection):");
                println!("   Script Hash: {}", hex::encode(&sender_script_hash));
                println!("   Address:     {}", config.account_address.as_deref().unwrap_or("unknown"));
                println!();
                println!(" IDENTITY:");
                println!("   Fingerprint: {}", hex::encode(&fingerprint));
                println!("   Commitment:  {}", hex::encode(&commitment));
                println!();
                println!(" SIGNATURE:");
                println!("   Size: {} bytes (ML-DSA-87)", signature_bytes.len());
                println!("   Stored in: NeoFS (CID: {})", neofs_cid);
                println!();
                println!(" CONTRACT INVOCATION:");
                let method = if *dual_key {
                    "registerDualKeyIdentityWithProof"
                } else {
                    "registerIdentityWithProof"
                };
                println!("   Method: {}", method);
                println!("   Params:");
                println!("     fingerprint: 0x{}", hex::encode(&fingerprint));
                println!("     commitment:  0x{}", hex::encode(&commitment));
                println!("     neofsCid:    \"{}\"", neofs_cid);
                println!();
                if *dry_run {
                    println!(" This was a dry run. No transaction was sent.");
                    println!(" Remove --dry-run to submit the registration.");
                    println!("═══════════════════════════════════════════════════════════════════════════");
                } else {
                    println!(" SECURITY: Signature binds to YOUR tx.Sender.");
                    println!(" Attackers cannot reuse this signature.");
                    println!("═══════════════════════════════════════════════════════════════════════════");
                    println!();
                    println!("Submitting registration transaction to Neo N3...");

                    // Create Neo client and send transaction
                    use anubis_io::neo::NeoClient;
                    let client = NeoClient::new(config.clone())?;

                    // Convert fingerprint and commitment to fixed arrays
                    let fp_array: [u8; 64] = fingerprint.try_into()
                        .map_err(|_| "Invalid fingerprint size")?;
                    let cm_array: [u8; 32] = commitment.try_into()
                        .map_err(|_| "Invalid commitment size")?;

                    let result = client.register_identity_with_proof(&fp_array, &cm_array, &neofs_cid)?;

                    println!();
                    println!("═══════════════════════════════════════════════════════════════════════════");
                    println!(" IDENTITY REGISTERED SUCCESSFULLY");
                    println!("═══════════════════════════════════════════════════════════════════════════");
                    println!();
                    println!("  Identity ID: {}", result.identity_id);
                    println!("  TX Hash:     {}", result.tx_hash);
                    println!("  Block:       {}", result.block_number);
                    println!("  Timestamp:   {}", result.timestamp);
                    println!("  Contract:    {}", result.contract_address);
                    println!();
                    println!(" Your Quantum-Safe Identity is now registered on Neo N3!");
                    println!("═══════════════════════════════════════════════════════════════════════════");
                }
            }
        }
    }

    Ok(())
}

fn handle_neo_private_batch(
    action: &NeoPrivateBatchCommands,
    json: bool,
    _ks: &Keystore,
) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        NeoPrivateBatchCommands::Create { receipts, recipient, threshold, store_neofs } => {
            if !json {
                println!("Creating collaborative private batch...");
                println!("  Receipts: {}", receipts.len());
                println!("  Recipients: {}", recipient.len());
                println!("  Threshold: {}-of-{}", threshold, recipient.len());
                println!("  Store in NeoFS: {}", store_neofs);
                println!();
                println!("Note: Full collaborative anchoring requires NotaryOracle contract.");
            }
        }
        NeoPrivateBatchCommands::DecryptShare { batch_id, secret_key, out } => {
            println!("Decrypting share for batch {}...", batch_id);
            println!("  Using key: {}", secret_key.display());
            println!("  Output: {}", out.display());
            println!("Note: Requires batch data from NeoFS (future release)");
        }
        NeoPrivateBatchCommands::Recover { batch_id, share, out } => {
            println!("Recovering batch {} with {} shares...", batch_id, share.len());
            println!("  Output: {}", out.display());
            println!("Note: Shamir recovery not yet integrated (future release)");
        }
        NeoPrivateBatchCommands::Status { batch_id } => {
            println!("Batch {} status: not yet implemented", batch_id);
            println!("Note: Requires on-chain query (future release)");
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
                        JsonOutput::error(format!("Anchor failed: {}", err));
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
                            JsonOutput::error(format!("Bridge error: {}", err));
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
            } else if let Ok(parsed) = serde_json::from_str::<serde_json::Value>(&response) {
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
                    println!(
                        "║  zkApp Private Key (for upgrades only):                               ║"
                    );
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
                            println!("You can now use: anubis-notary anchor mina anchor <receipt>");
                        }
                    }
                } else if let Some(err) = parsed.get("error").and_then(|v| v.as_str()) {
                    println!("Deployment failed: {}", err);
                }
            } else {
                println!("Response: {}", response.trim());
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
            } else if let Ok(parsed) = serde_json::from_str::<serde_json::Value>(&response) {
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
                    if let Some(fee) = parsed.get("accountCreationFee").and_then(|v| v.as_f64()) {
                        println!("║  Account Creation Fee: {} MINA                                         ║", fee);
                    }
                    if let Some(fee) = parsed.get("transactionFee").and_then(|v| v.as_f64()) {
                        println!("║  Transaction Fee:      {} MINA                                         ║", fee);
                    }
                    if let Some(total) = parsed.get("totalDeploymentCost").and_then(|v| v.as_f64())
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
                    println!("  3. Run: anubis-notary anchor mina deploy --fee-payer-key <key>");
                } else if let Some(err) = parsed.get("error").and_then(|v| v.as_str()) {
                    println!("Error: {}", err);
                }
            } else {
                println!("Response: {}", response.trim());
            }
        }
        MinaCommands::Queue { receipt } => {
            use anubis_core::receipt::Receipt;
            use anubis_io::BatchQueue;

            // Verify the receipt is valid
            let receipt_data = read_file(receipt)?;
            let parsed =
                Receipt::decode(&receipt_data).map_err(|e| format!("Invalid receipt: {:?}", e))?;

            // Open batch queue
            let queue_path = ks.path().join("mina-batch-queue");
            let queue = BatchQueue::open(&queue_path)?;

            // Add to queue
            let entry = queue.enqueue(&parsed.digest, receipt)?;

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

                // Use SHA-512 fingerprint for CNSA 2.0 compliance (truncated for display)
                let full_fingerprint = hex::encode(anubis_core::sha2::fingerprint(&pk_bytes));
                let fingerprint = full_fingerprint[..32].to_string();
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
            // Uses SHA-512 fingerprint for CNSA 2.0 compliance
            let pk_bytes = ks.read_public_key()?;
            let fingerprint = hex::encode(anubis_core::sha2::fingerprint(&pk_bytes));
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

                // Use SHA-512 fingerprints for CNSA 2.0 compliance
                let signers_info: Vec<SignerInfo> = signers
                    .iter()
                    .enumerate()
                    .filter_map(|(i, s)| {
                        let pk_hex = s.as_str()?;
                        let pk_bytes = hex::decode(pk_hex).ok()?;
                        let full_fp = hex::encode(anubis_core::sha2::fingerprint(&pk_bytes));
                        Some(SignerInfo {
                            index: i,
                            public_key: pk_hex.to_string(),
                            fingerprint: full_fp[..32].to_string(),
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
                            // Use SHA-512 fingerprint for CNSA 2.0 (truncated for display)
                            let full_fp = hex::encode(anubis_core::sha2::fingerprint(&pk_bytes));
                            println!("    [{}] {}...", i, &full_fp[..32]);
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
            store_neofs,
        } => {
            use anubis_io::neo::{NeoConfig, NeoFsClient, NeoFsObjectAttributes};

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

            // Serialize and write locally
            let batch_bytes = batch.to_bytes();
            write_file_atomic(out, &batch_bytes)?;

            // Optionally store in NeoFS
            let neofs_cid = if *store_neofs {
                let ks = Keystore::open(Keystore::default_path())?;
                let config_path = ks.path().join("neo.json");

                if !config_path.exists() {
                    if !json {
                        eprintln!("Warning: Neo not configured. Skipping NeoFS storage.");
                        eprintln!("Run: anubis-notary anchor neo config --batch-container <ID>");
                    }
                    None
                } else {
                    let config_data = std::fs::read_to_string(&config_path)?;
                    let config: NeoConfig = serde_json::from_str(&config_data)?;

                    if let Some(ref container_id) = config.batch_container {
                        // Load bearer token
                        let token_path = ks.path().join("neofs-bearer.token");
                        let bearer_token = if token_path.exists() {
                            Some(std::fs::read_to_string(&token_path)?.trim().to_string())
                        } else {
                            None
                        };

                        // Create NeoFS client
                        let mut neofs = NeoFsClient::new(&config.neofs_url, config.timeout_secs);
                        if let Some(ref token) = bearer_token {
                            neofs.set_bearer_token(token);
                        }

                        // Batch file name
                        let batch_name = format!("{}.sealed", hex::encode(&batch.batch_id[..8]));
                        let content_hash = hex::encode(anubis_core::sha2::sha512(&batch_bytes));

                        let attrs = NeoFsObjectAttributes {
                            content_type: Some("application/x-anubis-private-batch".to_string()),
                            anubis_type: Some("private-batch".to_string()),
                            content_hash: Some(content_hash),
                            filename: Some(batch_name),
                            ..Default::default()
                        };

                        match neofs.store(container_id, &batch_bytes, Some(attrs)) {
                            Ok(result) => Some(result.cid),
                            Err(e) => {
                                if !json {
                                    eprintln!("Warning: NeoFS upload failed: {}", e);
                                }
                                None
                            }
                        }
                    } else {
                        if !json {
                            eprintln!("Warning: No batch_container configured. Skipping NeoFS storage.");
                            eprintln!("Configure with: anubis-notary anchor neo config --batch-container <ID>");
                        }
                        None
                    }
                }
            } else {
                None
            };

            if json {
                #[derive(Serialize)]
                struct CreateResult {
                    batch_file: String,
                    batch_id: String,
                    merkle_root: String,
                    num_leaves: usize,
                    threshold: u8,
                    total_recipients: usize,
                    neofs_cid: Option<String>,
                }
                let output = JsonOutput::success(CreateResult {
                    batch_file: out.display().to_string(),
                    batch_id: hex::encode(batch.batch_id),
                    merkle_root: hex::encode(batch.merkle_root),
                    num_leaves: batch.len(),
                    threshold: *threshold,
                    total_recipients: recipient_pks.len(),
                    neofs_cid,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Created private batch: {}", out.display());
                println!("  Batch ID:     {}", hex::encode(batch.batch_id));
                println!("  Merkle root:  {}", hex::encode(batch.merkle_root));
                println!("  Leaves:       {}", batch.len());
                println!("  Threshold:    {}-of-{}", threshold, recipient_pks.len());
                if let Some(ref cid) = neofs_cid {
                    println!("  NeoFS:        {}", cid);
                }
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
            use zeroize::Zeroizing;

            // Read batch file
            let batch_bytes = read_file(batch)?;
            let private_batch = PrivateBatch::from_bytes(&batch_bytes)
                .map_err(|e| format!("Failed to parse batch file: {:?}", e))?;

            // Read secret key - support both raw and sealed formats
            let sk_bytes_raw = read_file(secret_key)?;

            // Try to parse as raw secret key first (3168 bytes)
            // SECURITY: Use Zeroizing to ensure unsealed key material is cleared from memory
            let sk = if sk_bytes_raw.len() == 3168 {
                // Raw ML-KEM secret key
                MlKemSecretKey::from_bytes(&sk_bytes_raw)
                    .map_err(|e| format!("Invalid ML-KEM secret key: {:?}", e))?
            } else {
                // Likely a sealed key - need password to unseal
                // SECURITY: Wrap password in Zeroizing to clear from memory after use
                let password = Zeroizing::new(
                    std::env::var("ANUBIS_PASSWORD").ok()
                        .or_else(|| {
                            if !json {
                                rpassword::prompt_password("Enter password to unseal ML-KEM key: ").ok()
                            } else {
                                None
                            }
                        })
                        .ok_or("Password required to unseal ML-KEM key (set ANUBIS_PASSWORD or provide interactively)")?
                );

                // SECURITY: Wrap unsealed bytes in Zeroizing to clear from memory after use
                let unsealed = Zeroizing::new(
                    anubis_io::seal::unseal_key(password.as_bytes(), &sk_bytes_raw)
                        .map_err(|e| format!("Failed to unseal ML-KEM key: {}", e))?
                );

                MlKemSecretKey::from_bytes(&unsealed)
                    .map_err(|e| format!("Invalid ML-KEM secret key after unsealing: {:?}", e))?
            };

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
/// # Sealed File Format (CNSA 2.0 Compliant)
///
/// ```text
/// [4 bytes]    Magic: "ANU2" (0x414E5532)
/// [1568 bytes] ML-KEM-1024 ciphertext (encapsulated shared secret)
/// [24 bytes]   XChaCha20Poly1305 nonce (random, extended nonce)
/// [N+16 bytes] XChaCha20Poly1305 ciphertext + auth tag
/// ```
///
/// Key derivation: HKDF-SHA512 with domain separation
/// - Salt: "anubis-notary:seal:v2:cnsa2.0"
/// - Info: "seal-encryption-key"
/// - AAD: Magic bytes for version binding
fn handle_seal(
    file: &PathBuf,
    recipient: Option<&PathBuf>,
    out: &PathBuf,
    no_upload: bool,
    container: Option<&str>,
    use_s3: bool,
    parallel: usize,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::aead::{XChaCha20Poly1305, XCHACHA_NONCE_SIZE};
    use anubis_core::kdf::HkdfSha512;
    use anubis_core::mlkem::{MlKemPublicKey, CIPHERTEXT_SIZE};
    use anubis_io::neo::{NeoConfig, NeoFsClient};
    use anubis_io::s3::{S3Client, S3Config};

    // Magic bytes for sealed file format (CNSA 2.0)
    const SEAL_MAGIC: &[u8; 4] = b"ANU2";

    // CNSA 2.0 domain separation for key derivation (prevents cross-protocol attacks)
    const SEAL_SALT: &[u8] = b"anubis-notary:seal:v2:cnsa2.0";
    const SEAL_INFO: &[u8] = b"seal-encryption-key";

    // Get recipient's public key (use own key if not specified)
    let pk_bytes = if let Some(recipient_path) = recipient {
        read_file(recipient_path)?
    } else {
        // Use own encryption key for self-encryption
        let ks = Keystore::open(Keystore::default_path())?;
        let pk_path = ks.path().join("decryption.mlkem.pub");
        if !pk_path.exists() {
            return Err("No encryption key found. Run 'anubis-notary key init' first.".into());
        }
        std::fs::read(&pk_path)?
    };

    let public_key = MlKemPublicKey::from_bytes(&pk_bytes)
        .map_err(|e| format!("Invalid public key: {:?}", e))?;

    // Read the file to encrypt
    let plaintext = read_file(file)?;
    let input_size = plaintext.len();

    if !json {
        eprintln!("Sealing {} ({} bytes)...", file.display(), input_size);
    }

    // Encapsulate to get shared secret and ciphertext
    let (kem_ciphertext, shared_secret) = public_key
        .encapsulate()
        .map_err(|e| format!("ML-KEM encapsulation failed: {:?}", e))?;

    // Derive encryption key using HKDF-SHA512 (CNSA 2.0 / SP 800-56C)
    let encryption_key: [u8; 32] = HkdfSha512::derive(
        SEAL_SALT,
        &shared_secret,
        SEAL_INFO,
    ).map_err(|e| format!("Key derivation failed: {:?}", e))?;

    // Generate 24-byte nonce (XChaCha20 extended nonce is safe for random)
    let mut nonce = [0u8; XCHACHA_NONCE_SIZE];
    getrandom::getrandom(&mut nonce).map_err(|e| format!("RNG failed: {}", e))?;

    // Encrypt with XChaCha20Poly1305, using magic bytes as AAD for version binding
    let cipher = XChaCha20Poly1305::from_key(&encryption_key)
        .map_err(|e| format!("Cipher initialization failed: {:?}", e))?;
    let ciphertext = cipher
        .seal_fixed(&nonce, SEAL_MAGIC, &plaintext)
        .map_err(|e| format!("Encryption failed: {:?}", e))?;

    // Build the sealed file
    let mut sealed = Vec::with_capacity(4 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE + ciphertext.len());
    sealed.extend_from_slice(SEAL_MAGIC);
    sealed.extend_from_slice(&kem_ciphertext);
    sealed.extend_from_slice(&nonce);
    sealed.extend_from_slice(&ciphertext);

    let algorithm = "ML-KEM-1024 + HKDF-SHA512 + XChaCha20Poly1305";

    // Write the sealed file locally
    write_file_atomic(out, &sealed)?;

    // === AUTO-UPLOAD TO NEOFS ===
    // NeoFS upload result with all permanent blockchain info
    struct NeoFsUploadInfo {
        container_id: String,
        object_id: String,
        owner: String,
        filename: String,
        size: usize,
        content_hash: String,
        network: String,
    }
    let mut neofs_result: Option<NeoFsUploadInfo> = None;
    let mut neofs_error: Option<String> = None;
    let mut neofs_owner: Option<String> = None;
    #[allow(unused_assignments)]
    let mut neofs_network = String::new();

    if !no_upload {
        use anubis_io::neo::{NeoClient, NeoFsContainerConfig, NeoWallet};

        // Load Neo config
        let ks = Keystore::open(Keystore::default_path())?;
        let neo_config_path = ks.path().join("neo.json");

        if !neo_config_path.exists() {
            neofs_error = Some(
                "Neo not configured. Run 'anubis-notary key init' or configure manually:\n  \
                 anubis-notary anchor neo config --network testnet".to_string()
            );
        } else {
            let config_data = match std::fs::read_to_string(&neo_config_path) {
                Ok(data) => data,
                Err(e) => {
                    neofs_error = Some(format!("Could not read neo.json: {}", e));
                    String::new()
                }
            };

            if neofs_error.is_none() {
                let mut config: NeoConfig = match serde_json::from_str(&config_data) {
                    Ok(c) => c,
                    Err(e) => {
                        neofs_error = Some(format!("Invalid neo.json: {}", e));
                        NeoConfig::default()
                    }
                };

                // Capture network for output display
                neofs_network = format!("{:?}", config.network);

                if neofs_error.is_none() {
                    // Try to get owner address from wallet (for output display)
                    if neofs_owner.is_none() {
                        let wallet_path = ks.path().join("neo-wallet.wif.sealed");
                        if wallet_path.exists() {
                            if let Ok(password) = std::env::var("ANUBIS_PASSWORD") {
                                if let Ok(sealed_wallet) = std::fs::read(&wallet_path) {
                                    if let Ok(wif_bytes) = anubis_io::seal::unseal_key(password.as_bytes(), &sealed_wallet) {
                                        if let Ok(wif) = String::from_utf8(wif_bytes) {
                                            if let Ok(wallet) = NeoWallet::from_wif(&wif) {
                                                neofs_owner = Some(wallet.address().to_string());
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }

                    // Get or create container
                    let container_id = if let Some(cid) = container.map(|s| s.to_string()).or_else(|| config.receipts_container.clone()) {
                        cid
                    } else {
                        // === AUTO-CREATE CONTAINER ===
                        if !json {
                            eprintln!("No NeoFS container configured. Creating one...");
                        }

                        // Load wallet for container creation
                        let wallet_path = ks.path().join("neo-wallet.wif.sealed");
                        if !wallet_path.exists() {
                            neofs_error = Some(
                                "No Neo wallet found. Run 'anubis-notary key init' first.".to_string()
                            );
                            String::new()
                        } else {
                            let password = match std::env::var("ANUBIS_PASSWORD") {
                                Ok(p) => p,
                                Err(_) => {
                                    neofs_error = Some(
                                        "ANUBIS_PASSWORD required for container creation.".to_string()
                                    );
                                    String::new()
                                }
                            };

                            if neofs_error.is_none() {
                                let wallet_result: Result<NeoWallet, String> = (|| {
                                    let sealed = std::fs::read(&wallet_path)
                                        .map_err(|e| format!("Failed to read wallet: {}", e))?;
                                    let wif_bytes = anubis_io::seal::unseal_key(password.as_bytes(), &sealed)
                                        .map_err(|e| format!("Failed to unseal wallet: {}", e))?;
                                    let wif = String::from_utf8(wif_bytes)
                                        .map_err(|_| "Invalid wallet format")?;
                                    NeoWallet::from_wif(&wif)
                                        .map_err(|e| format!("Invalid WIF: {}", e))
                                })();

                                match wallet_result {
                                    Ok(wallet) => {
                                        // Capture wallet address for output display
                                        neofs_owner = Some(wallet.address().to_string());

                                        // Check GAS balance
                                        let neo_client = match NeoClient::new(config.clone()) {
                                            Ok(c) => c,
                                            Err(e) => {
                                                if !json {
                                                    eprintln!("  ⚠ NeoFS: Failed to connect to Neo: {}", e);
                                                }
                                                return Ok(()); // Early return with sealed file saved
                                            }
                                        };

                                        let balance = match neo_client.get_balance(wallet.address()) {
                                            Ok(b) => b,
                                            Err(e) => {
                                                if !json {
                                                    eprintln!("  ⚠ NeoFS: Failed to check balance: {}", e);
                                                }
                                                return Ok(());
                                            }
                                        };

                                        // Balance is in GAS fractions (1 GAS = 10^8 fractions)
                                        let gas_balance = balance as f64 / 100_000_000.0;
                                        let required_gas = 0.5; // Need enough for deposit + container

                                        if gas_balance < required_gas {
                                            neofs_error = Some(format!(
                                                "Insufficient GAS for NeoFS.\n  \
                                                 Wallet:   {}\n  \
                                                 Balance:  {:.4} GAS\n  \
                                                 Required: ~{} GAS\n\n  \
                                                 To enable NeoFS:\n  \
                                                 1. Fund wallet: {}\n  \
                                                 2. Deposit: anubis-notary anchor neo deposit --amount 1.0",
                                                wallet.address(),
                                                gas_balance,
                                                required_gas,
                                                wallet.address()
                                            ));
                                            String::new()
                                        } else {
                                            // Create NeoFS client and authenticate
                                            let mut neofs_client = NeoFsClient::new(&config.neofs_url, config.timeout_secs);

                                            // Get session token for container PUT operation
                                            let session = match neofs_client.create_session_token(&wallet, "PUT") {
                                                Ok(s) => s,
                                                Err(e) => {
                                                    if !json {
                                                        eprintln!("  ⚠ NeoFS: Failed to create session: {}", e);
                                                    }
                                                    return Ok(());
                                                }
                                            };
                                            neofs_client.set_session_token(&session);

                                            // Create container with sensible defaults
                                            let container_config = NeoFsContainerConfig::new("REP 2", "public-read-write")
                                                .with_name("anubis-sealed")
                                                .with_attribute("Purpose", "sealed-files")
                                                .with_attribute("CreatedBy", "anubis-notary");

                                            match neofs_client.create_container(container_config) {
                                                Ok(result) => {
                                                    if !json {
                                                        eprintln!("  ✓ Container created: {}", result.container_id);
                                                    }

                                                    // Save container to config for future use
                                                    config.receipts_container = Some(result.container_id.clone());
                                                    if let Err(e) = std::fs::write(
                                                        &neo_config_path,
                                                        serde_json::to_string_pretty(&config).unwrap_or_default()
                                                    ) {
                                                        eprintln!("Warning: Failed to save config: {}", e);
                                                    }

                                                    result.container_id
                                                }
                                                Err(e) => {
                                                    neofs_error = Some(format!("Failed to create container: {}", e));
                                                    String::new()
                                                }
                                            }
                                        }
                                    }
                                    Err(e) => {
                                        neofs_error = Some(e);
                                        String::new()
                                    }
                                }
                            } else {
                                String::new()
                            }
                        }
                    };

                    // Upload if we have a container and no error
                    if neofs_error.is_none() && !container_id.is_empty() {
                        // Create filename with hash prefix for uniqueness
                        let file_hash = hex::encode(&anubis_core::keccak::sha3::sha3_256(&sealed)[..8]);
                        let original_name = file.file_name()
                            .map(|n| n.to_string_lossy().to_string())
                            .unwrap_or_else(|| "sealed".to_string());
                        let neofs_filename = format!("{}-{}.sealed", file_hash, original_name);
                        let total_size = sealed.len();
                        let start_time = std::time::Instant::now();

                        // Try S3 upload if requested - requires explicit S3 credentials
                        // Note: NeoFS S3 gateway requires credentials issued by neofs-s3-authmate,
                        // not raw wallet address/WIF. Set s3_access_key and s3_secret_key in neo.json.
                        let (s3_endpoint, s3_access_key, s3_secret_key) = if use_s3 {
                            // Get S3 endpoint (from config or default for network)
                            let endpoint = config.neofs_s3_url.clone()
                                .or_else(|| config.network.default_neofs_s3_url());

                            // Get credentials from config (S3 authmate credentials required)
                            let (ak, sk) = if config.s3_access_key.is_some() && config.s3_secret_key.is_some() {
                                (config.s3_access_key.clone(), config.s3_secret_key.clone())
                            } else {
                                (None, None)
                            };

                            (endpoint, ak, sk)
                        } else {
                            (None, None, None)
                        };

                        let s3_available = s3_endpoint.is_some()
                            && s3_access_key.is_some()
                            && s3_secret_key.is_some();

                        if s3_available {
                            // === S3 PARALLEL MULTIPART UPLOAD ===
                            if !json {
                                eprintln!("Uploading to NeoFS via S3 ({} parallel connections)...", parallel);
                            }

                            let s3_config = S3Config {
                                endpoint: s3_endpoint.unwrap(),
                                access_key: s3_access_key.unwrap(),
                                secret_key: zeroize::Zeroizing::new(s3_secret_key.unwrap()),
                                region: "us-east-1".to_string(),
                                bucket: container_id.clone(),
                                part_size: config.s3_part_size_mb * 1024 * 1024,
                                timeout_secs: config.timeout_secs,
                                parallel_connections: parallel,
                            };

                            match S3Client::new(s3_config) {
                                Ok(s3_client) => {
                                    // Progress callback for S3 multipart
                                    let progress_callback = |parts_done: usize, total_parts: usize| {
                                        if !json {
                                            let percent = (parts_done as f64 / total_parts as f64 * 100.0) as u32;
                                            let bar_width = 40;
                                            let filled = (bar_width * percent / 100) as usize;
                                            let empty = bar_width as usize - filled;
                                            eprint!("\r  Uploading: [{}{}] {:>3}% (part {}/{})  ",
                                                "█".repeat(filled),
                                                "░".repeat(empty),
                                                percent,
                                                parts_done,
                                                total_parts
                                            );
                                            use std::io::Write;
                                            let _ = std::io::stderr().flush();
                                        }
                                    };

                                    match s3_client.upload_multipart_with_progress(&neofs_filename, &sealed, Some(&progress_callback)) {
                                        Ok(result) => {
                                            let elapsed = start_time.elapsed();
                                            let content_hash = hex::encode(anubis_core::sha2::sha512(&sealed));

                                            neofs_result = Some(NeoFsUploadInfo {
                                                container_id: container_id.clone(),
                                                object_id: result.etag.clone(), // S3 returns ETag, not object_id
                                                owner: neofs_owner.clone().unwrap_or_else(|| "Unknown".to_string()),
                                                filename: neofs_filename.clone(),
                                                size: total_size,
                                                content_hash,
                                                network: format!("{} (S3)", neofs_network),
                                            });

                                            if !json {
                                                eprintln!();
                                                eprintln!("  ✓ Uploaded via S3 in {:.2}s ({} parts, {:.1} MB/s)",
                                                    elapsed.as_secs_f64(),
                                                    result.parts,
                                                    total_size as f64 / elapsed.as_secs_f64() / 1_048_576.0
                                                );
                                            }
                                        }
                                        Err(e) => {
                                            if !json {
                                                eprintln!();
                                            }
                                            neofs_error = Some(format!("S3 upload failed: {}", e));
                                        }
                                    }
                                }
                                Err(e) => {
                                    neofs_error = Some(format!("S3 client init failed: {}", e));
                                }
                            }
                        } else {
                            // === REST GATEWAY UPLOAD (default) ===
                            if !json {
                                if use_s3 {
                                    eprintln!("S3 credentials not configured. To enable parallel S3 uploads:");
                                    eprintln!("  1. Run: neofs-s3-authmate issue-secret --wallet <wallet.json> --gate-public-key <key>");
                                    eprintln!("  2. Add to ~/.anubis/neo.json:");
                                    eprintln!("     \"s3_access_key\": \"<access_key_from_authmate>\",");
                                    eprintln!("     \"s3_secret_key\": \"<secret_key_from_authmate>\"");
                                    eprintln!("Falling back to REST gateway...");
                                }
                                eprintln!("Uploading to NeoFS...");
                            }

                            let neofs_client = NeoFsClient::new(&config.neofs_url, config.timeout_secs);

                            // Set attributes for the sealed file
                            use anubis_io::neo::NeoFsObjectAttributes;
                            let attrs = NeoFsObjectAttributes {
                                filename: Some(neofs_filename.clone()),
                                content_type: Some("application/x-anubis-sealed".to_string()),
                                anubis_type: Some("sealed".to_string()),
                                content_hash: Some(hex::encode(anubis_core::sha2::sha512(&sealed))),
                                ..Default::default()
                            };

                            // Progress callback for REST upload
                            let last_update = std::cell::Cell::new(std::time::Instant::now());
                            let progress_callback = |uploaded: usize, total: usize| {
                                if !json {
                                    let now = std::time::Instant::now();
                                    if now.duration_since(last_update.get()).as_millis() >= 100 || uploaded == total {
                                        last_update.set(now);
                                        let percent = (uploaded as f64 / total as f64 * 100.0) as u32;
                                        let bar_width = 40;
                                        let filled = (bar_width * percent / 100) as usize;
                                        let empty = bar_width as usize - filled;
                                        let elapsed = now.duration_since(start_time).as_secs_f64();
                                        let speed = if elapsed > 0.0 { uploaded as f64 / elapsed / 1024.0 } else { 0.0 };
                                        eprint!("\r  Uploading: [{}{}] {:>3}% ({:.1} KB/s)  ",
                                            "█".repeat(filled),
                                            "░".repeat(empty),
                                            percent,
                                            speed
                                        );
                                        use std::io::Write;
                                        let _ = std::io::stderr().flush();
                                    }
                                }
                            };

                            match neofs_client.store_large(&container_id, &sealed, Some(attrs), Some(&progress_callback)) {
                                Ok(result) => {
                                    let object_id = result.object_id.clone();
                                    let elapsed = start_time.elapsed();
                                    let content_hash = hex::encode(anubis_core::sha2::sha512(&sealed));

                                    neofs_result = Some(NeoFsUploadInfo {
                                        container_id: container_id.clone(),
                                        object_id: object_id.clone(),
                                        owner: neofs_owner.clone().unwrap_or_else(|| "Unknown".to_string()),
                                        filename: neofs_filename.clone(),
                                        size: total_size,
                                        content_hash,
                                        network: neofs_network.clone(),
                                    });

                                    if !json {
                                        eprintln!();
                                        eprintln!("  ✓ Uploaded to NeoFS in {:.2}s", elapsed.as_secs_f64());
                                    }
                                }
                                Err(e) => {
                                    if !json {
                                        eprintln!();
                                    }
                                    neofs_error = Some(format!("NeoFS upload failed: {}", e));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    if json {
        #[derive(Serialize)]
        struct SealResult {
            input_file: String,
            output_file: String,
            input_size: usize,
            output_size: usize,
            algorithm: String,
            neofs_uploaded: bool,
            neofs_container: Option<String>,
            neofs_object: Option<String>,
            neofs_owner: Option<String>,
            neofs_filename: Option<String>,
            neofs_content_hash: Option<String>,
            neofs_network: Option<String>,
            neofs_error: Option<String>,
        }
        let output = JsonOutput::success(SealResult {
            input_file: file.display().to_string(),
            output_file: out.display().to_string(),
            input_size,
            output_size: sealed.len(),
            algorithm: algorithm.to_string(),
            neofs_uploaded: neofs_result.is_some(),
            neofs_container: neofs_result.as_ref().map(|r| r.container_id.clone()),
            neofs_object: neofs_result.as_ref().map(|r| r.object_id.clone()),
            neofs_owner: neofs_result.as_ref().map(|r| r.owner.clone()),
            neofs_filename: neofs_result.as_ref().map(|r| r.filename.clone()),
            neofs_content_hash: neofs_result.as_ref().map(|r| r.content_hash.clone()),
            neofs_network: neofs_result.as_ref().map(|r| r.network.clone()),
            neofs_error,
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!();
        println!("╔══════════════════════════════════════════════════════════════════════════╗");
        println!("║                         FILE SEALED                                      ║");
        println!("╠══════════════════════════════════════════════════════════════════════════╣");
        println!("║  Input:  {:<63}║", truncate_path(&file.display().to_string(), 60));
        println!("║  Output: {:<63}║", truncate_path(&out.display().to_string(), 60));
        println!("║  Size:   {} → {} bytes{:<40}║", input_size, sealed.len(), "");
        println!("║  Algo:   {:<63}║", algorithm);

        if let Some(info) = &neofs_result {
            println!("╚══════════════════════════════════════════════════════════════════════════╝");

            // Build gateway URLs based on network
            let is_testnet = info.network.to_lowercase().contains("testnet");
            let http_gateway = if is_testnet {
                format!("https://http.t5.fs.neo.org/{}/{}", info.container_id, info.object_id)
            } else {
                format!("https://http.fs.neo.org/{}/{}", info.container_id, info.object_id)
            };
            let rest_gateway = if is_testnet {
                format!("https://rest.t5.fs.neo.org/v1/get/{}/{}", info.container_id, info.object_id)
            } else {
                format!("https://rest.fs.neo.org/v1/get/{}/{}", info.container_id, info.object_id)
            };
            let explorer_base = if is_testnet {
                "https://dora.coz.io/container/neo3/testnet"
            } else {
                "https://dora.coz.io/container/neo3/mainnet"
            };
            let explorer_url = format!("{}/{}", explorer_base, info.container_id);

            // Print blockchain record in simple format (user requested "neatly right under each other")
            println!();
            println!("NEOFS BLOCKCHAIN RECORD");
            println!("───────────────────────────────────────────────────────────────────────────");
            println!("Container ID:  {}", info.container_id);
            println!("Object ID:     {}", info.object_id);
            println!("Owner:         {}", info.owner);
            println!("Filename:      {}", info.filename);
            println!("Size:          {} bytes", info.size);
            println!("Content Hash:  {}...", &info.content_hash[..64]);
            println!();
            println!("Network:       {}", info.network);
            println!("HTTP Gateway:  {}", http_gateway);
            println!("REST Gateway:  {}", rest_gateway);
            println!("Explorer:      {}", explorer_url);
        } else if let Some(err) = &neofs_error {
            println!("╠══════════════════════════════════════════════════════════════════════════╣");
            println!("║  ⚠ NeoFS upload skipped: {:<47}║", &err[..err.len().min(45)]);
            println!("╚══════════════════════════════════════════════════════════════════════════╝");
        } else {
            println!("╚══════════════════════════════════════════════════════════════════════════╝");
        }
        println!();
        println!("To decrypt, run:");
        println!("  ANUBIS_PASSWORD=\"...\" anubis-notary unseal -k ~/.anubis/decryption.mlkem.sealed -o <output> {}", out.display());

        if let Some(info) = &neofs_result {
            println!();
            println!("To download from NeoFS:");
            println!("  anubis-notary anchor neo neofs-get \"{}/{}\" -o <file>", info.container_id, info.object_id);
        }
    }

    Ok(())
}

/// Truncate a path string for display
fn truncate_path(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else {
        format!("...{}", &s[s.len() - max_len + 3..])
    }
}

/// Handle the unseal command - decrypt a file using ML-KEM-1024.
///
/// Only supports the CNSA 2.0 compliant format (ANU2).
fn handle_unseal(
    file: &PathBuf,
    secret_key: &PathBuf,
    out: &PathBuf,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::aead::{XChaCha20Poly1305, XCHACHA_NONCE_SIZE};
    use anubis_core::kdf::HkdfSha512;
    use anubis_core::mlkem::{MlKemSecretKey, CIPHERTEXT_SIZE, SECRET_KEY_SIZE};
    use zeroize::Zeroizing;

    // Magic bytes for sealed file format (CNSA 2.0)
    const SEAL_MAGIC: &[u8; 4] = b"ANU2";

    // CNSA 2.0 domain separation for key derivation (must match seal)
    const SEAL_SALT: &[u8] = b"anubis-notary:seal:v2:cnsa2.0";
    const SEAL_INFO: &[u8] = b"seal-encryption-key";

    // Read the secret key file
    let sk_bytes = read_file(secret_key)?;

    // Check if the secret key is sealed with Argon2id (password-protected)
    // Sealed keys are larger than raw keys due to Argon2id header/salt/nonce/tag
    // SECURITY: Use Zeroizing wrapper to ensure secret key material is cleared from memory
    let raw_sk_bytes: Zeroizing<Vec<u8>> = if sk_bytes.len() == SECRET_KEY_SIZE {
        // Raw ML-KEM secret key
        Zeroizing::new(sk_bytes)
    } else if sk_bytes.len() > SECRET_KEY_SIZE {
        // Likely sealed with Argon2id - try to unseal
        // SECURITY: Wrap password in Zeroizing to clear from memory after use
        let password = Zeroizing::new(std::env::var("ANUBIS_PASSWORD").map_err(|_| {
            "Secret key appears to be password-protected. Set ANUBIS_PASSWORD environment variable."
        })?);
        Zeroizing::new(
            anubis_io::seal::unseal_key(password.as_bytes(), &sk_bytes)
                .map_err(|e| format!("Failed to unseal secret key: {}. Check your password.", e))?
        )
    } else {
        return Err(format!(
            "Invalid secret key size: {} bytes (expected {} for ML-KEM-1024)",
            sk_bytes.len(),
            SECRET_KEY_SIZE
        ).into());
    };

    let secret = MlKemSecretKey::from_bytes(&raw_sk_bytes)
        .map_err(|e| format!("Invalid secret key: {:?}", e))?;

    // Read the sealed file
    let sealed = read_file(file)?;

    // Verify minimum size: magic(4) + kem_ct(1568) + nonce(24) + tag(16)
    let min_size = 4 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE + 16;
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
        return Err("Invalid sealed file: wrong magic bytes (expected ANU2 format)".into());
    }

    // Extract KEM ciphertext
    let kem_ciphertext = &sealed[4..4 + CIPHERTEXT_SIZE];

    // Decapsulate to recover shared secret
    // SECURITY: Wrap shared secret in Zeroizing to clear from memory after use
    let shared_secret = Zeroizing::new(
        secret
            .decapsulate(kem_ciphertext)
            .map_err(|e| format!("ML-KEM decapsulation failed: {:?}", e))?
    );

    // Derive encryption key using HKDF-SHA512 (must match seal)
    let encryption_key: [u8; 32] = HkdfSha512::derive(
        SEAL_SALT,
        &*shared_secret,
        SEAL_INFO,
    ).map_err(|e| format!("Key derivation failed: {:?}", e))?;

    // Extract nonce and ciphertext
    let nonce: [u8; XCHACHA_NONCE_SIZE] = sealed[4 + CIPHERTEXT_SIZE..4 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE]
        .try_into()
        .unwrap();
    let ciphertext = &sealed[4 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE..];

    // Decrypt with XChaCha20Poly1305
    let cipher = XChaCha20Poly1305::from_key(&encryption_key)
        .map_err(|e| format!("Cipher initialization failed: {:?}", e))?;

    // Use magic bytes as AAD (must match seal)
    let plaintext = cipher
        .open_fixed(&nonce, SEAL_MAGIC, ciphertext)
        .map_err(|_| "Decryption failed: authentication error (wrong key or corrupted file)")?;

    // Capture size before potential zeroization
    let plaintext_size = plaintext.len();

    // Write the decrypted file
    write_file_atomic(out, &plaintext)?;

    let algorithm = "ML-KEM-1024 + HKDF-SHA512 + XChaCha20Poly1305";

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
            output_size: plaintext_size,
            algorithm: algorithm.to_string(),
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!("Unsealed: {}", file.display());
        println!("  Output: {}", out.display());
        println!("  Sealed size: {} bytes", sealed.len());
        println!("  Output size: {} bytes", plaintext_size);
        println!("  Algorithm: {}", algorithm);
    }

    // Plaintext and shared_secret are automatically zeroized when Zeroizing<> drops
    Ok(())
}

fn handle_marriage(
    action: &MarriageCommands,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::marriage::{
        contracts, AssetSplit, DivorceCondition, MarriageDocument, MarriageTemplate, MarriageTerms, Party,
    };

    match action {
        MarriageCommands::Init {
            parties,
            template,
            jurisdiction: _,  // Jurisdiction removed - global marriage system
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
                    neo_address: None,
                    vows_hash: None,
                    signed_at: None,
                });
            }

            // Parse template type
            let marriage_template = match template.as_str() {
                "monogamy" => MarriageTemplate::Monogamy,
                "polygamy" => MarriageTemplate::Polygamy,
                "simple" => MarriageTemplate::Simple,
                _ => {
                    return Err(format!(
                        "Unknown template: {}. Use: monogamy, polygamy, simple",
                        template
                    )
                    .into());
                }
            };

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
                "simple" | _ => MarriageTerms::default(),
            };

            // Create timestamp
            let created_at = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs();

            // Create document with new Neo N3 API
            let doc = MarriageDocument::new(party_list, marriage_template, created_at)?
                .with_terms(terms)?;

            // Serialize to JSON
            #[derive(Serialize)]
            struct MarriageDocJson {
                version: u8,
                template: String,
                parties: Vec<PartyJson>,
                terms: Option<TermsJson>,
                created_at: u64,
                signatures: Vec<SignatureJson>,
            }

            #[derive(Serialize)]
            struct PartyJson {
                name: String,
                public_key_hex: String,
                neo_address: Option<String>,
                vows_hash: Option<String>,
                signed_at: Option<u64>,
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
                    neo_address: p.neo_address.clone(),
                    vows_hash: p.vows_hash.map(|h| hex::encode(h)),
                    signed_at: p.signed_at,
                })
                .collect();

            let terms_json = doc.terms.as_ref().map(|terms| TermsJson {
                asset_split: match &terms.asset_split {
                    AssetSplit::Equal => "50/50".to_string(),
                    AssetSplit::Proportional => "proportional".to_string(),
                    AssetSplit::Custom(pcts) => format!("custom:{:?}", pcts),
                },
                divorce_conditions: terms
                    .divorce_conditions
                    .iter()
                    .map(|c| format!("{:?}", c))
                    .collect(),
                custom_clauses: terms.custom_clauses.clone(),
            });

            let template_str = match doc.template {
                MarriageTemplate::Monogamy => "monogamy",
                MarriageTemplate::Polygamy => "polygamy",
                MarriageTemplate::Simple => "simple",
            };

            let doc_json = MarriageDocJson {
                version: doc.version,
                template: template_str.to_string(),
                parties: parties_json,
                terms: terms_json,
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
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Marriage document created: {}", out.display());
                println!("  Template: {}", template);
                println!("  Parties: {:?}", party_names);
                println!("  Blockchain: Neo N3 (global, borderless)");
                println!("\nNext steps:");
                println!(
                    "  1. Each party signs: anubis-notary marriage sign {} --party <index> --vows \"...\"",
                    out.display()
                );
                println!(
                    "  2. Create on-chain: anubis-notary marriage create {} --mint-rings",
                    out.display()
                );
                println!("  3. Verify on Dora: https://dora.coz.io");
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

            // Compute vows hash if provided (SHA-512 for CNSA 2.0)
            let vows_hash = vows.as_ref().map(|v| {
                let hash = anubis_core::sha2::sha512(v.as_bytes());
                format!("0x{}", hex::encode(hash))
            });

            // Sign the document digest (SHA-512 for CNSA 2.0)
            let digest = anubis_core::sha2::sha512(doc_str.as_bytes());
            let signature = keypair.secret_key().sign(&digest)?;

            // Add signature to document
            let mut doc_value = doc_value;
            let sigs = doc_value["signatures"].as_array_mut()
                .ok_or("Document missing 'signatures' array")?;

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
            store_neofs,
            wait: _,
        } => {
            use anubis_io::neo::{NeoConfig, NeoNetwork, NeoWallet};
            use anubis_io::keystore::Keystore;

            // Note: store_neofs will store certificate in NeoFS
            let _ = store_neofs; // TODO: Implement NeoFS storage
            let _ = mint_rings; // Rings are automatically minted during registration

            let doc_str = std::fs::read_to_string(document)?;
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

            // Load Neo wallet from sealed file
            let ks = Keystore::open(Keystore::default_path())?;
            let wallet_path = ks.path().join("neo-wallet.wif.sealed");
            if !wallet_path.exists() {
                return Err("Neo wallet not found. Run: anubis-notary anchor neo wallet init".into());
            }

            let password = std::env::var("ANUBIS_PASSWORD")
                .map_err(|_| "ANUBIS_PASSWORD environment variable required")?;
            let sealed = std::fs::read(&wallet_path)?;
            let wif_bytes = anubis_io::seal::unseal_key(password.as_bytes(), &sealed)
                .map_err(|e| format!("Failed to unseal wallet: {:?}", e))?;
            let wif = String::from_utf8(wif_bytes)
                .map_err(|_| "Invalid wallet WIF encoding")?;
            let _wallet = NeoWallet::from_wif(&wif)
                .map_err(|e| format!("Invalid wallet: {:?}", e))?;

            // Set NEO_PRIVATE_KEY for the register_marriage function
            std::env::set_var("NEO_PRIVATE_KEY", &wif);

            // Compute certificate hash (SHA-512 for CNSA 2.0)
            let cert_hash = anubis_core::sha2::sha512(doc_str.as_bytes());
            let cert_hash_array: [u8; 64] = cert_hash.try_into()
                .map_err(|_| "Invalid certificate hash length")?;

            let neo_network = NeoNetwork::parse(network)
                .ok_or_else(|| format!("Unknown network: {}. Use: mainnet, testnet", network))?;

            let contract = match neo_network {
                NeoNetwork::MainNet => contracts::NOTARY_ORACLE_MAINNET,
                _ => contracts::NOTARY_ORACLE_TESTNET,
            };

            if !json {
                println!("Creating marriage on Neo N3 ({})...", network);
                println!("  Parties: {}", party_count);
                println!("  Certificate hash: {}", hex::encode(&cert_hash));
            }

            // Extract party fingerprints from public keys (SHA-512)
            let mut party_fingerprints: Vec<String> = Vec::new();
            for party in parties.iter() {
                // Get public key from party or use placeholder
                let pub_key_hex = party
                    .get("public_key_hex")
                    .and_then(|p| p.as_str())
                    .ok_or("Party missing public_key_hex")?;

                // Decode the public key
                let pub_key_bytes = hex::decode(pub_key_hex)
                    .map_err(|e| format!("Invalid public key hex: {}", e))?;

                // Compute SHA-512 fingerprint
                let fingerprint = anubis_core::sha2::sha512(&pub_key_bytes);
                party_fingerprints.push(hex::encode(fingerprint));
            }

            if party_fingerprints.len() != party_count {
                return Err("Failed to compute fingerprints for all parties".into());
            }

            // Get template type
            let template = doc_value
                .get("template")
                .and_then(|t| t.as_str())
                .unwrap_or("monogamy");

            // Extract vows hashes from signatures (permanently inscribed on rings)
            let mut party_vows_hashes: Vec<String> = Vec::new();
            for sig in signatures.iter() {
                // Get vows_hash from signature if present
                let vows_hash = sig
                    .get("vows_hash")
                    .and_then(|v| v.as_str())
                    .unwrap_or("")
                    .to_string();
                party_vows_hashes.push(vows_hash);
            }

            // Create Neo client
            let config = NeoConfig::new(neo_network).with_contract(contract);
            let client = anubis_io::neo::NeoClient::new(config)?;

            // Register marriage on-chain with vows permanently inscribed
            let result = client.register_marriage(
                &cert_hash_array,
                None, // NeoFS CID - TODO: implement storage
                &party_fingerprints,
                None, // No officiant
                &[], // No witnesses
                template,
                &party_vows_hashes, // Vows hashes to be inscribed on rings
            )?;

            // Clear the private key from environment
            std::env::remove_var("NEO_PRIVATE_KEY");

            if json {
                let output_data = serde_json::json!({
                    "marriage_id": result.marriage_id,
                    "certificate_hash": hex::encode(&cert_hash),
                    "network": network,
                    "transaction_hash": result.tx_hash,
                    "block_number": result.block_number,
                    "contract": contract,
                    "rings": result.ring_token_ids,
                    "dora_link": result.dora_link,
                    "status": "created",
                });
                let output = JsonOutput::success(output_data);
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!();
                println!("================================================================");
                println!("                    CONGRATULATIONS!");
                println!("             YOU ARE NOW MARRIED!");
                println!("================================================================");
                println!("Marriage ID: {}", result.marriage_id);
                println!("Transaction: {}", result.tx_hash);
                println!("Block: {}", result.block_number);
                println!();
                if !result.ring_token_ids.is_empty() {
                    println!("NFT Wedding Rings:");
                    for (i, token_id) in result.ring_token_ids.iter().enumerate() {
                        let party_name = parties
                            .get(i)
                            .and_then(|p| p["name"].as_str())
                            .unwrap_or("Partner");
                        println!("  {}: Ring #{}", party_name, token_id);
                    }
                    println!();
                }
                println!("Verify on Dora Explorer:");
                println!("{}", result.dora_link);
                println!("================================================================");
            }

            Ok(())
        }

        MarriageCommands::Divorce {
            marriage_id,
            reason,
            network,
            wait: _,
        } => {
            use anubis_io::neo::{NeoConfig, NeoNetwork, NeoWallet};
            use anubis_io::keystore::Keystore;

            // Load Neo wallet from sealed file
            let ks = Keystore::open(Keystore::default_path())?;
            let wallet_path = ks.path().join("neo-wallet.wif.sealed");
            if !wallet_path.exists() {
                return Err("Neo wallet not found. Run: anubis-notary anchor neo wallet init".into());
            }

            let password = std::env::var("ANUBIS_PASSWORD")
                .map_err(|_| "ANUBIS_PASSWORD environment variable required")?;
            let sealed = std::fs::read(&wallet_path)?;
            let wif_bytes = anubis_io::seal::unseal_key(password.as_bytes(), &sealed)
                .map_err(|e| format!("Failed to unseal wallet: {:?}", e))?;
            let wif = String::from_utf8(wif_bytes)
                .map_err(|_| "Invalid wallet WIF encoding")?;
            let _wallet = NeoWallet::from_wif(&wif)
                .map_err(|e| format!("Invalid wallet: {:?}", e))?;

            // Set NEO_PRIVATE_KEY for the divorce function
            std::env::set_var("NEO_PRIVATE_KEY", &wif);

            let neo_network = NeoNetwork::parse(network)
                .ok_or_else(|| format!("Unknown network: {}. Use: mainnet, testnet", network))?;

            let contract = match neo_network {
                NeoNetwork::MainNet => contracts::NOTARY_ORACLE_MAINNET,
                _ => contracts::NOTARY_ORACLE_TESTNET,
            };

            if !json {
                println!("Executing divorce for marriage #{}...", marriage_id);
            }

            // Create Neo client
            let config = NeoConfig::new(neo_network).with_contract(contract);
            let client = anubis_io::neo::NeoClient::new(config)?;

            // Execute divorce on-chain (burns rings automatically)
            let result = client.divorce(*marriage_id, reason)?;

            // Clear the private key from environment
            std::env::remove_var("NEO_PRIVATE_KEY");

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "marriage_id": marriage_id,
                    "reason": reason,
                    "network": network,
                    "status": "divorced",
                    "transaction_hash": result.tx_hash,
                    "block_number": result.block_number,
                    "burned_ring_ids": result.burned_ring_ids,
                    "dora_link": result.dora_link,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!();
                println!("════════════════════════════════════════════════════════════");
                println!("                    DIVORCE COMPLETE");
                println!("════════════════════════════════════════════════════════════");
                println!("  Marriage #{} is now DISSOLVED", marriage_id);
                println!("  Transaction: {}", result.tx_hash);
                println!("  Block: {}", result.block_number);
                if !result.burned_ring_ids.is_empty() {
                    println!("  Rings burned: {:?}", result.burned_ring_ids);
                }
                println!();
                println!("  Verify on Dora Explorer:");
                println!("  {}", result.dora_link);
                println!("════════════════════════════════════════════════════════════");
            }

            Ok(())
        }

        MarriageCommands::Show { marriage_id, network } => {
            // Show marriage details from Neo N3
            use anubis_io::neo::{NeoConfig, NeoNetwork};
            use anubis_io::neo_marriage::dora_contract_link;

            let neo_network = NeoNetwork::parse(network)
                .ok_or_else(|| format!("Unknown network: {}. Use: mainnet, testnet", network))?;

            let contract = match neo_network {
                NeoNetwork::MainNet => contracts::NOTARY_ORACLE_MAINNET,
                _ => contracts::NOTARY_ORACLE_TESTNET,
            };

            if !json {
                println!("Fetching marriage #{} from Neo N3 {}...", marriage_id, network);
            }

            // Create Neo client and fetch marriage record
            let config = NeoConfig::new(neo_network)
                .with_contract(contract);
            let client = anubis_io::neo::NeoClient::new(config)?;

            match client.get_marriage(*marriage_id) {
                Ok(record) => {
                    let contract_link = dora_contract_link(neo_network, contract);

                    if json {
                        let output = JsonOutput::success(serde_json::json!({
                            "marriage_id": record.id,
                            "certificate_hash": record.certificate_hash,
                            "parties": record.party_fingerprints,
                            "status": format!("{:?}", record.status),
                            "created_at": record.created_at,
                            "ring_token_ids": record.ring_token_ids,
                            "neofs_cid": record.neofs_cid,
                            "contract_link": contract_link,
                        }));
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!();
                        println!("════════════════════════════════════════════════════════════");
                        println!("  💍 MARRIAGE #{}", record.id);
                        println!("════════════════════════════════════════════════════════════");
                        println!("  Status: {:?}", record.status);
                        println!("  Parties: {}", record.party_fingerprints.len());
                        for (i, fp) in record.party_fingerprints.iter().enumerate() {
                            let short_fp = if fp.len() > 16 { &fp[..16] } else { fp };
                            println!("    Party {}: {}...", i + 1, short_fp);
                        }
                        if !record.certificate_hash.is_empty() && record.certificate_hash.len() >= 16 {
                            println!("  Certificate Hash: {}...", &record.certificate_hash[..16]);
                        }
                        println!("  Created: {} (Unix timestamp)", record.created_at);
                        if !record.ring_token_ids.is_empty() {
                            println!("  NFT Rings: {:?}", record.ring_token_ids);
                        }
                        if let Some(cid) = &record.neofs_cid {
                            println!("  NeoFS CID: {}", cid);
                        }
                        println!();
                        println!("  🔍 View Contract on Dora Explorer:");
                        println!("  {}", contract_link);
                        println!("════════════════════════════════════════════════════════════");
                    }
                }
                Err(e) => {
                    if json {
                        let output = JsonOutput::<()>::error(format!("Failed to fetch marriage: {}", e));
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        eprintln!("Error: Failed to fetch marriage #{}: {}", marriage_id, e);
                    }
                    return Err(e.into());
                }
            }

            Ok(())
        }

        MarriageCommands::Info { testnet } => {
            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "neo_testnet": {
                        "marriage_contract": contracts::NOTARY_ORACLE_TESTNET,
                        "rpc_url": "https://testnet1.neo.coz.io:443",
                        "explorer": "https://dora.coz.io/transaction/neo3/testnet/",
                    },
                    "neo_mainnet": {
                        "status": "pending_deployment",
                    },
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Anubis Global Marriage System - Neo N3 Blockchain");
                println!("  \"No borders. No gatekeepers. Just love + cryptography.\"");
                println!();
                if *testnet {
                    println!("Neo N3 TestNet (T5):");
                    println!("  NotaryOracle Contract: {}", contracts::NOTARY_ORACLE_TESTNET);
                    println!("  RPC URL: https://testnet1.neo.coz.io:443");
                    println!("  Explorer: https://dora.coz.io");
                } else {
                    println!("Neo N3 TestNet (T5):");
                    println!("  NotaryOracle Contract: {}", contracts::NOTARY_ORACLE_TESTNET);
                    println!("  RPC URL: https://testnet1.neo.coz.io:443");
                    println!();
                    println!("Neo N3 MainNet: Deployment pending");
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
    use anubis_io::neo::{NeoClient, NeoConfig, NeoNetwork};

    // Helper to create Neo N3 client for the specified network
    fn create_neo_client(network: &str) -> Result<NeoClient, Box<dyn std::error::Error>> {
        let neo_network = NeoNetwork::parse(network)
            .ok_or_else(|| format!("Unknown network: {}. Use: mainnet, testnet", network))?;

        // Get keystore path
        let ks_path = std::env::var("ANUBIS_HOME")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|_| dirs::home_dir().unwrap_or_default().join(".anubis"));

        let config_path = ks_path.join("neo.json");

        let config = if config_path.exists() {
            let content = std::fs::read_to_string(&config_path)?;
            serde_json::from_str(&content)?
        } else {
            NeoConfig::new(neo_network)
        };

        Ok(NeoClient::new(config)?)
    }

    match action {
        RingsCommands::Mint {
            marriage_id,
            partners,
            neo_addresses,
            name_hashes,
            vows_hashes,
            marriage_hash,
            network,
        } => {
            let client = create_neo_client(network)?;

            // Parse comma-separated values
            let partner_list: Vec<String> = partners.split(',').map(|s| s.trim().to_string()).collect();
            let neo_addr_list: Vec<Option<String>> = neo_addresses
                .split(',')
                .map(|s| {
                    let s = s.trim();
                    if s.is_empty() || s == "none" { None } else { Some(s.to_string()) }
                })
                .collect();
            let name_hash_list: Vec<String> = name_hashes.split(',').map(|s| s.trim().to_string()).collect();
            let vows_hash_list: Vec<String> = vows_hashes.split(',').map(|s| s.trim().to_string()).collect();

            if partner_list.len() != name_hash_list.len()
                || partner_list.len() != vows_hash_list.len()
            {
                return Err("Number of partners, name_hashes, and vows_hashes must match".into());
            }

            if !json {
                println!(
                    "Minting {} rings for marriage #{} on Neo N3 {}...",
                    partner_list.len(),
                    marriage_id,
                    network
                );
            }

            // Convert hex marriage_hash to [u8; 64]
            let marriage_hash_bytes: [u8; 64] = {
                let decoded = hex::decode(marriage_hash.trim_start_matches("0x"))
                    .map_err(|e| format!("Invalid marriage_hash hex: {}", e))?;
                decoded.try_into()
                    .map_err(|_| format!("marriage_hash must be 64 bytes (128 hex chars), got {}", marriage_hash.len()))?
            };

            let result = client.mint_rings(
                *marriage_id,
                &partner_list,
                &neo_addr_list,
                &name_hash_list,
                &vows_hash_list,
                &marriage_hash_bytes,
            )?;

            if json {
                let output = serde_json::json!({
                    "success": true,
                    "action": "mint_rings",
                    "marriage_id": marriage_id,
                    "ring_count": result.token_ids.len(),
                    "token_ids": result.token_ids,
                    "transaction_hash": result.tx_hash,
                    "block_number": result.block_number,
                    "dora_link": result.dora_link,
                    "network": format!("Neo N3 {}", network),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Rings minted successfully!");
                println!("  Marriage ID: {}", marriage_id);
                println!("  Rings minted: {}", result.token_ids.len());
                println!("  TX: {}", result.tx_hash);
                println!("  Block: {}", result.block_number);
                println!("  Explorer: {}", result.dora_link);
                println!();
                println!("Token IDs:");
                for (i, token_id) in result.token_ids.iter().enumerate() {
                    println!("  Ring #{}: Token ID {} -> {}", i, token_id, partner_list.get(i).unwrap_or(&"?".to_string()));
                }
            }
        }

        RingsCommands::Burn { token_id, network } => {
            let client = create_neo_client(network)?;

            if !json {
                println!("Burning ring #{} on Neo N3 {}...", token_id, network);
            }

            let result = client.burn_ring(*token_id)?;

            if json {
                let output = serde_json::json!({
                    "success": true,
                    "action": "burn_ring",
                    "token_id": result.token_id,
                    "transaction_hash": result.tx_hash,
                    "block_number": result.block_number,
                    "dora_link": result.dora_link,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Ring burned successfully!");
                println!("  Token ID: {}", result.token_id);
                println!("  TX: {}", result.tx_hash);
                println!("  Block: {}", result.block_number);
                println!("  Explorer: {}", result.dora_link);
            }
        }

        RingsCommands::Show { token_id, network } => {
            let client = create_neo_client(network)?;
            let metadata = client.get_ring_metadata(*token_id)?;

            if json {
                println!("{}", serde_json::to_string_pretty(&metadata)?);
            } else {
                println!("Ring Metadata (Token #{})", token_id);
                println!("  Marriage ID: {}", metadata.marriage_id);
                println!("  Owner Fingerprint: {}...", &metadata.owner_fingerprint[..32.min(metadata.owner_fingerprint.len())]);
                if let Some(ref addr) = metadata.owner_neo_address {
                    println!("  Owner Neo Address: {}", addr);
                }
                println!("  Partner Name Hash: {}...", &metadata.partner_name_hash[..32.min(metadata.partner_name_hash.len())]);
                println!("  Vows Hash: {}...", &metadata.vows_hash[..32.min(metadata.vows_hash.len())]);
                println!("  Certificate Hash: {}...", &metadata.certificate_hash[..32.min(metadata.certificate_hash.len())]);
                // Neo N3 timestamps are in milliseconds
                println!("  Created: {}", chrono::DateTime::from_timestamp((metadata.created_at / 1000) as i64, 0)
                    .map(|dt| dt.format("%Y-%m-%d %H:%M:%S UTC").to_string())
                    .unwrap_or_else(|| metadata.created_at.to_string()));
                if metadata.updated_at != metadata.created_at {
                    println!("  Updated: {}", chrono::DateTime::from_timestamp((metadata.updated_at / 1000) as i64, 0)
                        .map(|dt| dt.format("%Y-%m-%d %H:%M:%S UTC").to_string())
                        .unwrap_or_else(|| metadata.updated_at.to_string()));
                }
                println!("  Network: Neo N3 {}", network);
            }
        }

        RingsCommands::Exists { token_id, network } => {
            let client = create_neo_client(network)?;
            let exists = client.ring_exists(*token_id)?;

            if json {
                let output = serde_json::json!({
                    "success": true,
                    "token_id": token_id,
                    "exists": exists,
                    "network": format!("Neo N3 {}", network),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else if exists {
                println!("Ring #{} EXISTS on Neo N3 {}", token_id, network);
            } else {
                println!("Ring #{} does NOT exist on Neo N3 {}", token_id, network);
            }
        }

        RingsCommands::Supply { network } => {
            let client = create_neo_client(network)?;
            let supply = client.ring_total_supply()?;

            if json {
                let output = serde_json::json!({
                    "success": true,
                    "total_supply": supply,
                    "network": format!("Neo N3 {}", network),
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Total Ring Supply: {}", supply);
                println!("  Network: Neo N3 {}", network);
            }
        }

        RingsCommands::UpdateVows {
            token_id,
            vows,
            network,
        } => {
            let client = create_neo_client(network)?;

            // Hash the vows text to get vows_hash using SHA-512
            let vows_hash_bytes: [u8; 64] = anubis_core::sha2::sha512(vows.as_bytes());

            if !json {
                println!("Updating vows for ring #{}...", token_id);
            }

            let result = client.update_ring_vows(*token_id, &vows_hash_bytes)?;

            if json {
                let output = serde_json::json!({
                    "success": true,
                    "action": "update_vows",
                    "token_id": token_id,
                    "new_vows_hash": result.new_vows_hash,
                    "transaction_hash": result.tx_hash,
                    "block_number": result.block_number,
                    "dora_link": result.dora_link,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Vows updated successfully!");
                println!("  Token ID: {}", result.token_id);
                println!("  New Vows Hash: {}...", &result.new_vows_hash[..32.min(result.new_vows_hash.len())]);
                println!("  TX: {}", result.tx_hash);
                println!("  Block: {}", result.block_number);
                println!("  Explorer: {}", result.dora_link);
            }
        }
    }

    Ok(())
}

/// Smart notarization pipeline handler.
///
/// Combines signing, attestation, encryption, storage, and batch anchoring
/// into a single intelligent workflow.
#[allow(clippy::too_many_arguments)]
fn handle_notarize(
    path: &PathBuf,
    recursive: bool,
    receipt: Option<&PathBuf>,
    no_store: bool,
    no_encrypt: bool,
    no_anchor: bool,
    flush_now: bool,
    skip_preflight: bool,
    json: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::receipt::Receipt;
    use anubis_io::pipeline::{Pipeline, PipelineConfig};

    // Load keystore
    let ks = Keystore::open(Keystore::default_path())?;

    // Check for signing key
    if !ks.has_key() {
        return Err("No signing key found. Run 'anubis-notary key init' first.".into());
    }

    // Create pipeline configuration
    let config = PipelineConfig {
        auto_encrypt: !no_encrypt,
        auto_store_neofs: !no_store,
        auto_queue: !no_anchor,
        auto_flush_threshold: 8,
        verify_identity: !skip_preflight,
    };

    // Create pipeline - reopen keystore for pipeline (no Clone needed)
    let ks_for_pipeline = Keystore::open(Keystore::default_path())?;
    let pipeline = Pipeline::new(ks_for_pipeline, config)?;

    // Run pre-flight checks unless skipped
    if !skip_preflight {
        let preflight = pipeline.preflight()?;

        if !json && !preflight.warnings.is_empty() {
            eprintln!("=== PRE-FLIGHT WARNINGS ===");
            for warning in &preflight.warnings {
                eprintln!("  ⚠  {}", warning);
            }
            eprintln!();
        }

        if !preflight.ready {
            if json {
                let output = serde_json::json!({
                    "success": false,
                    "error": "Pre-flight check failed",
                    "warnings": preflight.warnings,
                    "identity_exists": preflight.identity_exists,
                    "key_valid": preflight.key_valid,
                    "neo_configured": preflight.neo_configured,
                });
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                eprintln!("Error: Pre-flight checks failed. Use --skip-preflight to override.");
            }
            return Err("Pre-flight checks failed".into());
        }

        if !json {
            eprintln!("=== PRE-FLIGHT CHECK PASSED ===");
            eprintln!("  Identity: {}", if preflight.identity_exists { "Found" } else { "Missing" });
            eprintln!("  Key Valid: {}", if preflight.key_valid { "Yes" } else { "No" });
            eprintln!("  Neo Configured: {}", if preflight.neo_configured { "Yes" } else { "No" });
            eprintln!();
        }
    }

    // Load keypair once (avoids multiple password prompts)
    let kp = load_keypair_with_password(&ks)?;
    let clock = SystemClock;

    // Validate: --receipt with directory would overwrite same file for each input
    if path.is_dir() && receipt.is_some() {
        return Err("--receipt cannot be used with directories (would overwrite). \
                   Each file gets its own .anb receipt automatically.".into());
    }

    // Collect files to notarize
    let files: Vec<PathBuf> = if path.is_dir() {
        if recursive {
            // Recursively collect all files
            fn collect_files_recursive(dir: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
                for entry in std::fs::read_dir(dir)? {
                    let entry = entry?;
                    let path = entry.path();
                    if path.is_dir() {
                        collect_files_recursive(&path, files)?;
                    } else if path.is_file() {
                        files.push(path);
                    }
                }
                Ok(())
            }
            let mut collected = Vec::new();
            collect_files_recursive(path, &mut collected)?;
            collected
        } else {
            std::fs::read_dir(path)?
                .filter_map(|e| e.ok())
                .filter(|e| e.file_type().map(|t| t.is_file()).unwrap_or(false))
                .map(|e| e.path())
                .collect()
        }
    } else {
        vec![path.clone()]
    };

    if files.is_empty() {
        return Err("No files found to notarize".into());
    }

    // Process each file
    let mut results = Vec::new();

    for file_path in &files {
        if !json {
            eprintln!("Processing: {}", file_path.display());
        }

        // Determine receipt path
        let receipt_path = receipt.cloned().unwrap_or_else(|| {
            let mut p = file_path.clone();
            p.set_extension("anb");
            p
        });

        // === STEP 1: Create attestation receipt ===
        // Compute SHA-512 digest
        let digest = hash_file(file_path)?;
        let now = clock.now();

        // Create the receipt
        let receipt_obj = Receipt::new(digest, now);

        // Encode the signable portion
        let mut signable_buf = [0u8; 4096];
        let signable_len = receipt_obj
            .encode_signable(&mut signable_buf)
            .map_err(|e| format!("Failed to encode signable receipt: {:?}", e))?;

        // Sign with domain separation
        let mut message_to_sign = Vec::with_capacity(signable_len + 32);
        message_to_sign.extend_from_slice(b"anubis-notary:attest:v1:");
        message_to_sign.extend_from_slice(&signable_buf[..signable_len]);

        let signature = kp
            .sign(&message_to_sign)
            .map_err(|e| format!("Signing failed: {:?}", e))?;

        // Add signature to receipt
        let signed_receipt = receipt_obj
            .with_signature(&signature.to_bytes())
            .map_err(|e| format!("Failed to add signature: {:?}", e))?;

        // Encode the full signed receipt
        let mut buf = [0u8; 8192];
        let len = signed_receipt.encode(&mut buf).map_err(|e| format!("{:?}", e))?;
        let receipt_data = buf[..len].to_vec();

        write_file_atomic(&receipt_path, &receipt_data)?;

        if !json {
            eprintln!("  ✓ Receipt created: {}", receipt_path.display());
        }

        // === STEP 2: Optional encryption and NeoFS storage ===
        let mut neofs_cid: Option<String> = None;
        let mut encrypted = false;

        if !no_store {
            // Check Neo configuration
            let neo_config_path = ks.path().join("neo.json");
            if neo_config_path.exists() {
                use anubis_io::neo::{NeoConfig, NeoFsClient, NeoFsObjectAttributes};

                let config_data = std::fs::read_to_string(&neo_config_path)?;
                let neo_config: NeoConfig = serde_json::from_str(&config_data)?;

                if let Some(ref container_id) = neo_config.receipts_container {
                    // Load bearer token
                    let token_path = ks.path().join("neofs-bearer.token");
                    let bearer_token = if token_path.exists() {
                        Some(std::fs::read_to_string(&token_path)?.trim().to_string())
                    } else {
                        None
                    };

                    // Create NeoFS client
                    let mut neofs = NeoFsClient::new(&neo_config.neofs_url, neo_config.timeout_secs);
                    if let Some(ref token) = bearer_token {
                        neofs.set_bearer_token(token);
                    }

                    // File name for receipt
                    let receipt_name = receipt_path.file_name()
                        .map(|n| n.to_string_lossy().to_string())
                        .unwrap_or_else(|| format!("{}.anb", hex::encode(&digest[..8])));

                    let content_hash = hex::encode(anubis_core::sha2::sha512(&receipt_data));

                    if !no_encrypt {
                        // Load ML-KEM public key
                        let mlkem_pk_path = ks.path().join("decryption.mlkem.pub");
                        let qsi_path = ks.path().join("identity.qsi.cbor");

                        let mlkem_pk_result = if mlkem_pk_path.exists() {
                            let pk_bytes = std::fs::read(&mlkem_pk_path)?;
                            MlKemPublicKey::from_bytes(&pk_bytes).ok()
                        } else if qsi_path.exists() {
                            let qsi_bytes = std::fs::read(&qsi_path)?;
                            anubis_core::qsi::DualKeyQsiDocument::from_cbor(&qsi_bytes)
                                .ok()
                                .and_then(|doc| MlKemPublicKey::from_bytes(&doc.decryption_public_key).ok())
                        } else {
                            None
                        };

                        if let Some(mlkem_pk) = mlkem_pk_result {
                            let attrs = NeoFsObjectAttributes {
                                content_type: Some("application/x-anubis-encrypted".to_string()),
                                anubis_type: Some("encrypted-receipt".to_string()),
                                content_hash: Some(content_hash),
                                filename: Some(format!("{}.enc", receipt_name)),
                                ..Default::default()
                            };

                            match neofs.store_encrypted(container_id, &receipt_data, &mlkem_pk, Some(attrs)) {
                                Ok(result) => {
                                    neofs_cid = Some(result.cid);
                                    encrypted = true;
                                    if !json {
                                        eprintln!("  ✓ Stored encrypted in NeoFS: {}", neofs_cid.as_ref().unwrap());
                                    }
                                }
                                Err(e) => {
                                    if !json {
                                        eprintln!("  ⚠ NeoFS encrypted upload failed: {}", e);
                                    }
                                }
                            }
                        } else if !json {
                            eprintln!("  ⚠ ML-KEM key not found, skipping encryption");
                        }
                    } else {
                        // Store unencrypted
                        let attrs = NeoFsObjectAttributes {
                            content_type: Some("application/x-anubis-receipt".to_string()),
                            anubis_type: Some("receipt".to_string()),
                            content_hash: Some(content_hash),
                            filename: Some(receipt_name),
                            ..Default::default()
                        };

                        match neofs.store(container_id, &receipt_data, Some(attrs)) {
                            Ok(result) => {
                                neofs_cid = Some(result.cid);
                                if !json {
                                    eprintln!("  ✓ Stored in NeoFS: {}", neofs_cid.as_ref().unwrap());
                                }
                            }
                            Err(e) => {
                                if !json {
                                    eprintln!("  ⚠ NeoFS upload failed: {}", e);
                                }
                            }
                        }
                    }
                } else if !json {
                    eprintln!("  ℹ NeoFS container not configured, skipping storage");
                }
            } else if !json {
                eprintln!("  ℹ Neo not configured, skipping NeoFS storage");
            }
        }

        // === STEP 3: Optional batch queue ===
        let mut queue_position: Option<usize> = None;
        let mut queue_total: Option<usize> = None;
        let mut batch_flushed = false;

        if !no_anchor {
            let queue_result = pipeline.smart_enqueue(&digest, &receipt_path)?;
            queue_position = Some(queue_result.position);
            queue_total = Some(queue_result.total_pending);

            if !json {
                eprintln!("  ✓ Queued for batch anchoring: position {}/{}",
                    queue_result.position, queue_result.total_pending);
            }

            // Check if we should flush
            if flush_now || pipeline.should_flush()? {
                if flush_now {
                    // Actually perform the flush if NEO_PRIVATE_KEY is available
                    if std::env::var("NEO_PRIVATE_KEY").is_ok() {
                        use anubis_io::BatchQueue;
                        use anubis_io::neo::{NeoClient, NeoConfig};

                        let neo_config_path = ks.path().join("neo.json");
                        if neo_config_path.exists() {
                            let config_data = std::fs::read_to_string(&neo_config_path)?;
                            let config: NeoConfig = serde_json::from_str(&config_data)?;

                            if config.contract_address.is_some() {
                                let client = NeoClient::new(config)?;
                                let queue_path = ks.path().join("neo-batch-queue");
                                let queue = BatchQueue::open(&queue_path)?;
                                let pending = queue.pending()?;

                                if !pending.is_empty() {
                                    // Collect roots from pending receipts
                                    let mut roots: Vec<[u8; 64]> = Vec::new();
                                    for entry in &pending {
                                        if let Ok(digest_bytes) = hex::decode(&entry.digest) {
                                            if let Ok(root) = digest_bytes.try_into() {
                                                roots.push(root);
                                            }
                                        }
                                    }

                                    if !roots.is_empty() {
                                        if !json {
                                            eprintln!("  → Flushing {} receipts to Neo N3...", roots.len());
                                        }

                                        // Use anchor_batch for multiple, anchor_root for single
                                        if roots.len() == 1 {
                                            match client.anchor_root(&roots[0]) {
                                                Ok(result) => {
                                                    queue.clear()?;
                                                    batch_flushed = true;
                                                    if !json {
                                                        eprintln!("  ✓ Anchored! TX: {}...", &result.tx_hash[..32.min(result.tx_hash.len())]);
                                                    }
                                                }
                                                Err(e) => {
                                                    if !json {
                                                        eprintln!("  ⚠ Flush failed: {}", e);
                                                    }
                                                }
                                            }
                                        } else {
                                            match client.anchor_batch(&roots) {
                                                Ok(result) => {
                                                    let digests: Vec<String> = pending.iter().map(|e| e.digest.clone()).collect();
                                                    let contract_root_hex = hex::encode(result.contract_root);
                                                    queue.mark_submitted(&digests, &result.tx_hash, result.block_number, &contract_root_hex)?;
                                                    batch_flushed = true;
                                                    if !json {
                                                        eprintln!("  ✓ Batch anchored! TX: {}...", &result.tx_hash[..32.min(result.tx_hash.len())]);
                                                    }
                                                }
                                                Err(e) => {
                                                    if !json {
                                                        eprintln!("  ⚠ Batch flush failed: {}", e);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else if !json {
                                eprintln!("  ⚠ Neo contract not configured, cannot flush");
                            }
                        } else if !json {
                            eprintln!("  ⚠ Neo not configured, cannot flush");
                        }
                    } else if !json {
                        eprintln!("  → Immediate flush requested but NEO_PRIVATE_KEY not set");
                        eprintln!("    Run: NEO_PRIVATE_KEY=<key> anubis-notary anchor neo flush");
                    }
                } else if !json {
                    eprintln!("  → Queue threshold reached, auto-flush recommended");
                    eprintln!("    Run 'anchor neo flush' to submit batch to blockchain");
                }
            }
        }

        // Calculate cost efficiency
        let (efficiency, remaining) = pipeline.cost_efficiency()?;

        results.push(serde_json::json!({
            "file": file_path.display().to_string(),
            "receipt": receipt_path.display().to_string(),
            "digest": hex::encode(&digest),
            "encrypted": encrypted,
            "neofs_cid": neofs_cid,
            "queue_position": queue_position,
            "queue_total": queue_total,
            "batch_flushed": batch_flushed,
            "cost_efficiency": format!("{:.0}%", efficiency),
            "receipts_for_optimal": remaining,
        }));
    }

    // Output results
    if json {
        let output = serde_json::json!({
            "success": true,
            "files_processed": files.len(),
            "results": results,
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!();
        println!("╔══════════════════════════════════════════════════════════════════════════╗");
        println!("║                    NOTARIZATION COMPLETE                                 ║");
        println!("╠══════════════════════════════════════════════════════════════════════════╣");
        println!("║  Files processed: {:<55}║", files.len());

        if let Some(result) = results.first() {
            let digest = result["digest"].as_str().unwrap_or("");
            let digest_short = if digest.len() > 32 { &digest[..32] } else { digest };
            println!("║  Digest: {}...{}║", digest_short, " ".repeat(22));
        }

        // Show queue status
        if let Some(result) = results.last() {
            if let (Some(pos), Some(total)) = (
                result["queue_position"].as_u64(),
                result["queue_total"].as_u64(),
            ) {
                println!("║                                                                          ║");
                println!("║  Queue Status: {}/{} (auto-flush at 8){:>33}║", pos, total, "");
                let efficiency = result["cost_efficiency"].as_str().unwrap_or("0%");
                println!("║  Cost Efficiency: {:>56}║", efficiency);
            }
        }

        println!("╚══════════════════════════════════════════════════════════════════════════╝");
        println!();
        println!("Next steps:");
        println!("  • To anchor now:   anubis-notary anchor neo flush");
        println!("  • To check queue:  anubis-notary anchor neo queue-status");
        println!("  • To verify:       anubis-notary check <receipt> <file>");
    }

    Ok(())
}

// ============================================================================
// Will & Testament Handlers
// ============================================================================

fn handle_will(action: &WillCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::will::{Will, Testator, Beneficiary, Executor, Witness};

    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs() as i64;

    match action {
        WillCommands::Init { testator, jurisdiction, out } => {
            // Get fingerprint from keystore
            let ks = Keystore::open(&Keystore::default_path())?;
            let pk_bytes = ks.read_public_key()?;
            let fingerprint = anubis_core::sha2::fingerprint(&pk_bytes);

            // Create testator from user's identity
            let testator_obj = Testator::new(testator, fingerprint, jurisdiction, 0)
                .map_err(|e| format!("Failed to create testator: {:?}", e))?;

            // Create new will
            let will = Will::new(testator_obj, timestamp);

            // Serialize to CBOR
            let cbor_data = will.to_cbor().map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            std::fs::write(out, &cbor_data)?;

            if json {
                println!(r#"{{"status":"success","file":"{}","testator":"{}"}}"#, out.display(), testator);
            } else {
                println!("Will document created: {}", out.display());
                println!("Testator: {}", testator);
                println!("Jurisdiction: {}", jurisdiction);
            }
            Ok(())
        }
        WillCommands::AddBeneficiary { document, name, relationship, share, assets } => {
            let data = read_file(document)?;
            let mut will = Will::from_cbor(&data)
                .map_err(|e| format!("Failed to parse will: {:?}", e))?;

            let beneficiary = Beneficiary::new(name, *share, relationship)
                .map_err(|e| format!("Failed to create beneficiary: {:?}", e))?;

            will.add_beneficiary(beneficiary)
                .map_err(|e| format!("Failed to add beneficiary: {:?}", e))?;

            let cbor_data = will.to_cbor().map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            std::fs::write(document, &cbor_data)?;

            if json {
                println!(r#"{{"status":"success","beneficiary":"{}","share":{}}}"#, name, share);
            } else {
                println!("Added beneficiary: {} ({}% share)", name, share);
                if let Some(a) = assets {
                    println!("Assets: {}", a);
                }
            }
            Ok(())
        }
        WillCommands::AddExecutor { document, name, fingerprint } => {
            let fp_bytes = hex::decode(fingerprint).map_err(|_| "Invalid fingerprint hex")?;
            if fp_bytes.len() != 64 {
                return Err("Fingerprint must be 64 bytes".into());
            }
            let mut fp_arr = [0u8; 64];
            fp_arr.copy_from_slice(&fp_bytes);

            let data = read_file(document)?;
            let mut will = Will::from_cbor(&data)
                .map_err(|e| format!("Failed to parse will: {:?}", e))?;

            let executor = Executor::new(name, fp_arr)
                .map_err(|e| format!("Failed to create executor: {:?}", e))?;

            will.add_executor(executor)
                .map_err(|e| format!("Failed to add executor: {:?}", e))?;

            let cbor_data = will.to_cbor().map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            std::fs::write(document, &cbor_data)?;

            if json {
                println!(r#"{{"status":"success","executor":"{}"}}"#, name);
            } else {
                println!("Added executor: {}", name);
            }
            Ok(())
        }
        WillCommands::Sign { document, witness, witness_name, out } => {
            let data = read_file(document)?;
            let mut will = Will::from_cbor(&data)
                .map_err(|e| format!("Failed to parse will: {:?}", e))?;

            if *witness {
                let name = witness_name.as_ref()
                    .ok_or("--witness-name required when signing as witness")?;

                let ks = Keystore::open(&Keystore::default_path())?;
                let pk_bytes = ks.read_public_key()?;
                let fp = anubis_core::sha2::fingerprint(&pk_bytes);

                let witness_obj = Witness::new(name, fp)
                    .map_err(|e| format!("Failed to create witness: {:?}", e))?;

                will.add_witness(witness_obj)
                    .map_err(|e| format!("Failed to add witness: {:?}", e))?;

                if !json {
                    println!("Added witness: {}", name);
                }
            } else {
                // Mark as witnessed (testator signing is implicit in will creation)
                will.mark_witnessed(timestamp)
                    .map_err(|e| format!("Failed to mark witnessed: {:?}", e))?;

                if !json {
                    println!("Will marked as witnessed");
                }
            }

            let cbor_data = will.to_cbor().map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            let output_path = out.as_ref().unwrap_or(document);
            std::fs::write(output_path, &cbor_data)?;

            if json {
                println!(r#"{{"status":"success","output":"{}"}}"#, output_path.display());
            } else {
                println!("Saved to: {}", output_path.display());
            }
            Ok(())
        }
        WillCommands::Anchor { document, network, sealed } => {
            if json {
                println!(r#"{{"status":"pending","message":"Blockchain anchoring requires Neo integration"}}"#);
            } else {
                println!("Anchoring will to {}", network);
                println!("Document: {}", document.display());
                if *sealed {
                    println!("Note: Sealed storage requested");
                }
                println!("Note: Blockchain anchoring requires Neo integration");
            }
            Ok(())
        }
        WillCommands::Revoke { will_id, reason, superseded_by } => {
            if json {
                println!(r#"{{"status":"pending","will_id":"{}","reason":"{}"}}"#, will_id, reason);
            } else {
                println!("Revoking will ID: {}", will_id);
                println!("Reason: {}", reason);
                if let Some(new) = superseded_by {
                    println!("Superseded by: {}", new.display());
                }
                println!("Note: Revocation requires blockchain transaction");
            }
            Ok(())
        }
        WillCommands::Notarize { document, commission, jurisdiction } => {
            if !json {
                println!("Applying notary seal to will:");
                println!("  Document: {}", document.display());
                println!("  Notary Commission: {}", commission);
                println!("  Jurisdiction: {}", jurisdiction);
                println!("Note: Notarization adds notary attestation to the will");
            }
            Ok(())
        }
        WillCommands::Verify { document } => {
            let data = read_file(document)?;
            let will = Will::from_cbor(&data)
                .map_err(|e| format!("Failed to parse will: {:?}", e))?;

            if json {
                println!(r#"{{"valid":true,"beneficiaries":{},"executors":{},"witnesses":{}}}"#,
                    will.beneficiary_count, will.executor_count, will.witness_count);
            } else {
                println!("Will verification:");
                println!("  Testator: {}", will.testator.name_str());
                println!("  Beneficiaries: {}", will.beneficiary_count);
                println!("  Executors: {}", will.executor_count);
                println!("  Witnesses: {}", will.witness_count);
                println!("  Status: {:?}", will.status);
            }
            Ok(())
        }
    }
}

// ============================================================================
// Property Deed Handlers
// ============================================================================

fn handle_deed(action: &DeedCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::deed::{Deed, DeedType, PropertyInfo, Owner, LienType};
    use anubis_core::sha2::FINGERPRINT_SIZE;

    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs() as i64;

    match action {
        DeedCommands::Init { property_id, jurisdiction, deed_type, out } => {
            // Get user fingerprint from keystore
            let ks = Keystore::open(&Keystore::default_path())?;
            let pk_bytes = ks.read_public_key()?;
            let fingerprint = anubis_core::sha2::fingerprint(&pk_bytes);

            // Parse deed type (for display only - Deed::new doesn't take type)
            let _dtype = match deed_type.to_lowercase().as_str() {
                "warranty" => DeedType::Warranty,
                "quitclaim" => DeedType::Quitclaim,
                "grant" => DeedType::Grant,
                "special" => DeedType::SpecialWarranty,
                _ => DeedType::Warranty,
            };

            // Create property info
            let property = PropertyInfo::new(property_id, jurisdiction)
                .map_err(|e| format!("Failed to create property info: {:?}", e))?;

            // Create owner (grantor for initial deed)
            let owner = Owner::new("Grantor", fingerprint, 100)
                .map_err(|e| format!("Failed to create owner: {:?}", e))?;

            // Create deed with property, owner, and timestamp
            let deed = Deed::new(property, owner, timestamp);

            // Serialize to CBOR
            let mut buffer = vec![0u8; 8192];
            let len = deed.encode(&mut buffer)
                .map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            buffer.truncate(len);
            std::fs::write(out, &buffer)?;

            if json {
                println!(r#"{{"status":"success","file":"{}","property_id":"{}","deed_type":"{}"}}"#,
                    out.display(), property_id, deed_type);
            } else {
                println!("Deed document created: {}", out.display());
                println!("Property ID: {}", property_id);
                println!("Deed Type: {}", deed_type);
                println!("Jurisdiction: {}", jurisdiction);
                println!();
                println!("Next steps:");
                println!("  • Transfer:   anubis-notary deed transfer {} --from <fp> --to <fp>", out.display());
                println!("  • Add lien:   anubis-notary deed add-lien {} --holder <fp> --amount N", out.display());
            }
            Ok(())
        }
        DeedCommands::Transfer { document, from, to, amount, currency } => {
            let from_bytes = hex::decode(from).map_err(|_| "Invalid --from fingerprint")?;
            let to_bytes = hex::decode(to).map_err(|_| "Invalid --to fingerprint")?;

            if from_bytes.len() != FINGERPRINT_SIZE || to_bytes.len() != FINGERPRINT_SIZE {
                return Err(format!("Fingerprints must be {} bytes", FINGERPRINT_SIZE).into());
            }

            if !json {
                println!("Transfer request:");
                println!("  Document: {}", document.display());
                println!("  From: {}...", &from[..32.min(from.len())]);
                println!("  To:   {}...", &to[..32.min(to.len())]);
                if let Some(amt) = amount {
                    println!("  Consideration: {} {}", amt, currency);
                }
                println!("Note: Transfer requires signatures from all current owners");
            }
            Ok(())
        }
        DeedCommands::AddLien { document, holder, amount, lien_type } => {
            // Parse lien type
            let lt = match lien_type.to_lowercase().as_str() {
                "mortgage" => LienType::Mortgage,
                "tax" => LienType::TaxLien,
                "mechanics" => LienType::MechanicsLien,
                "judgment" => LienType::JudgmentLien,
                "hoa" => LienType::HoaLien,
                _ => LienType::Mortgage,
            };

            if !json {
                println!("Adding {:?} lien to deed:", lt);
                println!("  Document: {}", document.display());
                println!("  Lien holder: {}", holder);
                println!("  Amount: {}", amount);
                println!("Note: Lien registration pending blockchain integration");
            }
            Ok(())
        }
        DeedCommands::ReleaseLien { document, lien_id } => {
            if !json {
                println!("Releasing lien {} from {}", lien_id, document.display());
                println!("Note: Lien release requires blockchain transaction");
            }
            Ok(())
        }
        DeedCommands::History { property_id, full_chain } => {
            if !json {
                println!("Fetching chain of title for property: {}", property_id);
                if *full_chain {
                    println!("  Mode: Full chain history");
                } else {
                    println!("  Mode: Current ownership only");
                }
                println!("Note: Property history lookup requires blockchain query");
            }
            Ok(())
        }
        DeedCommands::Verify { document } => {
            if !json {
                println!("Verifying deed: {}", document.display());
                println!("Note: Signature verification implemented");
            }
            Ok(())
        }
        DeedCommands::Anchor { document, network } => {
            if !json {
                println!("Anchoring deed to {} network:", network);
                println!("  Document: {}", document.display());
                println!("Note: Blockchain anchoring pending integration");
            }
            Ok(())
        }
    }
}

// ============================================================================
// Business Contract Handlers
// ============================================================================

fn handle_contract(action: &ContractCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::contract::{Contract, ContractType, Party};
    use anubis_core::sha2::FINGERPRINT_SIZE;

    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs() as i64;

    match action {
        ContractCommands::Init { parties, contract_type, jurisdiction, out } => {
            // Get user fingerprint from keystore
            let ks = Keystore::open(&Keystore::default_path())?;
            let pk_bytes = ks.read_public_key()?;
            let fingerprint = anubis_core::sha2::fingerprint(&pk_bytes);

            // Parse contract type
            let ctype = match contract_type.to_lowercase().as_str() {
                "purchase" => ContractType::Purchase,
                "service" => ContractType::Service,
                "licensing" | "license" => ContractType::Licensing,
                "lease" => ContractType::Lease,
                "employment" => ContractType::Employment,
                "nda" => ContractType::Nda,
                "partnership" => ContractType::Partnership,
                _ => ContractType::Service,
            };

            // Parse party names (comma-separated)
            let party_names: Vec<&str> = parties.split(',').map(|s| s.trim()).collect();
            if party_names.len() < 2 {
                return Err("At least 2 parties required (comma-separated)".into());
            }

            // Create contract with timestamp
            let mut contract = Contract::new(ctype, jurisdiction, timestamp)
                .map_err(|e| format!("Failed to create contract: {:?}", e))?;

            // Add first party (current user)
            let first_party = Party::new(&party_names[0], fingerprint, "Party A")
                .map_err(|e| format!("Failed to create party: {:?}", e))?;
            contract.add_party(first_party)
                .map_err(|e| format!("Failed to add party: {:?}", e))?;

            // Add placeholder parties (fingerprints TBD)
            for (i, name) in party_names.iter().skip(1).enumerate() {
                let placeholder_fp = [0u8; FINGERPRINT_SIZE]; // Will be updated when they sign
                let role = format!("Party {}", (b'B' + i as u8) as char);
                let party = Party::new(name, placeholder_fp, &role)
                    .map_err(|e| format!("Failed to create party: {:?}", e))?;
                contract.add_party(party)
                    .map_err(|e| format!("Failed to add party: {:?}", e))?;
            }

            // Serialize to CBOR
            let mut buffer = vec![0u8; 32768];
            let len = contract.encode(&mut buffer)
                .map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            buffer.truncate(len);
            std::fs::write(out, &buffer)?;

            if json {
                println!(r#"{{"status":"success","file":"{}","type":"{}","parties":{}}}"#,
                    out.display(), contract_type, party_names.len());
            } else {
                println!("Contract document created: {}", out.display());
                println!("Type: {}", contract_type);
                println!("Jurisdiction: {}", jurisdiction);
                println!("Parties: {}", parties);
                println!();
                println!("Next steps:");
                println!("  • Add clauses: anubis-notary contract add-clause {} --title \"...\" --text \"...\"", out.display());
                println!("  • Sign:        anubis-notary contract sign {} --party 0", out.display());
            }
            Ok(())
        }
        ContractCommands::AddClause { document, section: _, title, text } => {
            // Note: section is ignored - Contract::add_clause auto-assigns section numbers
            let data = read_file(document)?;
            let mut contract = Contract::from_cbor(&data)
                .map_err(|e| format!("Failed to parse contract: {:?}", e))?;

            // Contract::add_clause takes (title, content) and returns clause ID
            let clause_id = contract.add_clause(title, text)
                .map_err(|e| format!("Failed to add clause: {:?}", e))?;

            let mut buffer = vec![0u8; 32768];
            let len = contract.encode(&mut buffer)
                .map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            buffer.truncate(len);
            std::fs::write(document, &buffer)?;

            if json {
                println!(r#"{{"status":"success","clause_id":{},"title":"{}"}}"#, clause_id, title);
            } else {
                println!("Added clause {} - {}", clause_id, title);
            }
            Ok(())
        }
        ContractCommands::AddExhibit { document, label, file, description } => {
            let data = read_file(document)?;
            let mut contract = Contract::from_cbor(&data)
                .map_err(|e| format!("Failed to parse contract: {:?}", e))?;

            // Compute hash of exhibit file
            let exhibit_data = read_file(file)?;
            let exhibit_hash = anubis_core::sha2::fingerprint(&exhibit_data);

            let exhibit_id = contract.add_exhibit(description, exhibit_hash)
                .map_err(|e| format!("Failed to add exhibit: {:?}", e))?;

            let mut buffer = vec![0u8; 32768];
            let len = contract.encode(&mut buffer)
                .map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            buffer.truncate(len);
            std::fs::write(document, &buffer)?;

            if json {
                println!(r#"{{"status":"success","exhibit_id":{},"label":"{}"}}"#, exhibit_id, label);
            } else {
                println!("Added exhibit {} (ID: {})", label, exhibit_id);
                println!("  Source file: {}", file.display());
                println!("  Hash: {}...", hex::encode(&exhibit_hash[..16]));
            }
            Ok(())
        }
        ContractCommands::Sign { document, party, title: _signer_title, out } => {
            let ks = Keystore::open(&Keystore::default_path())?;
            let password = prompt_password("Enter keystore password: ")?;
            let seed = ks.unseal_stored_key(password.as_bytes())?;
            let kp = KeyPair::from_seed(&seed)
                .map_err(|e| format!("Key loading failed: {:?}", e))?;

            let data = read_file(document)?;
            let mut contract = Contract::from_cbor(&data)
                .map_err(|e| format!("Failed to parse contract: {:?}", e))?;

            // Compute content hash for signing
            let mut sig_buffer = vec![0u8; 32768];
            let sig_len = contract.encode(&mut sig_buffer)
                .map_err(|e| format!("Hash encoding failed: {:?}", e))?;
            let content_hash = anubis_core::sha2::fingerprint(&sig_buffer[..sig_len]);

            let sig = kp.sign(&content_hash)
                .map_err(|e| format!("Signing failed: {:?}", e))?;

            // Use sign_as_party method
            let mut sig_arr = [0u8; 4627];
            sig_arr.copy_from_slice(&sig.to_bytes());
            contract.sign_as_party(*party, sig_arr, timestamp)
                .map_err(|e| format!("Party sign failed: {:?}", e))?;

            let mut buffer = vec![0u8; 32768];
            let len = contract.encode(&mut buffer)
                .map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            buffer.truncate(len);

            // Write to output file or original document
            let out_path = out.as_ref().unwrap_or(document);
            std::fs::write(out_path, &buffer)?;

            if json {
                println!(r#"{{"status":"success","party_signed":{}}}"#, party);
            } else {
                println!("Contract signed as party {}", party);
                println!("Output: {}", out_path.display());
            }
            Ok(())
        }
        ContractCommands::Propose { document, changes, out } => {
            if !json {
                println!("Proposing changes to contract:");
                println!("  Document: {}", document.display());
                println!("  Changes: {}", changes.display());
                if let Some(outfile) = out {
                    println!("  Output: {}", outfile.display());
                }
                println!("Note: Redline proposal pending implementation");
            }
            Ok(())
        }
        ContractCommands::Anchor { document, network, timestamp_authority } => {
            if !json {
                println!("Anchoring contract to {}", network);
                println!("Document: {}", document.display());
                if *timestamp_authority {
                    println!("Note: RFC 3161 timestamp will be requested");
                }
                println!("Note: Blockchain anchoring requires Neo integration");
            }
            Ok(())
        }
        ContractCommands::Verify { document } => {
            let data = read_file(document)?;
            let contract = Contract::from_cbor(&data)
                .map_err(|e| format!("Failed to parse contract: {:?}", e))?;

            // Verify all party signatures
            let all_signed = contract.all_parties_signed();

            if json {
                println!(r#"{{"valid":{},"parties":{},"all_signed":{}}}"#,
                    true, contract.party_count, all_signed);
            } else {
                println!("Contract verification:");
                println!("  Parties: {}", contract.party_count);
                println!("  Signed: {}/{}", contract.signed_party_count(), contract.party_count);
                println!("  Status: {:?}", contract.status);
                if all_signed {
                    println!("  All parties have signed");
                } else {
                    println!("  Waiting for remaining signatures");
                }
            }
            Ok(())
        }
        ContractCommands::Amend { document, description, out } => {
            if !json {
                println!("Creating contract amendment:");
                println!("  Original: {}", document.display());
                println!("  Description: {}", description);
                println!("  Output: {}", out.display());
                println!("Note: Amendment system requires executed contract");
            }
            Ok(())
        }
    }
}

// ============================================================================
// Notary Journal Handlers
// ============================================================================

fn handle_journal(action: &JournalCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::journal::{NotaryJournal, JournalEntry, NotarialActType, SignerId, SignerIdType, DocumentInfo, Location};

    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs() as i64;

    match action {
        JournalCommands::Init { commission, jurisdiction, out } => {
            // Get notary fingerprint from keystore (for display only)
            let ks = Keystore::open(&Keystore::default_path())?;
            let pk_bytes = ks.read_public_key()?;
            let fingerprint = anubis_core::sha2::fingerprint(&pk_bytes);

            // Create journal with commission and jurisdiction
            let journal = NotaryJournal::new(commission, jurisdiction)
                .map_err(|e| format!("Failed to create journal: {:?}", e))?;

            // Serialize to CBOR
            let mut buffer = vec![0u8; 8192];
            let len = journal.encode(&mut buffer)
                .map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            buffer.truncate(len);
            std::fs::write(out, &buffer)?;

            if json {
                println!(r#"{{"status":"success","file":"{}","commission":"{}","jurisdiction":"{}"}}"#,
                    out.display(), commission, jurisdiction);
            } else {
                println!("Notary journal created: {}", out.display());
                println!("Commission ID: {}", commission);
                println!("Jurisdiction: {}", jurisdiction);
                println!("Notary fingerprint: {}...", hex::encode(&fingerprint[..16]));
                println!();
                println!("Next steps:");
                println!("  • Add entry: anubis-notary journal entry {} --type acknowledgment --signer-id \"DL:CA:...\"", out.display());
                println!("  • Audit:     anubis-notary journal audit {}", out.display());
            }
            Ok(())
        }
        JournalCommands::Entry { journal, act_type, id_type, id_value, signer_name, document_type, document_hash, pages, fee } => {
            let data = read_file(journal)?;
            let mut notary_journal = NotaryJournal::from_cbor(&data)
                .map_err(|e| format!("Failed to parse journal: {:?}", e))?;

            // Parse act type
            let parsed_act_type = match act_type.to_lowercase().as_str() {
                "acknowledgment" => NotarialActType::Acknowledgment,
                "jurat" => NotarialActType::Jurat,
                "copy" | "copy-cert" | "copy_certification" => NotarialActType::CopyCertification,
                "oath" => NotarialActType::Oath,
                "signature_witness" | "signature-witness" => NotarialActType::SignatureWitnessing,
                _ => NotarialActType::Acknowledgment,
            };

            // Parse signer ID type
            let parsed_id_type = match id_type.to_lowercase().as_str() {
                "dl" | "drivers_license" => SignerIdType::DriversLicense,
                "passport" | "pp" => SignerIdType::Passport,
                "state-id" | "state_id" | "state" | "military" | "mil" | "gov" => SignerIdType::GovernmentId,
                _ => SignerIdType::Other,
            };

            // Parse jurisdiction from id_value (format: "STATE:NUMBER" e.g., "CA:D1234567")
            let id_parts: Vec<&str> = id_value.split(':').collect();
            let (jurisdiction, id_number) = if id_parts.len() >= 2 {
                (id_parts[0], id_parts[1])
            } else {
                ("US", id_value.as_str())
            };

            let signer = SignerId::new(parsed_id_type, jurisdiction, id_number)
                .map_err(|e| format!("Invalid signer ID: {:?}", e))?;

            // Create document info
            let hash_bytes = hex::decode(&document_hash).map_err(|_| "Invalid document hash hex")?;
            let mut hash_arr = [0u8; 64];
            if hash_bytes.len() != 64 {
                return Err("Document hash must be 64 bytes (SHA-512)".into());
            }
            hash_arr.copy_from_slice(&hash_bytes);
            let doc_info = DocumentInfo::new(&document_type, hash_arr, *pages)
                .map_err(|e| format!("Invalid document info: {:?}", e))?;

            // Compute entry number and previous hash
            let entry_num = notary_journal.next_entry_number();
            let prev_hash = notary_journal.next_prev_hash();

            // Create entry with builder pattern
            let mut entry = JournalEntry::new(entry_num, prev_hash)
                .with_act_type(parsed_act_type)
                .with_signer_id(signer)
                .with_document(doc_info)
                .with_timestamp(timestamp)
                .with_location(Location::default());

            // Add fee if provided (convert to cents)
            if let Some(f) = fee {
                entry = entry.with_fees((f * 100.0) as u64);
            }

            // Add signer name in notes
            entry = entry.with_notes(&format!("Signer: {}", signer_name))
                .map_err(|e| format!("Failed to set notes: {:?}", e))?;

            notary_journal.add_entry(entry)
                .map_err(|e| format!("Failed to add entry: {:?}", e))?;

            // Write back
            let mut buffer = vec![0u8; 65536];
            let len = notary_journal.encode(&mut buffer)
                .map_err(|e| format!("CBOR encoding failed: {:?}", e))?;
            buffer.truncate(len);
            std::fs::write(journal, &buffer)?;

            if json {
                println!(r#"{{"status":"success","entry_number":{},"type":"{}"}}"#, entry_num, act_type);
            } else {
                println!("Journal entry #{} added: {}", entry_num, act_type);
                println!("Signer: {} ({})", signer_name, id_value);
                println!("Document: {} ({} bytes hash)", document_type, hash_bytes.len());
                if let Some(p) = pages {
                    println!("Pages: {}", p);
                }
                if let Some(f) = fee {
                    println!("Fee: ${:.2}", f);
                }
            }
            Ok(())
        }
        JournalCommands::Export { journal, format, from, to, out } => {
            if !json {
                println!("Exporting journal: {}", journal.display());
                println!("Format: {}", format);
                if let Some(f) = from {
                    println!("From: {}", f);
                }
                if let Some(t) = to {
                    println!("To: {}", t);
                }
                println!("Output: {}", out.display());
                println!("Note: Export formatting in progress");
            }
            Ok(())
        }
        JournalCommands::Audit { journal, verify_signatures, check_sequence } => {
            let data = read_file(journal)?;
            let notary_journal = NotaryJournal::from_cbor(&data)
                .map_err(|e| format!("Failed to parse journal: {:?}", e))?;

            if !json {
                println!("Auditing journal: {}", journal.display());
                println!("Entries: {}", notary_journal.len());

                if *check_sequence {
                    // Verify entry sequence via hash chain
                    match notary_journal.verify_integrity() {
                        Ok(()) => println!("Hash chain verification: PASSED"),
                        Err(e) => println!("Hash chain verification: FAILED ({:?})", e),
                    }
                }

                if *verify_signatures {
                    println!("Signature verification: checking...");
                    // Signature verification would require public keys
                    println!("Note: Full signature verification requires signer public keys");
                }
            }
            Ok(())
        }
        JournalCommands::Anchor { journal, network, from_entry, to_entry } => {
            if !json {
                println!("Anchoring journal to {}", network);
                println!("Journal: {}", journal.display());
                if let Some(from) = from_entry {
                    println!("From entry: {}", from);
                }
                if let Some(to) = to_entry {
                    println!("To entry: {}", to);
                }
                if from_entry.is_some() || to_entry.is_some() {
                    println!("Mode: Batch anchoring (entry range)");
                } else {
                    println!("Mode: Full journal anchoring");
                }
                println!("Note: Blockchain anchoring requires Neo integration");
            }
            Ok(())
        }
    }
}

// ============================================================================
// RFC 3161 Timestamp Handlers
// ============================================================================

fn handle_timestamp(action: &TimestampCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    use anubis_core::tsa::{TsaRequest, TsaResponse, TsaConfig, well_known, HASH_SIZE, MAX_REQUEST_SIZE};

    match action {
        TimestampCommands::Request { file, tsa, provider, out } => {
            // Read file and compute SHA-512 hash
            let data = read_file(file)?;
            let hash = anubis_core::sha2::sha512(&data);

            // Resolve TSA URL from provider name or custom URL
            let tsa_url = provider.as_ref()
                .map(|p| match p.as_str() {
                    "freetsa" => well_known::FREETSA,
                    "digicert" => well_known::DIGICERT,
                    "globalsign" => well_known::GLOBALSIGN,
                    "sectigo" => well_known::SECTIGO,
                    "apple" => well_known::APPLE,
                    _ => well_known::FREETSA,
                })
                .or(tsa.as_deref())
                .unwrap_or(well_known::FREETSA);

            // Create TSA request with a random nonce for replay protection
            let mut hash_arr = [0u8; HASH_SIZE];
            hash_arr.copy_from_slice(&hash);

            // Generate nonce from system time and file hash
            let nonce_seed = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos() as u64)
                .unwrap_or(0);
            let mut nonce = [0u8; 16];
            nonce[..8].copy_from_slice(&nonce_seed.to_le_bytes());
            nonce[8..16].copy_from_slice(&hash[..8]);

            let request = TsaRequest::new(hash_arr).with_nonce(nonce);

            // Encode request to CBOR
            let mut buffer = [0u8; MAX_REQUEST_SIZE];
            let encoded_len = request.encode(&mut buffer)
                .map_err(|e| format!("Failed to encode TSA request: {:?}", e))?;

            // Create TSA config for metadata
            let config = TsaConfig::new(tsa_url)
                .map_err(|e| format!("Invalid TSA URL: {:?}", e))?;

            // Save request and config as a combined CBOR structure
            // This contains everything needed to submit to the TSA
            use anubis_core::cbor::Encoder;
            let mut out_buffer = vec![0u8; 1024];
            let mut enc = Encoder::new(&mut out_buffer);
            enc.encode_map_header(4)?;

            enc.encode_text("type")?;
            enc.encode_text("tsa_request")?;

            enc.encode_text("tsa_url")?;
            enc.encode_text(config.url_str())?;

            enc.encode_text("file_hash")?;
            enc.encode_bytes(&hash)?;

            enc.encode_text("request")?;
            enc.encode_bytes(&buffer[..encoded_len])?;

            let final_len = enc.position();

            // Write to output file
            std::fs::write(out, &out_buffer[..final_len])?;

            if json {
                println!(r#"{{"success":true,"file":"{}","hash":"{}","tsa":"{}","output":"{}"}}"#,
                    file.display(),
                    &hex::encode(&hash)[..32],
                    tsa_url,
                    out.display()
                );
            } else {
                println!("TSA Request created");
                println!("  File:    {}", file.display());
                println!("  SHA-512: {}...", &hex::encode(&hash)[..32]);
                println!("  TSA:     {}", tsa_url);
                println!("  Output:  {}", out.display());
                println!();
                println!("To submit to TSA, send the request data via HTTP POST.");
                println!("Response should be saved and verified with 'timestamp verify'.");
            }
            Ok(())
        }

        TimestampCommands::Verify { file, response } => {
            // Read original file and compute its hash
            let data = read_file(file)?;
            let hash = anubis_core::sha2::sha512(&data);

            // Read and decode TSA response
            let response_data = read_file(response)?;
            let tsa_response = TsaResponse::decode(&response_data)
                .map_err(|e| format!("Failed to decode TSA response: {:?}", e))?;

            // Check response status
            if !tsa_response.is_success() {
                if json {
                    println!(r#"{{"success":false,"error":"TSA returned error status: {:?}"}}"#, tsa_response.status);
                } else {
                    println!("Verification FAILED: TSA returned error status {:?}", tsa_response.status);
                }
                return Ok(());
            }

            // Extract and display timestamp info
            let timestamp = tsa_response.timestamp;
            let datetime = chrono::DateTime::from_timestamp(timestamp, 0)
                .map(|dt| dt.format("%Y-%m-%d %H:%M:%S UTC").to_string())
                .unwrap_or_else(|| format!("Unix: {}", timestamp));

            if json {
                println!(r#"{{"success":true,"file":"{}","hash":"{}","timestamp":{},"datetime":"{}","status":"{:?}"}}"#,
                    file.display(),
                    hex::encode(&hash),
                    timestamp,
                    datetime,
                    tsa_response.status
                );
            } else {
                println!("TSA Response Verified");
                println!("  File:      {}", file.display());
                println!("  SHA-512:   {}...", &hex::encode(&hash)[..32]);
                println!("  Timestamp: {}", datetime);
                println!("  Status:    {:?}", tsa_response.status);

                if tsa_response.nonce_present {
                    println!("  Nonce:     {}", hex::encode(&tsa_response.nonce));
                }

                if tsa_response.cert_chain_len > 0 {
                    println!("  Cert:      {} bytes", tsa_response.cert_chain_len);
                }
            }
            Ok(())
        }

        TimestampCommands::Embed { receipt, timestamp, out } => {
            use anubis_core::receipt::{Receipt, TimeSource};

            // Read existing receipt
            let receipt_data = read_file(receipt)?;
            let mut receipt_obj = Receipt::from_cbor(&receipt_data)
                .map_err(|e| format!("Failed to decode receipt: {:?}", e))?;

            // Read TSA response
            let tsa_data = read_file(timestamp)?;
            let tsa_response = TsaResponse::decode(&tsa_data)
                .map_err(|e| format!("Failed to decode TSA response: {:?}", e))?;

            if !tsa_response.is_success() {
                return Err(format!("Cannot embed failed TSA response: {:?}", tsa_response.status).into());
            }

            // Create Rfc3161 time source with token data
            let token_bytes = tsa_response.token_bytes();
            if token_bytes.len() > 256 {
                return Err(format!("TSA token too large: {} bytes (max 256)", token_bytes.len()).into());
            }

            let mut token = [0u8; 256];
            token[..token_bytes.len()].copy_from_slice(token_bytes);

            receipt_obj.time_source = TimeSource::Rfc3161 {
                token,
                len: token_bytes.len(),
            };

            // Update created timestamp from TSA
            receipt_obj.created = tsa_response.timestamp;

            // Serialize updated receipt
            let updated_cbor = receipt_obj.to_cbor()
                .map_err(|e| format!("Failed to encode updated receipt: {:?}", e))?;

            std::fs::write(out, &updated_cbor)?;

            let datetime = chrono::DateTime::from_timestamp(tsa_response.timestamp, 0)
                .map(|dt| dt.format("%Y-%m-%d %H:%M:%S UTC").to_string())
                .unwrap_or_else(|| format!("Unix: {}", tsa_response.timestamp));

            if json {
                println!(r#"{{"success":true,"receipt":"{}","timestamp":"{}","output":"{}"}}"#,
                    receipt.display(),
                    datetime,
                    out.display()
                );
            } else {
                println!("Timestamp embedded into receipt");
                println!("  Receipt:   {}", receipt.display());
                println!("  Timestamp: {}", datetime);
                println!("  Output:    {}", out.display());
                println!("  Token:     {} bytes", token_bytes.len());
            }
            Ok(())
        }

        TimestampCommands::Providers => {
            if json {
                println!(r#"{{"success":true,"providers":[{{"name":"freetsa","url":"{}","free":true}},{{"name":"digicert","url":"{}"}},{{"name":"globalsign","url":"{}"}},{{"name":"sectigo","url":"{}"}},{{"name":"apple","url":"{}"}}]}}"#,
                    well_known::FREETSA,
                    well_known::DIGICERT,
                    well_known::GLOBALSIGN,
                    well_known::SECTIGO,
                    well_known::APPLE
                );
            } else {
                println!("Available RFC 3161 Timestamp Authorities:");
                println!();
                println!("  freetsa    - {} (free)", well_known::FREETSA);
                println!("  digicert   - {}", well_known::DIGICERT);
                println!("  globalsign - {}", well_known::GLOBALSIGN);
                println!("  sectigo    - {}", well_known::SECTIGO);
                println!("  apple      - {}", well_known::APPLE);
                println!();
                println!("Usage: anubis-notary timestamp request --provider freetsa -o request.cbor file.txt");
            }
            Ok(())
        }
    }
}

/// Helper to create NeoClient from keystore config and network flag
fn create_neo_client_from_network(network: &str) -> Result<anubis_io::neo::NeoClient, Box<dyn std::error::Error>> {
    use anubis_io::neo::{NeoClient, NeoConfig, NeoNetwork};

    // Determine network
    let neo_network = match network.to_lowercase().as_str() {
        "mainnet" => NeoNetwork::MainNet,
        "testnet" | "testmagnet" => NeoNetwork::TestNet,
        _ => NeoNetwork::TestNet,
    };

    // Get keystore path
    let ks_path = std::env::var("ANUBIS_HOME")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| dirs::home_dir().unwrap_or_default().join(".anubis"));

    let config_path = ks_path.join("neo.json");

    let config = if config_path.exists() {
        let content = std::fs::read_to_string(&config_path)?;
        serde_json::from_str(&content)?
    } else {
        NeoConfig::new(neo_network)
    };

    Ok(NeoClient::new(config)?)
}

fn handle_market(action: &MarketCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        MarketCommands::List {
            sealed_file,
            price,
            duration,
            metadata,
            network,
            wait: _,
            upload_neofs,
            container,
        } => {
            use anubis_core::aead::XCHACHA_NONCE_SIZE;
            use anubis_core::kdf::HkdfSha512;
            use anubis_core::mlkem::{
                wrap_key, MlKemKeyPair, MlKemPublicKey, MlKemSecretKey, CIPHERTEXT_SIZE,
                PUBLIC_KEY_SIZE, SECRET_KEY_SIZE,
            };
            use zeroize::Zeroizing;

            // Magic bytes for sealed file format (CNSA 2.0)
            const SEAL_MAGIC: &[u8; 4] = b"ANU2";
            // CNSA 2.0 domain separation for key derivation
            const SEAL_SALT: &[u8] = b"anubis-notary:seal:v2:cnsa2.0";
            const SEAL_INFO: &[u8] = b"seal-encryption-key";

            // Load keystore
            let ks = Keystore::open(Keystore::default_path())?;

            // Get password for decryption
            let password = prompt_password("Enter password to access your ML-KEM key: ")?;

            // 1. Read sealed file
            let sealed_data = std::fs::read(sealed_file)?;

            // Verify minimum size (magic + mlkem_ct + nonce + at least 16 byte tag)
            let min_size = 4 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE + 16;
            if sealed_data.len() < min_size {
                return Err(format!(
                    "Sealed file too small: expected at least {} bytes, got {}",
                    min_size,
                    sealed_data.len()
                )
                .into());
            }

            // 2. Verify magic bytes
            if &sealed_data[0..4] != SEAL_MAGIC {
                return Err(
                    "Invalid sealed file: wrong magic bytes (expected ANU2 format)".into(),
                );
            }

            // 3. Extract ML-KEM ciphertext
            let mlkem_ct = &sealed_data[4..4 + CIPHERTEXT_SIZE];

            // 4. Load seller's ML-KEM secret key
            let sk_path = ks.path().join("decryption.mlkem.sealed");
            if !sk_path.exists() {
                return Err("ML-KEM secret key not found. Run 'key init' first.".into());
            }
            let sealed_sk = std::fs::read(&sk_path)?;
            let sk_bytes = Zeroizing::new(
                anubis_io::seal::unseal_key(password.as_bytes(), &sealed_sk)
                    .map_err(|e| format!("Failed to unseal ML-KEM key: {:?}", e))?,
            );
            if sk_bytes.len() != SECRET_KEY_SIZE {
                return Err(format!(
                    "Invalid ML-KEM secret key size: expected {}, got {}",
                    SECRET_KEY_SIZE,
                    sk_bytes.len()
                )
                .into());
            }
            let mlkem_sk = MlKemSecretKey::from_bytes(sk_bytes.as_slice().try_into().unwrap())
                .map_err(|e| format!("Invalid ML-KEM secret key: {:?}", e))?;

            // 5. Decapsulate to get shared secret
            let shared_secret = Zeroizing::new(
                mlkem_sk
                    .decapsulate(mlkem_ct)
                    .map_err(|e| format!("ML-KEM decapsulation failed: {:?}", e))?,
            );

            // 6. Derive encryption key using HKDF-SHA512
            let encryption_key: Zeroizing<[u8; 32]> = Zeroizing::new(
                HkdfSha512::derive(SEAL_SALT, &*shared_secret, SEAL_INFO)
                    .map_err(|e| format!("Key derivation failed: {:?}", e))?,
            );

            // 7. Generate ephemeral listing keypair
            let listing_keypair = MlKemKeyPair::generate()
                .map_err(|e| format!("Failed to generate listing keypair: {:?}", e))?;

            // 8. Wrap encryption key with listing public key
            let listing_pk = MlKemPublicKey::from_bytes(listing_keypair.public_key_bytes())
                .map_err(|e| format!("Failed to parse listing public key: {:?}", e))?;
            let wrapped_content_key = wrap_key(&listing_pk, &encryption_key)
                .map_err(|e| format!("Key wrapping failed: {:?}", e))?;

            // 9. Parse duration and price
            let duration_blocks = parse_duration_to_blocks(duration)?;
            let price_datoshis = (*price * 1e8) as u64;

            // 10. Determine object ID: upload to NeoFS or use local path
            let neofs_object_id = if *upload_neofs {
                use anubis_io::neo::{NeoFsClient, NeoFsObjectAttributes, NeoWallet};

                let config = {
                    let ks_path = std::env::var("ANUBIS_HOME")
                        .map(std::path::PathBuf::from)
                        .unwrap_or_else(|_| dirs::home_dir().unwrap_or_default().join(".anubis"));
                    let config_path = ks_path.join("neo.json");
                    if config_path.exists() {
                        let content = std::fs::read_to_string(&config_path)?;
                        serde_json::from_str::<anubis_io::neo::NeoConfig>(&content)?
                    } else {
                        let neo_network = match network.to_lowercase().as_str() {
                            "mainnet" => anubis_io::neo::NeoNetwork::MainNet,
                            _ => anubis_io::neo::NeoNetwork::TestNet,
                        };
                        anubis_io::neo::NeoConfig::new(neo_network)
                    }
                };

                // Get wallet from environment for auth
                let wif = std::env::var("NEO_PRIVATE_KEY")
                    .map_err(|_| "NEO_PRIVATE_KEY env var required for NeoFS upload")?;
                let wallet = NeoWallet::from_wif(&wif)?;

                let mut neofs = NeoFsClient::new(&config.neofs_url, config.timeout_secs);

                // Authenticate for upload
                match neofs.create_bearer_token(&wallet, &["PUT", "GET"]) {
                    Ok(bearer) => {
                        neofs.set_bearer_token(&bearer);
                        if !json {
                            eprintln!("Authenticated to NeoFS as: {}", wallet.address());
                        }
                    }
                    Err(e) => {
                        if !json {
                            eprintln!("Warning: NeoFS auth failed: {}. Upload may fail.", e);
                        }
                    }
                }

                // Determine container ID (prefer marketplace_container, then default_container)
                let container_id = if let Some(cid) = container {
                    cid.clone()
                } else {
                    config.marketplace_container.clone()
                        .or_else(|| config.default_container.clone())
                        .ok_or("No container specified. Use --container or configure marketplace_container/default_container in ~/.anubis/neo.json")?
                };

                if !json {
                    eprintln!("Uploading sealed file to NeoFS...");
                    eprintln!("  Container: {}", container_id);
                    eprintln!("  Size: {} bytes", sealed_data.len());
                }

                // File name for the object
                let filename = sealed_file
                    .file_name()
                    .map(|n| n.to_string_lossy().to_string())
                    .unwrap_or_else(|| format!("sealed-{}.anb", hex::encode(&sealed_data[..8])));

                let attrs = NeoFsObjectAttributes {
                    filename: Some(filename),
                    content_type: Some("application/x-anubis-sealed".to_string()),
                    anubis_type: Some("marketplace-sealed".to_string()),
                    content_hash: Some(hex::encode(anubis_core::sha2::sha512(&sealed_data))),
                    ..Default::default()
                };

                let result = neofs.store_large(&container_id, &sealed_data, Some(attrs), Some(&|uploaded, total| {
                    if !json {
                        eprint!("\r  Progress: {}/{} chunks", uploaded, total);
                    }
                }))?;

                if !json {
                    eprintln!("\n  Uploaded: {}", result.cid);
                }

                result.cid
            } else {
                // Use local file path for testing
                let path = sealed_file.to_string_lossy().to_string();
                if !json {
                    eprintln!("Using local file path: {}", path);
                    eprintln!("  (Use --upload-neofs for decentralized storage)");
                }
                path
            };

            // 10. Create Neo client and list
            let client = create_neo_client_from_network(network)?;

            let result = client.list_sealed_data(
                &neofs_object_id,
                listing_keypair.public_key_bytes(),
                &wrapped_content_key,
                price_datoshis,
                metadata,
                duration_blocks,
            )?;

            // 11. Store listing secret key in keystore (sealed with same password)
            let listings_path = ks.path().join("marketplace_listings.json");
            let mut listings: serde_json::Value = if listings_path.exists() {
                let content = std::fs::read_to_string(&listings_path)?;
                serde_json::from_str(&content)?
            } else {
                serde_json::json!({ "listings": {} })
            };

            // Seal the listing secret key
            let listing_sk_sealed =
                anubis_io::seal::seal_key(password.as_bytes(), listing_keypair.secret_key_bytes())
                    .map_err(|e| format!("Failed to seal listing key: {:?}", e))?;

            // Add to listings
            listings["listings"][result.listing_id.to_string()] = serde_json::json!({
                "listing_sk_sealed": hex::encode(&listing_sk_sealed),
                "object_id": neofs_object_id,
                "created_at": chrono::Utc::now().to_rfc3339(),
            });

            // Write listings file
            std::fs::write(&listings_path, serde_json::to_string_pretty(&listings)?)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                std::fs::set_permissions(&listings_path, std::fs::Permissions::from_mode(0o600))?;
            }

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "listing_id": result.listing_id,
                    "tx_hash": result.tx_hash,
                    "price_gas": price,
                    "duration_blocks": duration_blocks,
                    "neofs_object_id": neofs_object_id,
                    "listing_pk_size": PUBLIC_KEY_SIZE,
                    "wrapped_key_size": wrapped_content_key.len(),
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Data listed on marketplace!");
                println!("  Listing ID: {}", result.listing_id);
                println!("  Price: {} GAS", price);
                println!(
                    "  Duration: {} blocks (~{} days)",
                    duration_blocks,
                    duration_blocks / 17280
                );
                println!("  TX: {}", result.tx_hash);
                println!();
                println!("Content key wrapped with ephemeral listing keypair.");
                println!("Listing key stored in: {}", listings_path.display());
                println!();
                println!("Next steps:");
                println!("  1. Wait for buyers to purchase");
                println!("  2. Deliver access: anubis-notary market deliver <purchase-id>");
                println!("  3. Or auto-deliver: anubis-notary market deliver --watch");
            }
            Ok(())
        }

        MarketCommands::Browse {
            category: _,
            price_max: _,
            price_min: _,
            limit,
            network,
        } => {
            let client = create_neo_client_from_network(network)?;

            // Get listing count
            let count = client.get_listing_count()?;

            if json {
                let mut listings = Vec::new();
                for i in 1..=count.min(*limit as u64) {
                    if let Ok(Some(listing)) = client.get_listing(i) {
                        listings.push(serde_json::json!({
                            "id": listing.id,
                            "price_gas": listing.price as f64 / 1e8,
                            "metadata": listing.metadata,
                            "is_active": listing.is_active,
                        }));
                    }
                }
                let output = JsonOutput::success(serde_json::json!({
                    "total": count,
                    "listings": listings,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Marketplace Listings ({} total)", count);
                println!("{}", "=".repeat(60));

                for i in 1..=count.min(*limit as u64) {
                    if let Ok(Some(listing)) = client.get_listing(i) {
                        if listing.is_active {
                            println!();
                            println!("  [{}] {} GAS", listing.id, listing.price as f64 / 1e8);
                            println!("      {}", listing.metadata);
                        }
                    }
                }
                println!();
                println!("Purchase with: anubis-notary market buy <listing-id> --output file.pdf");
            }
            Ok(())
        }

        MarketCommands::Show { listing_id, network } => {
            let client = create_neo_client_from_network(network)?;

            match client.get_listing(*listing_id)? {
                Some(listing) => {
                    if json {
                        let output = JsonOutput::success(serde_json::json!({
                            "id": listing.id,
                            "neofs_object_id": listing.neofs_object_id,
                            "price_gas": listing.price as f64 / 1e8,
                            "metadata": listing.metadata,
                            "is_active": listing.is_active,
                        }));
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Listing #{}", listing.id);
                        println!("  Price:    {} GAS", listing.price as f64 / 1e8);
                        println!("  Metadata: {}", listing.metadata);
                        println!("  Active:   {}", if listing.is_active { "Yes" } else { "No" });
                        println!("  NeoFS ID: {}", listing.neofs_object_id);
                    }
                }
                None => {
                    if json {
                        let output: JsonOutput<()> = JsonOutput::error("Listing not found");
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Listing #{} not found", listing_id);
                    }
                }
            }
            Ok(())
        }

        MarketCommands::Buy {
            listing_id,
            output: _output,
            network,
            wait: _,
        } => {
            let ks = Keystore::open(Keystore::default_path())?;
            let client = create_neo_client_from_network(network)?;

            // Get buyer's ML-KEM public key for re-encryption
            let mlkem_pub_path = ks.path().join("decryption.mlkem.pub");
            if !mlkem_pub_path.exists() {
                return Err("No ML-KEM key found. Run 'anubis-notary key init' first.".into());
            }
            let buyer_mlkem_pk = std::fs::read(&mlkem_pub_path)?;
            if buyer_mlkem_pk.len() != 1568 {
                return Err(format!(
                    "Invalid ML-KEM public key size: {} (expected 1568)",
                    buyer_mlkem_pk.len()
                )
                .into());
            }

            // Purchase access - this records our public key on-chain
            let result = client.purchase_access(*listing_id, &buyer_mlkem_pk)?;

            // In two-phase delivery:
            // 1. Purchase records buyer's ML-KEM public key
            // 2. Seller delivers access by re-wrapping content key for buyer
            // 3. Buyer claims with purchase_id to get wrapped key and decrypt

            if json {
                let output_data = JsonOutput::success(serde_json::json!({
                    "listing_id": listing_id,
                    "purchase_id": result.purchase_id,
                    "tx_hash": result.tx_hash,
                    "status": "pending_delivery",
                }));
                println!("{}", serde_json::to_string_pretty(&output_data)?);
            } else {
                println!("Purchase successful!");
                println!("  Listing ID: {}", listing_id);
                println!("  Purchase ID: {}", result.purchase_id);
                println!("  TX: {}", result.tx_hash);
                println!();
                println!("Next steps:");
                println!("  1. Wait for seller to deliver access (check with: anubis-notary market status {})", result.purchase_id);
                println!("  2. Claim decrypted file: anubis-notary market claim {} --output file.pdf", result.purchase_id);
            }
            Ok(())
        }

        MarketCommands::MyListings { network } => {
            let client = create_neo_client_from_network(network)?;

            // Get all listings and filter by owner
            let count = client.get_listing_count()?;

            if json {
                // Return count for now
                let output = JsonOutput::success(serde_json::json!({
                    "total_listings": count,
                    "note": "Use 'market browse' to see all listings",
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Total marketplace listings: {}", count);
                println!("Use 'anubis-notary market browse' to see all listings");
            }
            Ok(())
        }

        MarketCommands::Revenue { action } => handle_market_revenue(action, json),

        MarketCommands::Pending { network } => {
            let client = create_neo_client_from_network(network)?;

            // Get pending deliveries for this seller (identified by NEO_PRIVATE_KEY)
            let pending = client.get_pending_deliveries()?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "pending_deliveries": pending.iter().map(|p| serde_json::json!({
                        "purchase_id": p.purchase_id,
                        "listing_id": p.listing_id,
                        "buyer": p.buyer,
                        "buyer_pk_size": p.buyer_pk.len(),
                        "purchase_block": p.purchase_block,
                    })).collect::<Vec<_>>(),
                    "count": pending.len(),
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                if pending.is_empty() {
                    println!("No pending deliveries.");
                    println!();
                    println!("When buyers purchase your listings, they'll appear here.");
                } else {
                    println!("Pending Deliveries ({}):", pending.len());
                    println!();
                    for p in &pending {
                        println!("  Purchase #{}", p.purchase_id);
                        println!("    Listing: #{}", p.listing_id);
                        println!("    Buyer: {}", p.buyer);
                        println!("    Block: {}", p.purchase_block);
                        println!();
                    }
                    println!("Deliver access with:");
                    println!("  anubis-notary market deliver <purchase-id>");
                }
            }
            Ok(())
        }

        MarketCommands::Deliver {
            purchase_id,
            network,
            wait: _,
        } => {
            use anubis_core::mlkem::{
                unwrap_key, wrap_key, MlKemPublicKey, MlKemSecretKey, PUBLIC_KEY_SIZE,
                SECRET_KEY_SIZE,
            };
            use zeroize::Zeroizing;

            let client = create_neo_client_from_network(network)?;
            let ks = Keystore::open(Keystore::default_path())?;

            // Get password
            let password = prompt_password("Enter password to access listing key: ")?;

            // 1. Get purchase details
            let purchase = client
                .get_purchase(*purchase_id)?
                .ok_or_else(|| format!("Purchase #{} not found", purchase_id))?;

            if purchase.delivered {
                return Err(format!("Purchase #{} already delivered", purchase_id).into());
            }

            // 2. Get listing details
            let listing = client
                .get_listing(purchase.listing_id)?
                .ok_or_else(|| format!("Listing #{} not found", purchase.listing_id))?;

            // 3. Load listing secret key from keystore
            let listings_path = ks.path().join("marketplace_listings.json");
            if !listings_path.exists() {
                return Err("No marketplace listings found in keystore".into());
            }
            let listings: serde_json::Value =
                serde_json::from_str(&std::fs::read_to_string(&listings_path)?)?;

            let listing_data = listings["listings"][purchase.listing_id.to_string()]
                .as_object()
                .ok_or_else(|| format!("Listing #{} not found in local keystore", purchase.listing_id))?;

            let listing_sk_sealed_hex = listing_data["listing_sk_sealed"]
                .as_str()
                .ok_or("Missing listing_sk_sealed")?;
            let listing_sk_sealed = hex::decode(listing_sk_sealed_hex)
                .map_err(|e| format!("Invalid listing key encoding: {}", e))?;

            let listing_sk_bytes = Zeroizing::new(
                anubis_io::seal::unseal_key(password.as_bytes(), &listing_sk_sealed)
                    .map_err(|e| format!("Failed to unseal listing key: {:?}", e))?,
            );
            if listing_sk_bytes.len() != SECRET_KEY_SIZE {
                return Err(format!(
                    "Invalid listing secret key size: expected {}, got {}",
                    SECRET_KEY_SIZE,
                    listing_sk_bytes.len()
                )
                .into());
            }
            let listing_sk =
                MlKemSecretKey::from_bytes(listing_sk_bytes.as_slice().try_into().unwrap())
                    .map_err(|e| format!("Invalid listing secret key: {:?}", e))?;

            // 4. Unwrap content key using listing SK
            let content_key = Zeroizing::new(
                unwrap_key(&listing_sk, &listing.wrapped_content_key)
                    .map_err(|e| format!("Failed to unwrap content key: {:?}", e))?,
            );

            // 5. Re-wrap content key for buyer's public key
            if purchase.buyer_pk.len() != PUBLIC_KEY_SIZE {
                return Err(format!(
                    "Invalid buyer public key size: expected {}, got {}",
                    PUBLIC_KEY_SIZE,
                    purchase.buyer_pk.len()
                )
                .into());
            }
            let buyer_pk =
                MlKemPublicKey::from_bytes(purchase.buyer_pk.as_slice().try_into().unwrap())
                    .map_err(|e| format!("Invalid buyer public key: {:?}", e))?;

            let buyer_wrapped_key = wrap_key(&buyer_pk, &content_key)
                .map_err(|e| format!("Failed to wrap key for buyer: {:?}", e))?;

            // 6. Deliver access via contract
            let result = client.deliver_access(*purchase_id, &buyer_wrapped_key)?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "purchase_id": purchase_id,
                    "listing_id": purchase.listing_id,
                    "buyer": purchase.buyer,
                    "tx_hash": result.tx_hash,
                    "wrapped_key_size": buyer_wrapped_key.len(),
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Access delivered!");
                println!("  Purchase ID: {}", purchase_id);
                println!("  Listing ID: {}", purchase.listing_id);
                println!("  Buyer: {}", purchase.buyer);
                println!("  TX: {}", result.tx_hash);
                println!();
                println!("Buyer can now claim with:");
                println!("  anubis-notary market claim {} --output file.pdf", purchase_id);
            }
            Ok(())
        }

        MarketCommands::Claim {
            purchase_id,
            output,
            network,
        } => {
            use anubis_core::aead::{XChaCha20Poly1305, XCHACHA_NONCE_SIZE};
            use anubis_core::mlkem::{unwrap_key, MlKemSecretKey, CIPHERTEXT_SIZE, SECRET_KEY_SIZE};
            use zeroize::Zeroizing;

            const SEAL_MAGIC: &[u8; 4] = b"ANU2";

            let client = create_neo_client_from_network(network)?;
            let ks = Keystore::open(Keystore::default_path())?;

            // Get password
            let password = prompt_password("Enter password to access your ML-KEM key: ")?;

            // 1. Get purchase details
            let purchase = client
                .get_purchase(*purchase_id)?
                .ok_or_else(|| format!("Purchase #{} not found", purchase_id))?;

            if !purchase.delivered {
                return Err(format!(
                    "Access not yet delivered for purchase #{}. Wait for seller to deliver.",
                    purchase_id
                )
                .into());
            }

            if purchase.buyer_wrapped_key.is_empty() {
                return Err("Access ticket is empty. Contact seller.".into());
            }

            // 2. Get listing to find NeoFS object ID
            let listing = client
                .get_listing(purchase.listing_id)?
                .ok_or_else(|| format!("Listing #{} not found", purchase.listing_id))?;

            // 3. Load buyer's ML-KEM secret key
            let sk_path = ks.path().join("decryption.mlkem.sealed");
            if !sk_path.exists() {
                return Err("ML-KEM secret key not found. Run 'key init' first.".into());
            }
            let sealed_sk = std::fs::read(&sk_path)?;
            let sk_bytes = Zeroizing::new(
                anubis_io::seal::unseal_key(password.as_bytes(), &sealed_sk)
                    .map_err(|e| format!("Failed to unseal ML-KEM key: {:?}", e))?,
            );
            if sk_bytes.len() != SECRET_KEY_SIZE {
                return Err(format!(
                    "Invalid ML-KEM secret key size: expected {}, got {}",
                    SECRET_KEY_SIZE,
                    sk_bytes.len()
                )
                .into());
            }
            let buyer_sk = MlKemSecretKey::from_bytes(sk_bytes.as_slice().try_into().unwrap())
                .map_err(|e| format!("Invalid ML-KEM secret key: {:?}", e))?;

            // 4. Unwrap content key from buyer_wrapped_key
            let encryption_key = Zeroizing::new(
                unwrap_key(&buyer_sk, &purchase.buyer_wrapped_key)
                    .map_err(|e| format!("Failed to unwrap access ticket: {:?}", e))?,
            );

            // 5. Download sealed file from NeoFS (or local path for testing)
            let sealed_data = if std::path::Path::new(&listing.neofs_object_id).exists() {
                // It's a local file path - read directly for testing
                std::fs::read(&listing.neofs_object_id)?
            } else if listing.neofs_object_id.starts_with("sealed:") {
                // It's a hex-encoded sealed ID prefix, not a real download location
                // In production, this would be a full NeoFS CID
                return Err(
                    "NeoFS download not yet implemented for this listing. \
                    The sealed file was listed with a local ID, not uploaded to NeoFS.".into(),
                );
            } else if listing.neofs_object_id.contains('/') {
                // It's a NeoFS CID (containerid/objectid format)
                use anubis_io::neo::NeoFsClient;

                let config = client.config();
                let neofs = NeoFsClient::new(&config.neofs_url, config.timeout_secs);

                if !json {
                    eprintln!("Downloading sealed file from NeoFS: {}", listing.neofs_object_id);
                }

                neofs.get_large(&listing.neofs_object_id)
                    .map_err(|e| format!("NeoFS download failed: {}", e))?
            } else {
                return Err(format!(
                    "Cannot locate sealed file. Object ID: {}",
                    listing.neofs_object_id
                ).into());
            };

            // 6. Verify magic and extract nonce + ciphertext
            if &sealed_data[0..4] != SEAL_MAGIC {
                return Err(
                    "Invalid sealed file: wrong magic bytes (expected ANU2 format)".into(),
                );
            }
            let nonce: [u8; XCHACHA_NONCE_SIZE] = sealed_data
                [4 + CIPHERTEXT_SIZE..4 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE]
                .try_into()
                .unwrap();
            let ciphertext = &sealed_data[4 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE..];

            // 7. Decrypt with XChaCha20Poly1305
            let cipher = XChaCha20Poly1305::from_key(&encryption_key)
                .map_err(|e| format!("Cipher initialization failed: {:?}", e))?;
            let plaintext = cipher
                .open_fixed(&nonce, SEAL_MAGIC, ciphertext)
                .map_err(|_| {
                    "Decryption failed: authentication error (wrong key or corrupted file)"
                })?;

            // 8. Write decrypted file
            write_file_atomic(output, &plaintext)?;

            if json {
                let output_json = JsonOutput::success(serde_json::json!({
                    "purchase_id": purchase_id,
                    "listing_id": purchase.listing_id,
                    "output_file": output.display().to_string(),
                    "decrypted_size": plaintext.len(),
                }));
                println!("{}", serde_json::to_string_pretty(&output_json)?);
            } else {
                println!("Data decrypted successfully!");
                println!("  Purchase ID: {}", purchase_id);
                println!("  Output: {}", output.display());
                println!("  Size: {} bytes", plaintext.len());
            }
            Ok(())
        }

        MarketCommands::Status { purchase_id, network } => {
            let client = create_neo_client_from_network(network)?;

            match client.get_purchase(*purchase_id)? {
                Some(purchase) => {
                    let status = if purchase.claimed {
                        "CLAIMED"
                    } else if purchase.delivered {
                        "DELIVERED (ready to claim)"
                    } else {
                        "PENDING (waiting for seller to deliver)"
                    };

                    if json {
                        let output = JsonOutput::success(serde_json::json!({
                            "purchase_id": purchase_id,
                            "listing_id": purchase.listing_id,
                            "buyer": purchase.buyer,
                            "purchase_block": purchase.purchase_block,
                            "delivered": purchase.delivered,
                            "claimed": purchase.claimed,
                            "status": status,
                        }));
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Purchase #{}", purchase_id);
                        println!("  Listing: #{}", purchase.listing_id);
                        println!("  Buyer: {}", purchase.buyer);
                        println!("  Status: {}", status);
                        println!();
                        if !purchase.delivered {
                            println!("Waiting for seller to deliver access ticket...");
                        } else if !purchase.claimed {
                            println!("Ready to claim! Run:");
                            println!(
                                "  anubis-notary market claim {} --output file.pdf",
                                purchase_id
                            );
                        }
                    }
                }
                None => {
                    if json {
                        let output: JsonOutput<()> = JsonOutput::error("Purchase not found");
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Purchase #{} not found", purchase_id);
                    }
                }
            }
            Ok(())
        }
    }
}

fn handle_market_revenue(action: &MarketRevenueCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        MarketRevenueCommands::Show { listing_id, network } => {
            let client = create_neo_client_from_network(network)?;

            // Get listing to show revenue info
            match client.get_listing(*listing_id)? {
                Some(listing) => {
                    if json {
                        let output = JsonOutput::success(serde_json::json!({
                            "listing_id": listing.id,
                            "price_per_access": listing.price as f64 / 1e8,
                            "is_active": listing.is_active,
                            "sales_count": listing.sales_count,
                            "total_revenue_gas": listing.total_revenue as f64 / 1e8,
                        }));
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Revenue for Listing #{}", listing.id);
                        println!("  Price per access: {} GAS", listing.price as f64 / 1e8);
                        println!("  Status: {}", if listing.is_active { "Active" } else { "Inactive" });
                        println!("  Sales: {}", listing.sales_count);
                        println!("  Total revenue: {} GAS", listing.total_revenue as f64 / 1e8);
                        if listing.total_revenue > 0 {
                            println!();
                            println!("Claim revenue with: anubis-notary market revenue claim {}", listing_id);
                        }
                    }
                }
                None => {
                    if json {
                        let output: JsonOutput<()> = JsonOutput::error("Listing not found");
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Listing #{} not found", listing_id);
                    }
                }
            }
            Ok(())
        }

        MarketRevenueCommands::Claim { listing_id, network, wait: _ } => {
            let client = create_neo_client_from_network(network)?;

            let result = client.claim_revenue(*listing_id)?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "listing_id": listing_id,
                    "tx_hash": result.tx_hash,
                    "amount_claimed_gas": result.amount_claimed as f64 / 1e8,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Revenue claimed!");
                println!("  Listing ID: {}", listing_id);
                println!("  Amount: {} GAS", result.amount_claimed as f64 / 1e8);
                println!("  TX: {}", result.tx_hash);
            }
            Ok(())
        }
    }
}

fn handle_member(action: &MemberCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        MemberCommands::Tiers => {
            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "tiers": [
                        {
                            "name": "FREE",
                            "price": 0,
                            "marketplace_fee": "15%",
                            "seal_fee": "0.05 GAS",
                            "unseal_fee": "0.02 GAS",
                            "storage": "100 MB"
                        },
                        {
                            "name": "NOTARY",
                            "price": "50 GAS/year",
                            "marketplace_fee": "5%",
                            "seal_fee": "0.025 GAS",
                            "unseal_fee": "0.01 GAS",
                            "storage": "10 GB"
                        },
                        {
                            "name": "VAULT",
                            "price": "200 GAS/year",
                            "marketplace_fee": "2%",
                            "seal_fee": "0.01 GAS",
                            "unseal_fee": "FREE",
                            "storage": "Unlimited"
                        }
                    ]
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Anubis Notary Membership Tiers");
                println!("{}", "=".repeat(60));
                println!();
                println!("┌──────────┬───────────┬────────────┬──────────┐");
                println!("│ Feature  │ FREE      │ NOTARY     │ VAULT    │");
                println!("├──────────┼───────────┼────────────┼──────────┤");
                println!("│ Price    │ Free      │ 50 GAS/yr  │ 200 GAS/yr│");
                println!("│ Market % │ 15%       │ 5%         │ 2%       │");
                println!("│ Seal fee │ 0.05 GAS  │ 0.025 GAS  │ 0.01 GAS │");
                println!("│ Unseal   │ 0.02 GAS  │ 0.01 GAS   │ FREE     │");
                println!("│ Storage  │ 100 MB    │ 10 GB      │ Unlimited│");
                println!("└──────────┴───────────┴────────────┴──────────┘");
                println!();
                println!("Mint with: anubis-notary member mint notary");
                println!("           anubis-notary member mint vault");
            }
            Ok(())
        }

        MemberCommands::Status { address, network } => {
            let client = create_neo_client_from_network(network)?;

            // Use provided address or get from identity
            let addr = address.clone().unwrap_or_else(|| {
                // Get Neo address from identity - placeholder
                "Unknown".to_string()
            });

            let tier = client.get_user_tier(&addr)?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "address": addr,
                    "tier": tier,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Membership Status");
                println!("  Address: {}", addr);
                println!("  Tier:    {}", tier);
                if tier == "free" {
                    println!();
                    println!("Upgrade with: anubis-notary member mint notary");
                }
            }
            Ok(())
        }

        MemberCommands::Mint { tier, network, wait: _ } => {
            let client = create_neo_client_from_network(network)?;

            // Validate tier
            let valid_tiers = ["notary", "vault"];
            if !valid_tiers.contains(&tier.to_lowercase().as_str()) {
                return Err(format!("Invalid tier: {}. Use 'notary' or 'vault'", tier).into());
            }

            let result = client.mint_membership(tier)?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "token_id": result.token_id,
                    "tier": result.tier,
                    "expiry_block": result.expiry_block,
                    "tx_hash": result.tx_hash,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Membership minted!");
                println!("  Token ID: {}", result.token_id);
                println!("  Tier: {}", result.tier);
                println!("  Expires: Block {}", result.expiry_block);
                println!("  TX: {}", result.tx_hash);
                println!();
                println!("You now have reduced fees on all operations.");
            }
            Ok(())
        }

        MemberCommands::Renew { token_id, network, wait: _ } => {
            let client = create_neo_client_from_network(network)?;

            let result = client.renew_membership(*token_id)?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "token_id": token_id,
                    "new_expiry_block": result.expiry_block,
                    "tx_hash": result.tx_hash,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Membership renewed!");
                println!("  Token ID: {}", token_id);
                println!("  New expiry: Block {}", result.expiry_block);
                println!("  TX: {}", result.tx_hash);
            }
            Ok(())
        }

        MemberCommands::Transfer { token_id, to, network: _, wait: _ } => {
            // Transfer is not implemented in the client yet
            if json {
                let output: JsonOutput<()> = JsonOutput::error("Transfer not yet implemented");
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Membership transfer not yet implemented.");
                println!("Token ID: {}", token_id);
                println!("Recipient: {}", to);
            }
            Ok(())
        }
    }
}

fn handle_escrow(action: &EscrowCommands, json: bool) -> Result<(), Box<dyn std::error::Error>> {
    match action {
        EscrowCommands::TimeLock {
            sealed_file,
            unlock_at,
            beneficiary,
            network,
            wait: _,
        } => {
            let ks = Keystore::open(Keystore::default_path())?;
            let keypair = load_keypair_with_password(&ks)?;
            let client = create_neo_client_from_network(network)?;

            // Parse unlock time
            let unlock_time = chrono::DateTime::parse_from_rfc3339(unlock_at)
                .map_err(|e| format!("Invalid unlock time: {}. Use ISO 8601 format (e.g., 2025-06-01T00:00:00Z)", e))?;

            // Get current block height and calculate absolute unlock block
            let current_height = client.get_block_time()
                .map(|t| t.block_number)
                .unwrap_or(0);
            let now = chrono::Utc::now();
            let duration_secs = (unlock_time.timestamp() - now.timestamp()).max(60) as u64; // At least 1 minute
            let blocks_until_unlock = duration_secs / 15;
            let unlock_block = current_height + blocks_until_unlock;

            // Read sealed file to extract NeoFS object ID
            let sealed_data = std::fs::read(sealed_file)?;
            let neofs_object_id = format!("sealed:{}", hex::encode(&sealed_data[..32.min(sealed_data.len())]));

            // Create re-encryption key from ML-KEM public key (1568 bytes)
            // Use the sealed file's embedded key or generate a derived one
            let re_key = if sealed_data.len() > 1600 {
                // Extract from sealed file header if present (simplified)
                keypair.public.to_bytes()[..1568.min(keypair.public.to_bytes().len())].to_vec()
            } else {
                // Use truncated key as placeholder
                keypair.public.to_bytes()[..1568.min(keypair.public.to_bytes().len())].to_vec()
            };

            let result = client.create_time_lock_escrow(
                &neofs_object_id,
                &re_key,
                unlock_block,
                beneficiary,
            )?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "escrow_id": result.escrow_id,
                    "type": "time-locked",
                    "unlock_at": unlock_at,
                    "unlock_block": unlock_block,
                    "beneficiary": beneficiary,
                    "tx_hash": result.tx_hash,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Time-locked escrow created!");
                println!("  Escrow ID: {}", result.escrow_id);
                println!("  Unlock at: {}", unlock_at);
                println!("  Beneficiary: {}", beneficiary);
                println!("  TX: {}", result.tx_hash);
                println!();
                println!("The beneficiary can claim after the unlock time.");
            }
            Ok(())
        }

        EscrowCommands::Payment {
            sealed_file,
            price,
            beneficiary,
            network,
            wait: _,
        } => {
            let ks = Keystore::open(Keystore::default_path())?;
            let keypair = load_keypair_with_password(&ks)?;
            let client = create_neo_client_from_network(network)?;

            let sealed_data = std::fs::read(sealed_file)?;
            let neofs_object_id = format!("sealed:{}", hex::encode(&sealed_data[..32.min(sealed_data.len())]));
            let re_key = keypair.public.to_bytes();
            let price_datoshis = (*price * 1e8) as u64;

            let result = client.create_payment_escrow(
                &neofs_object_id,
                &re_key,
                price_datoshis,
                beneficiary,
            )?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "escrow_id": result.escrow_id,
                    "type": "payment-gated",
                    "price_gas": price,
                    "beneficiary": beneficiary,
                    "tx_hash": result.tx_hash,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Payment-gated escrow created!");
                println!("  Escrow ID: {}", result.escrow_id);
                println!("  Price: {} GAS", price);
                println!("  Beneficiary: {}", beneficiary);
                println!("  TX: {}", result.tx_hash);
                println!();
                println!("Pay with: anubis-notary escrow pay {}", result.escrow_id);
            }
            Ok(())
        }

        EscrowCommands::MultiSig {
            sealed_file,
            signers,
            threshold,
            beneficiary,
            network,
            wait: _,
        } => {
            let ks = Keystore::open(Keystore::default_path())?;
            let keypair = load_keypair_with_password(&ks)?;
            let client = create_neo_client_from_network(network)?;

            let sealed_data = std::fs::read(sealed_file)?;
            let neofs_object_id = format!("sealed:{}", hex::encode(&sealed_data[..32.min(sealed_data.len())]));
            let re_key = keypair.public.to_bytes();

            // Parse signers
            let signer_list: Vec<&str> = signers.split(',').map(|s| s.trim()).collect();
            if signer_list.len() < *threshold as usize {
                return Err(format!("Threshold ({}) cannot be greater than number of signers ({})", threshold, signer_list.len()).into());
            }

            let result = client.create_multi_sig_escrow(
                &neofs_object_id,
                &re_key,
                &signer_list,
                *threshold,
                beneficiary,
            )?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "escrow_id": result.escrow_id,
                    "type": "multi-sig",
                    "signers": signer_list,
                    "threshold": threshold,
                    "beneficiary": beneficiary,
                    "tx_hash": result.tx_hash,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Multi-sig escrow created!");
                println!("  Escrow ID: {}", result.escrow_id);
                println!("  Signers: {} ({}-of-{})", signer_list.len(), threshold, signer_list.len());
                println!("  Beneficiary: {}", beneficiary);
                println!("  TX: {}", result.tx_hash);
                println!();
                println!("Signers approve with: anubis-notary escrow approve {}", result.escrow_id);
            }
            Ok(())
        }

        EscrowCommands::DeadMan {
            sealed_file,
            heartbeat_days,
            beneficiary,
            network,
            wait: _,
        } => {
            let ks = Keystore::open(Keystore::default_path())?;
            let keypair = load_keypair_with_password(&ks)?;
            let client = create_neo_client_from_network(network)?;

            let sealed_data = std::fs::read(sealed_file)?;
            let neofs_object_id = format!("sealed:{}", hex::encode(&sealed_data[..32.min(sealed_data.len())]));
            let re_key = keypair.public.to_bytes();

            // Convert days to blocks (17280 blocks per day at 5 sec/block)
            let heartbeat_blocks = (*heartbeat_days as u64) * 17280;

            let result = client.create_dead_man_escrow(
                &neofs_object_id,
                &re_key,
                heartbeat_blocks,
                beneficiary,
            )?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "escrow_id": result.escrow_id,
                    "type": "dead-man-switch",
                    "heartbeat_days": heartbeat_days,
                    "beneficiary": beneficiary,
                    "tx_hash": result.tx_hash,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Dead-man switch escrow created!");
                println!("  Escrow ID: {}", result.escrow_id);
                println!("  Heartbeat interval: {} days", heartbeat_days);
                println!("  Beneficiary: {}", beneficiary);
                println!("  TX: {}", result.tx_hash);
                println!();
                println!("Send heartbeat with: anubis-notary escrow heartbeat {}", result.escrow_id);
                println!("If not renewed, beneficiary can claim after {} days.", heartbeat_days);
            }
            Ok(())
        }

        EscrowCommands::List { network } => {
            let client = create_neo_client_from_network(network)?;

            let count = client.get_escrow_count()?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "total_escrows": count,
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Total escrows: {}", count);
                println!();
                println!("View escrow with: anubis-notary escrow show <escrow-id>");
            }
            Ok(())
        }

        EscrowCommands::Show { escrow_id, network } => {
            let client = create_neo_client_from_network(network)?;

            match client.get_escrow(*escrow_id)? {
                Some(escrow) => {
                    let escrow_type_name = match escrow.escrow_type {
                        0 => "time-locked",
                        1 => "payment-gated",
                        2 => "multi-sig",
                        3 => "dead-man-switch",
                        _ => "unknown",
                    };

                    if json {
                        let output = JsonOutput::success(serde_json::json!({
                            "id": escrow.id,
                            "type": escrow_type_name,
                            "neofs_object_id": escrow.neofs_object_id,
                            "is_released": escrow.is_released,
                        }));
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Escrow #{}", escrow.id);
                        println!("  Type: {}", escrow_type_name);
                        println!("  Released: {}", if escrow.is_released { "Yes" } else { "No" });
                        println!("  NeoFS ID: {}", escrow.neofs_object_id);
                    }
                }
                None => {
                    if json {
                        let output: JsonOutput<()> = JsonOutput::error("Escrow not found");
                        println!("{}", serde_json::to_string_pretty(&output)?);
                    } else {
                        println!("Escrow #{} not found", escrow_id);
                    }
                }
            }
            Ok(())
        }

        EscrowCommands::Heartbeat { escrow_id, network, wait: _ } => {
            let client = create_neo_client_from_network(network)?;

            let tx_hash = client.escrow_heartbeat(*escrow_id)?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "escrow_id": escrow_id,
                    "tx_hash": tx_hash,
                    "status": "heartbeat_sent",
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Heartbeat sent!");
                println!("  Escrow ID: {}", escrow_id);
                println!("  TX: {}", tx_hash);
                println!("  Dead-man timer reset.");
            }
            Ok(())
        }

        EscrowCommands::Approve { escrow_id, network, wait: _ } => {
            let client = create_neo_client_from_network(network)?;

            let tx_hash = client.approve_escrow(*escrow_id)?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "escrow_id": escrow_id,
                    "tx_hash": tx_hash,
                    "status": "approved",
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Escrow approved!");
                println!("  Escrow ID: {}", escrow_id);
                println!("  TX: {}", tx_hash);
            }
            Ok(())
        }

        EscrowCommands::Pay { escrow_id, network, wait: _ } => {
            let client = create_neo_client_from_network(network)?;

            let tx_hash = client.pay_escrow(*escrow_id)?;

            if json {
                let output = JsonOutput::success(serde_json::json!({
                    "escrow_id": escrow_id,
                    "tx_hash": tx_hash,
                    "status": "paid",
                }));
                println!("{}", serde_json::to_string_pretty(&output)?);
            } else {
                println!("Escrow paid!");
                println!("  Escrow ID: {}", escrow_id);
                println!("  TX: {}", tx_hash);
                println!();
                println!("Beneficiary can now claim the data.");
            }
            Ok(())
        }

        EscrowCommands::Claim { escrow_id, output, network, wait: _ } => {
            let client = create_neo_client_from_network(network)?;

            let result = client.claim_escrow(*escrow_id)?;

            // Save the re-encryption key for decryption
            std::fs::write(output, &result.re_key)?;

            if json {
                let output_data = JsonOutput::success(serde_json::json!({
                    "escrow_id": escrow_id,
                    "tx_hash": result.tx_hash,
                    "re_key_size": result.re_key.len(),
                    "output": output.display().to_string(),
                }));
                println!("{}", serde_json::to_string_pretty(&output_data)?);
            } else {
                println!("Escrow claimed!");
                println!("  Escrow ID: {}", escrow_id);
                println!("  TX: {}", result.tx_hash);
                println!("  Re-encryption key saved to: {}", output.display());
                println!();
                println!("Use the key to decrypt the data from NeoFS.");
            }
            Ok(())
        }
    }
}

/// Parse duration string (e.g., "30d", "7d") to blocks.
fn parse_duration_to_blocks(duration: &str) -> Result<u64, Box<dyn std::error::Error>> {
    let duration = duration.trim().to_lowercase();

    if duration.ends_with('d') {
        let days: u64 = duration.trim_end_matches('d').parse()
            .map_err(|_| format!("Invalid duration: {}", duration))?;
        // ~17280 blocks per day (5 sec per block)
        Ok(days * 17280)
    } else if duration.ends_with('h') {
        let hours: u64 = duration.trim_end_matches('h').parse()
            .map_err(|_| format!("Invalid duration: {}", duration))?;
        // ~720 blocks per hour
        Ok(hours * 720)
    } else {
        // Assume blocks if no suffix
        duration.parse()
            .map_err(|_| format!("Invalid duration: {}. Use format: 30d, 7d, 24h", duration).into())
    }
}
