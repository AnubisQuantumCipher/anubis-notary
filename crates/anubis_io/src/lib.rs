//! I/O layer for Anubis Notary.
//!
//! This crate provides side-effect operations:
//! - Filesystem operations (atomic writes, path traversal)
//! - Time sources (system clock, RFC 3161 TSA)
//! - Keystore management (Argon2id-sealed key storage)
//! - Key sealing/unsealing with password protection
//! - Mina Protocol integration for blockchain anchoring
//! - Starknet Protocol integration for low-cost STARK anchoring
//!
//! All cryptographic logic is in `anubis_core`; this crate only provides
//! the I/O bridge.
//!
//! # Mina Protocol Integration
//!
//! The [`mina`] module provides integration with the Mina Protocol blockchain
//! for timestamping and anchoring. This enables:
//!
//! - **Merkle Root Anchoring**: Store SHA3-256 Merkle roots on-chain
//! - **Blockchain Timestamps**: Leverage Mina's block timestamps for proof-of-existence
//! - **ZK Verification**: Generate proofs for offline verification
//!
//! ## Architecture
//!
//! Since there is no official Mina Rust SDK, this module uses a Node.js subprocess
//! bridge that interfaces with the o1js library:
//!
//! ```text
//! Rust (anubis_io) → stdin/stdout → Node.js (mina-bridge.js) → o1js → Mina Network
//! ```
//!
//! ## Example
//!
//! ```ignore
//! use anubis_io::mina::{MinaClient, MinaConfig};
//!
//! let config = MinaConfig::devnet("B62q...")
//!     .with_fee(100_000_000);  // 0.1 MINA
//!
//! let mut client = MinaClient::new(config)?;
//! client.connect()?;
//!
//! // Anchor a Merkle root
//! let result = client.anchor(&merkle_root)?;
//! println!("Anchored at block {}", result.block_height);
//! ```

use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use thiserror::Error;

pub use anubis_core;

pub mod anchor;
pub mod batch_queue;
pub mod mina;
pub mod mina_graphql;
pub mod rate_limit;
pub mod seal;
pub mod starknet;

// Mina module exports
pub use mina::{MinaAnchorResult, MinaClient, MinaConfig, MinaError, MinaNetwork, MinaTimeResult};
pub use mina_graphql::MinaGraphQL;
pub use batch_queue::{BatchQueue, BatchQueueEntry};

// Starknet module exports
pub use starknet::{
    sha256_to_poseidon_felt, AnchorRecord as StarknetAnchorRecord, StarknetAnchorResult,
    StarknetBatchResult, StarknetClient, StarknetConfig, StarknetError, StarknetNetwork,
    StarknetTimeResult,
};

pub use rate_limit::{format_delay, RateLimiter};
pub use rate_limit::{
    shared_rate_limiter, ApiRateLimitConfig, ApiRateLimiter, RateLimitResult, SharedApiRateLimiter,
};

/// I/O errors.
#[derive(Error, Debug)]
pub enum IoError {
    /// Filesystem error.
    #[error("filesystem error: {0}")]
    Fs(#[from] io::Error),

    /// Invalid path.
    #[error("invalid path: {0}")]
    InvalidPath(String),

    /// File not found.
    #[error("file not found: {0}")]
    NotFound(PathBuf),

    /// Permission denied.
    #[error("permission denied: {0}")]
    PermissionDenied(PathBuf),

    /// Keystore error.
    #[error("keystore error: {0}")]
    Keystore(String),

    /// Decryption failed (wrong password or corrupted data).
    ///
    /// This is a dedicated variant to avoid timing-leaking string comparisons
    /// when checking for password failures. The error message is intentionally
    /// vague to prevent oracle attacks.
    #[error("decryption failed: wrong password or corrupted data")]
    DecryptionFailed,

    /// Time error.
    #[error("time error: {0}")]
    Time(String),

    /// File too large.
    #[error("file too large: {size} bytes exceeds limit of {limit} bytes")]
    FileTooLarge { size: u64, limit: u64 },
}

/// Result type for I/O operations.
pub type Result<T> = std::result::Result<T, IoError>;

/// Maximum file size for read operations (100 MiB).
/// This prevents denial-of-service attacks from extremely large files.
pub const MAX_FILE_SIZE: u64 = 100 * 1024 * 1024;

/// Time source for obtaining timestamps.
pub trait TimeSource {
    /// Get current Unix timestamp in seconds.
    fn now(&self) -> i64;

    /// Get current Unix timestamp in milliseconds.
    fn now_millis(&self) -> i64;
}

/// System clock time source.
#[derive(Debug, Clone, Copy, Default)]
pub struct SystemClock;

impl TimeSource for SystemClock {
    fn now(&self) -> i64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            // Return -1 as sentinel for pre-epoch or system clock errors
            // (0 is 1970-01-01 00:00:00 which is valid, -1 is clearly invalid)
            .unwrap_or(-1)
    }

    fn now_millis(&self) -> i64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as i64)
            // Return -1 as sentinel for pre-epoch or system clock errors
            .unwrap_or(-1)
    }
}

/// Fixed time source for testing.
#[derive(Debug, Clone, Copy)]
pub struct FixedClock(pub i64);

impl TimeSource for FixedClock {
    fn now(&self) -> i64 {
        self.0
    }

    fn now_millis(&self) -> i64 {
        self.0 * 1000
    }
}

/// Read a file completely into a byte vector with default size limit.
///
/// Uses `MAX_FILE_SIZE` (100 MiB) as the limit to prevent DoS attacks.
/// For custom limits, use `read_file_with_limit`.
pub fn read_file(path: impl AsRef<Path>) -> Result<Vec<u8>> {
    read_file_with_limit(path, MAX_FILE_SIZE)
}

/// Read a file with a custom size limit.
///
/// # Arguments
/// * `path` - Path to the file
/// * `max_size` - Maximum allowed file size in bytes
///
/// # Errors
/// * `IoError::NotFound` - File does not exist
/// * `IoError::FileTooLarge` - File exceeds size limit
/// * `IoError::Fs` - Other filesystem errors
///
/// # Security
///
/// This function is TOCTOU-safe: it opens the file first, then checks the size
/// using the file handle's metadata. This prevents race conditions where an
/// attacker could swap files between existence check and read.
pub fn read_file_with_limit(path: impl AsRef<Path>, max_size: u64) -> Result<Vec<u8>> {
    let path = path.as_ref();

    // SECURITY: Open file first, then check metadata on the open handle.
    // This eliminates TOCTOU race conditions where an attacker could swap
    // the file between our check and read operations.
    let mut file = match File::open(path) {
        Ok(f) => f,
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            return Err(IoError::NotFound(path.to_path_buf()));
        }
        Err(e) => return Err(IoError::Fs(e)),
    };

    // Get metadata from the open file handle (not from path)
    // This ensures we check the same file we're about to read
    let metadata = file.metadata()?;
    let size = metadata.len();
    if size > max_size {
        return Err(IoError::FileTooLarge {
            size,
            limit: max_size,
        });
    }

    let mut contents = Vec::with_capacity(size as usize);
    file.read_to_end(&mut contents)?;
    Ok(contents)
}

/// Write data to a file atomically (temp file + rename).
pub fn write_file_atomic(path: impl AsRef<Path>, data: &[u8]) -> Result<()> {
    let path = path.as_ref();

    // Create temp file in same directory
    let parent = path.parent().unwrap_or(Path::new("."));
    let temp_name = format!(".{}.tmp", rand_hex(8));
    let temp_path = parent.join(&temp_name);

    // Write to temp file
    {
        let mut file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&temp_path)?;
        file.write_all(data)?;
        file.sync_all()?;
    }

    // Rename to target
    fs::rename(&temp_path, path)?;

    Ok(())
}

/// Generate random hex string for temp files.
///
/// Uses cryptographically secure randomness via `getrandom` for uniqueness.
/// This is used only for temporary file names during atomic writes.
fn rand_hex(len: usize) -> String {
    let mut bytes = [0u8; 8];
    // Use getrandom for cryptographically secure random bytes
    // Fall back to timestamp-based hash only if getrandom fails (extremely rare)
    if getrandom::getrandom(&mut bytes).is_err() {
        use std::collections::hash_map::RandomState;
        use std::hash::{BuildHasher, Hasher};

        let state = RandomState::new();
        let mut hasher = state.build_hasher();
        hasher.write_u64(
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos() as u64)
                .unwrap_or(0),
        );
        let hash = hasher.finish();
        return format!("{:0>width$x}", hash, width = len);
    }
    // Convert bytes to hex, truncated to requested length
    let hex: String = bytes.iter().map(|b| format!("{:02x}", b)).collect();
    hex[..len.min(16)].to_string()
}

/// Compute SHA3-256 hash of a file.
pub fn hash_file(path: impl AsRef<Path>) -> Result<[u8; 32]> {
    let data = read_file(path)?;
    Ok(anubis_core::keccak::sha3::sha3_256(&data))
}

/// Recursively hash a directory tree.
///
/// Returns a sorted list of (relative_path, hash) pairs.
pub fn hash_directory(path: impl AsRef<Path>) -> Result<Vec<(PathBuf, [u8; 32])>> {
    let root = path.as_ref();
    if !root.is_dir() {
        return Err(IoError::InvalidPath(format!(
            "not a directory: {}",
            root.display()
        )));
    }

    let mut entries = Vec::new();
    hash_dir_recursive(root, root, &mut entries)?;

    // Sort by path for determinism
    entries.sort_by(|a, b| a.0.cmp(&b.0));

    Ok(entries)
}

fn hash_dir_recursive(
    root: &Path,
    current: &Path,
    entries: &mut Vec<(PathBuf, [u8; 32])>,
) -> Result<()> {
    for entry in fs::read_dir(current)? {
        let entry = entry?;
        let path = entry.path();

        if path.is_file() {
            let relative = path
                .strip_prefix(root)
                .map_err(|_| IoError::InvalidPath(path.display().to_string()))?;
            let hash = hash_file(&path)?;
            entries.push((relative.to_path_buf(), hash));
        } else if path.is_dir() {
            // Skip hidden directories
            if !path
                .file_name()
                .map(|n| n.to_string_lossy().starts_with('.'))
                .unwrap_or(false)
            {
                hash_dir_recursive(root, &path, entries)?;
            }
        }
    }
    Ok(())
}

/// Keystore for managing signing keys.
pub mod keystore {
    use super::*;
    use crate::rate_limit::RateLimiter;
    use crate::seal;
    use std::fs;
    #[cfg(unix)]
    use std::os::unix::fs::PermissionsExt;

    /// Default keystore directory name.
    pub const DEFAULT_KEYSTORE_DIR: &str = ".anubis";

    /// Key file name.
    pub const KEY_FILE: &str = "key.sealed";

    /// Public key file name.
    pub const PUBKEY_FILE: &str = "key.pub";

    /// Archived keys directory.
    pub const ARCHIVE_DIR: &str = "archived";

    /// Rotation certificate file suffix.
    pub const ROTATION_CERT_SUFFIX: &str = ".rotation";

    /// Revoked keys file (plaintext, for backward compatibility).
    pub const REVOKED_FILE: &str = "revoked.list";

    /// Signed revocation list file (CBOR with ML-DSA-87 signature).
    pub const SIGNED_REVOKED_FILE: &str = "revoked.signed";

    /// Anchor queue directory.
    pub const ANCHOR_QUEUE_DIR: &str = "anchor_queue";

    /// Anchor records directory.
    pub const ANCHORS_DIR: &str = "anchors";

    /// Licenses directory.
    pub const LICENSES_DIR: &str = "licenses";

    /// Keystore manages encrypted key storage.
    #[derive(Debug)]
    pub struct Keystore {
        path: PathBuf,
    }

    impl Keystore {
        /// Create or open a keystore at the given path.
        pub fn open(path: impl AsRef<Path>) -> Result<Self> {
            let path = path.as_ref().to_path_buf();

            // Create directory if needed
            if !path.exists() {
                fs::create_dir_all(&path)?;
                // Set restrictive permissions (owner only)
                #[cfg(unix)]
                {
                    let perms = std::fs::Permissions::from_mode(0o700);
                    fs::set_permissions(&path, perms)?;
                }
            }

            Ok(Self { path })
        }

        /// Get the default keystore path.
        ///
        /// Checks in order:
        /// 1. `ANUBIS_HOME` environment variable (for CI/CD and custom deployments)
        /// 2. On Linux: XDG Base Directory Specification (`$XDG_DATA_HOME/anubis`)
        /// 3. On macOS/Windows: `~/.anubis` (traditional dotfile location)
        ///
        /// # Environment Variable
        ///
        /// Set `ANUBIS_HOME` to use a custom keystore location:
        /// ```bash
        /// export ANUBIS_HOME=/path/to/keystore
        /// anubis-notary key init
        /// ```
        pub fn default_path() -> PathBuf {
            // Check ANUBIS_HOME first (highest priority)
            if let Ok(anubis_home) = std::env::var("ANUBIS_HOME") {
                if !anubis_home.is_empty() {
                    return PathBuf::from(anubis_home);
                }
            }

            #[cfg(target_os = "linux")]
            {
                // XDG Base Directory Specification for Linux
                if let Ok(xdg_data) = std::env::var("XDG_DATA_HOME") {
                    return PathBuf::from(xdg_data).join("anubis");
                }
                // Default XDG_DATA_HOME is ~/.local/share
                if let Some(home) = dirs::home_dir() {
                    return home.join(".local").join("share").join("anubis");
                }
            }

            // macOS, Windows, and fallback: use ~/.anubis
            dirs::home_dir()
                .unwrap_or_else(|| PathBuf::from("."))
                .join(DEFAULT_KEYSTORE_DIR)
        }

        /// Check if a key exists.
        pub fn has_key(&self) -> bool {
            self.key_path().exists()
        }

        /// Get the keystore base path.
        pub fn path(&self) -> &Path {
            &self.path
        }

        /// Get the sealed key file path.
        pub fn key_path(&self) -> PathBuf {
            self.path.join(KEY_FILE)
        }

        /// Get the public key file path.
        pub fn pubkey_path(&self) -> PathBuf {
            self.path.join(PUBKEY_FILE)
        }

        /// Read the sealed key bytes.
        pub fn read_sealed_key(&self) -> Result<Vec<u8>> {
            read_file(self.key_path())
        }

        /// Write sealed key bytes.
        pub fn write_sealed_key(&self, data: &[u8]) -> Result<()> {
            let path = self.key_path();
            write_file_atomic(&path, data)?;

            // Set restrictive permissions
            #[cfg(unix)]
            {
                let perms = std::fs::Permissions::from_mode(0o600);
                fs::set_permissions(&path, perms)?;
            }

            Ok(())
        }

        /// Read the public key bytes.
        pub fn read_public_key(&self) -> Result<Vec<u8>> {
            read_file(self.pubkey_path())
        }

        /// Write public key bytes.
        pub fn write_public_key(&self, data: &[u8]) -> Result<()> {
            let path = self.pubkey_path();
            write_file_atomic(&path, data)?;

            // Public key can be world-readable
            #[cfg(unix)]
            {
                let perms = std::fs::Permissions::from_mode(0o644);
                fs::set_permissions(&path, perms)?;
            }

            Ok(())
        }

        /// Seal and store a secret key with password protection.
        ///
        /// This encrypts the secret key using Argon2id key derivation and
        /// ChaCha20Poly1305 authenticated encryption.
        ///
        /// # Arguments
        ///
        /// * `password` - Password to protect the key (minimum recommended: 16 bytes)
        /// * `secret_key` - The secret key material to encrypt
        ///
        /// # Security
        ///
        /// - Uses Argon2id with 4 GiB memory, 3 iterations
        /// - Random 256-bit salt and 96-bit nonce per sealing operation
        /// - Key file is stored with 0o600 permissions (owner-only)
        ///
        /// For systems with limited RAM (< 8 GiB), use `seal_and_store_key_low_memory`.
        pub fn seal_and_store_key(&self, password: &[u8], secret_key: &[u8]) -> Result<()> {
            let sealed = seal::seal_key(password, secret_key)
                .map_err(|e| IoError::Keystore(format!("seal failed: {}", e)))?;
            self.write_sealed_key(&sealed)
        }

        /// Seal and store secret key using low-memory Argon2id (1 GiB).
        ///
        /// This is identical to `seal_and_store_key` but uses only 1 GiB of memory
        /// for the Argon2id key derivation, suitable for systems with limited RAM.
        ///
        /// # Security
        ///
        /// - Uses Argon2id with 1 GiB memory, 4 iterations (one extra to compensate)
        /// - Still far exceeds OWASP minimum recommendation of 47 MiB
        /// - Provides strong protection against brute-force attacks
        ///
        /// # RefinedRust Specification
        /// ```text
        /// #[rr::ensures("uses_argon2id_low_memory_params()")]
        /// #[rr::ensures("sealed_key_version() = VERSION_LOW_MEMORY")]
        /// ```
        pub fn seal_and_store_key_low_memory(
            &self,
            password: &[u8],
            secret_key: &[u8],
        ) -> Result<()> {
            let sealed = seal::seal_key_low_memory(password, secret_key)
                .map_err(|e| IoError::Keystore(format!("seal failed: {}", e)))?;
            self.write_sealed_key(&sealed)
        }

        /// Unseal a stored secret key with password.
        ///
        /// This reads the encrypted key file and decrypts it using the password.
        ///
        /// # Arguments
        ///
        /// * `password` - Password used when sealing the key
        ///
        /// # Errors
        ///
        /// Returns an error if:
        /// - Key file doesn't exist
        /// - Password is incorrect
        /// - Key file is corrupted or tampered
        ///
        /// # Security
        ///
        /// - Constant-time authentication tag verification
        /// - No partial plaintext returned on failure
        pub fn unseal_stored_key(&self, password: &[u8]) -> Result<Vec<u8>> {
            let sealed = self.read_sealed_key()?;
            seal::unseal_key(password, &sealed).map_err(|e| {
                // Use dedicated DecryptionFailed variant for decryption errors
                // to avoid timing-leaking string comparisons
                match e {
                    seal::SealError::DecryptionFailed => IoError::DecryptionFailed,
                    other => IoError::Keystore(format!("unseal failed: {}", other)),
                }
            })
        }

        /// Check if the stored key can be unsealed with the given password.
        ///
        /// This is useful for password verification without keeping the key in memory.
        ///
        /// # Security
        ///
        /// Uses constant-time pattern matching on error types instead of
        /// timing-leaking string comparisons.
        pub fn verify_password(&self, password: &[u8]) -> Result<bool> {
            match self.unseal_stored_key(password) {
                Ok(mut key) => {
                    // Zeroize the key immediately
                    use zeroize::Zeroize;
                    key.zeroize();
                    Ok(true)
                }
                Err(IoError::DecryptionFailed) => Ok(false),
                Err(e) => Err(e),
            }
        }

        /// Create a rate limiter for this keystore.
        ///
        /// The rate limiter state is stored in the keystore directory.
        pub fn rate_limiter(&self) -> RateLimiter {
            RateLimiter::new(&self.path)
        }

        /// Unseal a stored secret key with password and rate limiting.
        ///
        /// This method enforces exponential backoff after failed password attempts
        /// to protect against brute-force attacks.
        ///
        /// # Returns
        ///
        /// - `Ok(Ok(key))` - Password correct, key returned
        /// - `Ok(Err(wait_duration))` - Must wait before next attempt
        /// - `Err(e)` - I/O or other error (not a password failure)
        ///
        /// # Security
        ///
        /// - After 3 failures: 1 second delay
        /// - After 5 failures: 5 seconds delay
        /// - After 7 failures: 30 seconds delay
        /// - After 10+ failures: 60 seconds delay
        ///
        /// Successful authentication resets the failure counter.
        pub fn unseal_stored_key_rate_limited(
            &self,
            password: &[u8],
        ) -> Result<std::result::Result<Vec<u8>, std::time::Duration>> {
            let limiter = self.rate_limiter();

            // Check if we need to wait
            if let Some(wait_duration) = limiter.check_rate_limit() {
                return Ok(Err(wait_duration));
            }

            // Attempt to unseal
            match self.unseal_stored_key(password) {
                Ok(key) => {
                    // Success - reset rate limit
                    limiter.record_success()?;
                    Ok(Ok(key))
                }
                Err(IoError::DecryptionFailed) => {
                    // Wrong password - record failure
                    let failures = limiter.record_failure()?;
                    let delay = RateLimiter::delay_seconds(failures);
                    if delay > 0 {
                        Ok(Err(std::time::Duration::from_secs(delay)))
                    } else {
                        // No delay yet, return immediate "wrong password" error
                        Err(IoError::DecryptionFailed)
                    }
                }
                Err(e) => Err(e),
            }
        }

        /// Get the current number of failed password attempts.
        pub fn failed_password_attempts(&self) -> u32 {
            self.rate_limiter().failure_count()
        }

        /// List all files in the keystore.
        pub fn list_files(&self) -> Result<Vec<PathBuf>> {
            let mut files = Vec::new();
            for entry in fs::read_dir(&self.path)? {
                let entry = entry?;
                if entry.path().is_file() {
                    files.push(entry.path());
                }
            }
            Ok(files)
        }

        /// Get the archive directory path.
        pub fn archive_path(&self) -> PathBuf {
            self.path.join(ARCHIVE_DIR)
        }

        /// Archive the current key with a timestamp identifier.
        ///
        /// Returns the archive ID (timestamp) for the archived key.
        pub fn archive_current_key(&self, timestamp: i64) -> Result<String> {
            let archive_dir = self.archive_path();

            // Create archive directory if needed
            if !archive_dir.exists() {
                fs::create_dir_all(&archive_dir)?;
                #[cfg(unix)]
                {
                    let perms = std::fs::Permissions::from_mode(0o700);
                    fs::set_permissions(&archive_dir, perms)?;
                }
            }

            let archive_id = format!("{}", timestamp);

            // Archive public key
            let current_pubkey = self.read_public_key()?;
            let archived_pubkey_path = archive_dir.join(format!("{}.pub", archive_id));
            write_file_atomic(&archived_pubkey_path, &current_pubkey)?;
            #[cfg(unix)]
            {
                let perms = std::fs::Permissions::from_mode(0o644);
                fs::set_permissions(&archived_pubkey_path, perms)?;
            }

            // Archive sealed key
            let current_sealed = self.read_sealed_key()?;
            let archived_sealed_path = archive_dir.join(format!("{}.sealed", archive_id));
            write_file_atomic(&archived_sealed_path, &current_sealed)?;
            #[cfg(unix)]
            {
                let perms = std::fs::Permissions::from_mode(0o600);
                fs::set_permissions(&archived_sealed_path, perms)?;
            }

            Ok(archive_id)
        }

        /// Write a rotation certificate (signature proving key rotation authorization).
        pub fn write_rotation_cert(&self, archive_id: &str, cert_data: &[u8]) -> Result<()> {
            let cert_path = self
                .archive_path()
                .join(format!("{}{}", archive_id, ROTATION_CERT_SUFFIX));
            write_file_atomic(&cert_path, cert_data)?;
            #[cfg(unix)]
            {
                let perms = std::fs::Permissions::from_mode(0o644);
                fs::set_permissions(&cert_path, perms)?;
            }
            Ok(())
        }

        /// List all archived key IDs.
        pub fn list_archived_keys(&self) -> Result<Vec<String>> {
            let archive_dir = self.archive_path();
            if !archive_dir.exists() {
                return Ok(Vec::new());
            }

            let mut ids = Vec::new();
            for entry in fs::read_dir(&archive_dir)? {
                let entry = entry?;
                let name = entry.file_name().to_string_lossy().to_string();
                if name.ends_with(".pub") {
                    let id = name.trim_end_matches(".pub").to_string();
                    ids.push(id);
                }
            }
            ids.sort();
            Ok(ids)
        }

        /// Read an archived public key.
        pub fn read_archived_public_key(&self, archive_id: &str) -> Result<Vec<u8>> {
            let path = self.archive_path().join(format!("{}.pub", archive_id));
            read_file(path)
        }

        /// Get the revoked keys file path.
        pub fn revoked_path(&self) -> PathBuf {
            self.path.join(REVOKED_FILE)
        }

        /// Check if a public key fingerprint is revoked.
        ///
        /// Fingerprint is the hex-encoded SHA3-256 hash of the public key bytes.
        pub fn is_revoked(&self, fingerprint: &str) -> Result<bool> {
            let revoked_path = self.revoked_path();
            if !revoked_path.exists() {
                return Ok(false);
            }

            let contents = read_file(&revoked_path)?;
            let contents_str = String::from_utf8_lossy(&contents);

            for line in contents_str.lines() {
                let line = line.trim();
                if line.is_empty() || line.starts_with('#') {
                    continue;
                }
                // Format: fingerprint:timestamp:reason
                let parts: Vec<&str> = line.splitn(3, ':').collect();
                if !parts.is_empty() && parts[0] == fingerprint {
                    return Ok(true);
                }
            }
            Ok(false)
        }

        /// Revoke a public key by its fingerprint.
        ///
        /// This adds the key to the revocation list with a timestamp and reason.
        pub fn revoke_key(&self, fingerprint: &str, timestamp: i64, reason: &str) -> Result<()> {
            let revoked_path = self.revoked_path();

            // Read existing revocations
            let mut contents = if revoked_path.exists() {
                String::from_utf8_lossy(&read_file(&revoked_path)?).to_string()
            } else {
                String::from(
                    "# Anubis Notary Revoked Keys\n# Format: fingerprint:timestamp:reason\n",
                )
            };

            // Check if already revoked
            for line in contents.lines() {
                let line = line.trim();
                if line.starts_with('#') || line.is_empty() {
                    continue;
                }
                let parts: Vec<&str> = line.splitn(3, ':').collect();
                if !parts.is_empty() && parts[0] == fingerprint {
                    return Err(IoError::Keystore("Key already revoked".to_string()));
                }
            }

            // Sanitize reason (no colons or newlines)
            let safe_reason: String = reason
                .chars()
                .filter(|c| *c != ':' && *c != '\n' && *c != '\r')
                .collect();

            // Append new revocation
            contents.push_str(&format!("{}:{}:{}\n", fingerprint, timestamp, safe_reason));

            write_file_atomic(&revoked_path, contents.as_bytes())?;

            #[cfg(unix)]
            {
                let perms = std::fs::Permissions::from_mode(0o644);
                fs::set_permissions(&revoked_path, perms)?;
            }

            Ok(())
        }

        /// List all revoked key fingerprints with their revocation info.
        ///
        /// Returns (fingerprint, timestamp, reason) tuples.
        pub fn list_revoked(&self) -> Result<Vec<(String, i64, String)>> {
            let revoked_path = self.revoked_path();
            if !revoked_path.exists() {
                return Ok(Vec::new());
            }

            let contents = read_file(&revoked_path)?;
            let contents_str = String::from_utf8_lossy(&contents);

            let mut revocations = Vec::new();
            for line in contents_str.lines() {
                let line = line.trim();
                if line.is_empty() || line.starts_with('#') {
                    continue;
                }
                let parts: Vec<&str> = line.splitn(3, ':').collect();
                if parts.len() >= 3 {
                    let fingerprint = parts[0].to_string();
                    let timestamp = parts[1].parse().unwrap_or(0);
                    let reason = parts[2].to_string();
                    revocations.push((fingerprint, timestamp, reason));
                }
            }
            Ok(revocations)
        }

        /// Get the signed revocation list file path.
        pub fn signed_revoked_path(&self) -> PathBuf {
            self.path.join(SIGNED_REVOKED_FILE)
        }

        /// Create a signed revocation list from the current revocations.
        ///
        /// The signed list is CBOR-encoded with the following structure:
        /// ```json
        /// {
        ///   "v": 1,
        ///   "issuer": "<hex fingerprint>",
        ///   "created": <unix timestamp>,
        ///   "revocations": [
        ///     {"fp": "<fingerprint>", "ts": <timestamp>, "reason": "<reason>"},
        ///     ...
        ///   ],
        ///   "sig": <ML-DSA-87 signature>
        /// }
        /// ```
        ///
        /// # Arguments
        ///
        /// * `keypair` - The signing keypair (must be the issuer's key)
        /// * `issuer_fingerprint` - Fingerprint of the issuing key
        /// * `timestamp` - Creation timestamp for the list
        pub fn sign_revocation_list(
            &self,
            keypair: &anubis_core::mldsa::KeyPair,
            issuer_fingerprint: &str,
            timestamp: i64,
        ) -> Result<Vec<u8>> {
            use anubis_core::cbor::Encoder;

            let revocations = self.list_revoked()?;

            // Build signable content (everything except signature)
            let mut signable_buf = [0u8; 65536]; // 64KB should be enough for revocation list
            let mut enc = Encoder::new(&mut signable_buf);

            // Map with 4 fields for signable portion
            enc.encode_map_header(4)
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            // "created" - creation timestamp
            enc.encode_text("created")
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            enc.encode_int(timestamp)
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            // "issuer" - issuing key fingerprint
            enc.encode_text("issuer")
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            enc.encode_text(issuer_fingerprint)
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            // "revocations" - array of revocation entries
            enc.encode_text("revocations")
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            enc.encode_array_header(revocations.len())
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            for (fp, ts, reason) in &revocations {
                // Each revocation is a map with 3 fields
                enc.encode_map_header(3)
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

                enc.encode_text("fp")
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
                enc.encode_text(fp)
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

                enc.encode_text("reason")
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
                enc.encode_text(reason)
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

                enc.encode_text("ts")
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
                enc.encode_int(*ts)
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            }

            // "v" - version
            enc.encode_text("v")
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            enc.encode_uint(1)
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            let signable_len = enc.position();

            // Sign with domain separation
            let mut message = Vec::with_capacity(signable_len + 32);
            message.extend_from_slice(b"anubis-notary:revocation-list:v1:");
            message.extend_from_slice(&signable_buf[..signable_len]);

            let signature = keypair
                .sign(&message)
                .map_err(|e| IoError::Keystore(format!("Signing failed: {:?}", e)))?;

            // Build final output with signature
            let mut output_buf = [0u8; 70000]; // signable + signature
            let mut out_enc = Encoder::new(&mut output_buf);

            // Map with 5 fields (signable fields + signature)
            out_enc
                .encode_map_header(5)
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            // Copy signable fields (created, issuer, revocations, v)
            out_enc
                .encode_text("created")
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            out_enc
                .encode_int(timestamp)
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            out_enc
                .encode_text("issuer")
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            out_enc
                .encode_text(issuer_fingerprint)
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            out_enc
                .encode_text("revocations")
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            out_enc
                .encode_array_header(revocations.len())
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            for (fp, ts, reason) in &revocations {
                out_enc
                    .encode_map_header(3)
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
                out_enc
                    .encode_text("fp")
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
                out_enc
                    .encode_text(fp)
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
                out_enc
                    .encode_text("reason")
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
                out_enc
                    .encode_text(reason)
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
                out_enc
                    .encode_text("ts")
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
                out_enc
                    .encode_int(*ts)
                    .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            }

            // "sig" - signature
            out_enc
                .encode_text("sig")
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            out_enc
                .encode_bytes(&signature.to_bytes())
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            out_enc
                .encode_text("v")
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;
            out_enc
                .encode_uint(1)
                .map_err(|e| IoError::Keystore(format!("CBOR encode error: {:?}", e)))?;

            let output_len = out_enc.position();
            Ok(output_buf[..output_len].to_vec())
        }

        /// Verify and parse a signed revocation list.
        ///
        /// # Arguments
        ///
        /// * `data` - The signed revocation list bytes
        /// * `issuer_pubkey` - The public key to verify against
        ///
        /// # Returns
        ///
        /// Returns (issuer_fingerprint, created_timestamp, revocations) if valid.
        #[allow(clippy::type_complexity)] // Complex return type matches API design
        pub fn verify_signed_revocation_list(
            data: &[u8],
            issuer_pubkey: &anubis_core::mldsa::PublicKey,
        ) -> std::result::Result<(String, i64, Vec<(String, i64, String)>), IoError> {
            use anubis_core::cbor::Decoder;

            let mut dec = Decoder::new(data);

            // Decode map header
            let map_len = dec.decode_map_header().map_err(|e| {
                IoError::Keystore(format!("Invalid signed revocation list: {:?}", e))
            })?;
            if map_len != 5 {
                return Err(IoError::Keystore(
                    "Invalid signed revocation list: expected 5 fields".to_string(),
                ));
            }

            let mut created: Option<i64> = None;
            let mut issuer: Option<String> = None;
            let mut revocations: Vec<(String, i64, String)> = Vec::new();
            let mut signature: Option<Vec<u8>> = None;
            let mut version: Option<u64> = None;

            // Parse fields
            for _ in 0..map_len {
                let key = dec
                    .decode_text()
                    .map_err(|e| IoError::Keystore(format!("Invalid field key: {:?}", e)))?;

                match key {
                    "created" => {
                        created =
                            Some(dec.decode_int().map_err(|e| {
                                IoError::Keystore(format!("Invalid created: {:?}", e))
                            })?);
                    }
                    "issuer" => {
                        issuer = Some(
                            dec.decode_text()
                                .map_err(|e| IoError::Keystore(format!("Invalid issuer: {:?}", e)))?
                                .to_string(),
                        );
                    }
                    "revocations" => {
                        let arr_len = dec.decode_array_header().map_err(|e| {
                            IoError::Keystore(format!("Invalid revocations: {:?}", e))
                        })?;
                        for _ in 0..arr_len {
                            let entry_len = dec.decode_map_header().map_err(|e| {
                                IoError::Keystore(format!("Invalid entry: {:?}", e))
                            })?;
                            if entry_len != 3 {
                                return Err(IoError::Keystore(
                                    "Invalid revocation entry".to_string(),
                                ));
                            }

                            let mut fp = String::new();
                            let mut ts = 0i64;
                            let mut reason = String::new();

                            for _ in 0..3 {
                                let field = dec
                                    .decode_text()
                                    .map_err(|e| {
                                        IoError::Keystore(format!("Invalid field: {:?}", e))
                                    })?
                                    .to_string();
                                match field.as_str() {
                                    "fp" => {
                                        fp = dec
                                            .decode_text()
                                            .map_err(|e| {
                                                IoError::Keystore(format!("Invalid fp: {:?}", e))
                                            })?
                                            .to_string()
                                    }
                                    "ts" => {
                                        ts = dec.decode_int().map_err(|e| {
                                            IoError::Keystore(format!("Invalid ts: {:?}", e))
                                        })?
                                    }
                                    "reason" => {
                                        reason = dec
                                            .decode_text()
                                            .map_err(|e| {
                                                IoError::Keystore(format!(
                                                    "Invalid reason: {:?}",
                                                    e
                                                ))
                                            })?
                                            .to_string()
                                    }
                                    _ => {
                                        return Err(IoError::Keystore(format!(
                                            "Unknown field: {}",
                                            field
                                        )))
                                    }
                                }
                            }
                            revocations.push((fp, ts, reason));
                        }
                    }
                    "sig" => {
                        signature = Some(
                            dec.decode_bytes()
                                .map_err(|e| {
                                    IoError::Keystore(format!("Invalid signature: {:?}", e))
                                })?
                                .to_vec(),
                        );
                    }
                    "v" => {
                        version =
                            Some(dec.decode_uint().map_err(|e| {
                                IoError::Keystore(format!("Invalid version: {:?}", e))
                            })?);
                    }
                    _ => {
                        dec.skip_value()
                            .map_err(|e| IoError::Keystore(format!("Skip failed: {:?}", e)))?;
                    }
                }
            }

            // Validate required fields
            let created =
                created.ok_or_else(|| IoError::Keystore("Missing created".to_string()))?;
            let issuer = issuer.ok_or_else(|| IoError::Keystore("Missing issuer".to_string()))?;
            let signature =
                signature.ok_or_else(|| IoError::Keystore("Missing signature".to_string()))?;
            let version =
                version.ok_or_else(|| IoError::Keystore("Missing version".to_string()))?;

            if version != 1 {
                return Err(IoError::Keystore(format!(
                    "Unsupported version: {}",
                    version
                )));
            }

            // Reconstruct signable content
            let mut signable_buf = [0u8; 65536];
            let mut enc = anubis_core::cbor::Encoder::new(&mut signable_buf);

            enc.encode_map_header(4)
                .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
            enc.encode_text("created")
                .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
            enc.encode_int(created)
                .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
            enc.encode_text("issuer")
                .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
            enc.encode_text(&issuer)
                .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
            enc.encode_text("revocations")
                .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
            enc.encode_array_header(revocations.len())
                .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;

            for (fp, ts, reason) in &revocations {
                enc.encode_map_header(3)
                    .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
                enc.encode_text("fp")
                    .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
                enc.encode_text(fp)
                    .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
                enc.encode_text("reason")
                    .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
                enc.encode_text(reason)
                    .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
                enc.encode_text("ts")
                    .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
                enc.encode_int(*ts)
                    .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
            }

            enc.encode_text("v")
                .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;
            enc.encode_uint(1)
                .map_err(|e| IoError::Keystore(format!("CBOR error: {:?}", e)))?;

            let signable_len = enc.position();

            // Build message with domain separation
            let mut message = Vec::with_capacity(signable_len + 32);
            message.extend_from_slice(b"anubis-notary:revocation-list:v1:");
            message.extend_from_slice(&signable_buf[..signable_len]);

            // Verify signature
            let sig = anubis_core::mldsa::Signature::from_bytes(&signature)
                .map_err(|e| IoError::Keystore(format!("Invalid signature bytes: {:?}", e)))?;

            if !issuer_pubkey.verify(&message, &sig) {
                return Err(IoError::Keystore(
                    "Signature verification failed".to_string(),
                ));
            }

            Ok((issuer, created, revocations))
        }

        /// Save a signed revocation list to the keystore.
        pub fn save_signed_revocation_list(&self, data: &[u8]) -> Result<()> {
            write_file_atomic(self.signed_revoked_path(), data)?;

            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let perms = std::fs::Permissions::from_mode(0o644);
                fs::set_permissions(self.signed_revoked_path(), perms)?;
            }

            Ok(())
        }

        /// Load the signed revocation list from the keystore.
        pub fn load_signed_revocation_list(&self) -> Result<Vec<u8>> {
            read_file(self.signed_revoked_path())
        }

        // ========== Anchor Queue Methods ==========

        /// Get the anchor queue directory path.
        pub fn anchor_queue_path(&self) -> PathBuf {
            self.path.join(ANCHOR_QUEUE_DIR)
        }

        /// Get the anchors directory path.
        pub fn anchors_path(&self) -> PathBuf {
            self.path.join(ANCHORS_DIR)
        }

        /// Add a receipt to the anchor queue.
        ///
        /// Returns the queue entry ID (digest hex).
        pub fn queue_receipt(&self, receipt_path: &std::path::Path) -> Result<String> {
            let queue_dir = self.anchor_queue_path();

            // Create queue directory if needed
            if !queue_dir.exists() {
                fs::create_dir_all(&queue_dir)?;
                #[cfg(unix)]
                {
                    let perms = std::fs::Permissions::from_mode(0o700);
                    fs::set_permissions(&queue_dir, perms)?;
                }
            }

            // Read the receipt
            let receipt_data = read_file(receipt_path)?;

            // Compute digest as ID
            let digest = anubis_core::keccak::sha3::sha3_256(&receipt_data);
            let digest_hex = hex::encode(digest);

            // Store in queue with metadata
            let queue_entry_path = queue_dir.join(format!("{}.queued", &digest_hex));

            // Store original path and data
            let mut entry_data = Vec::new();
            entry_data.extend_from_slice(receipt_path.to_string_lossy().as_bytes());
            entry_data.push(b'\n');
            entry_data.extend_from_slice(&receipt_data);

            write_file_atomic(&queue_entry_path, &entry_data)?;

            Ok(digest_hex)
        }

        /// List all queued receipt IDs.
        pub fn list_queue(&self) -> Result<Vec<String>> {
            let queue_dir = self.anchor_queue_path();
            if !queue_dir.exists() {
                return Ok(Vec::new());
            }

            let mut ids = Vec::new();
            for entry in fs::read_dir(&queue_dir)? {
                let entry = entry?;
                let name = entry.file_name().to_string_lossy().to_string();
                if name.ends_with(".queued") {
                    let id = name.trim_end_matches(".queued").to_string();
                    ids.push(id);
                }
            }
            ids.sort();
            Ok(ids)
        }

        /// Get a queued receipt's data.
        ///
        /// Returns (original_path, receipt_data).
        pub fn get_queued_receipt(&self, id: &str) -> Result<(String, Vec<u8>)> {
            let queue_path = self.anchor_queue_path().join(format!("{}.queued", id));
            let data = read_file(&queue_path)?;

            // Split at first newline
            let newline_pos = data
                .iter()
                .position(|&b| b == b'\n')
                .ok_or_else(|| IoError::Keystore("Invalid queue entry format".to_string()))?;

            let path_str = String::from_utf8_lossy(&data[..newline_pos]).to_string();
            let receipt_data = data[newline_pos + 1..].to_vec();

            Ok((path_str, receipt_data))
        }

        /// Remove a receipt from the queue.
        pub fn remove_from_queue(&self, id: &str) -> Result<()> {
            let queue_path = self.anchor_queue_path().join(format!("{}.queued", id));
            if queue_path.exists() {
                fs::remove_file(&queue_path)?;
            }
            Ok(())
        }

        /// Clear the entire queue.
        pub fn clear_queue(&self) -> Result<usize> {
            let queue_dir = self.anchor_queue_path();
            if !queue_dir.exists() {
                return Ok(0);
            }

            let mut count = 0;
            for entry in fs::read_dir(&queue_dir)? {
                let entry = entry?;
                if entry.path().is_file() {
                    fs::remove_file(entry.path())?;
                    count += 1;
                }
            }
            Ok(count)
        }

        // ========== Anchor Record Methods ==========

        /// Store an anchor record.
        ///
        /// The anchor_id is typically the Merkle root hex.
        pub fn store_anchor(&self, anchor_id: &str, anchor_data: &[u8]) -> Result<()> {
            let anchors_dir = self.anchors_path();

            // Create anchors directory if needed
            if !anchors_dir.exists() {
                fs::create_dir_all(&anchors_dir)?;
                #[cfg(unix)]
                {
                    let perms = std::fs::Permissions::from_mode(0o700);
                    fs::set_permissions(&anchors_dir, perms)?;
                }
            }

            let anchor_path = anchors_dir.join(format!("{}.anchor", anchor_id));
            write_file_atomic(&anchor_path, anchor_data)?;

            Ok(())
        }

        /// Get an anchor record.
        pub fn get_anchor(&self, anchor_id: &str) -> Result<Vec<u8>> {
            let anchor_path = self.anchors_path().join(format!("{}.anchor", anchor_id));
            read_file(anchor_path)
        }

        /// List all anchor IDs.
        pub fn list_anchors(&self) -> Result<Vec<String>> {
            let anchors_dir = self.anchors_path();
            if !anchors_dir.exists() {
                return Ok(Vec::new());
            }

            let mut ids = Vec::new();
            for entry in fs::read_dir(&anchors_dir)? {
                let entry = entry?;
                let name = entry.file_name().to_string_lossy().to_string();
                if name.ends_with(".anchor") {
                    let id = name.trim_end_matches(".anchor").to_string();
                    ids.push(id);
                }
            }
            ids.sort();
            Ok(ids)
        }

        // ========== License Methods ==========

        /// Get the licenses directory path.
        pub fn licenses_path(&self) -> PathBuf {
            self.path.join(LICENSES_DIR)
        }

        /// Store a license record.
        ///
        /// The license_id is derived from the license hash.
        /// Returns the license ID.
        pub fn store_license(&self, license_data: &[u8], metadata: &[u8]) -> Result<String> {
            let licenses_dir = self.licenses_path();

            // Create licenses directory if needed
            if !licenses_dir.exists() {
                fs::create_dir_all(&licenses_dir)?;
                #[cfg(unix)]
                {
                    let perms = std::fs::Permissions::from_mode(0o700);
                    fs::set_permissions(&licenses_dir, perms)?;
                }
            }

            // Compute license ID from hash
            let digest = anubis_core::keccak::sha3::sha3_256(license_data);
            let license_id = hex::encode(&digest[..16]); // First 16 bytes = 32 hex chars

            // Store the license file
            let license_path = licenses_dir.join(format!("{}.license", license_id));
            write_file_atomic(&license_path, license_data)?;

            // Store the metadata file (JSON with product, user, expiry, etc.)
            let meta_path = licenses_dir.join(format!("{}.meta", license_id));
            write_file_atomic(&meta_path, metadata)?;

            Ok(license_id)
        }

        /// Get a license record.
        pub fn get_license(&self, license_id: &str) -> Result<Vec<u8>> {
            let license_path = self.licenses_path().join(format!("{}.license", license_id));
            read_file(license_path)
        }

        /// Get license metadata.
        pub fn get_license_metadata(&self, license_id: &str) -> Result<Vec<u8>> {
            let meta_path = self.licenses_path().join(format!("{}.meta", license_id));
            read_file(meta_path)
        }

        /// List all license IDs.
        pub fn list_licenses(&self) -> Result<Vec<String>> {
            let licenses_dir = self.licenses_path();
            if !licenses_dir.exists() {
                return Ok(Vec::new());
            }

            let mut ids = Vec::new();
            for entry in fs::read_dir(&licenses_dir)? {
                let entry = entry?;
                let name = entry.file_name().to_string_lossy().to_string();
                if name.ends_with(".license") {
                    let id = name.trim_end_matches(".license").to_string();
                    ids.push(id);
                }
            }
            ids.sort();
            Ok(ids)
        }
    }
}

// Try to use dirs crate, fall back to env var
mod dirs {
    use std::path::PathBuf;

    pub fn home_dir() -> Option<PathBuf> {
        std::env::var_os("HOME").map(PathBuf::from)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_system_clock() {
        let clock = SystemClock;
        let now = clock.now();
        assert!(now > 0);
    }

    #[test]
    fn test_fixed_clock() {
        let clock = FixedClock(1703462400);
        assert_eq!(clock.now(), 1703462400);
        assert_eq!(clock.now_millis(), 1703462400000);
    }
}
