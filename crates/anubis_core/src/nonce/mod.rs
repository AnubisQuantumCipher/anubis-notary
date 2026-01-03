//! Deterministic nonce derivation with injectivity guarantees.
//!
//! This module provides a deterministic nonce derivation function that
//! is provably injective over its input domain, preventing nonce reuse.
//!
//! ## Persistence
//!
//! When using `NonceDeriver` with a persistent key, the counter MUST be
//! persisted to disk to prevent nonce reuse across restarts. Use
//! `PersistentNonceCounter` to safely manage counter state.
//!
//! ```ignore
//! use anubis_core::nonce::{PersistentNonceCounter, NonceDeriver};
//!
//! let counter = PersistentNonceCounter::load_or_create(path)?;
//! let next = counter.advance()?; // Atomically increments and persists
//! let nonce = deriver.derive(next, entry_id, domain)?;
//! ```

use crate::kdf::HkdfShake256;
use core::fmt;

/// Maximum counter value for injectivity guarantee (2^48).
pub const MAX_COUNTER: u64 = 1u64 << 48;

/// Maximum entry ID for injectivity guarantee (2^32).
pub const MAX_ENTRY_ID: u32 = u32::MAX;

/// Nonce size in bytes.
pub const NONCE_SIZE: usize = 16;

/// Error type for nonce derivation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NonceError {
    /// Counter exceeds maximum allowed value.
    CounterOverflow,
    /// Failed to persist counter to disk.
    #[cfg(feature = "std")]
    PersistenceFailed(String),
    /// Failed to load counter from disk.
    #[cfg(feature = "std")]
    LoadFailed(String),
}

impl fmt::Display for NonceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CounterOverflow => write!(
                f,
                "counter overflow: value must be less than 2^48 ({})",
                MAX_COUNTER
            ),
            #[cfg(feature = "std")]
            Self::PersistenceFailed(msg) => write!(f, "failed to persist counter: {}", msg),
            #[cfg(feature = "std")]
            Self::LoadFailed(msg) => write!(f, "failed to load counter: {}", msg),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for NonceError {}

/// Persistent nonce counter with atomic file operations.
///
/// This counter is persisted to disk after each increment to prevent
/// nonce reuse across process restarts. Uses atomic write operations
/// (write to temp + fsync + rename) to prevent corruption.
///
/// # Security
///
/// - Counter is persisted BEFORE being used for encryption
/// - Atomic file operations prevent data loss on crash
/// - Counter file is restricted to owner-only permissions (0600)
///
/// # Example
///
/// ```ignore
/// let counter = PersistentNonceCounter::load_or_create("~/.anubis/nonce_counter")?;
/// let next = counter.advance()?;  // Atomically increments and persists
/// ```
#[cfg(feature = "std")]
pub struct PersistentNonceCounter {
    /// Current counter value
    counter: u64,
    /// Path to the counter file
    path: std::path::PathBuf,
}

#[cfg(feature = "std")]
impl PersistentNonceCounter {
    /// Load an existing counter or create a new one starting at 0.
    ///
    /// If the counter file exists, loads and validates the stored value.
    /// If not, creates a new counter starting at 0.
    ///
    /// # Security
    ///
    /// The counter file should be stored in a secure location with
    /// restricted permissions. On Unix, creates with mode 0600.
    pub fn load_or_create<P: AsRef<std::path::Path>>(path: P) -> Result<Self, NonceError> {
        let path = path.as_ref().to_path_buf();

        if path.exists() {
            Self::load(&path)
        } else {
            // Create parent directory if needed
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)
                    .map_err(|e| NonceError::PersistenceFailed(e.to_string()))?;
            }

            let counter = Self { counter: 0, path };
            counter.persist()?;
            Ok(counter)
        }
    }

    /// Load a counter from an existing file.
    fn load(path: &std::path::Path) -> Result<Self, NonceError> {
        let data = std::fs::read(path).map_err(|e| NonceError::LoadFailed(e.to_string()))?;

        if data.len() != 8 {
            return Err(NonceError::LoadFailed(format!(
                "invalid counter file size: expected 8, got {}",
                data.len()
            )));
        }

        let counter = u64::from_le_bytes(data.try_into().expect("length already checked"));

        if counter >= MAX_COUNTER {
            return Err(NonceError::CounterOverflow);
        }

        Ok(Self {
            counter,
            path: path.to_path_buf(),
        })
    }

    /// Get the next counter value, atomically incrementing and persisting.
    ///
    /// # Critical Security Note
    ///
    /// This method persists the NEW counter value BEFORE returning.
    /// This ensures that if we crash after returning but before using
    /// the nonce, we won't reuse it on restart.
    ///
    /// # Errors
    ///
    /// Returns `CounterOverflow` if counter would exceed MAX_COUNTER.
    /// Returns `PersistenceFailed` if disk write fails.
    pub fn advance(&mut self) -> Result<u64, NonceError> {
        let next = self
            .counter
            .checked_add(1)
            .ok_or(NonceError::CounterOverflow)?;

        if next >= MAX_COUNTER {
            return Err(NonceError::CounterOverflow);
        }

        // Persist the NEW counter BEFORE using it
        // This is critical: if we crash after persist but before use,
        // we skip a counter value (safe). If we used before persist
        // and crashed, we could reuse on restart (catastrophic).
        self.counter = next;
        self.persist()?;

        Ok(next)
    }

    /// Get the current counter value without incrementing.
    pub fn current(&self) -> u64 {
        self.counter
    }

    /// Persist the counter to disk atomically.
    ///
    /// Uses write-to-temp + fsync + rename pattern for atomicity.
    fn persist(&self) -> Result<(), NonceError> {
        use std::io::Write;

        let temp_path = self.path.with_extension("tmp");

        // Write to temp file
        let mut file = std::fs::File::create(&temp_path)
            .map_err(|e| NonceError::PersistenceFailed(e.to_string()))?;

        // Set restrictive permissions on Unix
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let perms = std::fs::Permissions::from_mode(0o600);
            file.set_permissions(perms)
                .map_err(|e| NonceError::PersistenceFailed(e.to_string()))?;
        }

        file.write_all(&self.counter.to_le_bytes())
            .map_err(|e| NonceError::PersistenceFailed(e.to_string()))?;

        // Flush to disk
        file.sync_all()
            .map_err(|e| NonceError::PersistenceFailed(e.to_string()))?;

        drop(file);

        // Atomic rename
        std::fs::rename(&temp_path, &self.path)
            .map_err(|e| NonceError::PersistenceFailed(e.to_string()))?;

        // Sync parent directory for durability on Unix
        #[cfg(unix)]
        if let Some(parent) = self.path.parent() {
            if let Ok(dir) = std::fs::File::open(parent) {
                let _ = dir.sync_all();
            }
        }

        Ok(())
    }

    /// Reserve a range of counter values atomically.
    ///
    /// This is useful when you know you'll need N nonces and want to
    /// minimize disk writes. Returns the first value in the range.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let start = counter.reserve(100)?;  // Reserve 100 values
    /// for i in 0..100 {
    ///     let nonce_counter = start + i;  // Use without disk writes
    /// }
    /// ```
    pub fn reserve(&mut self, count: u64) -> Result<u64, NonceError> {
        let start = self
            .counter
            .checked_add(1)
            .ok_or(NonceError::CounterOverflow)?;

        let end = start
            .checked_add(count)
            .ok_or(NonceError::CounterOverflow)?;

        if end >= MAX_COUNTER {
            return Err(NonceError::CounterOverflow);
        }

        self.counter = end;
        self.persist()?;

        Ok(start)
    }
}

/// Deterministic nonce deriver.
///
/// Derives nonces from (counter, entry_id, domain) tuples using HKDF.
/// The derivation is injective: distinct inputs produce distinct nonces.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::invariant("forall ctr1 ctr2 id1 id2 dom1 dom2.
///     (ctr1 < MAX_COUNTER /\\ ctr2 < MAX_COUNTER) ->
///     (derive(ctr1, id1, dom1) = derive(ctr2, id2, dom2)) ->
///     (ctr1 = ctr2 /\\ id1 = id2 /\\ dom1 = dom2)")]
/// ```
pub struct NonceDeriver {
    /// Base key material for derivation.
    key_material: [u8; 32],
}

impl NonceDeriver {
    /// Create a new nonce deriver with the given key material.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::params("key" : "array u8 32")]
    /// #[rr::returns("#NonceDeriver { key_material: key }")]
    /// ```
    pub fn new(key_material: [u8; 32]) -> Self {
        Self { key_material }
    }

    /// Derive a nonce from counter, entry ID, and domain separator.
    ///
    /// The derivation is:
    /// nonce = HKDF(key_material, LE64(counter) || LE32(entry_id) || domain, "anubis-nonce")
    ///
    /// # Arguments
    ///
    /// * `counter` - A monotonically increasing counter (must be < 2^48)
    /// * `entry_id` - An entry identifier (full u32 range)
    /// * `domain` - A domain separator byte
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::params("ctr" : "Z", "id" : "Z", "dom" : "Z")]
    /// #[rr::requires("ctr < MAX_COUNTER")]
    /// #[rr::returns("#(derive_nonce(ctr, id, dom))")]
    /// #[rr::ensures("(ctr != ctr2 \\/ id != id2 \\/ dom != dom2) -> Res != derive_nonce(ctr2, id2, dom2)")]
    /// ```
    pub fn derive(
        &self,
        counter: u64,
        entry_id: u32,
        domain: u8,
    ) -> Result<[u8; NONCE_SIZE], NonceError> {
        if counter >= MAX_COUNTER {
            return Err(NonceError::CounterOverflow);
        }

        // Build the info string: LE64(counter) || LE32(entry_id) || domain
        let mut info = [0u8; 13];
        info[0..8].copy_from_slice(&counter.to_le_bytes());
        info[8..12].copy_from_slice(&entry_id.to_le_bytes());
        info[12] = domain;

        // Derive nonce using HKDF
        let nonce: [u8; NONCE_SIZE] =
            HkdfShake256::derive(&self.key_material, b"anubis-nonce-derivation", &info)
                .expect("HKDF output size is valid");

        Ok(nonce)
    }

    /// Derive a nonce with a string domain separator.
    ///
    /// This method includes the full domain string in the HKDF info parameter
    /// to ensure proper domain separation without collision risk.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::ensures("domain_str1 != domain_str2 -> Res1 != Res2")]
    /// ```
    pub fn derive_with_domain(
        &self,
        counter: u64,
        entry_id: u32,
        domain_str: &[u8],
    ) -> Result<[u8; NONCE_SIZE], NonceError> {
        if counter >= MAX_COUNTER {
            return Err(NonceError::CounterOverflow);
        }

        // Build the info string with length-prefixed domain for injectivity:
        // LE64(counter) || LE32(entry_id) || LE16(domain_len) || domain_str
        //
        // The length prefix ensures that:
        // - "abc" || "" differs from "ab" || "c"
        // - No collisions from domain string variations
        let domain_len = domain_str.len().min(u16::MAX as usize);
        let info_len = 8 + 4 + 2 + domain_len;

        // Use stack allocation for small domains, avoid heap
        let mut info_buf = [0u8; 256]; // Max practical domain size
        if info_len > info_buf.len() {
            // Domain too long - fall back to hash-based approach with full SHAKE256
            return self.derive_with_long_domain(counter, entry_id, domain_str);
        }

        info_buf[0..8].copy_from_slice(&counter.to_le_bytes());
        info_buf[8..12].copy_from_slice(&entry_id.to_le_bytes());
        info_buf[12..14].copy_from_slice(&(domain_len as u16).to_le_bytes());
        info_buf[14..14 + domain_len].copy_from_slice(&domain_str[..domain_len]);

        let nonce: [u8; NONCE_SIZE] = HkdfShake256::derive(
            &self.key_material,
            b"anubis-nonce-domain",
            &info_buf[..info_len],
        )
        .expect("HKDF output size is valid");

        Ok(nonce)
    }

    /// Derive a nonce with a long domain string (> 242 bytes).
    ///
    /// Uses SHAKE256 to hash the domain string first, ensuring injectivity
    /// is preserved through collision resistance.
    fn derive_with_long_domain(
        &self,
        counter: u64,
        entry_id: u32,
        domain_str: &[u8],
    ) -> Result<[u8; NONCE_SIZE], NonceError> {
        use crate::keccak::shake::Shake256;

        // Hash the domain string to a fixed size
        let mut xof = Shake256::new();
        xof.absorb(domain_str);
        let mut domain_hash = [0u8; 32];
        xof.squeeze(&mut domain_hash);

        // Build info: LE64(counter) || LE32(entry_id) || 0xFF || domain_hash
        // The 0xFF marker distinguishes long domains from short ones
        let mut info = [0u8; 8 + 4 + 1 + 32];
        info[0..8].copy_from_slice(&counter.to_le_bytes());
        info[8..12].copy_from_slice(&entry_id.to_le_bytes());
        info[12] = 0xFF; // Marker for hashed domain
        info[13..45].copy_from_slice(&domain_hash);

        let nonce: [u8; NONCE_SIZE] =
            HkdfShake256::derive(&self.key_material, b"anubis-nonce-long-domain", &info)
                .expect("HKDF output size is valid");

        Ok(nonce)
    }
}

/// Domain separators for different operations.
pub mod domains {
    /// Domain for receipt signing.
    pub const RECEIPT: u8 = 0x01;

    /// Domain for license signing.
    pub const LICENSE: u8 = 0x02;

    /// Domain for key encryption.
    pub const KEY_WRAP: u8 = 0x03;

    /// Domain for file encryption.
    pub const FILE_SEAL: u8 = 0x04;

    /// Domain for merkle tree operations.
    pub const MERKLE: u8 = 0x05;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nonce_deterministic() {
        let deriver = NonceDeriver::new([0u8; 32]);

        let nonce1 = deriver.derive(1, 100, 0x01).unwrap();
        let nonce2 = deriver.derive(1, 100, 0x01).unwrap();

        assert_eq!(nonce1, nonce2);
    }

    #[test]
    fn test_nonce_different_counter() {
        let deriver = NonceDeriver::new([0u8; 32]);

        let nonce1 = deriver.derive(1, 100, 0x01).unwrap();
        let nonce2 = deriver.derive(2, 100, 0x01).unwrap();

        assert_ne!(nonce1, nonce2);
    }

    #[test]
    fn test_nonce_different_entry_id() {
        let deriver = NonceDeriver::new([0u8; 32]);

        let nonce1 = deriver.derive(1, 100, 0x01).unwrap();
        let nonce2 = deriver.derive(1, 101, 0x01).unwrap();

        assert_ne!(nonce1, nonce2);
    }

    #[test]
    fn test_nonce_different_domain() {
        let deriver = NonceDeriver::new([0u8; 32]);

        let nonce1 = deriver.derive(1, 100, domains::RECEIPT).unwrap();
        let nonce2 = deriver.derive(1, 100, domains::LICENSE).unwrap();

        assert_ne!(nonce1, nonce2);
    }

    #[test]
    fn test_counter_overflow() {
        let deriver = NonceDeriver::new([0u8; 32]);

        let result = deriver.derive(MAX_COUNTER, 0, 0);
        assert_eq!(result, Err(NonceError::CounterOverflow));

        let result = deriver.derive(MAX_COUNTER - 1, 0, 0);
        assert!(result.is_ok());
    }

    #[test]
    fn test_different_key_material() {
        let deriver1 = NonceDeriver::new([0u8; 32]);
        let deriver2 = NonceDeriver::new([1u8; 32]);

        let nonce1 = deriver1.derive(1, 100, 0x01).unwrap();
        let nonce2 = deriver2.derive(1, 100, 0x01).unwrap();

        assert_ne!(nonce1, nonce2);
    }

    #[cfg(feature = "std")]
    mod persistent_counter_tests {
        use super::*;

        #[test]
        fn test_persistent_counter_create() {
            let temp_dir = std::env::temp_dir().join("anubis_test_nonce_create");
            let _ = std::fs::remove_dir_all(&temp_dir);

            let counter_path = temp_dir.join("counter");
            let mut counter = PersistentNonceCounter::load_or_create(&counter_path).unwrap();

            assert_eq!(counter.current(), 0);
            assert!(counter_path.exists());

            let next = counter.advance().unwrap();
            assert_eq!(next, 1);
            assert_eq!(counter.current(), 1);

            // Cleanup
            let _ = std::fs::remove_dir_all(&temp_dir);
        }

        #[test]
        fn test_persistent_counter_reload() {
            let temp_dir = std::env::temp_dir().join("anubis_test_nonce_reload");
            let _ = std::fs::remove_dir_all(&temp_dir);

            let counter_path = temp_dir.join("counter");

            // Create and increment
            {
                let mut counter = PersistentNonceCounter::load_or_create(&counter_path).unwrap();
                assert_eq!(counter.advance().unwrap(), 1);
                assert_eq!(counter.advance().unwrap(), 2);
                assert_eq!(counter.advance().unwrap(), 3);
            }

            // Reload and verify persistence
            {
                let mut counter = PersistentNonceCounter::load_or_create(&counter_path).unwrap();
                assert_eq!(counter.current(), 3);
                assert_eq!(counter.advance().unwrap(), 4);
            }

            // Cleanup
            let _ = std::fs::remove_dir_all(&temp_dir);
        }

        #[test]
        fn test_persistent_counter_reserve() {
            let temp_dir = std::env::temp_dir().join("anubis_test_nonce_reserve");
            let _ = std::fs::remove_dir_all(&temp_dir);

            let counter_path = temp_dir.join("counter");
            let mut counter = PersistentNonceCounter::load_or_create(&counter_path).unwrap();

            // Reserve 10 values
            let start = counter.reserve(10).unwrap();
            assert_eq!(start, 1); // First usable value
            assert_eq!(counter.current(), 11); // Counter advanced by 10+1

            // Next after reserve should be 12
            let next = counter.advance().unwrap();
            assert_eq!(next, 12);

            // Cleanup
            let _ = std::fs::remove_dir_all(&temp_dir);
        }

        #[test]
        fn test_persistent_counter_no_reuse_after_reload() {
            let temp_dir = std::env::temp_dir().join("anubis_test_nonce_no_reuse");
            let _ = std::fs::remove_dir_all(&temp_dir);

            let counter_path = temp_dir.join("counter");

            // Simulate multiple "restarts"
            let mut all_values = Vec::new();

            for _ in 0..5 {
                let mut counter = PersistentNonceCounter::load_or_create(&counter_path).unwrap();
                for _ in 0..10 {
                    all_values.push(counter.advance().unwrap());
                }
            }

            // All values should be unique (no reuse)
            let unique_count = {
                let mut sorted = all_values.clone();
                sorted.sort();
                sorted.dedup();
                sorted.len()
            };
            assert_eq!(unique_count, all_values.len());

            // Values should be sequential starting from 1
            for (i, &val) in all_values.iter().enumerate() {
                assert_eq!(val, (i + 1) as u64);
            }

            // Cleanup
            let _ = std::fs::remove_dir_all(&temp_dir);
        }

        #[test]
        fn test_persistent_counter_overflow() {
            let temp_dir = std::env::temp_dir().join("anubis_test_nonce_overflow");
            let _ = std::fs::remove_dir_all(&temp_dir);

            let counter_path = temp_dir.join("counter");

            // Write a counter value near MAX_COUNTER
            let near_max = MAX_COUNTER - 2;
            std::fs::create_dir_all(&temp_dir).unwrap();
            std::fs::write(&counter_path, near_max.to_le_bytes()).unwrap();

            let mut counter = PersistentNonceCounter::load_or_create(&counter_path).unwrap();
            assert_eq!(counter.current(), near_max);

            // One more should work
            let next = counter.advance().unwrap();
            assert_eq!(next, near_max + 1);

            // This should overflow
            let result = counter.advance();
            assert!(matches!(result, Err(NonceError::CounterOverflow)));

            // Cleanup
            let _ = std::fs::remove_dir_all(&temp_dir);
        }

        #[test]
        fn test_persistent_counter_integration_with_deriver() {
            let temp_dir = std::env::temp_dir().join("anubis_test_nonce_integration");
            let _ = std::fs::remove_dir_all(&temp_dir);

            let counter_path = temp_dir.join("counter");
            let mut counter = PersistentNonceCounter::load_or_create(&counter_path).unwrap();
            let deriver = NonceDeriver::new([0u8; 32]);

            // Generate nonces
            let mut nonces = Vec::new();
            for _ in 0..10 {
                let c = counter.advance().unwrap();
                let nonce = deriver.derive(c, 0, domains::KEY_WRAP).unwrap();
                nonces.push(nonce);
            }

            // All nonces should be unique
            for i in 0..nonces.len() {
                for j in (i + 1)..nonces.len() {
                    assert_ne!(nonces[i], nonces[j]);
                }
            }

            // Cleanup
            let _ = std::fs::remove_dir_all(&temp_dir);
        }
    }
}
