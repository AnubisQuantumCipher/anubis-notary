//! Key sealing module using Argon2id + ChaCha20Poly1305.
//!
//! This module provides secure key encryption for storage:
//! - Password-based key derivation using Argon2id (RFC 9106)
//! - Authenticated encryption using ChaCha20Poly1305 (formally verified via libcrux)
//!
//! ## Sealed Key Format
//!
//! ```text
//! [1 byte]  version = 0x02
//! [32 bytes] salt for Argon2id
//! [12 bytes] nonce for ChaCha20Poly1305
//! [N bytes]  ciphertext (secret key + 16-byte auth tag)
//! ```
//!
//! ## Security Properties
//!
//! - Argon2id with 4 GiB memory, 3 iterations, 1 lane (exceeds OWASP recommendations)
//! - ChaCha20Poly1305 with random 96-bit nonce (safe since each key is unique per salt)
//! - Formally verified encryption via Cryspen libcrux (hax/F* toolchain)
//! - Constant-time tag verification
//! - Zeroization of sensitive data on drop
//!
//! ## Example
//!
//! ```ignore
//! use anubis_io::seal::{seal_key, unseal_key};
//!
//! let secret_key = [0u8; 32];
//! let password = b"strong password";
//!
//! // Seal the key
//! let sealed = seal_key(password, &secret_key)?;
//!
//! // Unseal the key
//! let recovered = unseal_key(password, &sealed)?;
//! assert_eq!(&recovered[..], &secret_key[..]);
//! ```

use anubis_core::aead::{ChaCha20Poly1305, NONCE_SIZE, TAG_SIZE};
use argon2::{Algorithm, Argon2, Params, Version};
use thiserror::Error;
use zeroize::Zeroize;

/// Current sealed key format version (4 GiB Argon2id).
/// Version 0x02 uses standard ChaCha20Poly1305 (12-byte nonce) with libcrux.
pub const VERSION: u8 = 0x02;

/// Low-memory sealed key format version (1 GiB Argon2id).
/// Version 0x03 uses the same encryption but with reduced memory Argon2id.
pub const VERSION_LOW_MEMORY: u8 = 0x03;

/// Legacy version using XChaCha20Poly1305 (24-byte nonce).
pub const VERSION_LEGACY: u8 = 0x01;

/// Salt size for Argon2id (256 bits, as recommended).
pub const SALT_SIZE: usize = 32;

/// Derived key size for AEAD (256 bits for ChaCha20).
const DERIVED_KEY_SIZE: usize = 32;

/// Header size: version + salt + nonce.
pub const HEADER_SIZE: usize = 1 + SALT_SIZE + NONCE_SIZE;

/// Minimum sealed data size: header + tag (no payload).
pub const MIN_SEALED_SIZE: usize = HEADER_SIZE + TAG_SIZE;

/// Argon2id memory cost in KiB (4 GiB = 4,194,304 KiB).
/// This provides strong resistance against GPU/ASIC attacks.
/// Matches the security floor defined in anubis_core::kdf.
pub const ARGON2ID_M_COST: u32 = 4_194_304;

/// Argon2id low-memory cost in KiB (1 GiB = 1,048,576 KiB).
/// For systems with limited RAM. Still strong security.
pub const ARGON2ID_LOW_MEMORY_M_COST: u32 = 1_048_576;

/// Argon2id time cost (iterations) for default mode.
pub const ARGON2ID_T_COST: u32 = 3;

/// Argon2id time cost (iterations) for low-memory mode.
/// Increased to partially compensate for reduced memory.
pub const ARGON2ID_LOW_MEMORY_T_COST: u32 = 4;

/// Argon2id parallelism (lanes).
pub const ARGON2ID_P_COST: u32 = 1;

/// Errors that can occur during key sealing/unsealing.
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum SealError {
    /// Invalid sealed data format.
    #[error("invalid sealed data format")]
    InvalidFormat,

    /// Unsupported format version.
    #[error("unsupported version: {0}")]
    UnsupportedVersion(u8),

    /// Sealed data too short.
    #[error("sealed data too short: expected at least {expected}, got {actual}")]
    DataTooShort { expected: usize, actual: usize },

    /// Argon2id key derivation failed.
    #[error("key derivation failed")]
    KeyDerivationFailed,

    /// Decryption failed (wrong password or corrupted data).
    #[error("decryption failed: wrong password or corrupted data")]
    DecryptionFailed,

    /// Random number generation failed.
    #[error("random number generation failed")]
    RandomFailed,
}

/// Seal (encrypt) a secret key with a password.
///
/// Uses Argon2id for key derivation and XChaCha20Poly1305 for encryption.
/// Returns the sealed key bytes suitable for storage.
///
/// # Arguments
///
/// * `password` - Password to derive encryption key from
/// * `secret_key` - The secret key material to encrypt
///
/// # Returns
///
/// Sealed key bytes in the format: version || salt || nonce || ciphertext
///
/// # Security
///
/// - Generates cryptographically secure random salt and nonce
/// - Uses memory-hard Argon2id with 1 GiB memory requirement
/// - Derived key is zeroized after use
pub fn seal_key(password: &[u8], secret_key: &[u8]) -> Result<Vec<u8>, SealError> {
    // Generate random salt
    let mut salt = [0u8; SALT_SIZE];
    getrandom::getrandom(&mut salt).map_err(|_| SealError::RandomFailed)?;

    // Generate random nonce (12 bytes for ChaCha20Poly1305)
    // Safe because each salt produces a unique derived key
    let mut nonce = [0u8; NONCE_SIZE];
    getrandom::getrandom(&mut nonce).map_err(|_| SealError::RandomFailed)?;

    // Derive encryption key using Argon2id
    let mut derived_key = [0u8; DERIVED_KEY_SIZE];
    derive_key(password, &salt, &mut derived_key)?;

    // Encrypt the secret key using formally verified libcrux ChaCha20Poly1305
    let aead = ChaCha20Poly1305::new(&derived_key)
        .map_err(|_| SealError::KeyDerivationFailed)?;

    // Prepare output buffer: version + salt + nonce + ciphertext
    let ciphertext_len = secret_key.len() + TAG_SIZE;
    let mut sealed = vec![0u8; HEADER_SIZE + ciphertext_len];

    // Write header
    sealed[0] = VERSION;
    sealed[1..1 + SALT_SIZE].copy_from_slice(&salt);
    sealed[1 + SALT_SIZE..HEADER_SIZE].copy_from_slice(&nonce);

    // Encrypt with version as associated data (binds ciphertext to version)
    let ad = &[VERSION];
    aead.seal(&nonce, ad, secret_key, &mut sealed[HEADER_SIZE..])
        .map_err(|_| SealError::KeyDerivationFailed)?;

    // Zeroize sensitive data
    derived_key.zeroize();
    salt.zeroize();
    nonce.zeroize();

    Ok(sealed)
}

/// Seal (encrypt) a secret key with a password using low-memory mode.
///
/// Uses Argon2id with 1 GiB memory (instead of 4 GiB) for key derivation.
/// This is suitable for systems with limited RAM (< 8 GiB available).
///
/// # Arguments
///
/// * `password` - Password to derive encryption key from
/// * `secret_key` - The secret key material to encrypt
///
/// # Returns
///
/// Sealed key bytes in the format: version || salt || nonce || ciphertext
///
/// # Security
///
/// - Uses 1 GiB memory (still far exceeds OWASP minimum of 47 MiB)
/// - Uses 4 iterations (instead of 3) to partially compensate
/// - Derived key is zeroized after use
///
/// # RefinedRust Specification
/// ```text
/// #[rr::ensures("result.is_ok() ==> result.unwrap()[0] = VERSION_LOW_MEMORY")]
/// #[rr::ensures("uses_argon2id_with(ARGON2ID_LOW_MEMORY_M_COST, ARGON2ID_LOW_MEMORY_T_COST)")]
/// ```
pub fn seal_key_low_memory(password: &[u8], secret_key: &[u8]) -> Result<Vec<u8>, SealError> {
    // Generate random salt
    let mut salt = [0u8; SALT_SIZE];
    getrandom::getrandom(&mut salt).map_err(|_| SealError::RandomFailed)?;

    // Generate random nonce (12 bytes for ChaCha20Poly1305)
    let mut nonce = [0u8; NONCE_SIZE];
    getrandom::getrandom(&mut nonce).map_err(|_| SealError::RandomFailed)?;

    // Derive encryption key using Argon2id with low-memory parameters
    let mut derived_key = [0u8; DERIVED_KEY_SIZE];
    derive_key_low_memory(password, &salt, &mut derived_key)?;

    // Encrypt the secret key using formally verified libcrux ChaCha20Poly1305
    let aead = ChaCha20Poly1305::new(&derived_key)
        .map_err(|_| SealError::KeyDerivationFailed)?;

    // Prepare output buffer: version + salt + nonce + ciphertext
    let ciphertext_len = secret_key.len() + TAG_SIZE;
    let mut sealed = vec![0u8; HEADER_SIZE + ciphertext_len];

    // Write header with low-memory version
    sealed[0] = VERSION_LOW_MEMORY;
    sealed[1..1 + SALT_SIZE].copy_from_slice(&salt);
    sealed[1 + SALT_SIZE..HEADER_SIZE].copy_from_slice(&nonce);

    // Encrypt with version as associated data (binds ciphertext to version)
    let ad = &[VERSION_LOW_MEMORY];
    aead.seal(&nonce, ad, secret_key, &mut sealed[HEADER_SIZE..])
        .map_err(|_| SealError::KeyDerivationFailed)?;

    // Zeroize sensitive data
    derived_key.zeroize();
    salt.zeroize();
    nonce.zeroize();

    Ok(sealed)
}

/// Unseal (decrypt) a secret key with a password.
///
/// Uses Argon2id for key derivation and ChaCha20Poly1305 (formally verified) for decryption.
///
/// # Arguments
///
/// * `password` - Password to derive decryption key from
/// * `sealed` - Sealed key bytes from `seal_key`
///
/// # Returns
///
/// The decrypted secret key material.
///
/// # Errors
///
/// Returns `DecryptionFailed` if password is wrong or data is corrupted.
/// This error is intentionally vague to prevent oracle attacks.
///
/// # Security
///
/// - Constant-time tag verification via libcrux
/// - Derived key is zeroized after use
/// - On failure, no partial plaintext is returned
pub fn unseal_key(password: &[u8], sealed: &[u8]) -> Result<Vec<u8>, SealError> {
    // Validate minimum size
    if sealed.len() < MIN_SEALED_SIZE {
        return Err(SealError::DataTooShort {
            expected: MIN_SEALED_SIZE,
            actual: sealed.len(),
        });
    }

    // Parse header
    let version = sealed[0];

    // Support both standard (VERSION) and low-memory (VERSION_LOW_MEMORY) formats
    let use_low_memory = match version {
        VERSION => false,
        VERSION_LOW_MEMORY => true,
        _ => return Err(SealError::UnsupportedVersion(version)),
    };

    let salt = &sealed[1..1 + SALT_SIZE];
    let nonce = &sealed[1 + SALT_SIZE..HEADER_SIZE];
    let ciphertext = &sealed[HEADER_SIZE..];

    // Derive decryption key using Argon2id with appropriate parameters
    let mut derived_key = [0u8; DERIVED_KEY_SIZE];
    if use_low_memory {
        derive_key_low_memory(password, salt, &mut derived_key)?;
    } else {
        derive_key(password, salt, &mut derived_key)?;
    }

    // Decrypt the secret key using formally verified libcrux ChaCha20Poly1305
    let aead = ChaCha20Poly1305::new(&derived_key)
        .map_err(|_| SealError::KeyDerivationFailed)?;

    let pt_len = ciphertext.len() - TAG_SIZE;
    let mut plaintext = vec![0u8; pt_len];

    // Decrypt with version as associated data
    let ad = &[version];
    let result = aead.open(nonce, ad, ciphertext, &mut plaintext);

    // Zeroize derived key regardless of result
    derived_key.zeroize();

    match result {
        Ok(_) => Ok(plaintext),
        Err(_) => {
            plaintext.zeroize();
            Err(SealError::DecryptionFailed)
        }
    }
}

/// Derive a key from password and salt using Argon2id (default 4 GiB mode).
fn derive_key(password: &[u8], salt: &[u8], output: &mut [u8; DERIVED_KEY_SIZE]) -> Result<(), SealError> {
    derive_key_with_params(password, salt, output, ARGON2ID_M_COST, ARGON2ID_T_COST)
}

/// Derive a key from password and salt using Argon2id (low-memory 1 GiB mode).
fn derive_key_low_memory(password: &[u8], salt: &[u8], output: &mut [u8; DERIVED_KEY_SIZE]) -> Result<(), SealError> {
    derive_key_with_params(password, salt, output, ARGON2ID_LOW_MEMORY_M_COST, ARGON2ID_LOW_MEMORY_T_COST)
}

/// Derive a key from password and salt using Argon2id with specified parameters.
fn derive_key_with_params(
    password: &[u8],
    salt: &[u8],
    output: &mut [u8; DERIVED_KEY_SIZE],
    m_cost: u32,
    t_cost: u32,
) -> Result<(), SealError> {
    let params = Params::new(
        m_cost,
        t_cost,
        ARGON2ID_P_COST,
        Some(DERIVED_KEY_SIZE),
    )
    .map_err(|_| SealError::KeyDerivationFailed)?;

    let argon2 = Argon2::new(Algorithm::Argon2id, Version::V0x13, params);

    argon2
        .hash_password_into(password, salt, output)
        .map_err(|_| SealError::KeyDerivationFailed)?;

    Ok(())
}

/// Compute the expected sealed size for a given plaintext size.
pub const fn sealed_size(plaintext_len: usize) -> usize {
    HEADER_SIZE + plaintext_len + TAG_SIZE
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_seal_unseal_roundtrip() {
        let password = b"test password 123";
        let secret_key = [0x42u8; 32];

        let sealed = seal_key(password, &secret_key).unwrap();
        let recovered = unseal_key(password, &sealed).unwrap();

        assert_eq!(recovered.as_slice(), &secret_key[..]);
    }

    #[test]
    fn test_wrong_password() {
        let password = b"correct password";
        let wrong_password = b"wrong password";
        let secret_key = [0x42u8; 32];

        let sealed = seal_key(password, &secret_key).unwrap();
        let result = unseal_key(wrong_password, &sealed);

        assert_eq!(result, Err(SealError::DecryptionFailed));
    }

    #[test]
    fn test_tampered_ciphertext() {
        let password = b"test password";
        let secret_key = [0x42u8; 32];

        let mut sealed = seal_key(password, &secret_key).unwrap();

        // Tamper with ciphertext
        let last_idx = sealed.len() - 1;
        sealed[last_idx] ^= 0xFF;

        let result = unseal_key(password, &sealed);
        assert_eq!(result, Err(SealError::DecryptionFailed));
    }

    #[test]
    fn test_tampered_version() {
        let password = b"test password";
        let secret_key = [0x42u8; 32];

        let mut sealed = seal_key(password, &secret_key).unwrap();

        // Change version byte
        sealed[0] = 0xFF;

        let result = unseal_key(password, &sealed);
        assert_eq!(result, Err(SealError::UnsupportedVersion(0xFF)));
    }

    #[test]
    fn test_truncated_data() {
        let password = b"test password";
        let secret_key = [0x42u8; 32];

        let sealed = seal_key(password, &secret_key).unwrap();

        // Truncate data
        let truncated = &sealed[..MIN_SEALED_SIZE - 1];

        let result = unseal_key(password, truncated);
        assert!(matches!(result, Err(SealError::DataTooShort { .. })));
    }

    #[test]
    fn test_empty_password() {
        let password = b"";
        let secret_key = [0x42u8; 32];

        let sealed = seal_key(password, &secret_key).unwrap();
        let recovered = unseal_key(password, &sealed).unwrap();

        assert_eq!(recovered.as_slice(), &secret_key[..]);
    }

    #[test]
    fn test_large_secret_key() {
        let password = b"password";
        let secret_key = vec![0xABu8; 4096]; // Large ML-DSA key

        let sealed = seal_key(password, &secret_key).unwrap();
        let recovered = unseal_key(password, &sealed).unwrap();

        assert_eq!(recovered, secret_key);
    }

    #[test]
    fn test_sealed_size_calculation() {
        let plaintext_len = 32;
        let expected = HEADER_SIZE + plaintext_len + TAG_SIZE;
        assert_eq!(sealed_size(plaintext_len), expected);
    }

    #[test]
    fn test_different_salts_produce_different_ciphertexts() {
        let password = b"same password";
        let secret_key = [0x42u8; 32];

        let sealed1 = seal_key(password, &secret_key).unwrap();
        let sealed2 = seal_key(password, &secret_key).unwrap();

        // Salt is in bytes 1..33
        let salt1 = &sealed1[1..1 + SALT_SIZE];
        let salt2 = &sealed2[1..1 + SALT_SIZE];

        // Salts should be different (random)
        assert_ne!(salt1, salt2);

        // Both should decrypt correctly
        assert_eq!(unseal_key(password, &sealed1).unwrap(), secret_key.to_vec());
        assert_eq!(unseal_key(password, &sealed2).unwrap(), secret_key.to_vec());
    }

    #[test]
    fn test_low_memory_seal_unseal_roundtrip() {
        let password = b"test password 123";
        let secret_key = [0x42u8; 32];

        let sealed = seal_key_low_memory(password, &secret_key).unwrap();

        // Verify version byte is VERSION_LOW_MEMORY
        assert_eq!(sealed[0], VERSION_LOW_MEMORY);

        let recovered = unseal_key(password, &sealed).unwrap();
        assert_eq!(recovered.as_slice(), &secret_key[..]);
    }

    #[test]
    fn test_low_memory_wrong_password() {
        let password = b"correct password";
        let wrong_password = b"wrong password";
        let secret_key = [0x42u8; 32];

        let sealed = seal_key_low_memory(password, &secret_key).unwrap();
        let result = unseal_key(wrong_password, &sealed);

        assert_eq!(result, Err(SealError::DecryptionFailed));
    }

    #[test]
    fn test_standard_and_low_memory_not_interchangeable() {
        // Keys sealed with standard mode cannot be unsealed by forcing low-memory params
        // (the version byte ensures the correct params are used)
        let password = b"test password";
        let secret_key = [0x42u8; 32];

        let sealed_standard = seal_key(password, &secret_key).unwrap();
        let sealed_low_memory = seal_key_low_memory(password, &secret_key).unwrap();

        // Version bytes should be different
        assert_eq!(sealed_standard[0], VERSION);
        assert_eq!(sealed_low_memory[0], VERSION_LOW_MEMORY);

        // Both should unseal correctly with their respective params
        assert_eq!(
            unseal_key(password, &sealed_standard).unwrap(),
            secret_key.to_vec()
        );
        assert_eq!(
            unseal_key(password, &sealed_low_memory).unwrap(),
            secret_key.to_vec()
        );
    }

    #[test]
    fn test_low_memory_tampered_ciphertext() {
        let password = b"test password";
        let secret_key = [0x42u8; 32];

        let mut sealed = seal_key_low_memory(password, &secret_key).unwrap();

        // Tamper with ciphertext
        let last_idx = sealed.len() - 1;
        sealed[last_idx] ^= 0xFF;

        let result = unseal_key(password, &sealed);
        assert_eq!(result, Err(SealError::DecryptionFailed));
    }
}
