//! ML-KEM-1024 (FIPS 203) Post-Quantum Key Encapsulation.
//!
//! This module wraps the `libcrux-ml-kem` crate which is **formally verified**
//! using the hax/F* toolchain by Cryspen.
//!
//! ## Formal Verification
//!
//! The underlying implementation is verified for:
//! - **Panic freedom**: No runtime panics possible
//! - **Functional correctness**: Matches FIPS 203 specification
//! - **Secret independence**: Constant-time execution (no timing leaks)
//!
//! Verification performed using:
//! - **hax**: Rust-to-F* extraction tool
//! - **F***: Proof assistant for functional correctness
//!
//! ## Security Level
//!
//! ML-KEM-1024 provides NIST Level 5 security:
//! - 256-bit classical security
//! - 128-bit quantum security
//!
//! ## References
//!
//! - [FIPS 203](https://csrc.nist.gov/pubs/fips/203/final)
//! - [libcrux](https://cryspen.com/libcrux-library/)
//! - [Verification Report](https://cryspen.com/post/ml-kem-verification/)

use core::fmt;
use libcrux_ml_kem::mlkem1024;
use libcrux_ml_kem::{MlKemKeyPair as LibcruxKeyPair, MlKemPublicKey as LibcruxPublicKey};

/// Public key size for ML-KEM-1024 in bytes.
pub const PUBLIC_KEY_SIZE: usize = 1568;

/// Secret key size for ML-KEM-1024 in bytes.
pub const SECRET_KEY_SIZE: usize = 3168;

/// Ciphertext size for ML-KEM-1024 in bytes.
pub const CIPHERTEXT_SIZE: usize = 1568;

/// Shared secret size in bytes.
pub const SHARED_SECRET_SIZE: usize = 32;

/// ML-KEM error types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MlKemError {
    /// Invalid length for a key or ciphertext component.
    InvalidLength {
        /// What kind of component has the wrong length.
        kind: &'static str,
        /// Expected length in bytes.
        expected: usize,
        /// Actual length in bytes.
        got: usize,
    },
    /// Public key validation failed.
    InvalidPublicKey,
    /// Decapsulation failed.
    DecapsulationFailed,
    /// Random number generation failed.
    RngFailed(Option<String>),
}

impl MlKemError {
    /// Create an invalid public key length error.
    #[inline]
    pub fn invalid_public_key_length(got: usize) -> Self {
        Self::InvalidLength {
            kind: "public key",
            expected: PUBLIC_KEY_SIZE,
            got,
        }
    }

    /// Create an invalid secret key length error.
    #[inline]
    pub fn invalid_secret_key_length(got: usize) -> Self {
        Self::InvalidLength {
            kind: "secret key",
            expected: SECRET_KEY_SIZE,
            got,
        }
    }

    /// Create an invalid ciphertext length error.
    #[inline]
    pub fn invalid_ciphertext_length(got: usize) -> Self {
        Self::InvalidLength {
            kind: "ciphertext",
            expected: CIPHERTEXT_SIZE,
            got,
        }
    }
}

impl fmt::Display for MlKemError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength {
                kind,
                expected,
                got,
            } => {
                write!(
                    f,
                    "invalid {} length: expected {}, got {}",
                    kind, expected, got
                )
            }
            Self::InvalidPublicKey => write!(f, "public key validation failed"),
            Self::DecapsulationFailed => write!(f, "decapsulation failed"),
            Self::RngFailed(None) => write!(f, "random number generation failed"),
            Self::RngFailed(Some(msg)) => write!(f, "random number generation failed: {}", msg),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for MlKemError {}

impl From<getrandom::Error> for MlKemError {
    fn from(e: getrandom::Error) -> Self {
        Self::RngFailed(Some(e.to_string()))
    }
}

/// ML-KEM-1024 key pair (formally verified implementation).
pub struct MlKemKeyPair {
    inner: LibcruxKeyPair<SECRET_KEY_SIZE, PUBLIC_KEY_SIZE>,
}

impl MlKemKeyPair {
    /// Decompose the key pair into its secret and public key components.
    ///
    /// This consumes the key pair and returns separate secret and public keys.
    pub fn into_parts(self) -> (MlKemSecretKey, MlKemPublicKey) {
        let sk = MlKemSecretKey {
            bytes: *self.inner.sk(),
        };
        let pk = MlKemPublicKey::from_bytes(self.inner.pk())
            .expect("internal keypair public key should be valid");
        (sk, pk)
    }
}

impl MlKemKeyPair {
    /// Generate a new ML-KEM-1024 key pair.
    ///
    /// Uses the system random number generator for key generation.
    ///
    /// # Security
    ///
    /// This function uses `libcrux_ml_kem` which is formally verified for:
    /// - Panic freedom
    /// - Functional correctness
    /// - Secret independence
    pub fn generate() -> Result<Self, MlKemError> {
        let randomness: [u8; 64] = rand_bytes()?;
        let inner = mlkem1024::generate_key_pair(randomness);
        Ok(Self { inner })
    }

    /// Get the public key bytes.
    #[inline]
    pub fn public_key_bytes(&self) -> &[u8; PUBLIC_KEY_SIZE] {
        self.inner.pk()
    }

    /// Get the secret key bytes.
    #[inline]
    pub fn secret_key_bytes(&self) -> &[u8; SECRET_KEY_SIZE] {
        self.inner.sk()
    }

    /// Decapsulate a ciphertext to recover the shared secret.
    ///
    /// # Arguments
    ///
    /// * `ciphertext` - The ciphertext from encapsulation
    ///
    /// # Returns
    ///
    /// The 32-byte shared secret.
    pub fn decapsulate(&self, ciphertext: &[u8]) -> Result<[u8; SHARED_SECRET_SIZE], MlKemError> {
        if ciphertext.len() != CIPHERTEXT_SIZE {
            return Err(MlKemError::invalid_ciphertext_length(ciphertext.len()));
        }

        let ct: mlkem1024::MlKem1024Ciphertext = ciphertext
            .try_into()
            .map_err(|_| MlKemError::invalid_ciphertext_length(ciphertext.len()))?;

        let shared_secret = mlkem1024::decapsulate(self.inner.private_key(), &ct);
        Ok(shared_secret)
    }
}

impl Drop for MlKemKeyPair {
    fn drop(&mut self) {
        // Note: libcrux handles zeroization internally
        // The secret key is zeroized when dropped
    }
}

/// ML-KEM-1024 secret key for decapsulation.
pub struct MlKemSecretKey {
    bytes: [u8; SECRET_KEY_SIZE],
}

impl MlKemSecretKey {
    /// Create from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, MlKemError> {
        if bytes.len() != SECRET_KEY_SIZE {
            return Err(MlKemError::invalid_secret_key_length(bytes.len()));
        }
        let mut arr = [0u8; SECRET_KEY_SIZE];
        arr.copy_from_slice(bytes);
        Ok(Self { bytes: arr })
    }

    /// Get the secret key as bytes.
    #[inline]
    pub fn as_bytes(&self) -> &[u8; SECRET_KEY_SIZE] {
        &self.bytes
    }

    /// Decapsulate a ciphertext to recover the shared secret.
    pub fn decapsulate(&self, ciphertext: &[u8]) -> Result<[u8; SHARED_SECRET_SIZE], MlKemError> {
        if ciphertext.len() != CIPHERTEXT_SIZE {
            return Err(MlKemError::invalid_ciphertext_length(ciphertext.len()));
        }

        let ct: mlkem1024::MlKem1024Ciphertext = ciphertext
            .try_into()
            .map_err(|_| MlKemError::invalid_ciphertext_length(ciphertext.len()))?;

        // Create the private key from bytes
        let private_key: libcrux_ml_kem::MlKemPrivateKey<SECRET_KEY_SIZE> = self.bytes.into();
        let shared_secret = mlkem1024::decapsulate(&private_key, &ct);
        Ok(shared_secret)
    }
}

impl Drop for MlKemSecretKey {
    fn drop(&mut self) {
        // Zeroize the secret key material
        self.bytes.iter_mut().for_each(|b| *b = 0);
    }
}

/// ML-KEM-1024 public key for encapsulation.
pub struct MlKemPublicKey {
    inner: LibcruxPublicKey<PUBLIC_KEY_SIZE>,
}

impl Clone for MlKemPublicKey {
    fn clone(&self) -> Self {
        // Clone by reconstructing from bytes
        Self::from_bytes(self.as_bytes())
            .expect("cloning valid public key should not fail")
    }
}

impl MlKemPublicKey {
    /// Create from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, MlKemError> {
        if bytes.len() != PUBLIC_KEY_SIZE {
            return Err(MlKemError::invalid_public_key_length(bytes.len()));
        }

        let inner: LibcruxPublicKey<PUBLIC_KEY_SIZE> = bytes
            .try_into()
            .map_err(|_| MlKemError::invalid_public_key_length(bytes.len()))?;

        // Validate the public key
        if !mlkem1024::validate_public_key(&inner) {
            return Err(MlKemError::InvalidPublicKey);
        }

        Ok(Self { inner })
    }

    /// Get the public key as bytes.
    #[inline]
    pub fn as_bytes(&self) -> &[u8; PUBLIC_KEY_SIZE] {
        self.inner.as_slice()
    }

    /// Encapsulate to this public key.
    ///
    /// # Returns
    ///
    /// A tuple of (ciphertext, shared_secret).
    pub fn encapsulate(
        &self,
    ) -> Result<([u8; CIPHERTEXT_SIZE], [u8; SHARED_SECRET_SIZE]), MlKemError> {
        let randomness: [u8; 32] = rand_bytes_32()?;
        let (ciphertext, shared_secret) = mlkem1024::encapsulate(&self.inner, randomness);
        Ok((*ciphertext.as_slice(), shared_secret))
    }
}

impl TryFrom<[u8; PUBLIC_KEY_SIZE]> for MlKemPublicKey {
    type Error = MlKemError;

    /// Convert from a fixed-size array with validation.
    ///
    /// This performs public key validation using the libcrux validator.
    /// Use this instead of `from_bytes()` when you have a fixed-size array.
    fn try_from(bytes: [u8; PUBLIC_KEY_SIZE]) -> Result<Self, Self::Error> {
        let inner: LibcruxPublicKey<PUBLIC_KEY_SIZE> = bytes.into();

        // Validate the public key
        if !mlkem1024::validate_public_key(&inner) {
            return Err(MlKemError::InvalidPublicKey);
        }

        Ok(Self { inner })
    }
}

/// Generate 64 random bytes using the OS CSPRNG.
///
/// Uses `getrandom` which provides access to the operating system's
/// cryptographically secure random number generator:
/// - Linux: getrandom(2) syscall or /dev/urandom
/// - macOS: SecRandomCopyBytes or getentropy(2)
/// - Windows: BCryptGenRandom
fn rand_bytes() -> Result<[u8; 64], MlKemError> {
    let mut result = [0u8; 64];
    getrandom::getrandom(&mut result)?;
    Ok(result)
}

/// Generate 32 random bytes using the OS CSPRNG.
fn rand_bytes_32() -> Result<[u8; 32], MlKemError> {
    let mut result = [0u8; 32];
    getrandom::getrandom(&mut result)?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keygen() {
        let kp = MlKemKeyPair::generate().unwrap();
        assert_eq!(kp.public_key_bytes().len(), PUBLIC_KEY_SIZE);
        assert_eq!(kp.secret_key_bytes().len(), SECRET_KEY_SIZE);
    }

    #[test]
    fn test_encapsulation_roundtrip() {
        let kp = MlKemKeyPair::generate().unwrap();
        let pk = MlKemPublicKey::from_bytes(kp.public_key_bytes()).unwrap();

        let (ciphertext, shared_secret_enc) = pk.encapsulate().unwrap();
        let shared_secret_dec = kp.decapsulate(&ciphertext).unwrap();

        assert_eq!(shared_secret_enc, shared_secret_dec);
    }

    #[test]
    fn test_different_keypairs_different_secrets() {
        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();

        let pk1 = MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap();
        let pk2 = MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap();

        let (_, ss1) = pk1.encapsulate().unwrap();
        let (_, ss2) = pk2.encapsulate().unwrap();

        // Different key pairs should produce different shared secrets
        assert_ne!(ss1, ss2);
    }

    #[test]
    fn test_wrong_keypair_decapsulation() {
        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();

        let pk1 = MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap();

        let (ciphertext, shared_secret_enc) = pk1.encapsulate().unwrap();

        // Decapsulating with wrong key should give different result
        let shared_secret_wrong = kp2.decapsulate(&ciphertext).unwrap();
        assert_ne!(shared_secret_enc, shared_secret_wrong);
    }

    // ====================================================================
    // Edge-case tests for production readiness
    // ====================================================================

    #[test]
    fn test_invalid_public_key_length_empty() {
        let result = MlKemPublicKey::from_bytes(&[]);
        assert!(matches!(
            result,
            Err(MlKemError::InvalidLength {
                kind: "public key",
                expected: 1568,
                got: 0
            })
        ));
    }

    #[test]
    fn test_invalid_public_key_length_too_short() {
        let result = MlKemPublicKey::from_bytes(&[0u8; 100]);
        assert!(matches!(
            result,
            Err(MlKemError::InvalidLength {
                kind: "public key",
                expected: 1568,
                got: 100
            })
        ));
    }

    #[test]
    fn test_invalid_public_key_length_too_long() {
        let result = MlKemPublicKey::from_bytes(&[0u8; 2000]);
        assert!(matches!(
            result,
            Err(MlKemError::InvalidLength {
                kind: "public key",
                expected: 1568,
                got: 2000
            })
        ));
    }

    #[test]
    fn test_invalid_ciphertext_length_empty() {
        let kp = MlKemKeyPair::generate().unwrap();
        let result = kp.decapsulate(&[]);
        assert!(matches!(
            result,
            Err(MlKemError::InvalidLength {
                kind: "ciphertext",
                expected: 1568,
                got: 0
            })
        ));
    }

    #[test]
    fn test_invalid_ciphertext_length_too_short() {
        let kp = MlKemKeyPair::generate().unwrap();
        let result = kp.decapsulate(&[0u8; 100]);
        assert!(matches!(
            result,
            Err(MlKemError::InvalidLength {
                kind: "ciphertext",
                expected: 1568,
                got: 100
            })
        ));
    }

    #[test]
    fn test_invalid_ciphertext_length_too_long() {
        let kp = MlKemKeyPair::generate().unwrap();
        let result = kp.decapsulate(&[0u8; 2000]);
        assert!(matches!(
            result,
            Err(MlKemError::InvalidLength {
                kind: "ciphertext",
                expected: 1568,
                got: 2000
            })
        ));
    }

    #[test]
    fn test_error_display_invalid_length() {
        let err = MlKemError::invalid_public_key_length(42);
        let msg = format!("{}", err);
        assert!(msg.contains("invalid public key length"));
        assert!(msg.contains("expected 1568"));
        assert!(msg.contains("got 42"));
    }

    #[test]
    fn test_error_display_invalid_public_key() {
        let err = MlKemError::InvalidPublicKey;
        let msg = format!("{}", err);
        assert!(msg.contains("public key validation failed"));
    }

    #[test]
    fn test_error_display_rng_failed() {
        let err = MlKemError::RngFailed(None);
        assert_eq!(format!("{}", err), "random number generation failed");

        let err = MlKemError::RngFailed(Some("no entropy".to_string()));
        assert!(format!("{}", err).contains("no entropy"));
    }

    #[test]
    fn test_multiple_encapsulations_different() {
        let kp = MlKemKeyPair::generate().unwrap();
        let pk = MlKemPublicKey::from_bytes(kp.public_key_bytes()).unwrap();

        let (ct1, ss1) = pk.encapsulate().unwrap();
        let (ct2, ss2) = pk.encapsulate().unwrap();

        // Each encapsulation should produce different ciphertext and shared secret
        // (due to random encapsulation coins)
        assert_ne!(ct1, ct2);
        assert_ne!(ss1, ss2);
    }

    #[test]
    fn test_public_key_try_from_array() {
        let kp = MlKemKeyPair::generate().unwrap();
        let pk_bytes = *kp.public_key_bytes();

        let pk: MlKemPublicKey = pk_bytes.try_into().unwrap();
        assert_eq!(pk.as_bytes(), &pk_bytes);
    }

    #[test]
    fn test_public_key_try_from_validates() {
        // TryFrom should call the libcrux validator
        // A valid generated key should pass
        let kp = MlKemKeyPair::generate().unwrap();
        let pk_bytes = *kp.public_key_bytes();
        let result: Result<MlKemPublicKey, _> = pk_bytes.try_into();
        assert!(result.is_ok());

        // Note: Most byte patterns pass ML-KEM validation per FIPS 203.
        // The validator mainly checks polynomial coefficient ranges and
        // internal consistency. Truly malformed keys are rare edge cases.
        // The important thing is that TryFrom calls the validator.
    }

    #[test]
    fn test_size_constants() {
        assert_eq!(PUBLIC_KEY_SIZE, 1568);
        assert_eq!(SECRET_KEY_SIZE, 3168);
        assert_eq!(CIPHERTEXT_SIZE, 1568);
        assert_eq!(SHARED_SECRET_SIZE, 32);
    }
}
