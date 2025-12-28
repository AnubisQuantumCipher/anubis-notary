//! ML-DSA-87 (Dilithium) post-quantum digital signatures.
//!
//! ML-DSA-87 is a lattice-based signature scheme standardized in FIPS 204.
//! It provides NIST Level 5 security (256-bit classical, 128-bit quantum).
//!
//! ## Parameters (ML-DSA-87)
//!
//! - Public key: 2592 bytes
//! - Secret key: 4896 bytes
//! - Signature: 4627 bytes
//! - Security: NIST Level 5
//!
//! ## Formal Verification (libcrux)
//!
//! This module uses **Cryspen libcrux-ml-dsa**, which is formally verified using
//! the hax/F* toolchain. Verification provides:
//! - Panic freedom (no runtime panics possible)
//! - Functional correctness (matches FIPS 204 specification)
//! - Secret independence (timing side-channel resistance)
//!
//! ## Our Wrapper Verification Status
//!
//! **NOT FORMALLY VERIFIED**. The RefinedRust-style specifications in doc comments
//! describe intended properties, not actual verification. While libcrux is verified,
//! our wrapper code (fault detection, hedged signing, API surface) has not been
//! formally proven.
//!
//! The specifications in `specs/refinedrust/theories/mldsa_spec.v` represent
//! design goals we intend to verify in the future.
//!
//! ## References
//!
//! - [FIPS 204: ML-DSA Standard](https://csrc.nist.gov/pubs/fips/204/final)
//! - [libcrux](https://github.com/cryspen/libcrux)
//! - [Cryspen Formal Verification](https://cryspen.com/post/ml-kem-verification/)

use libcrux_ml_dsa::ml_dsa_87::{
    self, MLDSA87KeyPair, MLDSA87Signature, MLDSA87SigningKey, MLDSA87VerificationKey,
};
use zeroize::Zeroize;

// Re-export for trait implementations
pub use signature::{Signer, Verifier};

/// Public key size in bytes (FIPS 204 ML-DSA-87).
pub const PUBLIC_KEY_SIZE: usize = 2592;

/// Secret key size in bytes (FIPS 204 ML-DSA-87).
pub const SECRET_KEY_SIZE: usize = 4896;

/// Signature size in bytes (FIPS 204 ML-DSA-87).
pub const SIGNATURE_SIZE: usize = 4627;

/// Seed size for deterministic key generation.
pub const SEED_SIZE: usize = 32;

/// Size of randomness required for key generation.
const KEY_GEN_RANDOMNESS_SIZE: usize = 32;

/// Size of randomness required for signing.
const SIGNING_RANDOMNESS_SIZE: usize = 32;

/// Maximum context length for domain separation (FIPS 204 requirement).
pub const MAX_CONTEXT_LENGTH: usize = 255;

/// ML-DSA error types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MlDsaError {
    /// Invalid length for key or signature.
    InvalidLength {
        /// What was being parsed.
        kind: &'static str,
        /// Expected length in bytes.
        expected: usize,
        /// Actual length in bytes.
        got: usize,
    },
    /// Signature verification failed.
    VerificationFailed,
    /// Signing operation failed.
    SigningFailed,
    /// Random number generation failed.
    RngFailed(Option<String>),
    /// Context too long (max 255 bytes per FIPS 204).
    ContextTooLong {
        /// Actual length provided.
        got: usize,
    },
    /// Fault detected during cryptographic operation.
    ///
    /// This indicates a potential fault injection attack was detected through
    /// post-operation verification. The signature may be corrupted.
    FaultDetected,
}

impl MlDsaError {
    /// Create an invalid length error for public key.
    #[inline]
    pub fn invalid_public_key_length(got: usize) -> Self {
        Self::InvalidLength {
            kind: "public key",
            expected: PUBLIC_KEY_SIZE,
            got,
        }
    }

    /// Create an invalid length error for secret key.
    #[inline]
    pub fn invalid_secret_key_length(got: usize) -> Self {
        Self::InvalidLength {
            kind: "secret key",
            expected: SECRET_KEY_SIZE,
            got,
        }
    }

    /// Create an invalid length error for signature.
    #[inline]
    pub fn invalid_signature_length(got: usize) -> Self {
        Self::InvalidLength {
            kind: "signature",
            expected: SIGNATURE_SIZE,
            got,
        }
    }

    /// Create an invalid length error for seed.
    #[inline]
    pub fn invalid_seed_length(got: usize) -> Self {
        Self::InvalidLength {
            kind: "seed",
            expected: SEED_SIZE,
            got,
        }
    }
}

impl core::fmt::Display for MlDsaError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidLength { kind, expected, got } => {
                write!(f, "invalid {} length: expected {}, got {}", kind, expected, got)
            }
            Self::VerificationFailed => write!(f, "signature verification failed"),
            Self::SigningFailed => write!(f, "signing operation failed"),
            Self::RngFailed(Some(msg)) => write!(f, "RNG failed: {}", msg),
            Self::RngFailed(None) => write!(f, "RNG failed"),
            Self::ContextTooLong { got } => {
                write!(f, "context too long: max {}, got {}", MAX_CONTEXT_LENGTH, got)
            }
            Self::FaultDetected => {
                write!(f, "fault detected: signature verification after signing failed")
            }
        }
    }
}

impl std::error::Error for MlDsaError {}

impl From<getrandom::Error> for MlDsaError {
    fn from(e: getrandom::Error) -> Self {
        Self::RngFailed(Some(e.to_string()))
    }
}

impl From<signature::Error> for MlDsaError {
    fn from(_: signature::Error) -> Self {
        Self::VerificationFailed
    }
}

/// Generate cryptographically secure random bytes.
fn secure_random<const N: usize>() -> Result<[u8; N], MlDsaError> {
    let mut buf = [0u8; N];
    getrandom::getrandom(&mut buf)?;
    Ok(buf)
}

/// ML-DSA-87 public key (verifying key).
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("pk" : "mldsa_spec.MLDSA87_pk")]
/// #[rr::invariant("len(pk.bytes) = PUBLIC_KEY_SIZE")]
/// #[rr::invariant("valid_pk(pk)")]
/// ```
#[derive(Clone)]
pub struct PublicKey {
    inner: MLDSA87VerificationKey,
}

impl PublicKey {
    /// Create a public key from bytes.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("bytes" : "list u8")]
    /// #[rr::args("#bytes")]
    /// #[rr::requires("len(bytes) = PUBLIC_KEY_SIZE -> valid_pk_bytes(bytes)")]
    /// #[rr::returns("Ok(pk) where pk.bytes = bytes | Err(InvalidLength)")]
    /// #[rr::ensures("is_ok(result) <-> len(bytes) = PUBLIC_KEY_SIZE")]
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, MlDsaError> {
        let key_bytes: [u8; PUBLIC_KEY_SIZE] = bytes
            .try_into()
            .map_err(|_| MlDsaError::invalid_public_key_length(bytes.len()))?;

        Ok(Self {
            inner: MLDSA87VerificationKey::new(key_bytes),
        })
    }

    /// Get the public key as bytes.
    #[inline]
    pub fn to_bytes(&self) -> [u8; PUBLIC_KEY_SIZE] {
        *self.inner.as_ref()
    }

    /// Verify a signature on a message.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("msg" : "list u8", "sig" : "mldsa_spec.MLDSA87_sig")]
    /// #[rr::args("#msg", "#sig")]
    /// #[rr::returns("#mldsa_verify(self.pk, msg, sig)")]
    /// #[rr::ensures("timing_independent_of(sig.bytes)")]
    /// #[rr::pure]
    /// ```
    ///
    /// Security: Returns true iff the signature is valid for the message under this public key.
    /// The verification is constant-time in the signature to prevent timing attacks.
    pub fn verify(&self, message: &[u8], signature: &Signature) -> bool {
        self.verify_with_context(message, b"", signature)
    }

    /// Verify a signature on a message with domain separation context.
    ///
    /// The context must be at most 255 bytes per FIPS 204.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("msg" : "list u8", "ctx" : "list u8", "sig" : "mldsa_spec.MLDSA87_sig")]
    /// #[rr::args("#msg", "#ctx", "#sig")]
    /// #[rr::requires("len(ctx) <= MAX_CONTEXT_LENGTH")]
    /// #[rr::returns("#mldsa_verify_ctx(self.pk, msg, ctx, sig)")]
    /// #[rr::ensures("timing_independent_of(sig.bytes)")]
    /// ```
    pub fn verify_with_context(&self, message: &[u8], context: &[u8], signature: &Signature) -> bool {
        ml_dsa_87::verify(&self.inner, message, context, &signature.inner).is_ok()
    }
}

/// ML-DSA-87 secret key (signing key).
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("sk" : "mldsa_spec.MLDSA87_sk")]
/// #[rr::invariant("len(sk.bytes) = SECRET_KEY_SIZE")]
/// #[rr::invariant("valid_sk(sk)")]
/// #[rr::owns("sk.bytes")]
/// ```
///
/// Security: This type implements Zeroize to securely erase the key material on drop.
/// The inner bytes are overwritten with zeros before deallocation.
pub struct SecretKey {
    inner: MLDSA87SigningKey,
}

impl SecretKey {
    /// Create a secret key from bytes.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("bytes" : "list u8")]
    /// #[rr::args("#bytes")]
    /// #[rr::requires("len(bytes) = SECRET_KEY_SIZE -> valid_sk_bytes(bytes)")]
    /// #[rr::returns("Ok(sk) where sk.bytes = bytes | Err(InvalidLength)")]
    /// #[rr::ensures("is_ok(result) <-> len(bytes) = SECRET_KEY_SIZE")]
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, MlDsaError> {
        let key_bytes: [u8; SECRET_KEY_SIZE] = bytes
            .try_into()
            .map_err(|_| MlDsaError::invalid_secret_key_length(bytes.len()))?;

        Ok(Self {
            inner: MLDSA87SigningKey::new(key_bytes),
        })
    }

    /// Get the secret key as bytes.
    #[inline]
    pub fn to_bytes(&self) -> [u8; SECRET_KEY_SIZE] {
        *self.inner.as_ref()
    }

    /// Sign a message.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("msg" : "list u8")]
    /// #[rr::args("#msg")]
    /// #[rr::returns("Ok(sig) | Err(e)")]
    /// #[rr::ensures("is_ok(result) -> mldsa_verify(corresponding_pk(self), msg, unwrap(result))")]
    /// #[rr::ensures("len(unwrap(result).bytes) = SIGNATURE_SIZE")]
    /// #[rr::timing("constant_time_in(self.sk)")]
    /// ```
    ///
    /// EUF-CMA Security: The signature scheme provides existential unforgeability
    /// under chosen message attack. An adversary cannot forge a signature on any
    /// message without knowledge of the secret key.
    pub fn sign(&self, message: &[u8]) -> Result<Signature, MlDsaError> {
        self.sign_with_context(message, b"")
    }

    /// Sign a message with domain separation context.
    ///
    /// The context must be at most 255 bytes per FIPS 204.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("msg" : "list u8", "ctx" : "list u8")]
    /// #[rr::args("#msg", "#ctx")]
    /// #[rr::requires("len(ctx) <= MAX_CONTEXT_LENGTH")]
    /// #[rr::returns("Ok(sig) | Err(ContextTooLong) | Err(SigningFailed)")]
    /// #[rr::ensures("is_ok(result) -> mldsa_verify_ctx(corresponding_pk(self), msg, ctx, unwrap(result))")]
    /// #[rr::timing("constant_time_in(self.sk)")]
    /// ```
    pub fn sign_with_context(&self, message: &[u8], context: &[u8]) -> Result<Signature, MlDsaError> {
        if context.len() > MAX_CONTEXT_LENGTH {
            return Err(MlDsaError::ContextTooLong { got: context.len() });
        }

        let randomness: [u8; SIGNING_RANDOMNESS_SIZE] = secure_random()?;

        let inner = ml_dsa_87::sign(&self.inner, message, context, randomness)
            .map_err(|_| MlDsaError::SigningFailed)?;

        Ok(Signature { inner })
    }
}

impl Clone for SecretKey {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl Zeroize for SecretKey {
    /// Securely erase the secret key material.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::requires("self.sk is valid")]
    /// #[rr::ensures("forall i. 0 <= i < SECRET_KEY_SIZE -> self.sk.bytes[i] = 0")]
    /// #[rr::ensures("zeroized(self)")]
    /// #[rr::volatile_write]
    /// ```
    fn zeroize(&mut self) {
        // Zero the internal key by overwriting with zeros
        // libcrux uses fixed arrays internally
        let zeros = [0u8; SECRET_KEY_SIZE];
        self.inner = MLDSA87SigningKey::new(zeros);
    }
}

impl Drop for SecretKey {
    fn drop(&mut self) {
        self.zeroize();
    }
}

/// ML-DSA-87 signature.
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("sig" : "mldsa_spec.MLDSA87_sig")]
/// #[rr::invariant("len(sig.bytes) = SIGNATURE_SIZE")]
/// ```
#[derive(Clone)]
pub struct Signature {
    inner: MLDSA87Signature,
}

impl Signature {
    /// Create a signature from bytes.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("bytes" : "list u8")]
    /// #[rr::args("#bytes")]
    /// #[rr::returns("Ok(sig) where sig.bytes = bytes | Err(InvalidLength)")]
    /// #[rr::ensures("is_ok(result) <-> len(bytes) = SIGNATURE_SIZE")]
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, MlDsaError> {
        let sig_bytes: [u8; SIGNATURE_SIZE] = bytes
            .try_into()
            .map_err(|_| MlDsaError::invalid_signature_length(bytes.len()))?;

        Ok(Self {
            inner: MLDSA87Signature::new(sig_bytes),
        })
    }

    /// Get the signature as bytes.
    #[inline]
    pub fn to_bytes(&self) -> [u8; SIGNATURE_SIZE] {
        *self.inner.as_ref()
    }
}

/// ML-DSA-87 key pair.
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("kp" : "mldsa_spec.MLDSA87_keypair")]
/// #[rr::invariant("valid_keypair(kp.pk, kp.sk)")]
/// #[rr::invariant("forall m. mldsa_verify(kp.pk, m, mldsa_sign(kp.sk, m))")]
/// #[rr::owns("kp.sk.bytes")]
/// ```
pub struct KeyPair {
    /// Public key (verifying key).
    pub public: PublicKey,
    /// Secret key (signing key).
    secret: SecretKey,
}

impl KeyPair {
    /// Generate a new key pair from a 32-byte seed.
    ///
    /// The key generation is deterministic: the same seed always produces
    /// the same key pair. This implements ML-DSA.KeyGen_internal from FIPS 204.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("seed" : "array u8 SEED_SIZE")]
    /// #[rr::args("#seed")]
    /// #[rr::returns("Ok(kp) | Err(InvalidLength)")]
    /// #[rr::ensures("is_ok(result) -> valid_keypair(unwrap(result))")]
    /// #[rr::ensures("is_ok(result) -> forall m. mldsa_verify(unwrap(result).pk, m, mldsa_sign(unwrap(result).sk, m))")]
    /// #[rr::ensures("deterministic: same seed -> same keypair")]
    /// ```
    pub fn from_seed(seed: &[u8]) -> Result<Self, MlDsaError> {
        let randomness: [u8; KEY_GEN_RANDOMNESS_SIZE] = seed
            .try_into()
            .map_err(|_| MlDsaError::invalid_seed_length(seed.len()))?;

        // Use the FIPS 204 deterministic key generation
        let keypair: MLDSA87KeyPair = ml_dsa_87::generate_key_pair(randomness);

        Ok(Self {
            public: PublicKey {
                inner: keypair.verification_key,
            },
            secret: SecretKey {
                inner: keypair.signing_key,
            },
        })
    }

    /// Generate a new random key pair.
    ///
    /// Uses the OS CSPRNG to generate cryptographically secure randomness.
    pub fn generate() -> Result<Self, MlDsaError> {
        let randomness: [u8; KEY_GEN_RANDOMNESS_SIZE] = secure_random()?;
        let keypair: MLDSA87KeyPair = ml_dsa_87::generate_key_pair(randomness);

        Ok(Self {
            public: PublicKey {
                inner: keypair.verification_key,
            },
            secret: SecretKey {
                inner: keypair.signing_key,
            },
        })
    }

    /// Get the public key.
    #[inline]
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }

    /// Get the secret key.
    #[inline]
    pub fn secret_key(&self) -> &SecretKey {
        &self.secret
    }

    /// Sign a message.
    ///
    /// # Note
    ///
    /// For maximum fault injection resistance, prefer `sign_verified` which
    /// verifies the signature after generation.
    #[inline]
    pub fn sign(&self, message: &[u8]) -> Result<Signature, MlDsaError> {
        self.secret.sign(message)
    }

    /// Sign a message with domain separation context.
    ///
    /// # Note
    ///
    /// For maximum fault injection resistance, prefer `sign_verified_with_context`
    /// which verifies the signature after generation.
    #[inline]
    pub fn sign_with_context(&self, message: &[u8], context: &[u8]) -> Result<Signature, MlDsaError> {
        self.secret.sign_with_context(message, context)
    }

    /// Sign a message with fault injection countermeasures.
    ///
    /// This method provides protection against fault injection attacks by:
    /// 1. Generating the signature
    /// 2. Verifying the signature with the public key
    /// 3. Only returning the signature if verification succeeds
    ///
    /// # Security
    ///
    /// This countermeasure detects faults that would produce invalid signatures,
    /// such as:
    /// - Voltage/clock glitching during signing
    /// - Electromagnetic fault injection
    /// - Computation skipping attacks
    ///
    /// The ~50% overhead (one extra verification) provides strong fault detection.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("msg" : "list u8")]
    /// #[rr::args("#msg")]
    /// #[rr::returns("Ok(sig) | Err(e)")]
    /// #[rr::ensures("is_ok(result) -> mldsa_verify(self.pk, msg, unwrap(result))")]
    /// #[rr::ensures("is_ok(result) -> fault_verified(result)")]
    /// ```
    pub fn sign_verified(&self, message: &[u8]) -> Result<Signature, MlDsaError> {
        self.sign_verified_with_context(message, b"")
    }

    /// Sign a message with context and fault injection countermeasures.
    ///
    /// See `sign_verified` for security details.
    ///
    /// # Arguments
    ///
    /// * `message` - The message to sign
    /// * `context` - Domain separation context (max 255 bytes per FIPS 204)
    ///
    /// # Returns
    ///
    /// The signature if generation and verification succeed, or:
    /// - `SigningFailed` if the signing operation failed
    /// - `FaultDetected` if post-signing verification failed (potential attack)
    /// - `ContextTooLong` if context exceeds 255 bytes
    pub fn sign_verified_with_context(
        &self,
        message: &[u8],
        context: &[u8],
    ) -> Result<Signature, MlDsaError> {
        // Generate the signature
        let signature = self.secret.sign_with_context(message, context)?;

        // Verify the signature we just generated
        // This detects faults that corrupted the signature
        if self.public.verify_with_context(message, context, &signature) {
            Ok(signature)
        } else {
            // Signature verification failed - potential fault injection attack
            // Do NOT return the corrupted signature
            Err(MlDsaError::FaultDetected)
        }
    }
}

impl Clone for KeyPair {
    fn clone(&self) -> Self {
        Self {
            public: self.public.clone(),
            secret: self.secret.clone(),
        }
    }
}

impl Zeroize for KeyPair {
    fn zeroize(&mut self) {
        self.secret.zeroize();
    }
}

impl Drop for KeyPair {
    fn drop(&mut self) {
        self.zeroize();
    }
}

// ============================================================================
// Signature crate trait implementations
// ============================================================================

impl signature::SignatureEncoding for Signature {
    type Repr = [u8; SIGNATURE_SIZE];
}

impl TryFrom<&[u8]> for Signature {
    type Error = MlDsaError;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        Self::from_bytes(bytes)
    }
}

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        self.inner.as_ref()
    }
}

impl Signer<Signature> for SecretKey {
    fn try_sign(&self, msg: &[u8]) -> Result<Signature, signature::Error> {
        self.sign(msg).map_err(|_| signature::Error::new())
    }
}

impl Signer<Signature> for KeyPair {
    fn try_sign(&self, msg: &[u8]) -> Result<Signature, signature::Error> {
        self.sign(msg).map_err(|_| signature::Error::new())
    }
}

impl Verifier<Signature> for PublicKey {
    fn verify(&self, msg: &[u8], signature: &Signature) -> Result<(), signature::Error> {
        if PublicKey::verify(self, msg, signature) {
            Ok(())
        } else {
            Err(signature::Error::new())
        }
    }
}

// ============================================================================
// Additional conversions
// ============================================================================

impl From<[u8; PUBLIC_KEY_SIZE]> for PublicKey {
    fn from(bytes: [u8; PUBLIC_KEY_SIZE]) -> Self {
        Self {
            inner: MLDSA87VerificationKey::new(bytes),
        }
    }
}

impl From<[u8; SECRET_KEY_SIZE]> for SecretKey {
    fn from(bytes: [u8; SECRET_KEY_SIZE]) -> Self {
        Self {
            inner: MLDSA87SigningKey::new(bytes),
        }
    }
}

impl From<[u8; SIGNATURE_SIZE]> for Signature {
    fn from(bytes: [u8; SIGNATURE_SIZE]) -> Self {
        Self {
            inner: MLDSA87Signature::new(bytes),
        }
    }
}

impl From<PublicKey> for [u8; PUBLIC_KEY_SIZE] {
    fn from(pk: PublicKey) -> Self {
        pk.to_bytes()
    }
}

impl From<&PublicKey> for [u8; PUBLIC_KEY_SIZE] {
    fn from(pk: &PublicKey) -> Self {
        pk.to_bytes()
    }
}

impl From<Signature> for [u8; SIGNATURE_SIZE] {
    fn from(sig: Signature) -> Self {
        sig.to_bytes()
    }
}

impl From<&Signature> for [u8; SIGNATURE_SIZE] {
    fn from(sig: &Signature) -> Self {
        sig.to_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keypair_generation() {
        let seed = [0u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();
        assert_eq!(kp.public_key().to_bytes().len(), PUBLIC_KEY_SIZE);
    }

    #[test]
    fn test_random_keypair_generation() {
        let kp = KeyPair::generate().unwrap();
        assert_eq!(kp.public_key().to_bytes().len(), PUBLIC_KEY_SIZE);
    }

    #[test]
    fn test_sign_verify() {
        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        let message = b"Hello, post-quantum world!";
        let signature = kp.sign(message).unwrap();

        assert!(kp.public_key().verify(message, &signature));
    }

    #[test]
    fn test_sign_verify_with_context() {
        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        let message = b"Hello, post-quantum world!";
        let context = b"anubis-notary-v1";
        let signature = kp.sign_with_context(message, context).unwrap();

        assert!(kp.public_key().verify_with_context(message, context, &signature));
        // Wrong context should fail
        assert!(!kp.public_key().verify_with_context(message, b"wrong-context", &signature));
    }

    #[test]
    fn test_wrong_message_fails() {
        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        let message = b"Original message";
        let signature = kp.sign(message).unwrap();

        let wrong_message = b"Tampered message";
        assert!(!kp.public_key().verify(wrong_message, &signature));
    }

    #[test]
    fn test_deterministic_keygen() {
        let seed = [1u8; SEED_SIZE];
        let kp1 = KeyPair::from_seed(&seed).unwrap();
        let kp2 = KeyPair::from_seed(&seed).unwrap();

        assert_eq!(kp1.public_key().to_bytes(), kp2.public_key().to_bytes());
    }

    #[test]
    fn test_different_seeds_different_keys() {
        let seed1 = [1u8; SEED_SIZE];
        let seed2 = [2u8; SEED_SIZE];
        let kp1 = KeyPair::from_seed(&seed1).unwrap();
        let kp2 = KeyPair::from_seed(&seed2).unwrap();

        assert_ne!(kp1.public_key().to_bytes(), kp2.public_key().to_bytes());
    }

    #[test]
    fn test_signature_size() {
        let seed = [0u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();
        let sig = kp.sign(b"test").unwrap();

        assert_eq!(sig.to_bytes().len(), SIGNATURE_SIZE);
    }

    #[test]
    fn test_key_serialization_roundtrip() {
        let seed = [99u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        // Test public key roundtrip
        let pk_bytes = kp.public_key().to_bytes();
        let pk_restored = PublicKey::from_bytes(&pk_bytes).unwrap();
        assert_eq!(pk_bytes, pk_restored.to_bytes());

        // Test secret key roundtrip
        let sk_bytes = kp.secret_key().to_bytes();
        let sk_restored = SecretKey::from_bytes(&sk_bytes).unwrap();
        assert_eq!(sk_bytes, sk_restored.to_bytes());

        // Verify restored key can sign
        let message = b"Test message";
        let sig = sk_restored.sign(message).unwrap();
        assert!(pk_restored.verify(message, &sig));
    }

    #[test]
    fn test_signature_serialization_roundtrip() {
        let seed = [77u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        let message = b"Roundtrip test";
        let sig = kp.sign(message).unwrap();

        let sig_bytes = sig.to_bytes();
        let sig_restored = Signature::from_bytes(&sig_bytes).unwrap();

        assert!(kp.public_key().verify(message, &sig_restored));
    }

    // ========================================================================
    // Edge case tests
    // ========================================================================

    #[test]
    fn test_context_too_long() {
        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        // Context exactly at limit (255 bytes) should work
        let max_context = [0u8; MAX_CONTEXT_LENGTH];
        let result = kp.sign_with_context(b"test", &max_context);
        assert!(result.is_ok());

        // Context 1 byte over limit (256 bytes) should fail
        let too_long_context = [0u8; MAX_CONTEXT_LENGTH + 1];
        let result = kp.sign_with_context(b"test", &too_long_context);
        assert!(matches!(result, Err(MlDsaError::ContextTooLong { got: 256 })));
    }

    #[test]
    fn test_invalid_public_key_length() {
        // Too short
        let short = [0u8; PUBLIC_KEY_SIZE - 1];
        let result = PublicKey::from_bytes(&short);
        assert!(matches!(
            result,
            Err(MlDsaError::InvalidLength {
                kind: "public key",
                expected: PUBLIC_KEY_SIZE,
                got,
            }) if got == PUBLIC_KEY_SIZE - 1
        ));

        // Too long
        let long = [0u8; PUBLIC_KEY_SIZE + 1];
        let result = PublicKey::from_bytes(&long);
        assert!(matches!(
            result,
            Err(MlDsaError::InvalidLength {
                kind: "public key",
                expected: PUBLIC_KEY_SIZE,
                got,
            }) if got == PUBLIC_KEY_SIZE + 1
        ));

        // Empty
        let result = PublicKey::from_bytes(&[]);
        assert!(matches!(
            result,
            Err(MlDsaError::InvalidLength {
                kind: "public key",
                expected: PUBLIC_KEY_SIZE,
                got: 0,
            })
        ));
    }

    #[test]
    fn test_invalid_secret_key_length() {
        let short = [0u8; SECRET_KEY_SIZE - 1];
        let result = SecretKey::from_bytes(&short);
        assert!(matches!(
            result,
            Err(MlDsaError::InvalidLength {
                kind: "secret key",
                expected: SECRET_KEY_SIZE,
                ..
            })
        ));
    }

    #[test]
    fn test_invalid_signature_length() {
        let short = [0u8; SIGNATURE_SIZE - 1];
        let result = Signature::from_bytes(&short);
        assert!(matches!(
            result,
            Err(MlDsaError::InvalidLength {
                kind: "signature",
                expected: SIGNATURE_SIZE,
                ..
            })
        ));
    }

    #[test]
    fn test_invalid_seed_length() {
        // Too short
        let short = [0u8; SEED_SIZE - 1];
        let result = KeyPair::from_seed(&short);
        assert!(matches!(
            result,
            Err(MlDsaError::InvalidLength {
                kind: "seed",
                expected: SEED_SIZE,
                ..
            })
        ));

        // Too long
        let long = [0u8; SEED_SIZE + 1];
        let result = KeyPair::from_seed(&long);
        assert!(matches!(
            result,
            Err(MlDsaError::InvalidLength {
                kind: "seed",
                expected: SEED_SIZE,
                ..
            })
        ));
    }

    #[test]
    fn test_zeroize_clears_secret_key() {
        let seed = [0xAB; SEED_SIZE];
        let mut kp = KeyPair::from_seed(&seed).unwrap();

        // Get bytes before zeroize
        let sk_bytes_before = kp.secret_key().to_bytes();
        assert!(sk_bytes_before.iter().any(|&b| b != 0));

        // Zeroize
        kp.zeroize();

        // Get bytes after zeroize
        let sk_bytes_after = kp.secret_key().to_bytes();
        assert!(sk_bytes_after.iter().all(|&b| b == 0));
    }

    #[test]
    fn test_signer_trait() {
        use signature::Signer;

        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        let message = b"Test message for Signer trait";

        // Use Signer trait
        let sig: Signature = kp.try_sign(message).unwrap();

        // Verify using the inherent method
        assert!(kp.public_key().verify(message, &sig));
    }

    #[test]
    fn test_verifier_trait() {
        use signature::Verifier;

        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        let message = b"Test message for Verifier trait";
        let sig = kp.sign(message).unwrap();

        // Use Verifier trait
        let result = Verifier::verify(kp.public_key(), message, &sig);
        assert!(result.is_ok());

        // Wrong message should fail
        let wrong_result = Verifier::verify(kp.public_key(), b"wrong", &sig);
        assert!(wrong_result.is_err());
    }

    #[test]
    fn test_from_array_conversions() {
        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        // PublicKey from array
        let pk_bytes: [u8; PUBLIC_KEY_SIZE] = kp.public_key().to_bytes();
        let pk_from_array: PublicKey = pk_bytes.into();
        assert_eq!(pk_from_array.to_bytes(), kp.public_key().to_bytes());

        // Signature from array
        let sig = kp.sign(b"test").unwrap();
        let sig_bytes: [u8; SIGNATURE_SIZE] = sig.to_bytes();
        let sig_from_array: Signature = sig_bytes.into();
        assert!(kp.public_key().verify(b"test", &sig_from_array));
    }

    #[test]
    fn test_error_display() {
        let err = MlDsaError::InvalidLength {
            kind: "public key",
            expected: 2592,
            got: 100,
        };
        assert_eq!(
            format!("{}", err),
            "invalid public key length: expected 2592, got 100"
        );

        let err = MlDsaError::ContextTooLong { got: 300 };
        assert_eq!(format!("{}", err), "context too long: max 255, got 300");

        let err = MlDsaError::VerificationFailed;
        assert_eq!(format!("{}", err), "signature verification failed");

        let err = MlDsaError::RngFailed(Some("entropy exhausted".to_string()));
        assert_eq!(format!("{}", err), "RNG failed: entropy exhausted");
    }

    #[test]
    fn test_try_from_slice_for_signature() {
        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();
        let sig = kp.sign(b"test").unwrap();

        // Use TryFrom trait
        let sig_bytes = sig.to_bytes();
        let sig_slice: &[u8] = &sig_bytes;
        let sig_from_try: Signature = sig_slice.try_into().unwrap();
        assert!(kp.public_key().verify(b"test", &sig_from_try));
    }

    // ========================================================================
    // Fault injection countermeasure tests
    // ========================================================================

    #[test]
    fn test_sign_verified() {
        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        let message = b"Test message for verified signing";
        let signature = kp.sign_verified(message).unwrap();

        // Signature should be valid
        assert!(kp.public_key().verify(message, &signature));
    }

    #[test]
    fn test_sign_verified_with_context() {
        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();

        let message = b"Test message";
        let context = b"test-context";
        let signature = kp.sign_verified_with_context(message, context).unwrap();

        // Signature should be valid with correct context
        assert!(kp.public_key().verify_with_context(message, context, &signature));

        // And invalid with wrong context
        assert!(!kp.public_key().verify_with_context(message, b"wrong", &signature));
    }

    #[test]
    fn test_sign_verified_multiple_messages() {
        let kp = KeyPair::generate().unwrap();

        // Sign multiple messages with fault protection
        for i in 0..10 {
            let message = format!("Message number {}", i);
            let sig = kp.sign_verified(message.as_bytes()).unwrap();
            assert!(kp.public_key().verify(message.as_bytes(), &sig));
        }
    }

    #[test]
    fn test_fault_detected_error_display() {
        let err = MlDsaError::FaultDetected;
        assert_eq!(
            format!("{}", err),
            "fault detected: signature verification after signing failed"
        );
    }

    #[test]
    fn test_signature_as_ref() {
        let seed = [42u8; SEED_SIZE];
        let kp = KeyPair::from_seed(&seed).unwrap();
        let sig = kp.sign(b"test").unwrap();

        // Use AsRef trait
        let sig_slice: &[u8] = sig.as_ref();
        assert_eq!(sig_slice.len(), SIGNATURE_SIZE);
    }
}
