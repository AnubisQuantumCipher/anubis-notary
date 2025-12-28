//! Authenticated Encryption with Associated Data (AEAD).
//!
//! This module provides ChaCha20Poly1305 AEAD using libcrux-chacha20poly1305,
//! which is formally verified using the hax/F* toolchain.
//!
//! ## Formal Verification (libcrux)
//!
//! The underlying libcrux-chacha20poly1305 is verified for:
//! - Panic freedom (no runtime panics)
//! - Functional correctness (matches RFC 8439)
//! - Memory safety
//! - Derived from HACL* verified C code
//!
//! ## Our Wrapper Verification Status
//!
//! **NOT FORMALLY VERIFIED**. The RefinedRust-style specifications in doc comments
//! describe intended properties, not actual verification. While libcrux is verified,
//! our wrapper code (fault detection, API surface) has not been formally proven.
//!
//! The specifications in `specs/refinedrust/theories/aead_spec.v` represent design
//! goals we intend to verify in the future.
//!
//! ## Security Properties
//!
//! - 256-bit key
//! - 96-bit nonce (must be unique per key)
//! - 128-bit authentication tag
//! - Constant-time implementation (from libcrux)

use zeroize::Zeroize;

/// Key size for ChaCha20Poly1305 (256 bits).
pub const KEY_SIZE: usize = 32;

/// Nonce size for ChaCha20Poly1305 (96 bits).
pub const NONCE_SIZE: usize = 12;

/// Tag size (128 bits).
pub const TAG_SIZE: usize = 16;

/// AEAD error type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AeadError {
    /// Authentication tag verification failed.
    AuthenticationFailed,
    /// Input buffer too small.
    BufferTooSmall,
    /// Invalid key size.
    InvalidKeySize,
    /// Invalid nonce size.
    InvalidNonceSize,
    /// Fault detected during cryptographic operation.
    ///
    /// This indicates a potential fault injection attack was detected through
    /// post-operation verification (decrypt after encrypt verification failed).
    FaultDetected,
}

impl core::fmt::Display for AeadError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::AuthenticationFailed => write!(f, "authentication tag verification failed"),
            Self::BufferTooSmall => write!(f, "buffer too small"),
            Self::InvalidKeySize => write!(f, "invalid key size"),
            Self::InvalidNonceSize => write!(f, "invalid nonce size"),
            Self::FaultDetected => {
                write!(f, "fault detected: encryption verification failed")
            }
        }
    }
}

impl std::error::Error for AeadError {}

/// ChaCha20Poly1305 AEAD cipher (formally verified via libcrux).
///
/// This uses the Cryspen libcrux-chacha20poly1305 crate which is
/// formally verified using the hax/F* toolchain.
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("aead" : "aead_spec.ChaCha20Poly1305_state")]
/// #[rr::invariant("len(aead.key) = KEY_SIZE")]
/// #[rr::invariant("valid_aead_key(aead.key)")]
/// #[rr::owns("aead.key")]
/// ```
///
/// Security: The key is zeroized on drop to prevent key leakage.
pub struct ChaCha20Poly1305 {
    key: [u8; KEY_SIZE],
}

impl ChaCha20Poly1305 {
    /// Create a new ChaCha20Poly1305 instance.
    ///
    /// # Arguments
    ///
    /// * `key` - 32-byte (256-bit) key
    ///
    /// # Errors
    ///
    /// Returns `InvalidKeySize` if key is not 32 bytes.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("key" : "list u8")]
    /// #[rr::args("#key")]
    /// #[rr::returns("Ok(aead) where aead.key = key | Err(InvalidKeySize)")]
    /// #[rr::ensures("is_ok(result) <-> len(key) = KEY_SIZE")]
    /// ```
    pub fn new(key: &[u8]) -> Result<Self, AeadError> {
        if key.len() != KEY_SIZE {
            return Err(AeadError::InvalidKeySize);
        }
        let mut k = [0u8; KEY_SIZE];
        k.copy_from_slice(key);
        Ok(Self { key: k })
    }

    /// Create from a fixed-size key array (preferred).
    #[inline]
    pub fn from_key(key: &[u8; KEY_SIZE]) -> Self {
        Self { key: *key }
    }

    /// Encrypt plaintext and generate authentication tag.
    ///
    /// # Arguments
    ///
    /// * `nonce` - 12-byte nonce (must be unique per encryption with same key)
    /// * `ad` - Associated data (authenticated but not encrypted)
    /// * `plaintext` - Data to encrypt
    /// * `ciphertext` - Output buffer (must be at least plaintext.len() + 16)
    ///
    /// # Returns
    ///
    /// Number of bytes written to ciphertext (plaintext.len() + 16).
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("nonce" : "list u8", "ad" : "list u8", "pt" : "list u8", "ct" : "list u8")]
    /// #[rr::args("#nonce", "#ad", "#pt", "(#ct, gamma) @ &mut [u8]")]
    /// #[rr::requires("len(nonce) = NONCE_SIZE")]
    /// #[rr::requires("len(ct) >= len(pt) + TAG_SIZE")]
    /// #[rr::returns("Ok(n) where n = len(pt) + TAG_SIZE | Err(e)")]
    /// #[rr::ensures("is_ok(result) -> gamma(aead_encrypt(self.key, nonce, ad, pt))")]
    /// #[rr::ensures("is_ok(result) -> aead_decrypt(self.key, nonce, ad, ct[..n]) = Some(pt)")]
    /// ```
    ///
    /// IND-CPA Security: The ciphertext is computationally indistinguishable from random
    /// to any adversary without the key.
    pub fn seal(
        &self,
        nonce: &[u8],
        ad: &[u8],
        plaintext: &[u8],
        ciphertext: &mut [u8],
    ) -> Result<usize, AeadError> {
        if nonce.len() != NONCE_SIZE {
            return Err(AeadError::InvalidNonceSize);
        }
        if ciphertext.len() < plaintext.len() + TAG_SIZE {
            return Err(AeadError::BufferTooSmall);
        }

        let nonce_array: [u8; NONCE_SIZE] = nonce.try_into().unwrap();

        // libcrux encrypt writes ciphertext+tag into output buffer
        match libcrux_chacha20poly1305::encrypt(
            &self.key,
            plaintext,
            &mut ciphertext[..plaintext.len() + TAG_SIZE],
            ad,
            &nonce_array,
        ) {
            Ok(_) => Ok(plaintext.len() + TAG_SIZE),
            Err(_) => Err(AeadError::BufferTooSmall),
        }
    }

    /// Type-safe encryption with fixed-size nonce.
    pub fn seal_fixed(
        &self,
        nonce: &[u8; NONCE_SIZE],
        ad: &[u8],
        plaintext: &[u8],
    ) -> Vec<u8> {
        let mut result = vec![0u8; plaintext.len() + TAG_SIZE];
        libcrux_chacha20poly1305::encrypt(
            &self.key,
            plaintext,
            &mut result,
            ad,
            nonce,
        ).expect("encryption should not fail with valid inputs");
        result
    }

    /// Decrypt ciphertext and verify authentication tag.
    ///
    /// # Arguments
    ///
    /// * `nonce` - 12-byte nonce used during encryption
    /// * `ad` - Associated data used during encryption
    /// * `ciphertext` - Encrypted data with tag (at least 16 bytes)
    /// * `plaintext` - Output buffer (must be at least ciphertext.len() - 16)
    ///
    /// # Returns
    ///
    /// Number of plaintext bytes on success.
    ///
    /// # Security
    ///
    /// On authentication failure, the plaintext buffer is zeroized.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("nonce" : "list u8", "ad" : "list u8", "ct" : "list u8", "pt" : "list u8")]
    /// #[rr::args("#nonce", "#ad", "#ct", "(#pt, gamma) @ &mut [u8]")]
    /// #[rr::requires("len(nonce) = NONCE_SIZE")]
    /// #[rr::requires("len(ct) >= TAG_SIZE")]
    /// #[rr::requires("len(pt) >= len(ct) - TAG_SIZE")]
    /// #[rr::returns("Ok(n) | Err(AuthenticationFailed)")]
    /// #[rr::ensures("is_ok(result) -> gamma(aead_decrypt(self.key, nonce, ad, ct))")]
    /// #[rr::ensures("is_err(result) -> gamma(zeros(len(ct) - TAG_SIZE))")]
    /// #[rr::ensures("timing_independent_of(ct)")]
    /// ```
    ///
    /// INT-CTXT Security: Any modification to the ciphertext or associated data
    /// will be detected with overwhelming probability. Tag verification is constant-time.
    pub fn open(
        &self,
        nonce: &[u8],
        ad: &[u8],
        ciphertext: &[u8],
        plaintext: &mut [u8],
    ) -> Result<usize, AeadError> {
        if nonce.len() != NONCE_SIZE {
            return Err(AeadError::InvalidNonceSize);
        }
        if ciphertext.len() < TAG_SIZE {
            return Err(AeadError::BufferTooSmall);
        }
        let pt_len = ciphertext.len() - TAG_SIZE;
        if plaintext.len() < pt_len {
            return Err(AeadError::BufferTooSmall);
        }

        let nonce_array: [u8; NONCE_SIZE] = nonce.try_into().unwrap();

        // libcrux decrypt expects ciphertext with tag appended
        match libcrux_chacha20poly1305::decrypt(
            &self.key,
            &mut plaintext[..pt_len],
            ciphertext,
            ad,
            &nonce_array,
        ) {
            Ok(_) => Ok(pt_len),
            Err(_) => {
                plaintext[..pt_len].zeroize();
                Err(AeadError::AuthenticationFailed)
            }
        }
    }

    /// Type-safe decryption with fixed-size nonce.
    pub fn open_fixed(
        &self,
        nonce: &[u8; NONCE_SIZE],
        ad: &[u8],
        ciphertext: &[u8],
    ) -> Result<Vec<u8>, AeadError> {
        if ciphertext.len() < TAG_SIZE {
            return Err(AeadError::BufferTooSmall);
        }
        let pt_len = ciphertext.len() - TAG_SIZE;
        let mut plaintext = vec![0u8; pt_len];

        match libcrux_chacha20poly1305::decrypt(
            &self.key,
            &mut plaintext,
            ciphertext,
            ad,
            nonce,
        ) {
            Ok(_) => Ok(plaintext),
            Err(_) => {
                plaintext.zeroize();
                Err(AeadError::AuthenticationFailed)
            }
        }
    }

    /// Encrypt with fault injection countermeasures.
    ///
    /// This method provides protection against fault injection attacks by:
    /// 1. Encrypting the plaintext
    /// 2. Decrypting the ciphertext
    /// 3. Comparing decrypted result with original plaintext
    /// 4. Only returning the ciphertext if verification succeeds
    ///
    /// # Security
    ///
    /// This countermeasure detects faults that would produce incorrect ciphertext,
    /// such as:
    /// - Round skipping attacks
    /// - Tag computation faults
    /// - Key mixing faults
    ///
    /// The ~100% overhead (one extra decryption + comparison) provides strong
    /// fault detection.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("nonce" : "list u8", "ad" : "list u8", "pt" : "list u8")]
    /// #[rr::args("#nonce", "#ad", "#pt")]
    /// #[rr::requires("len(nonce) = NONCE_SIZE")]
    /// #[rr::returns("Ok(ct) | Err(e)")]
    /// #[rr::ensures("is_ok(result) -> aead_decrypt(self.key, nonce, ad, unwrap(result)) = Some(pt)")]
    /// #[rr::ensures("is_ok(result) -> fault_verified(result)")]
    /// ```
    pub fn seal_verified(
        &self,
        nonce: &[u8; NONCE_SIZE],
        ad: &[u8],
        plaintext: &[u8],
    ) -> Result<Vec<u8>, AeadError> {
        // Encrypt
        let ciphertext = self.seal_fixed(nonce, ad, plaintext);

        // Verify by decrypting and comparing
        match self.open_fixed(nonce, ad, &ciphertext) {
            Ok(decrypted) => {
                // Constant-time comparison
                if crate::ct::ct_eq(plaintext, &decrypted) {
                    Ok(ciphertext)
                } else {
                    // Decryption produced different result - fault detected
                    Err(AeadError::FaultDetected)
                }
            }
            Err(_) => {
                // Decryption failed - ciphertext is corrupted
                Err(AeadError::FaultDetected)
            }
        }
    }

    /// Encrypt into buffer with fault injection countermeasures.
    ///
    /// See `seal_verified` for security details.
    ///
    /// # Arguments
    ///
    /// * `nonce` - 12-byte nonce (must be unique per encryption with same key)
    /// * `ad` - Associated data (authenticated but not encrypted)
    /// * `plaintext` - Data to encrypt
    /// * `ciphertext` - Output buffer (must be at least plaintext.len() + 16)
    ///
    /// # Returns
    ///
    /// Number of bytes written on success, or:
    /// - `InvalidNonceSize` if nonce is not 12 bytes
    /// - `BufferTooSmall` if output buffer is too small
    /// - `FaultDetected` if post-encryption verification failed
    pub fn seal_verified_into(
        &self,
        nonce: &[u8],
        ad: &[u8],
        plaintext: &[u8],
        ciphertext: &mut [u8],
    ) -> Result<usize, AeadError> {
        if nonce.len() != NONCE_SIZE {
            return Err(AeadError::InvalidNonceSize);
        }
        if ciphertext.len() < plaintext.len() + TAG_SIZE {
            return Err(AeadError::BufferTooSmall);
        }

        let nonce_array: [u8; NONCE_SIZE] = nonce.try_into().unwrap();
        let ct_len = plaintext.len() + TAG_SIZE;

        // Encrypt
        match libcrux_chacha20poly1305::encrypt(
            &self.key,
            plaintext,
            &mut ciphertext[..ct_len],
            ad,
            &nonce_array,
        ) {
            Ok(_) => {}
            Err(_) => return Err(AeadError::BufferTooSmall),
        }

        // Verify by decrypting
        let mut verify_buf = vec![0u8; plaintext.len()];
        match libcrux_chacha20poly1305::decrypt(
            &self.key,
            &mut verify_buf,
            &ciphertext[..ct_len],
            ad,
            &nonce_array,
        ) {
            Ok(_) => {
                // Constant-time comparison
                if crate::ct::ct_eq(plaintext, &verify_buf) {
                    verify_buf.zeroize();
                    Ok(ct_len)
                } else {
                    verify_buf.zeroize();
                    // Zero the potentially corrupted ciphertext
                    ciphertext[..ct_len].zeroize();
                    Err(AeadError::FaultDetected)
                }
            }
            Err(_) => {
                verify_buf.zeroize();
                ciphertext[..ct_len].zeroize();
                Err(AeadError::FaultDetected)
            }
        }
    }
}

impl Drop for ChaCha20Poly1305 {
    /// Securely erase the key material on drop.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::ensures("forall i. 0 <= i < KEY_SIZE -> self.key[i] = 0")]
    /// #[rr::ensures("zeroized(self)")]
    /// #[rr::volatile_write]
    /// ```
    fn drop(&mut self) {
        self.key.zeroize();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundtrip() {
        let key = [0u8; KEY_SIZE];
        let nonce = [0u8; NONCE_SIZE];
        let plaintext = b"Hello, World!";
        let ad = b"associated data";

        let cipher = ChaCha20Poly1305::new(&key).unwrap();

        let mut ciphertext = [0u8; 64];
        let ct_len = cipher.seal(&nonce, ad, plaintext, &mut ciphertext).unwrap();

        let mut decrypted = [0u8; 64];
        let pt_len = cipher
            .open(&nonce, ad, &ciphertext[..ct_len], &mut decrypted)
            .unwrap();

        assert_eq!(&decrypted[..pt_len], plaintext);
    }

    #[test]
    fn test_tamper_detection() {
        let key = [0u8; KEY_SIZE];
        let nonce = [0u8; NONCE_SIZE];
        let plaintext = b"Secret message";
        let ad = b"";

        let cipher = ChaCha20Poly1305::new(&key).unwrap();

        let mut ciphertext = [0u8; 64];
        let ct_len = cipher.seal(&nonce, ad, plaintext, &mut ciphertext).unwrap();

        // Tamper with ciphertext
        ciphertext[0] ^= 1;

        let mut decrypted = [0u8; 64];
        let result = cipher.open(&nonce, ad, &ciphertext[..ct_len], &mut decrypted);

        assert_eq!(result, Err(AeadError::AuthenticationFailed));
    }

    #[test]
    fn test_empty_plaintext() {
        let key = [0u8; KEY_SIZE];
        let nonce = [0u8; NONCE_SIZE];
        let plaintext = b"";
        let ad = b"some ad";

        let cipher = ChaCha20Poly1305::new(&key).unwrap();

        let mut ciphertext = [0u8; 64];
        let ct_len = cipher.seal(&nonce, ad, plaintext, &mut ciphertext).unwrap();

        assert_eq!(ct_len, TAG_SIZE);

        let mut decrypted = [0u8; 64];
        let pt_len = cipher
            .open(&nonce, ad, &ciphertext[..ct_len], &mut decrypted)
            .unwrap();

        assert_eq!(pt_len, 0);
    }

    #[test]
    fn test_fixed_api() {
        let key = [0u8; KEY_SIZE];
        let nonce = [0u8; NONCE_SIZE];
        let plaintext = b"Type-safe API test";

        let cipher = ChaCha20Poly1305::from_key(&key);
        let ciphertext = cipher.seal_fixed(&nonce, b"", plaintext);
        let decrypted = cipher.open_fixed(&nonce, b"", &ciphertext).unwrap();

        assert_eq!(decrypted, plaintext);
    }

    // ========================================================================
    // Fault injection countermeasure tests
    // ========================================================================

    #[test]
    fn test_seal_verified() {
        let key = [0u8; KEY_SIZE];
        let nonce = [0u8; NONCE_SIZE];
        let plaintext = b"Verified encryption test";
        let ad = b"authenticated data";

        let cipher = ChaCha20Poly1305::from_key(&key);
        let ciphertext = cipher.seal_verified(&nonce, ad, plaintext).unwrap();

        // Should decrypt successfully
        let decrypted = cipher.open_fixed(&nonce, ad, &ciphertext).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn test_seal_verified_into() {
        let key = [0u8; KEY_SIZE];
        let nonce = [0u8; NONCE_SIZE];
        let plaintext = b"Buffer-based verified encryption";
        let ad = b"";

        let cipher = ChaCha20Poly1305::from_key(&key);
        let mut ciphertext = vec![0u8; plaintext.len() + TAG_SIZE];
        let ct_len = cipher
            .seal_verified_into(&nonce, ad, plaintext, &mut ciphertext)
            .unwrap();

        assert_eq!(ct_len, plaintext.len() + TAG_SIZE);

        // Should decrypt successfully
        let decrypted = cipher.open_fixed(&nonce, ad, &ciphertext).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn test_seal_verified_empty_plaintext() {
        let key = [0xAB; KEY_SIZE];
        let nonce = [0xCD; NONCE_SIZE];
        let plaintext = b"";

        let cipher = ChaCha20Poly1305::from_key(&key);
        let ciphertext = cipher.seal_verified(&nonce, b"some ad", plaintext).unwrap();

        assert_eq!(ciphertext.len(), TAG_SIZE);
    }

    #[test]
    fn test_seal_verified_large_plaintext() {
        let key = [0x42; KEY_SIZE];
        let nonce = [0x13; NONCE_SIZE];
        let plaintext = vec![0xAA; 10000]; // 10 KB

        let cipher = ChaCha20Poly1305::from_key(&key);
        let ciphertext = cipher.seal_verified(&nonce, b"", &plaintext).unwrap();

        let decrypted = cipher.open_fixed(&nonce, b"", &ciphertext).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn test_error_display() {
        assert_eq!(
            format!("{}", AeadError::AuthenticationFailed),
            "authentication tag verification failed"
        );
        assert_eq!(
            format!("{}", AeadError::FaultDetected),
            "fault detected: encryption verification failed"
        );
        assert_eq!(format!("{}", AeadError::BufferTooSmall), "buffer too small");
        assert_eq!(format!("{}", AeadError::InvalidKeySize), "invalid key size");
        assert_eq!(
            format!("{}", AeadError::InvalidNonceSize),
            "invalid nonce size"
        );
    }
}
