//! SHA3-256 hash function using libcrux-sha3 (formally verified).
//!
//! This module provides SHA3-256 hashing via the Cryspen libcrux-sha3 crate,
//! which is formally verified using the hax/F* toolchain.
//!
//! ## Formal Verification
//!
//! libcrux-sha3 is verified for:
//! - Panic freedom (no runtime panics)
//! - Functional correctness (matches FIPS 202)
//! - Memory safety

/// SHA3-256 output size in bytes.
pub const SHA3_256_OUTPUT: usize = 32;

/// Compute SHA3-256 hash of the input data.
///
/// Returns a 32-byte hash digest.
///
/// # Example
///
/// ```
/// use anubis_core::keccak::sha3::sha3_256;
///
/// let hash = sha3_256(b"hello world");
/// assert_eq!(hash.len(), 32);
/// ```
#[inline]
pub fn sha3_256(data: &[u8]) -> [u8; SHA3_256_OUTPUT] {
    libcrux_sha3::sha256(data)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sha3_256_nist_vectors() {
        // NIST test vector: empty string
        let hash = sha3_256(b"");
        assert_eq!(
            hash,
            [
                0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66, 0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61,
                0xd6, 0x62, 0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa, 0x82, 0xd8, 0x0a, 0x4b,
                0x80, 0xf8, 0x43, 0x4a,
            ]
        );

        // NIST test vector: "abc"
        let hash = sha3_256(b"abc");
        assert_eq!(
            hash,
            [
                0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2, 0x04, 0x5c, 0x17, 0x2d, 0x6b, 0xd3,
                0x90, 0xbd, 0x85, 0x5f, 0x08, 0x6e, 0x3e, 0x9d, 0x52, 0x5b, 0x46, 0xbf, 0xe2, 0x45,
                0x11, 0x43, 0x15, 0x32,
            ]
        );
    }

    #[test]
    fn test_sha3_256_deterministic() {
        let h1 = sha3_256(b"test data");
        let h2 = sha3_256(b"test data");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_sha3_256_different_inputs() {
        let h1 = sha3_256(b"input1");
        let h2 = sha3_256(b"input2");
        assert_ne!(h1, h2);
    }
}
