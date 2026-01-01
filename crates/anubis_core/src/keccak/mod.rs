//! SHA3 and SHAKE hash functions using libcrux-sha3 (formally verified).
//!
//! This module wraps the Cryspen libcrux-sha3 crate, which is formally verified
//! using the hax/F* toolchain for panic freedom and functional correctness.
//!
//! ## Formal Verification Status
//!
//! All functions in this module use libcrux-sha3 which has been:
//! - Verified for panic freedom (no runtime panics possible)
//! - Verified for functional correctness (matches FIPS 202 specification)
//! - Verified using the hax extraction to F* proof assistant
//!
//! ## Available Functions
//!
//! - `sha3_256`: SHA3-256 hash (32-byte output)
//! - `shake256`: SHAKE256 XOF (arbitrary output length)
//! - `shake256_x4`: Parallel SHAKE256 for 4 inputs (ML-DSA optimization)

pub mod sha3;
pub mod shake;

// Re-export the main functions at module level for convenience
pub use sha3::sha3_256;
pub use shake::{shake256, Shake256};

/// Rate for SHA3-256 in bytes (1088 bits / 8).
pub const SHA3_256_RATE: usize = 136;

/// Rate for SHAKE256 in bytes (1088 bits / 8).
pub const SHAKE256_RATE: usize = 136;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sha3_256_empty() {
        let hash = sha3_256(b"");
        // Known test vector for SHA3-256("")
        let expected = [
            0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66, 0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61,
            0xd6, 0x62, 0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa, 0x82, 0xd8, 0x0a, 0x4b,
            0x80, 0xf8, 0x43, 0x4a,
        ];
        assert_eq!(hash, expected);
    }

    #[test]
    fn test_sha3_256_abc() {
        let hash = sha3_256(b"abc");
        // Known test vector for SHA3-256("abc")
        let expected = [
            0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2, 0x04, 0x5c, 0x17, 0x2d, 0x6b, 0xd3,
            0x90, 0xbd, 0x85, 0x5f, 0x08, 0x6e, 0x3e, 0x9d, 0x52, 0x5b, 0x46, 0xbf, 0xe2, 0x45,
            0x11, 0x43, 0x15, 0x32,
        ];
        assert_eq!(hash, expected);
    }

    #[test]
    fn test_shake256_deterministic() {
        let out1: [u8; 64] = shake256(b"test input");
        let out2: [u8; 64] = shake256(b"test input");
        assert_eq!(out1, out2);
    }

    #[test]
    fn test_shake256_different_lengths() {
        let short: [u8; 32] = shake256(b"data");
        let long: [u8; 64] = shake256(b"data");
        // First 32 bytes should match
        assert_eq!(short, long[..32]);
    }
}
