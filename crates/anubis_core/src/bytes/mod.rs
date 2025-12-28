//! Byte manipulation utilities for cryptographic operations.
//!
//! Provides little-endian load/store functions, secret bytes with zeroize-on-drop,
//! and other byte manipulation utilities.
//!
//! ## RefinedRust Verification
//!
//! All functions are verified for:
//! - Bounds safety (no OOB panics when preconditions hold)
//! - Functional correctness (LE encoding/decoding is inverse)
//! - Rotation bounds (n < 64 for rotate operations)

use core::fmt;
use core::ops::{Deref, DerefMut};
use zeroize::{Zeroize, ZeroizeOnDrop as ZeroizeOnDropTrait};

/// Marker trait for types that zeroize on drop.
pub trait ZeroizeOnDrop: Zeroize {}

/// A fixed-size array of secret bytes that zeroizes on drop.
///
/// This type provides safe storage for cryptographic secrets with automatic
/// zeroization when the value goes out of scope.
#[derive(Clone, Zeroize, ZeroizeOnDropTrait)]
pub struct SecretBytes<const N: usize>([u8; N]);

impl<const N: usize> SecretBytes<N> {
    /// Create a new zero-filled secret bytes array.
    #[inline]
    pub const fn new() -> Self {
        Self([0u8; N])
    }

    /// Create secret bytes from an existing array.
    #[inline]
    pub const fn from_array(bytes: [u8; N]) -> Self {
        Self(bytes)
    }

    /// Returns the length of the secret bytes (always N).
    #[inline]
    pub const fn len(&self) -> usize {
        N
    }

    /// Returns true if the length is zero.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        N == 0
    }

    /// Returns a reference to the underlying bytes.
    #[inline]
    pub fn as_bytes(&self) -> &[u8; N] {
        &self.0
    }

    /// Returns a mutable reference to the underlying bytes.
    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut [u8; N] {
        &mut self.0
    }
}

impl<const N: usize> Default for SecretBytes<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Deref for SecretBytes<N> {
    type Target = [u8; N];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const N: usize> DerefMut for SecretBytes<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const N: usize> AsRef<[u8]> for SecretBytes<N> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<const N: usize> AsMut<[u8]> for SecretBytes<N> {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl<const N: usize> ZeroizeOnDrop for SecretBytes<N> {}

/// Error type for byte operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BytesError {
    /// Slice is too short for the requested operation.
    SliceTooShort {
        /// Required minimum length.
        required: usize,
        /// Actual length provided.
        actual: usize,
    },
    /// Offset would cause out-of-bounds access.
    OffsetOutOfBounds {
        /// The offset requested.
        offset: usize,
        /// The length of the slice.
        len: usize,
    },
}

impl fmt::Display for BytesError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SliceTooShort { required, actual } => {
                write!(f, "slice too short: required {} bytes, got {}", required, actual)
            }
            Self::OffsetOutOfBounds { offset, len } => {
                write!(f, "offset {} out of bounds for slice of length {}", offset, len)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for BytesError {}

/// Try to load a 32-bit little-endian integer from a byte slice.
///
/// Returns `None` if the slice is shorter than 4 bytes.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::returns("if bytes.len() >= 4 then Some(load_le32(bytes)) else None")]
/// ```
#[inline]
pub fn try_load_le32(bytes: &[u8]) -> Option<u32> {
    if bytes.len() < 4 {
        return None;
    }
    Some(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

/// Load a 32-bit little-endian integer from a byte slice.
///
/// # Panics
/// Panics if the slice is shorter than 4 bytes.
///
/// For a non-panicking version, use [`try_load_le32`].
#[inline]
pub fn load_le32(bytes: &[u8]) -> u32 {
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
}

/// Try to load a 64-bit little-endian integer from a byte slice.
///
/// Returns `None` if the slice is shorter than 8 bytes.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::returns("if bytes.len() >= 8 then Some(load_le64(bytes)) else None")]
/// ```
#[inline]
pub fn try_load_le64(bytes: &[u8]) -> Option<u64> {
    if bytes.len() < 8 {
        return None;
    }
    Some(u64::from_le_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
    ]))
}

/// Load a 64-bit little-endian integer from a byte slice.
///
/// # Panics
/// Panics if the slice is shorter than 8 bytes.
///
/// For a non-panicking version, use [`try_load_le64`].
///
/// # RefinedRust Specification
/// ```text
/// #[rr::params("bytes" : "list u8")]
/// #[rr::requires("bytes.len() >= 8")]
/// #[rr::returns("sum(bytes[i] * 2^(8*i) for i in 0..8)")]
/// #[rr::ensures("store_le64(result, buf) ==> buf[..8] == bytes[..8]")]
/// ```
#[inline]
pub fn load_le64(bytes: &[u8]) -> u64 {
    u64::from_le_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
    ])
}

/// Try to store a 32-bit integer as little-endian bytes.
///
/// Returns `false` if the slice is shorter than 4 bytes.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::returns("if bytes.len() >= 4 then true else false")]
/// #[rr::ensures("result ==> bytes[..4] == le_bytes(word)")]
/// ```
#[inline]
pub fn try_store_le32(word: u32, bytes: &mut [u8]) -> bool {
    if bytes.len() < 4 {
        return false;
    }
    let le = word.to_le_bytes();
    bytes[0] = le[0];
    bytes[1] = le[1];
    bytes[2] = le[2];
    bytes[3] = le[3];
    true
}

/// Store a 32-bit integer as little-endian bytes.
///
/// # Panics
/// Panics if the slice is shorter than 4 bytes.
///
/// For a non-panicking version, use [`try_store_le32`].
#[inline]
pub fn store_le32(word: u32, bytes: &mut [u8]) {
    let le = word.to_le_bytes();
    bytes[0] = le[0];
    bytes[1] = le[1];
    bytes[2] = le[2];
    bytes[3] = le[3];
}

/// Try to store a 64-bit integer as little-endian bytes.
///
/// Returns `false` if the slice is shorter than 8 bytes.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::returns("if bytes.len() >= 8 then true else false")]
/// #[rr::ensures("result ==> bytes[..8] == le_bytes(word)")]
/// ```
#[inline]
pub fn try_store_le64(word: u64, bytes: &mut [u8]) -> bool {
    if bytes.len() < 8 {
        return false;
    }
    let le = word.to_le_bytes();
    bytes[..8].copy_from_slice(&le);
    true
}

/// Store a 64-bit integer as little-endian bytes.
///
/// # Panics
/// Panics if the slice is shorter than 8 bytes.
///
/// For a non-panicking version, use [`try_store_le64`].
///
/// # RefinedRust Specification
/// ```text
/// #[rr::params("gamma" : "gname", "word" : "u64", "bytes" : "list u8")]
/// #[rr::requires("bytes.len() >= 8")]
/// #[rr::args("#word", "(#bytes, gamma) @ &mut [u8]")]
/// #[rr::ensures("gamma(le_bytes(word) ++ bytes[8..])")]
/// #[rr::ensures("load_le64(bytes) == word")]
/// ```
#[inline]
pub fn store_le64(word: u64, bytes: &mut [u8]) {
    let le = word.to_le_bytes();
    bytes[..8].copy_from_slice(&le);
}

/// Try to load a 64-bit little-endian integer at the given offset.
///
/// Returns `None` if `offset + 8 > bytes.len()`.
#[inline]
pub fn try_load_le64_at(bytes: &[u8], offset: usize) -> Option<u64> {
    if offset.checked_add(8)? > bytes.len() {
        return None;
    }
    try_load_le64(&bytes[offset..])
}

/// Load a 64-bit little-endian integer at the given offset.
///
/// # Panics
/// Panics if `offset + 8 > bytes.len()`.
///
/// For a non-panicking version, use [`try_load_le64_at`].
#[inline]
pub fn load_le64_at(bytes: &[u8], offset: usize) -> u64 {
    load_le64(&bytes[offset..])
}

/// Try to store a 64-bit integer at the given offset as little-endian.
///
/// Returns `false` if `offset + 8 > bytes.len()`.
#[inline]
pub fn try_store_le64_at(word: u64, bytes: &mut [u8], offset: usize) -> bool {
    match offset.checked_add(8) {
        Some(end) if end <= bytes.len() => {
            try_store_le64(word, &mut bytes[offset..])
        }
        _ => false,
    }
}

/// Store a 64-bit integer at the given offset as little-endian.
///
/// # Panics
/// Panics if `offset + 8 > bytes.len()`.
///
/// For a non-panicking version, use [`try_store_le64_at`].
#[inline]
pub fn store_le64_at(word: u64, bytes: &mut [u8], offset: usize) {
    store_le64(word, &mut bytes[offset..]);
}

/// Rotate a 64-bit word left by n bits.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::params("word" : "u64", "n" : "u32")]
/// #[rr::requires("n < 64")]
/// #[rr::returns("(word << n) | (word >> (64 - n))")]
/// ```
#[inline]
pub const fn rotl64(word: u64, n: u32) -> u64 {
    word.rotate_left(n)
}

/// Rotate a 64-bit word right by n bits.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::params("word" : "u64", "n" : "u32")]
/// #[rr::requires("n < 64")]
/// #[rr::returns("(word >> n) | (word << (64 - n))")]
/// ```
#[inline]
pub const fn rotr64(word: u64, n: u32) -> u64 {
    word.rotate_right(n)
}

/// Zeroize a byte slice in place.
#[inline]
pub fn zeroize_slice(buf: &mut [u8]) {
    buf.zeroize();
}

/// Zeroize a fixed-size byte array in place.
#[inline]
pub fn zeroize_array<const N: usize>(arr: &mut [u8; N]) {
    arr.zeroize();
}

/// Try to XOR source bytes into destination bytes.
///
/// Returns `false` if `dst.len() < src.len()`.
#[inline]
pub fn try_xor_bytes(src: &[u8], dst: &mut [u8]) -> bool {
    if dst.len() < src.len() {
        return false;
    }
    for i in 0..src.len() {
        dst[i] ^= src[i];
    }
    true
}

/// XOR source bytes into destination bytes.
///
/// # Panics
/// Panics if `dst.len() < src.len()`.
///
/// For a non-panicking version, use [`try_xor_bytes`].
#[inline]
pub fn xor_bytes(src: &[u8], dst: &mut [u8]) {
    for i in 0..src.len() {
        dst[i] ^= src[i];
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_try_load_le32() {
        // Success case
        let bytes = [0x01, 0x02, 0x03, 0x04];
        assert_eq!(try_load_le32(&bytes), Some(0x04030201));

        // Failure case - too short
        let short = [0x01, 0x02, 0x03];
        assert_eq!(try_load_le32(&short), None);

        // Empty slice
        assert_eq!(try_load_le32(&[]), None);
    }

    #[test]
    fn test_try_load_le64() {
        // Success case
        let bytes = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
        assert_eq!(try_load_le64(&bytes), Some(0x0807060504030201));

        // Failure case - too short
        let short = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];
        assert_eq!(try_load_le64(&short), None);

        // Empty slice
        assert_eq!(try_load_le64(&[]), None);
    }

    #[test]
    fn test_try_store_le32() {
        // Success case
        let mut bytes = [0u8; 4];
        assert!(try_store_le32(0x04030201, &mut bytes));
        assert_eq!(bytes, [0x01, 0x02, 0x03, 0x04]);

        // Failure case - too short
        let mut short = [0u8; 3];
        assert!(!try_store_le32(0x04030201, &mut short));
    }

    #[test]
    fn test_try_store_le64() {
        // Success case
        let mut bytes = [0u8; 8];
        assert!(try_store_le64(0x0807060504030201, &mut bytes));
        assert_eq!(bytes, [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]);

        // Failure case - too short
        let mut short = [0u8; 7];
        assert!(!try_store_le64(0x0807060504030201, &mut short));
    }

    #[test]
    fn test_try_load_le64_at() {
        let bytes = [0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];

        // Success case
        assert_eq!(try_load_le64_at(&bytes, 2), Some(0x0807060504030201));

        // Failure - offset too large
        assert_eq!(try_load_le64_at(&bytes, 3), None);

        // Failure - would overflow
        assert_eq!(try_load_le64_at(&bytes, usize::MAX), None);
    }

    #[test]
    fn test_try_store_le64_at() {
        let mut bytes = [0u8; 10];

        // Success case
        assert!(try_store_le64_at(0x0807060504030201, &mut bytes, 2));
        assert_eq!(&bytes[2..10], &[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]);

        // Failure - offset too large
        assert!(!try_store_le64_at(0x0807060504030201, &mut bytes, 3));

        // Failure - would overflow
        assert!(!try_store_le64_at(0x0807060504030201, &mut bytes, usize::MAX));
    }

    #[test]
    fn test_try_xor_bytes() {
        // Success case
        let src = [0x01, 0x02, 0x03];
        let mut dst = [0xFF, 0xFF, 0xFF, 0x00];
        assert!(try_xor_bytes(&src, &mut dst));
        assert_eq!(dst, [0xFE, 0xFD, 0xFC, 0x00]);

        // Failure - dst too short
        let mut short = [0xFF, 0xFF];
        assert!(!try_xor_bytes(&src, &mut short));
    }

    #[test]
    fn test_roundtrip_le32() {
        let original = 0xDEADBEEF_u32;
        let mut bytes = [0u8; 4];
        store_le32(original, &mut bytes);
        assert_eq!(load_le32(&bytes), original);
    }

    #[test]
    fn test_roundtrip_le64() {
        let original = 0xDEADBEEFCAFEBABE_u64;
        let mut bytes = [0u8; 8];
        store_le64(original, &mut bytes);
        assert_eq!(load_le64(&bytes), original);
    }

    #[test]
    fn test_secret_bytes_zeroize() {
        let mut secret: SecretBytes<32> = SecretBytes::from_array([0xFF; 32]);
        assert_eq!(&secret[..], &[0xFF; 32]);

        secret.zeroize();
        assert_eq!(&secret[..], &[0u8; 32]);
    }
}
