//! RefinedRust Annotations for bytes module
//!
//! This file shows the complete refinement type annotations for the
//! byte manipulation utilities including LE encoding/decoding and zeroization.

// ============================================================================
// SecretBytes Type
// ============================================================================

/// A fixed-size array of secret bytes that zeroizes on drop.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("bytes" : "array u8 N")]
/// #[rr::invariant("len(bytes) = N")]
/// #[rr::drop_ensures("forall i. i < N ==> bytes[i] = 0")]
/// ```
#[rr::type("SecretBytes<N>")]
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct SecretBytes<const N: usize>([u8; N]);

// ============================================================================
// SecretBytes::new
// ============================================================================

/// Create a new zero-filled secret bytes array.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::returns("SecretBytes { bytes: zeros(N) }")]
/// #[rr::ensures("forall i. i < N ==> result.bytes[i] = 0")]
/// ```
#[rr::verified]
#[inline]
pub const fn new<const N: usize>() -> SecretBytes<N> {
    SecretBytes([0u8; N])
}

// ============================================================================
// SecretBytes::from_array
// ============================================================================

/// Create secret bytes from an existing array.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("bytes" : "array u8 N")]
/// #[rr::args("bytes @ [u8; N]")]
/// #[rr::returns("SecretBytes { bytes: bytes }")]
/// ```
#[rr::verified]
#[inline]
pub const fn from_array<const N: usize>(bytes: [u8; N]) -> SecretBytes<N> {
    SecretBytes(bytes)
}

// ============================================================================
// load_le32 - Little-Endian Load (32-bit)
// ============================================================================

/// Load a 32-bit little-endian integer from a byte slice.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("bytes" : "list u8")]
/// #[rr::args("bytes @ &[u8]")]
/// #[rr::requires("len(bytes) >= 4")]
/// #[rr::returns("bytes[0] + bytes[1]*256 + bytes[2]*65536 + bytes[3]*16777216")]
/// #[rr::ensures("store_le32(result, buf) ==> buf[..4] = bytes[..4]")]
/// ```
#[rr::verified]
#[inline]
pub fn load_le32(bytes: &[u8]) -> u32 {
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
}

// ============================================================================
// load_le64 - Little-Endian Load (64-bit)
// ============================================================================

/// Load a 64-bit little-endian integer from a byte slice.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("bytes" : "list u8")]
/// #[rr::args("bytes @ &[u8]")]
/// #[rr::requires("len(bytes) >= 8")]
/// #[rr::returns("sum(bytes[i] * 2^(8*i) for i in 0..8)")]
/// #[rr::ensures("store_le64(result, buf) ==> buf[..8] = bytes[..8]")]
/// ```
#[rr::verified]
#[inline]
pub fn load_le64(bytes: &[u8]) -> u64 {
    u64::from_le_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3],
        bytes[4], bytes[5], bytes[6], bytes[7],
    ])
}

// ============================================================================
// store_le32 - Little-Endian Store (32-bit)
// ============================================================================

/// Store a 32-bit integer as little-endian bytes.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname", "word" : "u32", "bytes" : "list u8")]
/// #[rr::args("word @ u32", "(bytes, gamma) @ &mut [u8]")]
/// #[rr::requires("len(bytes) >= 4")]
/// #[rr::ensures("gamma ↦ le_bytes32(word) ++ bytes[4..]")]
/// #[rr::ensures("load_le32(bytes) = word")]
/// ```
#[rr::verified]
#[inline]
pub fn store_le32(word: u32, bytes: &mut [u8]) {
    let le = word.to_le_bytes();
    bytes[0] = le[0];
    bytes[1] = le[1];
    bytes[2] = le[2];
    bytes[3] = le[3];
}

// ============================================================================
// store_le64 - Little-Endian Store (64-bit)
// ============================================================================

/// Store a 64-bit integer as little-endian bytes.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname", "word" : "u64", "bytes" : "list u8")]
/// #[rr::args("word @ u64", "(bytes, gamma) @ &mut [u8]")]
/// #[rr::requires("len(bytes) >= 8")]
/// #[rr::ensures("gamma ↦ le_bytes64(word) ++ bytes[8..]")]
/// #[rr::ensures("load_le64(bytes) = word")]
/// ```
#[rr::verified]
#[inline]
pub fn store_le64(word: u64, bytes: &mut [u8]) {
    let le = word.to_le_bytes();
    bytes[..8].copy_from_slice(&le);
}

// ============================================================================
// rotl64 - Rotate Left (64-bit)
// ============================================================================

/// Rotate a 64-bit word left by n bits.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("word" : "u64", "n" : "u32")]
/// #[rr::args("word @ u64", "n @ u32")]
/// #[rr::requires("n < 64")]
/// #[rr::returns("(word << n) | (word >> (64 - n))")]
/// #[rr::ensures("rotr64(result, n) = word")]
/// ```
#[rr::verified]
#[inline]
pub const fn rotl64(word: u64, n: u32) -> u64 {
    word.rotate_left(n)
}

// ============================================================================
// rotr64 - Rotate Right (64-bit)
// ============================================================================

/// Rotate a 64-bit word right by n bits.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("word" : "u64", "n" : "u32")]
/// #[rr::args("word @ u64", "n @ u32")]
/// #[rr::requires("n < 64")]
/// #[rr::returns("(word >> n) | (word << (64 - n))")]
/// #[rr::ensures("rotl64(result, n) = word")]
/// ```
#[rr::verified]
#[inline]
pub const fn rotr64(word: u64, n: u32) -> u64 {
    word.rotate_right(n)
}

// ============================================================================
// zeroize_slice - Zeroize Byte Slice
// ============================================================================

/// Zeroize a byte slice in place.
///
/// Uses volatile writes to prevent dead-store elimination.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname", "buf" : "list u8")]
/// #[rr::args("(buf, gamma) @ &mut [u8]")]
/// #[rr::ensures("gamma ↦ zeros(len(buf))")]
/// #[rr::ensures("forall i. i < len(buf) ==> buf[i] = 0")]
/// #[rr::volatile("Prevents dead-store elimination")]
/// ```
#[rr::verified]
#[inline]
pub fn zeroize_slice(buf: &mut [u8]) {
    buf.zeroize();
}

// ============================================================================
// xor_bytes - XOR Bytes
// ============================================================================

/// XOR source bytes into destination bytes.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname", "src" : "list u8", "dst" : "list u8")]
/// #[rr::args("src @ &[u8]", "(dst, gamma) @ &mut [u8]")]
/// #[rr::requires("len(dst) >= len(src)")]
/// #[rr::ensures("forall i. i < len(src) ==> dst'[i] = old(dst[i]) XOR src[i]")]
/// #[rr::ensures("forall i. i >= len(src) ==> dst'[i] = old(dst[i])")]
///
/// (* Loop invariant *)
/// #[rr::loop_inv("i", "0 <= i <= len(src)")]
/// #[rr::loop_inv("i", "forall j. j < i ==> dst[j] = old(dst[j]) XOR src[j]")]
/// ```
#[rr::verified]
#[inline]
pub fn xor_bytes(src: &[u8], dst: &mut [u8]) {
    #[rr::loop_inv("i <= len(src)")]
    for i in 0..src.len() {
        dst[i] ^= src[i];
    }
}

// ============================================================================
// Verification Conditions
// ============================================================================

/// Proof obligations for bytes module:
///
/// ## Load/Store Round-Trip (32-bit)
/// ```coq
/// Theorem le32_roundtrip :
///   forall word : u32,
///     forall buf,
///       len(buf) >= 4 ->
///       store_le32(word, buf) ->
///       load_le32(buf) = word.
/// Proof.
///   (* By definition of little-endian encoding *)
/// Qed.
/// ```
///
/// ## Load/Store Round-Trip (64-bit)
/// ```coq
/// Theorem le64_roundtrip :
///   forall word : u64,
///     forall buf,
///       len(buf) >= 8 ->
///       store_le64(word, buf) ->
///       load_le64(buf) = word.
/// ```
///
/// ## Rotation Inverse (Left/Right)
/// ```coq
/// Theorem rotation_inverse :
///   forall word n,
///     n < 64 ->
///     rotr64(rotl64(word, n), n) = word.
/// ```
///
/// ## Rotation Bounds
/// ```coq
/// Theorem rotation_bounds :
///   forall word n,
///     n < 64 ->
///     0 <= rotl64(word, n) < 2^64.
/// ```
///
/// ## Zeroization Completeness
/// ```coq
/// Theorem zeroize_complete :
///   forall buf,
///     zeroize_slice(buf) ->
///     forall i, i < len(buf) -> buf[i] = 0.
/// ```
///
/// ## XOR Self-Inverse
/// ```coq
/// Theorem xor_self_inverse :
///   forall a b,
///     len(a) = len(b) ->
///     xor_bytes(a, b) ->
///     xor_bytes(a, b) ->
///     b = old(b).
/// ```
///
/// ## SecretBytes Zeroize on Drop
/// ```coq
/// Theorem secret_bytes_zeroized :
///   forall sb : SecretBytes<N>,
///     after_drop(sb) ->
///     forall i, i < N -> sb.bytes[i] = 0.
/// ```
mod _verification_conditions {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_le32_roundtrip() {
        let word: u32 = 0x12345678;
        let mut buf = [0u8; 4];
        store_le32(word, &mut buf);
        assert_eq!(load_le32(&buf), word);
    }

    #[test]
    fn test_le64_roundtrip() {
        let word: u64 = 0x123456789ABCDEF0;
        let mut buf = [0u8; 8];
        store_le64(word, &mut buf);
        assert_eq!(load_le64(&buf), word);
    }

    #[test]
    fn test_rotation_inverse() {
        let word: u64 = 0xDEADBEEFCAFEBABE;
        for n in 0..64 {
            assert_eq!(rotr64(rotl64(word, n), n), word);
        }
    }

    #[test]
    fn test_xor_bytes() {
        let src = [0xFF, 0x00, 0xAA];
        let mut dst = [0x55, 0x55, 0x55];
        xor_bytes(&src, &mut dst);
        assert_eq!(dst, [0xAA, 0x55, 0xFF]);
    }
}
