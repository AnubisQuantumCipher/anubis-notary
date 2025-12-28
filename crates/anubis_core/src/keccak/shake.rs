//! SHAKE256 extendable output function using libcrux-sha3 (formally verified).
//!
//! This module provides SHAKE256 XOF via the Cryspen libcrux-sha3 crate,
//! which is formally verified using the hax/F* toolchain.
//!
//! ## Formal Verification
//!
//! libcrux-sha3 is verified for:
//! - Panic freedom (no runtime panics)
//! - Functional correctness (matches FIPS 202)
//! - Memory safety

/// Compute SHAKE256 with fixed-size output.
///
/// Returns an array of N bytes.
///
/// # Example
///
/// ```
/// use anubis_core::keccak::shake::shake256;
///
/// let output: [u8; 32] = shake256(b"test");
/// ```
#[inline]
pub fn shake256<const N: usize>(data: &[u8]) -> [u8; N] {
    libcrux_sha3::shake256(data)
}

/// Incremental SHAKE256 hasher for streaming input.
///
/// This provides an incremental API by collecting absorbed data and
/// computing the final SHAKE256 output when squeeze is called.
pub struct Shake256 {
    buffer: Vec<u8>,
}

impl Shake256 {
    /// Create a new SHAKE256 hasher.
    #[inline]
    pub fn new() -> Self {
        Self { buffer: Vec::new() }
    }

    /// Absorb input data into the hasher.
    #[inline]
    pub fn absorb(&mut self, data: &[u8]) {
        self.buffer.extend_from_slice(data);
    }

    /// Finalize and produce a fixed-size output.
    #[inline]
    pub fn squeeze_fixed<const N: usize>(&self) -> [u8; N] {
        libcrux_sha3::shake256(&self.buffer)
    }

    /// Finalize and fill output buffer.
    #[inline]
    pub fn squeeze(&self, output: &mut [u8]) {
        // For dynamic sizes, we need to use the const generic version
        // and copy. This is less efficient but maintains API compatibility.
        match output.len() {
            0 => {}
            16 => {
                let out: [u8; 16] = libcrux_sha3::shake256(&self.buffer);
                output.copy_from_slice(&out);
            }
            32 => {
                let out: [u8; 32] = libcrux_sha3::shake256(&self.buffer);
                output.copy_from_slice(&out);
            }
            64 => {
                let out: [u8; 64] = libcrux_sha3::shake256(&self.buffer);
                output.copy_from_slice(&out);
            }
            128 => {
                let out: [u8; 128] = libcrux_sha3::shake256(&self.buffer);
                output.copy_from_slice(&out);
            }
            _ => {
                // For other sizes, generate max needed and truncate
                let out: [u8; 256] = libcrux_sha3::shake256(&self.buffer);
                let len = output.len().min(256);
                output[..len].copy_from_slice(&out[..len]);
            }
        }
    }
}

impl Default for Shake256 {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shake256_empty() {
        let output: [u8; 32] = shake256(b"");
        // SHAKE256("", 32) expected output
        let expected = [
            0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13,
            0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb, 0x24,
            0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82,
            0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5, 0x76, 0x2f,
        ];
        assert_eq!(output, expected);
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

    #[test]
    fn test_shake256_incremental() {
        let mut hasher = Shake256::new();
        hasher.absorb(b"test");
        hasher.absorb(b" ");
        hasher.absorb(b"input");
        let output: [u8; 32] = hasher.squeeze_fixed();

        // Compare with one-shot (should differ since incremental concatenates)
        let oneshot: [u8; 32] = shake256(b"test input");
        assert_eq!(output, oneshot);
    }
}
