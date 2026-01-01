//! Password recovery using Shamir's Secret Sharing Scheme.
//!
//! This module implements (t, n) threshold secret sharing for key recovery,
//! allowing a secret to be split into n shares where any t shares can
//! reconstruct the original secret.
//!
//! ## Security Properties
//!
//! - Information-theoretic security: t-1 shares reveal nothing about the secret
//! - Uses GF(2^8) arithmetic for byte-level operations
//! - Cryptographically random share generation
//! - Zeroization of sensitive data on drop
//!
//! ## Usage
//!
//! ```ignore
//! // Split a secret key into 5 shares, requiring 3 to recover
//! let shares = ShamirSharing::split(&secret_key, 3, 5)?;
//!
//! // Distribute shares to trustees
//! for (i, share) in shares.iter().enumerate() {
//!     send_to_trustee(i, share);
//! }
//!
//! // Later, recover with any 3 shares
//! let recovered = ShamirSharing::combine(&[shares[0], shares[2], shares[4]])?;
//! assert_eq!(recovered, secret_key);
//! ```

use zeroize::{Zeroize, ZeroizeOnDrop};

use crate::keccak::sha3::sha3_256;
use getrandom::getrandom;

/// Maximum number of shares (limited by GF(2^8) field size).
pub const MAX_SHARES: u8 = 255;

/// Maximum threshold.
pub const MAX_THRESHOLD: u8 = 255;

/// Minimum threshold (need at least 2 for meaningful splitting).
pub const MIN_THRESHOLD: u8 = 2;

/// Errors from secret sharing operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ShamirError {
    /// Threshold must be >= 2.
    ThresholdTooLow,
    /// Threshold must be <= total shares.
    ThresholdExceedsShares,
    /// Number of shares must be >= 2.
    TooFewShares,
    /// Number of shares exceeds maximum (255).
    TooManyShares,
    /// Not enough shares provided for recovery.
    InsufficientShares,
    /// Share data is corrupted or invalid.
    InvalidShare,
    /// Duplicate share indices detected.
    DuplicateShares,
    /// Secret is empty.
    EmptySecret,
    /// Share lengths don't match.
    MismatchedShareLengths,
    /// Checksum verification failed.
    ChecksumMismatch,
    /// Random number generation failed.
    RngError,
}

/// A single share from Shamir's Secret Sharing.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct Share {
    /// Share index (1-255, 0 is reserved for the secret).
    pub index: u8,
    /// Share data (same length as original secret + 4 bytes checksum).
    pub data: Vec<u8>,
    /// Threshold required to reconstruct (stored for verification).
    pub threshold: u8,
}

impl Share {
    /// Create a new share.
    fn new(index: u8, data: Vec<u8>, threshold: u8) -> Self {
        Self {
            index,
            data,
            threshold,
        }
    }

    /// Get the share as bytes for storage/transmission.
    ///
    /// Format: [version:1][threshold:1][index:1][data_len:2][data:N][checksum:4]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut result = Vec::with_capacity(5 + self.data.len() + 4);
        result.push(1); // Version
        result.push(self.threshold);
        result.push(self.index);
        result.extend_from_slice(&(self.data.len() as u16).to_le_bytes());
        result.extend_from_slice(&self.data);

        // Compute checksum of everything so far
        let checksum = sha3_256(&result);
        result.extend_from_slice(&checksum[..4]);

        result
    }

    /// Parse a share from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ShamirError> {
        if bytes.len() < 9 {
            return Err(ShamirError::InvalidShare);
        }

        let version = bytes[0];
        if version != 1 {
            return Err(ShamirError::InvalidShare);
        }

        let threshold = bytes[1];
        let index = bytes[2];
        let data_len = u16::from_le_bytes([bytes[3], bytes[4]]) as usize;

        if bytes.len() != 5 + data_len + 4 {
            return Err(ShamirError::InvalidShare);
        }

        let data = bytes[5..5 + data_len].to_vec();
        let stored_checksum = &bytes[5 + data_len..];

        // Verify checksum
        let computed_checksum = sha3_256(&bytes[..5 + data_len]);
        if &computed_checksum[..4] != stored_checksum {
            return Err(ShamirError::ChecksumMismatch);
        }

        Ok(Self {
            index,
            data,
            threshold,
        })
    }

    /// Get hex encoding of the share for display.
    pub fn to_hex(&self) -> String {
        hex::encode(self.to_bytes())
    }

    /// Parse from hex string.
    pub fn from_hex(s: &str) -> Result<Self, ShamirError> {
        let bytes = hex::decode(s).map_err(|_| ShamirError::InvalidShare)?;
        Self::from_bytes(&bytes)
    }
}

impl std::fmt::Debug for Share {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Share")
            .field("index", &self.index)
            .field("threshold", &self.threshold)
            .field("data_len", &self.data.len())
            .finish()
    }
}

/// GF(2^8) field operations for Shamir's Secret Sharing.
///
/// Uses the Rijndael polynomial: x^8 + x^4 + x^3 + x + 1 (0x11B)
mod gf256 {
    /// Precomputed log table for GF(2^8) with generator 3.
    /// LOG_TABLE[x] = log_3(x) for x in 1..255, LOG_TABLE[0] = 0 (undefined).
    #[rustfmt::skip]
    static LOG_TABLE: [u8; 256] = [
        0x00, 0x00, 0x19, 0x01, 0x32, 0x02, 0x1a, 0xc6, 0x4b, 0xc7, 0x1b, 0x68, 0x33, 0xee, 0xdf, 0x03,
        0x64, 0x04, 0xe0, 0x0e, 0x34, 0x8d, 0x81, 0xef, 0x4c, 0x71, 0x08, 0xc8, 0xf8, 0x69, 0x1c, 0xc1,
        0x7d, 0xc2, 0x1d, 0xb5, 0xf9, 0xb9, 0x27, 0x6a, 0x4d, 0xe4, 0xa6, 0x72, 0x9a, 0xc9, 0x09, 0x78,
        0x65, 0x2f, 0x8a, 0x05, 0x21, 0x0f, 0xe1, 0x24, 0x12, 0xf0, 0x82, 0x45, 0x35, 0x93, 0xda, 0x8e,
        0x96, 0x8f, 0xdb, 0xbd, 0x36, 0xd0, 0xce, 0x94, 0x13, 0x5c, 0xd2, 0xf1, 0x40, 0x46, 0x83, 0x38,
        0x66, 0xdd, 0xfd, 0x30, 0xbf, 0x06, 0x8b, 0x62, 0xb3, 0x25, 0xe2, 0x98, 0x22, 0x88, 0x91, 0x10,
        0x7e, 0x6e, 0x48, 0xc3, 0xa3, 0xb6, 0x1e, 0x42, 0x3a, 0x6b, 0x28, 0x54, 0xfa, 0x85, 0x3d, 0xba,
        0x2b, 0x79, 0x0a, 0x15, 0x9b, 0x9f, 0x5e, 0xca, 0x4e, 0xd4, 0xac, 0xe5, 0xf3, 0x73, 0xa7, 0x57,
        0xaf, 0x58, 0xa8, 0x50, 0xf4, 0xea, 0xd6, 0x74, 0x4f, 0xae, 0xe9, 0xd5, 0xe7, 0xe6, 0xad, 0xe8,
        0x2c, 0xd7, 0x75, 0x7a, 0xeb, 0x16, 0x0b, 0xf5, 0x59, 0xcb, 0x5f, 0xb0, 0x9c, 0xa9, 0x51, 0xa0,
        0x7f, 0x0c, 0xf6, 0x6f, 0x17, 0xc4, 0x49, 0xec, 0xd8, 0x43, 0x1f, 0x2d, 0xa4, 0x76, 0x7b, 0xb7,
        0xcc, 0xbb, 0x3e, 0x5a, 0xfb, 0x60, 0xb1, 0x86, 0x3b, 0x52, 0xa1, 0x6c, 0xaa, 0x55, 0x29, 0x9d,
        0x97, 0xb2, 0x87, 0x90, 0x61, 0xbe, 0xdc, 0xfc, 0xbc, 0x95, 0xcf, 0xcd, 0x37, 0x3f, 0x5b, 0xd1,
        0x53, 0x39, 0x84, 0x3c, 0x41, 0xa2, 0x6d, 0x47, 0x14, 0x2a, 0x9e, 0x5d, 0x56, 0xf2, 0xd3, 0xab,
        0x44, 0x11, 0x92, 0xd9, 0x23, 0x20, 0x2e, 0x89, 0xb4, 0x7c, 0xb8, 0x26, 0x77, 0x99, 0xe3, 0xa5,
        0x67, 0x4a, 0xed, 0xde, 0xc5, 0x31, 0xfe, 0x18, 0x0d, 0x63, 0x8c, 0x80, 0xc0, 0xf7, 0x70, 0x07,
    ];

    /// Precomputed exp table for GF(2^8) with generator 3.
    /// EXP_TABLE[i] = 3^i mod p(x) for i in 0..255.
    /// Note: EXP_TABLE[255] = 1 = EXP_TABLE[0] (the group has order 255).
    #[rustfmt::skip]
    static EXP_TABLE: [u8; 256] = [
        0x01, 0x03, 0x05, 0x0f, 0x11, 0x33, 0x55, 0xff, 0x1a, 0x2e, 0x72, 0x96, 0xa1, 0xf8, 0x13, 0x35,
        0x5f, 0xe1, 0x38, 0x48, 0xd8, 0x73, 0x95, 0xa4, 0xf7, 0x02, 0x06, 0x0a, 0x1e, 0x22, 0x66, 0xaa,
        0xe5, 0x34, 0x5c, 0xe4, 0x37, 0x59, 0xeb, 0x26, 0x6a, 0xbe, 0xd9, 0x70, 0x90, 0xab, 0xe6, 0x31,
        0x53, 0xf5, 0x04, 0x0c, 0x14, 0x3c, 0x44, 0xcc, 0x4f, 0xd1, 0x68, 0xb8, 0xd3, 0x6e, 0xb2, 0xcd,
        0x4c, 0xd4, 0x67, 0xa9, 0xe0, 0x3b, 0x4d, 0xd7, 0x62, 0xa6, 0xf1, 0x08, 0x18, 0x28, 0x78, 0x88,
        0x83, 0x9e, 0xb9, 0xd0, 0x6b, 0xbd, 0xdc, 0x7f, 0x81, 0x98, 0xb3, 0xce, 0x49, 0xdb, 0x76, 0x9a,
        0xb5, 0xc4, 0x57, 0xf9, 0x10, 0x30, 0x50, 0xf0, 0x0b, 0x1d, 0x27, 0x69, 0xbb, 0xd6, 0x61, 0xa3,
        0xfe, 0x19, 0x2b, 0x7d, 0x87, 0x92, 0xad, 0xec, 0x2f, 0x71, 0x93, 0xae, 0xe9, 0x20, 0x60, 0xa0,
        0xfb, 0x16, 0x3a, 0x4e, 0xd2, 0x6d, 0xb7, 0xc2, 0x5d, 0xe7, 0x32, 0x56, 0xfa, 0x15, 0x3f, 0x41,
        0xc3, 0x5e, 0xe2, 0x3d, 0x47, 0xc9, 0x40, 0xc0, 0x5b, 0xed, 0x2c, 0x74, 0x9c, 0xbf, 0xda, 0x75,
        0x9f, 0xba, 0xd5, 0x64, 0xac, 0xef, 0x2a, 0x7e, 0x82, 0x9d, 0xbc, 0xdf, 0x7a, 0x8e, 0x89, 0x80,
        0x9b, 0xb6, 0xc1, 0x58, 0xe8, 0x23, 0x65, 0xaf, 0xea, 0x25, 0x6f, 0xb1, 0xc8, 0x43, 0xc5, 0x54,
        0xfc, 0x1f, 0x21, 0x63, 0xa5, 0xf4, 0x07, 0x09, 0x1b, 0x2d, 0x77, 0x99, 0xb0, 0xcb, 0x46, 0xca,
        0x45, 0xcf, 0x4a, 0xde, 0x79, 0x8b, 0x86, 0x91, 0xa8, 0xe3, 0x3e, 0x42, 0xc6, 0x51, 0xf3, 0x0e,
        0x12, 0x36, 0x5a, 0xee, 0x29, 0x7b, 0x8d, 0x8c, 0x8f, 0x8a, 0x85, 0x94, 0xa7, 0xf2, 0x0d, 0x17,
        0x39, 0x4b, 0xdd, 0x7c, 0x84, 0x97, 0xa2, 0xfd, 0x1c, 0x24, 0x6c, 0xb4, 0xc7, 0x52, 0xf6, 0x01,
    ];

    /// Add two elements in GF(2^8).
    #[inline]
    pub fn add(a: u8, b: u8) -> u8 {
        a ^ b
    }

    /// Subtract in GF(2^8) (same as add).
    #[inline]
    pub fn sub(a: u8, b: u8) -> u8 {
        a ^ b
    }

    /// Multiply two elements in GF(2^8).
    #[inline]
    pub fn mul(a: u8, b: u8) -> u8 {
        if a == 0 || b == 0 {
            return 0;
        }
        let log_a = LOG_TABLE[a as usize] as usize;
        let log_b = LOG_TABLE[b as usize] as usize;
        // The multiplicative group has order 255, so we must reduce mod 255
        let sum = log_a + log_b;
        let reduced = if sum >= 255 { sum - 255 } else { sum };
        EXP_TABLE[reduced]
    }

    /// Compute multiplicative inverse in GF(2^8).
    #[inline]
    #[allow(dead_code)]
    pub fn inv(a: u8) -> u8 {
        if a == 0 {
            return 0; // 0 has no inverse, but we return 0 for consistency
        }
        let log_a = LOG_TABLE[a as usize] as usize;
        EXP_TABLE[255 - log_a]
    }

    /// Divide in GF(2^8).
    #[inline]
    pub fn div(a: u8, b: u8) -> u8 {
        if b == 0 {
            return 0; // Avoid division by zero
        }
        if a == 0 {
            return 0;
        }
        let log_a = LOG_TABLE[a as usize] as usize;
        let log_b = LOG_TABLE[b as usize] as usize;
        // (log_a - log_b + 255) mod 255
        let diff = if log_a >= log_b {
            log_a - log_b
        } else {
            log_a + 255 - log_b
        };
        EXP_TABLE[diff]
    }

    /// Evaluate polynomial at point x using Horner's method.
    pub fn eval_poly(coeffs: &[u8], x: u8) -> u8 {
        if coeffs.is_empty() {
            return 0;
        }

        let mut result = coeffs[coeffs.len() - 1];
        for i in (0..coeffs.len() - 1).rev() {
            result = add(mul(result, x), coeffs[i]);
        }
        result
    }

    /// Lagrange interpolation to find f(0).
    #[allow(clippy::needless_range_loop)] // Index comparison required for Lagrange basis
    pub fn interpolate_at_zero(points: &[(u8, u8)]) -> u8 {
        let n = points.len();
        let mut result = 0u8;

        for i in 0..n {
            let (xi, yi) = points[i];
            let mut numerator = 1u8;
            let mut denominator = 1u8;

            for j in 0..n {
                if i != j {
                    let (xj, _) = points[j];
                    // numerator *= (0 - xj) = xj (in GF(2^8))
                    numerator = mul(numerator, xj);
                    // denominator *= (xi - xj)
                    denominator = mul(denominator, sub(xi, xj));
                }
            }

            // term = yi * numerator / denominator
            let term = mul(yi, div(numerator, denominator));
            result = add(result, term);
        }

        result
    }
}

/// Shamir's Secret Sharing implementation.
pub struct ShamirSharing;

impl ShamirSharing {
    /// Split a secret into n shares, requiring t shares to reconstruct.
    ///
    /// # Arguments
    /// * `secret` - The secret bytes to split
    /// * `threshold` - Minimum shares required to reconstruct (t)
    /// * `total_shares` - Total number of shares to create (n)
    ///
    /// # Returns
    /// A vector of shares, each containing an index and data.
    ///
    /// # Errors
    /// Returns error if parameters are invalid.
    pub fn split(
        secret: &[u8],
        threshold: u8,
        total_shares: u8,
    ) -> Result<Vec<Share>, ShamirError> {
        // Validate parameters
        if secret.is_empty() {
            return Err(ShamirError::EmptySecret);
        }
        if threshold < MIN_THRESHOLD {
            return Err(ShamirError::ThresholdTooLow);
        }
        if total_shares < threshold {
            return Err(ShamirError::ThresholdExceedsShares);
        }
        if total_shares < 2 {
            return Err(ShamirError::TooFewShares);
        }

        let mut shares: Vec<Share> = (1..=total_shares)
            .map(|i| Share::new(i, vec![0u8; secret.len()], threshold))
            .collect();

        // Pre-allocate random bytes for all coefficients
        // We need (threshold - 1) random bytes per secret byte
        let random_bytes_needed = secret.len() * (threshold as usize - 1);
        let mut random_bytes = vec![0u8; random_bytes_needed];

        // Use OS entropy for cryptographically secure randomness
        // This ensures each split produces unique shares
        getrandom(&mut random_bytes).map_err(|_| ShamirError::RngError)?;

        let mut random_idx = 0;

        for (byte_idx, &secret_byte) in secret.iter().enumerate() {
            // Generate random coefficients for polynomial of degree threshold-1
            // coeffs[0] = secret_byte, coeffs[1..threshold] = truly random from OS
            let mut coeffs = vec![0u8; threshold as usize];
            coeffs[0] = secret_byte;

            for coeff in coeffs.iter_mut().skip(1).take(threshold as usize - 1) {
                // Use cryptographically secure random bytes from OS entropy
                *coeff = random_bytes[random_idx];
                random_idx += 1;
            }

            // Evaluate polynomial at each share index
            for share in &mut shares {
                share.data[byte_idx] = gf256::eval_poly(&coeffs, share.index);
            }

            // Zeroize coefficients
            coeffs.zeroize();
        }

        // Zeroize random bytes buffer
        random_bytes.zeroize();

        Ok(shares)
    }

    /// Reconstruct the secret from shares.
    ///
    /// # Arguments
    /// * `shares` - At least `threshold` shares
    ///
    /// # Returns
    /// The reconstructed secret bytes.
    ///
    /// # Errors
    /// Returns error if shares are invalid or insufficient.
    pub fn combine(shares: &[Share]) -> Result<Vec<u8>, ShamirError> {
        if shares.is_empty() {
            return Err(ShamirError::InsufficientShares);
        }

        let threshold = shares[0].threshold;
        if shares.len() < threshold as usize {
            return Err(ShamirError::InsufficientShares);
        }

        // Verify all shares have same threshold and length
        let data_len = shares[0].data.len();
        for share in shares {
            if share.threshold != threshold {
                return Err(ShamirError::InvalidShare);
            }
            if share.data.len() != data_len {
                return Err(ShamirError::MismatchedShareLengths);
            }
        }

        // Check for duplicate indices
        let mut indices: Vec<u8> = shares.iter().map(|s| s.index).collect();
        indices.sort();
        for i in 1..indices.len() {
            if indices[i] == indices[i - 1] {
                return Err(ShamirError::DuplicateShares);
            }
        }

        // Use only the first `threshold` shares
        let shares_to_use = &shares[..threshold as usize];

        // Reconstruct each byte using Lagrange interpolation
        let mut secret = vec![0u8; data_len];

        #[allow(clippy::needless_range_loop)]
        // Index needed for parallel access to secret and share.data
        for byte_idx in 0..data_len {
            let points: Vec<(u8, u8)> = shares_to_use
                .iter()
                .map(|s| (s.index, s.data[byte_idx]))
                .collect();

            secret[byte_idx] = gf256::interpolate_at_zero(&points);
        }

        Ok(secret)
    }

    /// Verify that a set of shares can reconstruct a valid secret.
    ///
    /// This doesn't reveal the secret, just checks consistency.
    pub fn verify_shares(shares: &[Share]) -> bool {
        if shares.len() < 2 {
            return false;
        }

        // Check basic validity
        let threshold = shares[0].threshold;
        let data_len = shares[0].data.len();

        for share in shares {
            if share.threshold != threshold || share.data.len() != data_len {
                return false;
            }
        }

        // If we have enough shares, try combining and verify it works
        if shares.len() >= threshold as usize {
            Self::combine(shares).is_ok()
        } else {
            true // Can't fully verify without threshold shares
        }
    }
}

/// Recovery coordinator for managing the key recovery process.
pub struct RecoveryCoordinator {
    /// Collected shares.
    shares: Vec<Share>,
    /// Required threshold.
    threshold: u8,
}

impl RecoveryCoordinator {
    /// Create a new recovery coordinator.
    pub fn new(threshold: u8) -> Self {
        Self {
            shares: Vec::new(),
            threshold,
        }
    }

    /// Add a share to the recovery process.
    pub fn add_share(&mut self, share: Share) -> Result<(), ShamirError> {
        // Check for duplicates
        for existing in &self.shares {
            if existing.index == share.index {
                return Err(ShamirError::DuplicateShares);
            }
        }

        // Verify threshold matches
        if share.threshold != self.threshold {
            return Err(ShamirError::InvalidShare);
        }

        self.shares.push(share);
        Ok(())
    }

    /// Get the number of shares collected.
    pub fn shares_collected(&self) -> usize {
        self.shares.len()
    }

    /// Get the number of shares still needed.
    pub fn shares_needed(&self) -> usize {
        if self.shares.len() >= self.threshold as usize {
            0
        } else {
            self.threshold as usize - self.shares.len()
        }
    }

    /// Check if we have enough shares to recover.
    pub fn can_recover(&self) -> bool {
        self.shares.len() >= self.threshold as usize
    }

    /// Attempt to recover the secret.
    pub fn recover(&self) -> Result<Vec<u8>, ShamirError> {
        if !self.can_recover() {
            return Err(ShamirError::InsufficientShares);
        }
        ShamirSharing::combine(&self.shares)
    }

    /// Clear all collected shares.
    pub fn clear(&mut self) {
        for share in &mut self.shares {
            share.zeroize();
        }
        self.shares.clear();
    }
}

impl Drop for RecoveryCoordinator {
    fn drop(&mut self) {
        self.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gf256_basic() {
        // Test basic field properties
        assert_eq!(gf256::add(0, 0), 0);
        assert_eq!(gf256::add(1, 1), 0);
        assert_eq!(gf256::mul(1, 1), 1);
        assert_eq!(gf256::mul(0, 255), 0);
        assert_eq!(gf256::inv(1), 1);

        // Test inverse property: a * inv(a) = 1
        for a in 1..=255u8 {
            let inv_a = gf256::inv(a);
            assert_eq!(gf256::mul(a, inv_a), 1, "Failed for a={}", a);
        }
    }

    #[test]
    fn test_split_combine_basic() {
        let secret = b"Hello, World!";
        let shares = ShamirSharing::split(secret, 3, 5).unwrap();

        assert_eq!(shares.len(), 5);
        for share in &shares {
            assert_eq!(share.threshold, 3);
            assert_eq!(share.data.len(), secret.len());
        }

        // Combine with exactly threshold shares
        let recovered = ShamirSharing::combine(&shares[0..3]).unwrap();
        assert_eq!(&recovered, secret);

        // Combine with different subset
        let recovered2 =
            ShamirSharing::combine(&[shares[1].clone(), shares[3].clone(), shares[4].clone()])
                .unwrap();
        assert_eq!(&recovered2, secret);
    }

    #[test]
    fn test_split_combine_all_shares() {
        let secret = b"Test secret data for recovery";
        let shares = ShamirSharing::split(secret, 2, 5).unwrap();

        // Should work with all shares too
        let recovered = ShamirSharing::combine(&shares).unwrap();
        assert_eq!(&recovered, secret);
    }

    #[test]
    fn test_insufficient_shares() {
        let secret = b"Secret";
        let shares = ShamirSharing::split(secret, 3, 5).unwrap();

        // Only 2 shares when 3 are needed
        let result = ShamirSharing::combine(&shares[0..2]);
        assert!(matches!(result, Err(ShamirError::InsufficientShares)));
    }

    #[test]
    fn test_share_serialization() {
        let secret = b"Test secret";
        let shares = ShamirSharing::split(secret, 2, 3).unwrap();

        for share in &shares {
            let bytes = share.to_bytes();
            let parsed = Share::from_bytes(&bytes).unwrap();
            assert_eq!(parsed.index, share.index);
            assert_eq!(parsed.data, share.data);
            assert_eq!(parsed.threshold, share.threshold);
        }
    }

    #[test]
    fn test_share_hex_encoding() {
        let secret = b"Hex test";
        let shares = ShamirSharing::split(secret, 2, 3).unwrap();

        for share in &shares {
            let hex = share.to_hex();
            let parsed = Share::from_hex(&hex).unwrap();
            assert_eq!(parsed.index, share.index);
            assert_eq!(parsed.data, share.data);
        }
    }

    #[test]
    fn test_duplicate_shares_rejected() {
        let secret = b"Dup test";
        let shares = ShamirSharing::split(secret, 2, 3).unwrap();

        // Same share twice
        let result = ShamirSharing::combine(&[shares[0].clone(), shares[0].clone()]);
        assert!(matches!(result, Err(ShamirError::DuplicateShares)));
    }

    #[test]
    fn test_recovery_coordinator() {
        let secret = b"Coordinator test";
        let shares = ShamirSharing::split(secret, 3, 5).unwrap();

        let mut coord = RecoveryCoordinator::new(3);
        assert!(!coord.can_recover());
        assert_eq!(coord.shares_needed(), 3);

        coord.add_share(shares[0].clone()).unwrap();
        assert_eq!(coord.shares_collected(), 1);
        assert_eq!(coord.shares_needed(), 2);

        coord.add_share(shares[2].clone()).unwrap();
        coord.add_share(shares[4].clone()).unwrap();

        assert!(coord.can_recover());
        let recovered = coord.recover().unwrap();
        assert_eq!(&recovered, secret);
    }

    #[test]
    fn test_checksum_verification() {
        let secret = b"Checksum test";
        let shares = ShamirSharing::split(secret, 2, 3).unwrap();

        let mut bytes = shares[0].to_bytes();
        // Corrupt the data
        bytes[6] ^= 0xFF;

        let result = Share::from_bytes(&bytes);
        assert!(matches!(result, Err(ShamirError::ChecksumMismatch)));
    }

    #[test]
    fn test_parameter_validation() {
        let secret = b"Test";

        // Threshold too low
        assert!(matches!(
            ShamirSharing::split(secret, 1, 5),
            Err(ShamirError::ThresholdTooLow)
        ));

        // Threshold exceeds shares
        assert!(matches!(
            ShamirSharing::split(secret, 5, 3),
            Err(ShamirError::ThresholdExceedsShares)
        ));

        // Empty secret
        assert!(matches!(
            ShamirSharing::split(&[], 2, 3),
            Err(ShamirError::EmptySecret)
        ));
    }

    #[test]
    fn test_large_secret() {
        // Test with a larger secret (256 bytes)
        let secret: Vec<u8> = (0..=255).collect();
        let shares = ShamirSharing::split(&secret, 5, 10).unwrap();

        // Use shares 2, 4, 6, 8, 10
        let subset: Vec<_> = shares.iter().step_by(2).cloned().collect();
        let recovered = ShamirSharing::combine(&subset).unwrap();
        assert_eq!(recovered, secret);
    }
}
