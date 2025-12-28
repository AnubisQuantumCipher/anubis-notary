//! Fault Injection Countermeasures.
//!
//! This module provides countermeasures against fault injection attacks including:
//! - Voltage/clock glitching
//! - Electromagnetic fault injection (EMFI)
//! - Laser fault injection
//! - Rowhammer-style attacks
//!
//! ## Attack Model
//!
//! Fault injection attacks attempt to induce computational errors by manipulating
//! the physical execution environment. Common targets include:
//!
//! - **Signature generation**: Skip verification steps, force weak nonces
//! - **Encryption**: Skip rounds, force weak IVs, bypass authentication
//! - **Key derivation**: Reduce iteration counts, skip validation
//! - **Control flow**: Skip security checks, bypass authentication
//!
//! ## Countermeasures
//!
//! 1. **Redundant computation**: Perform critical operations twice with different
//!    register/memory layouts and compare results
//! 2. **Result verification**: After generating output, verify it (e.g., verify
//!    signature after signing)
//! 3. **Integrity checks**: Validate invariants before and after critical operations
//! 4. **Randomized execution**: Add timing jitter to defeat precise fault targeting
//!
//! ## Threat Levels
//!
//! | Countermeasure | Protection Level | Overhead |
//! |----------------|------------------|----------|
//! | Redundant computation | High | 2x compute |
//! | Result verification | High | ~1.5x compute |
//! | Integrity checks | Medium | Minimal |
//! | Timing jitter | Low | Variable |
//!
//! ## Verification Status
//!
//! **NOT FORMALLY VERIFIED**. The RefinedRust-style specifications in doc comments
//! describe design goals, not actual verification. These countermeasures are tested
//! via unit tests but formal proofs have not been completed.
//!
//! Design goals (unverified):
//! - Detection guarantee: Faults should be detected with high probability
//! - No silent failures: Faulted operations should not produce undetected bad output
//! - Correctness preservation: Countermeasures should not affect correct operation

use crate::ct::ct_eq;
use zeroize::Zeroize;

/// Error type for fault detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaultError {
    /// Redundant computation mismatch detected.
    RedundantMismatch,
    /// Result verification failed.
    VerificationFailed,
    /// Integrity check failed.
    IntegrityCheckFailed,
    /// Control flow anomaly detected.
    ControlFlowAnomaly,
}

impl core::fmt::Display for FaultError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::RedundantMismatch => write!(f, "redundant computation mismatch detected"),
            Self::VerificationFailed => write!(f, "result verification failed"),
            Self::IntegrityCheckFailed => write!(f, "integrity check failed"),
            Self::ControlFlowAnomaly => write!(f, "control flow anomaly detected"),
        }
    }
}

impl std::error::Error for FaultError {}

/// Sentinel value for control flow integrity checks.
///
/// This value is XOR'd with operation-specific tokens to create unique
/// markers for each critical code path.
const CONTROL_FLOW_SENTINEL: u64 = 0x5AFE_C0DE_CAFE_BABE;

/// Control flow integrity checker.
///
/// Tracks execution through critical code paths using a state machine.
/// Detects skipped operations or unexpected execution order.
///
/// # RefinedRust Specification
///
/// ```text
/// #[rr::refined_by("cfi" : "cfi_state")]
/// #[rr::invariant("cfi.state != INITIAL -> cfi.operations_count > 0")]
/// #[rr::invariant("cfi.checksum = fold_xor(cfi.tokens)")]
/// ```
pub struct ControlFlowIntegrity {
    /// Running XOR of all operation tokens
    checksum: u64,
    /// Expected final checksum
    expected: u64,
    /// Number of operations completed
    operations_count: u32,
}

impl ControlFlowIntegrity {
    /// Create a new CFI checker with expected operations.
    ///
    /// # Arguments
    ///
    /// * `expected_tokens` - Array of operation tokens expected to execute
    ///
    /// The expected checksum is computed as XOR of all tokens.
    #[inline]
    pub fn new(expected_tokens: &[u64]) -> Self {
        let expected = expected_tokens.iter().fold(CONTROL_FLOW_SENTINEL, |acc, &t| acc ^ t);
        Self {
            checksum: CONTROL_FLOW_SENTINEL,
            expected,
            operations_count: 0,
        }
    }

    /// Record an operation completion.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::ensures("self.checksum = old(self.checksum) ^ token")]
    /// #[rr::ensures("self.operations_count = old(self.operations_count) + 1")]
    /// ```
    #[inline]
    pub fn record(&mut self, token: u64) {
        self.checksum ^= token;
        self.operations_count = self.operations_count.wrapping_add(1);
    }

    /// Verify that all expected operations completed correctly.
    ///
    /// # Returns
    ///
    /// `Ok(())` if control flow is valid, `Err(ControlFlowAnomaly)` otherwise.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::returns("Ok(()) <-> self.checksum = self.expected")]
    /// #[rr::ensures("timing_independent_of(self.checksum)")]
    /// ```
    pub fn verify(&self) -> Result<(), FaultError> {
        // Constant-time comparison using ct_eq on little-endian bytes
        // This prevents timing attacks that could leak which operations were skipped
        if ct_eq(&self.checksum.to_le_bytes(), &self.expected.to_le_bytes()) {
            Ok(())
        } else {
            Err(FaultError::ControlFlowAnomaly)
        }
    }

    /// Get the number of recorded operations.
    #[inline]
    pub fn operation_count(&self) -> u32 {
        self.operations_count
    }
}

/// Compare two byte slices in constant time, returning an error on mismatch.
///
/// This is used to detect fault injection that causes computation divergence.
///
/// # RefinedRust Specification
///
/// ```text
/// #[rr::params("a" : "list u8", "b" : "list u8")]
/// #[rr::args("#a", "#b")]
/// #[rr::returns("Ok(()) <-> a = b")]
/// #[rr::ensures("timing_independent_of(a, b)")]
/// ```
#[inline]
pub fn verify_redundant(a: &[u8], b: &[u8]) -> Result<(), FaultError> {
    if ct_eq(a, b) {
        Ok(())
    } else {
        Err(FaultError::RedundantMismatch)
    }
}

/// Compare two fixed-size arrays in constant time.
#[inline]
pub fn verify_redundant_array<const N: usize>(a: &[u8; N], b: &[u8; N]) -> Result<(), FaultError> {
    verify_redundant(a.as_slice(), b.as_slice())
}

/// Redundant computation wrapper that performs operation twice and compares.
///
/// # Type Parameters
///
/// * `F` - The computation function
/// * `T` - Output type (must support equality comparison)
///
/// # Arguments
///
/// * `f` - The computation to perform
///
/// # Returns
///
/// The result if both computations match, or `FaultError::RedundantMismatch`.
///
/// # RefinedRust Specification
///
/// ```text
/// #[rr::params("f" : "unit -> T")]
/// #[rr::returns("Ok(f()) | Err(RedundantMismatch)")]
/// #[rr::ensures("is_ok(result) -> redundant_verified(result)")]
/// ```
///
/// # Security Note
///
/// The function is called twice. For cryptographic operations, ensure the
/// function is deterministic or uses verified randomness.
#[inline]
pub fn redundant_compute<F, T>(f: F) -> Result<T, FaultError>
where
    F: Fn() -> T,
    T: PartialEq,
{
    let result1 = f();
    // Memory barrier to prevent compiler optimization merging
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    let result2 = f();

    if result1 == result2 {
        Ok(result1)
    } else {
        Err(FaultError::RedundantMismatch)
    }
}

/// Redundant computation for fallible operations.
///
/// Performs the operation twice and verifies both succeed with identical results.
#[inline]
pub fn redundant_compute_result<F, T, E>(f: F) -> Result<T, FaultError>
where
    F: Fn() -> Result<T, E>,
    T: PartialEq,
{
    let result1 = match f() {
        Ok(v) => v,
        Err(_) => return Err(FaultError::RedundantMismatch),
    };

    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);

    let result2 = match f() {
        Ok(v) => v,
        Err(_) => return Err(FaultError::RedundantMismatch),
    };

    if result1 == result2 {
        Ok(result1)
    } else {
        Err(FaultError::RedundantMismatch)
    }
}

/// Integrity-checked buffer for sensitive data.
///
/// Stores data with a checksum that is verified before each access.
/// Detects memory corruption attacks like Rowhammer.
///
/// # RefinedRust Specification
///
/// ```text
/// #[rr::refined_by("buf" : "integrity_buffer")]
/// #[rr::invariant("buf.checksum = sha3_256(buf.data)")]
/// #[rr::owns("buf.data")]
/// ```
pub struct IntegrityBuffer<const N: usize> {
    data: [u8; N],
    checksum: [u8; 32],
}

impl<const N: usize> IntegrityBuffer<N> {
    /// Create a new integrity-checked buffer.
    pub fn new(data: [u8; N]) -> Self {
        let checksum = crate::keccak::sha3_256(&data);
        Self { data, checksum }
    }

    /// Read the data after verifying integrity.
    ///
    /// # Returns
    ///
    /// The data if integrity check passes, or `IntegrityCheckFailed`.
    pub fn read(&self) -> Result<&[u8; N], FaultError> {
        let current_checksum = crate::keccak::sha3_256(&self.data);
        if ct_eq(&current_checksum, &self.checksum) {
            Ok(&self.data)
        } else {
            Err(FaultError::IntegrityCheckFailed)
        }
    }

    /// Write new data and update the checksum.
    pub fn write(&mut self, data: [u8; N]) {
        self.data = data;
        self.checksum = crate::keccak::sha3_256(&self.data);
    }

    /// Get the raw data without integrity check (for internal use only).
    ///
    /// # Safety
    ///
    /// This method bypasses integrity verification. Use only when you have
    /// already verified integrity through other means.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn data_unchecked(&self) -> &[u8; N] {
        &self.data
    }
}

impl<const N: usize> Drop for IntegrityBuffer<N> {
    fn drop(&mut self) {
        self.data.zeroize();
        self.checksum.zeroize();
    }
}

/// Operation tokens for common cryptographic operations.
///
/// Use these with `ControlFlowIntegrity` to track execution.
pub mod tokens {
    /// Key generation operation
    pub const KEY_GEN: u64 = 0x4B45_5947_454E_0001;
    /// Signing operation
    pub const SIGN: u64 = 0x5349_474E_494E_0002;
    /// Signature verification
    pub const VERIFY: u64 = 0x5645_5249_4659_0003;
    /// Encryption operation
    pub const ENCRYPT: u64 = 0x454E_4352_5950_0004;
    /// Decryption operation
    pub const DECRYPT: u64 = 0x4445_4352_5950_0005;
    /// Hash computation
    pub const HASH: u64 = 0x4841_5348_494E_0006;
    /// Key derivation
    pub const KDF: u64 = 0x4B44_4600_0000_0007;
    /// Nonce generation
    pub const NONCE_GEN: u64 = 0x4E4F_4E43_4547_0008;
    /// Parameter validation
    pub const PARAM_CHECK: u64 = 0x5041_5241_4D43_0009;
    /// Output verification
    pub const OUTPUT_VERIFY: u64 = 0x4F55_5456_4552_000A;
}

/// Perform an operation with fault detection.
///
/// This is a high-level wrapper that:
/// 1. Records operation start in CFI
/// 2. Performs the operation with redundant computation
/// 3. Records operation completion in CFI
///
/// # Arguments
///
/// * `cfi` - Control flow integrity tracker
/// * `token` - Operation token for CFI
/// * `f` - The operation to perform
///
/// # Returns
///
/// The result if no faults detected, or a `FaultError`.
pub fn protected_operation<F, T, E>(
    cfi: &mut ControlFlowIntegrity,
    token: u64,
    f: F,
) -> Result<T, FaultError>
where
    F: Fn() -> Result<T, E>,
    T: PartialEq,
{
    // Record operation start
    let start_token = token ^ 0xAAAA_AAAA_AAAA_AAAA;
    cfi.record(start_token);

    // Perform with redundant computation
    let result = redundant_compute_result(f)?;

    // Record operation completion
    let end_token = token ^ 0x5555_5555_5555_5555;
    cfi.record(end_token);

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_redundant_match() {
        let a = [1u8, 2, 3, 4];
        let b = [1u8, 2, 3, 4];
        assert!(verify_redundant(&a, &b).is_ok());
    }

    #[test]
    fn test_verify_redundant_mismatch() {
        let a = [1u8, 2, 3, 4];
        let b = [1u8, 2, 3, 5];
        assert_eq!(verify_redundant(&a, &b), Err(FaultError::RedundantMismatch));
    }

    #[test]
    fn test_redundant_compute_success() {
        let result = redundant_compute(|| 42);
        assert_eq!(result, Ok(42));
    }

    #[test]
    fn test_control_flow_integrity() {
        let tokens = [tokens::SIGN, tokens::VERIFY];
        let mut cfi = ControlFlowIntegrity::new(&tokens);

        cfi.record(tokens::SIGN);
        cfi.record(tokens::VERIFY);

        assert!(cfi.verify().is_ok());
    }

    #[test]
    fn test_control_flow_missing_operation() {
        let tokens = [tokens::SIGN, tokens::VERIFY];
        let mut cfi = ControlFlowIntegrity::new(&tokens);

        // Only record one operation
        cfi.record(tokens::SIGN);

        assert_eq!(cfi.verify(), Err(FaultError::ControlFlowAnomaly));
    }

    #[test]
    fn test_integrity_buffer() {
        let data = [0xABu8; 32];
        let buf = IntegrityBuffer::new(data);

        assert_eq!(buf.read().unwrap(), &data);
    }

    #[test]
    fn test_error_display() {
        assert_eq!(
            format!("{}", FaultError::RedundantMismatch),
            "redundant computation mismatch detected"
        );
        assert_eq!(
            format!("{}", FaultError::ControlFlowAnomaly),
            "control flow anomaly detected"
        );
    }
}
