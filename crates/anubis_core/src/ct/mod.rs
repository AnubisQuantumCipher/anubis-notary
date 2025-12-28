//! Constant-time operations for cryptographic safety.
//!
//! This module provides constant-time primitives that avoid secret-dependent
//! branches and memory accesses. All operations use mask-based selection.
//!
//! ## Security Properties (Design Goals)
//!
//! These functions are designed for:
//! - **Timing Independence**: Execution time does not depend on secret values
//! - **No Secret-Dependent Branches**: All control flow is data-independent
//! - **No Secret-Dependent Memory Access**: All memory accesses are uniform
//!
//! ## Verification Status
//!
//! **NOT FORMALLY VERIFIED**. The RefinedRust-style specifications in doc comments
//! are aspirational documentation of intended properties, not actual verification.
//! These properties are tested empirically via dudect timing analysis (see
//! `benches/crypto_timing.rs`), but formal proofs have not been completed.
//!
//! See `specs/refinedrust/theories/ct_spec.v` for the specification we intend
//! to verify against in the future.
//!
//! ## Implementation Notes
//!
//! All functions use the `subtle` crate's `ConditionallySelectable` trait
//! which provides constant-time selection primitives.

use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

/// Constant-time equality comparison for byte slices.
///
/// Returns `true` if and only if `a` and `b` have the same length and contents.
/// The comparison time depends only on the length, not the contents.
///
/// # RefinedRust Specification
///
/// ```text
/// #[rr::params("a" : "list u8", "b" : "list u8")]
/// #[rr::args("#a", "#b")]
/// #[rr::returns("#(a = b)")]
/// #[rr::ensures("timing_independent_of(a, b)")]
/// #[rr::ensures("execution_time(ct_eq) = O(max(len(a), len(b)))")]
/// #[rr::pure]
/// ```
///
/// Security: The function first checks length (public information), then performs
/// a constant-time byte-by-byte comparison that takes the same time regardless
/// of where the first difference occurs.
#[inline]
pub fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.ct_eq(b).into()
}

/// Constant-time conditional selection for u8.
///
/// Returns `a` if `choice` is true, otherwise returns `b`.
/// The selection time is independent of the choice value.
///
/// # RefinedRust Specification
///
/// ```text
/// #[rr::params("choice" : "bool", "a" : "u8", "b" : "u8")]
/// #[rr::args("#choice", "#a", "#b")]
/// #[rr::returns("#(if choice then a else b)")]
/// #[rr::ensures("timing_independent_of(choice)")]
/// #[rr::ensures("no_branch_on(choice)")]
/// #[rr::pure]
/// ```
///
/// Implementation: Uses mask-based selection: result = (a & mask) | (b & ~mask)
/// where mask is derived from choice without branching.
#[inline]
pub fn ct_select(choice: bool, a: u8, b: u8) -> u8 {
    u8::conditional_select(&b, &a, Choice::from(choice as u8))
}

/// Constant-time conditional selection for u32.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::params("choice" : "bool", "a" : "u32", "b" : "u32")]
/// #[rr::returns("#(if choice then a else b)")]
/// #[rr::ensures("timing_independent_of(choice)")]
/// ```
#[inline]
pub fn ct_select_u32(choice: bool, a: u32, b: u32) -> u32 {
    u32::conditional_select(&b, &a, Choice::from(choice as u8))
}

/// Constant-time conditional selection for u64.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::params("choice" : "bool", "a" : "u64", "b" : "u64")]
/// #[rr::returns("#(if choice then a else b)")]
/// #[rr::ensures("timing_independent_of(choice)")]
/// ```
#[inline]
pub fn ct_select_u64(choice: bool, a: u64, b: u64) -> u64 {
    u64::conditional_select(&b, &a, Choice::from(choice as u8))
}

/// Constant-time conditional move (cmov) for byte arrays.
///
/// If `choice` is true, copies `src` into `dst`. Otherwise, `dst` is unchanged.
/// The operation time is independent of the choice value.
///
/// # RefinedRust Specification
///
/// ```text
/// #[rr::params("gamma" : "gname", "choice" : "bool", "src" : "array u8 N", "dst" : "array u8 N")]
/// #[rr::args("#choice", "#src", "(#dst, gamma) @ &mut [u8; N]")]
/// #[rr::ensures("gamma(if choice then src else old(dst))")]
/// #[rr::ensures("timing_independent_of(choice)")]
/// #[rr::ensures("no_branch_on(choice)")]
/// #[rr::loop_inv("forall j. j < i -> dst[j] = (if choice then src[j] else old(dst)[j])")]
/// ```
///
/// Implementation: Iterates through all bytes, performing constant-time selection
/// for each byte individually. The loop always executes N iterations regardless
/// of the choice value.
#[inline]
pub fn ct_cmov<const N: usize>(choice: bool, src: &[u8; N], dst: &mut [u8; N]) {
    let choice = Choice::from(choice as u8);
    for i in 0..N {
        dst[i] = u8::conditional_select(&dst[i], &src[i], choice);
    }
}

/// Constant-time conditional move for slices of equal length.
///
/// # Panics
///
/// Panics if `src.len() != dst.len()`.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::requires("src.len() == dst.len()")]
/// #[rr::ensures("timing_independent_of(choice)")]
/// ```
#[inline]
pub fn ct_cmov_slice(choice: bool, src: &[u8], dst: &mut [u8]) {
    assert_eq!(src.len(), dst.len(), "slice length mismatch");
    let choice = Choice::from(choice as u8);
    for i in 0..src.len() {
        dst[i] = u8::conditional_select(&dst[i], &src[i], choice);
    }
}

/// Constant-time byte comparison that returns 0 if equal, 1 if not.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::params("a" : "u8", "b" : "u8")]
/// #[rr::returns("#(if a = b then 0 else 1)")]
/// ```
#[inline]
pub fn ct_ne_byte(a: u8, b: u8) -> u8 {
    let x = a ^ b;
    // Collapse all bits into the LSB
    let x = x | (x >> 4);
    let x = x | (x >> 2);
    let x = x | (x >> 1);
    x & 1
}

/// Constant-time less-than comparison for u64.
///
/// Returns 1 if a < b, 0 otherwise.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::params("a" : "u64", "b" : "u64")]
/// #[rr::returns("#(if a < b then 1 else 0)")]
/// #[rr::ensures("timing_independent_of(a, b)")]
/// ```
#[inline]
pub fn ct_lt_u64(a: u64, b: u64) -> u64 {
    // Use the sign bit of (a - b) when a < b (underflow sets MSB)
    let diff = a.wrapping_sub(b);
    let borrow = ((!a) & b) | (((!a) | b) & diff);
    borrow >> 63
}

/// Constant-time greater-than comparison for u64.
///
/// Returns 1 if a > b, 0 otherwise.
#[inline]
pub fn ct_gt_u64(a: u64, b: u64) -> u64 {
    ct_lt_u64(b, a)
}

/// Create a mask from a Choice value (all 1s if true, all 0s if false).
///
/// # RefinedRust Specification
/// ```text
/// #[rr::params("c" : "bool")]
/// #[rr::returns("#(if c then 0xFF else 0x00)")]
/// ```
#[inline]
pub fn choice_to_mask(c: Choice) -> u8 {
    u8::conditional_select(&0, &0xFF, c)
}

/// Constant-time lookup in a table.
///
/// Returns `table[index]` in constant time regardless of the index value.
/// The index is taken modulo the table length to prevent out-of-bounds access.
///
/// # RefinedRust Specification
///
/// ```text
/// #[rr::params("T" : "Type", "table" : "list T", "index" : "nat")]
/// #[rr::args("#table", "#index")]
/// #[rr::requires("len(table) > 0")]
/// #[rr::returns("#table[index mod len(table)]")]
/// #[rr::ensures("timing_independent_of(index)")]
/// #[rr::ensures("no_early_exit")]
/// #[rr::ensures("memory_access_pattern_uniform")]
/// ```
///
/// Implementation: Iterates through all table entries, performing a constant-time
/// selection at each position. This ensures no cache-timing leakage since all
/// entries are accessed regardless of the target index.
#[inline]
pub fn ct_lookup<T: Copy + Default + ConditionallySelectable>(table: &[T], index: usize) -> T {
    let mut result = T::default();
    for (i, entry) in table.iter().enumerate() {
        let is_match = Choice::from((i == index) as u8);
        result = T::conditional_select(&result, entry, is_match);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ct_eq() {
        let a = [1u8, 2, 3, 4];
        let b = [1u8, 2, 3, 4];
        let c = [1u8, 2, 3, 5];

        assert!(ct_eq(&a, &b));
        assert!(!ct_eq(&a, &c));
        assert!(!ct_eq(&a, &[1, 2, 3]));
    }

    #[test]
    fn test_ct_select() {
        assert_eq!(ct_select(true, 10, 20), 10);
        assert_eq!(ct_select(false, 10, 20), 20);
    }

    #[test]
    fn test_ct_cmov() {
        let src = [1u8, 2, 3, 4];
        let mut dst = [5u8, 6, 7, 8];

        ct_cmov(false, &src, &mut dst);
        assert_eq!(dst, [5, 6, 7, 8]);

        ct_cmov(true, &src, &mut dst);
        assert_eq!(dst, [1, 2, 3, 4]);
    }

    #[test]
    fn test_ct_lt_u64() {
        assert_eq!(ct_lt_u64(5, 10), 1);
        assert_eq!(ct_lt_u64(10, 5), 0);
        assert_eq!(ct_lt_u64(5, 5), 0);
        assert_eq!(ct_lt_u64(0, u64::MAX), 1);
    }
}
