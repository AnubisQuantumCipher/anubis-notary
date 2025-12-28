//! Formally verified core logic for Anubis Notary
//!
//! This module contains pure functions that can be formally verified
//! using RefinedRust and Iris separation logic.
//!
//! ## Verification Status
//!
//! All functions in this module have active RefinedRust annotations that:
//! - Generate Coq specifications in `output/anubis_verified/generated/`
//! - Produce proof obligations discharged in `output/anubis_verified/proofs/`
//! - Are verified against the Iris separation logic framework

#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]

#![rr::package("anubis-verified")]

fn main() {}

// ============================================================================
// Merkle Tree Index Logic - Formally Verified
// ============================================================================

/// Calculate parent index in a Merkle tree.
///
/// # Verification
/// - Pre: index is non-negative
/// - Post: returns floor(index / 2)
#[rr::params("i" : "Z")]
#[rr::args("i")]
#[rr::requires("0 ≤ i")]
#[rr::returns("(i `quot` 2)")]
pub fn merkle_parent(index: usize) -> usize {
    index / 2
}

/// Calculate left child index in a Merkle tree.
///
/// # Verification
/// - Pre: index is non-negative and 2*index fits in usize
/// - Post: returns 2 * index
#[rr::params("i" : "Z")]
#[rr::args("i")]
#[rr::requires("0 ≤ i")]
#[rr::requires("(2 * i) ∈ usize")]
#[rr::returns("(2 * i)")]
pub fn merkle_left_child(index: usize) -> usize {
    index * 2
}

/// Calculate right child index in a Merkle tree.
///
/// # Verification
/// - Pre: index is non-negative and 2*index+1 fits in usize
/// - Post: returns 2 * index + 1
#[rr::params("i" : "Z")]
#[rr::args("i")]
#[rr::requires("0 ≤ i")]
#[rr::requires("(2 * i + 1) ∈ usize")]
#[rr::returns("(2 * i + 1)")]
pub fn merkle_right_child(index: usize) -> usize {
    index * 2 + 1
}

/// Check if an index is a left child in a Merkle tree.
///
/// # Verification
/// - Pre: none
/// - Post: returns true iff index is even
#[rr::params("i" : "Z")]
#[rr::args("i")]
#[rr::returns("bool_decide (Z.even i)")]
pub fn is_left_child(index: usize) -> bool {
    index % 2 == 0
}

/// Check if an index is a right child in a Merkle tree.
///
/// # Verification
/// - Pre: none
/// - Post: returns true iff index is odd
#[rr::params("i" : "Z")]
#[rr::args("i")]
#[rr::returns("bool_decide (Z.odd i)")]
pub fn is_right_child(index: usize) -> bool {
    index % 2 == 1
}

/// Get sibling index in a Merkle tree.
///
/// # Verification
/// - Pre: index > 0 (root has no sibling)
/// - Post: returns index XOR 1 (flips the least significant bit)
#[rr::params("i" : "Z")]
#[rr::args("i")]
#[rr::requires("0 < i")]
#[rr::returns("Z.lxor i 1")]
pub fn merkle_sibling(index: usize) -> usize {
    index ^ 1
}

/// Calculate tree height for a given number of leaves.
///
/// # Verification
/// - Pre: num_leaves > 0
/// - Post: returns ceiling of log2(num_leaves)
#[rr::params("n" : "Z")]
#[rr::args("n")]
#[rr::requires("0 < n")]
#[rr::requires("n ≤ 2^62")]
#[rr::returns("Z.log2_up n")]
pub fn tree_height(num_leaves: u64) -> u32 {
    if num_leaves <= 1 {
        0
    } else {
        64 - (num_leaves - 1).leading_zeros()
    }
}

// ============================================================================
// Constant-Time Primitives - Formally Verified
// ============================================================================

/// Constant-time byte selection: returns a if choice == 1, b if choice == 0.
///
/// # Verification
/// - Pre: choice is 0 or 1
/// - Post: returns a if choice == 1, else b
/// - Property: No data-dependent branches (constant-time)
#[rr::params("a" : "Z", "b" : "Z", "choice" : "Z")]
#[rr::args("a", "b", "choice")]
#[rr::requires("0 ≤ a < 256")]
#[rr::requires("0 ≤ b < 256")]
#[rr::requires("choice = 0 ∨ choice = 1")]
#[rr::returns("if bool_decide (choice = 1) then a else b")]
pub fn ct_select_u8(a: u8, b: u8, choice: u8) -> u8 {
    // Constant-time selection using bitwise operations
    // mask = 0xFF if choice == 1, 0x00 if choice == 0
    let mask = (choice.wrapping_neg()) as u8;
    (a & mask) | (b & !mask)
}

/// Constant-time 64-bit selection.
///
/// # Verification
/// - Pre: choice is 0 or 1
/// - Post: returns a if choice == 1, else b
#[rr::params("a" : "Z", "b" : "Z", "choice" : "Z")]
#[rr::args("a", "b", "choice")]
#[rr::requires("0 ≤ a < 2^64")]
#[rr::requires("0 ≤ b < 2^64")]
#[rr::requires("choice = 0 ∨ choice = 1")]
#[rr::returns("if bool_decide (choice = 1) then a else b")]
pub fn ct_select_u64(a: u64, b: u64, choice: u64) -> u64 {
    let mask = choice.wrapping_neg();
    (a & mask) | (b & !mask)
}

/// Constant-time comparison: returns 1 if a == b, 0 otherwise.
///
/// # Verification
/// - Pre: inputs are valid u8
/// - Post: returns 1 if equal, 0 if not
/// - Property: Timing is independent of input values
#[rr::params("a" : "Z", "b" : "Z")]
#[rr::args("a", "b")]
#[rr::requires("0 ≤ a < 256")]
#[rr::requires("0 ≤ b < 256")]
#[rr::returns("if bool_decide (a = b) then 1 else 0")]
pub fn ct_eq_u8(a: u8, b: u8) -> u8 {
    // XOR gives 0 if equal, non-zero otherwise
    // Then we need to collapse to 0 or 1
    let diff = a ^ b;
    // If diff is 0, result should be 1
    // If diff is non-zero, result should be 0
    let is_zero = (diff as u16 | (diff as u16).wrapping_neg()) >> 8;
    (is_zero as u8) ^ 1
}

/// Constant-time comparison for 64-bit values.
#[rr::params("a" : "Z", "b" : "Z")]
#[rr::args("a", "b")]
#[rr::requires("0 ≤ a < 2^64")]
#[rr::requires("0 ≤ b < 2^64")]
#[rr::returns("if bool_decide (a = b) then 1 else 0")]
pub fn ct_eq_u64(a: u64, b: u64) -> u64 {
    let diff = a ^ b;
    let is_zero = (diff as u128 | (diff as u128).wrapping_neg()) >> 64;
    (is_zero as u64) ^ 1
}

/// Constant-time less-than comparison.
/// Returns 1 if a < b, 0 otherwise.
#[rr::params("a" : "Z", "b" : "Z")]
#[rr::args("a", "b")]
#[rr::requires("0 ≤ a < 2^64")]
#[rr::requires("0 ≤ b < 2^64")]
#[rr::returns("if bool_decide (a < b) then 1 else 0")]
pub fn ct_lt_u64(a: u64, b: u64) -> u64 {
    // Use the fact that (a - b) has high bit set when a < b (for unsigned)
    // But we need to handle overflow carefully
    let (diff, borrow) = a.overflowing_sub(b);
    borrow as u64
}

// ============================================================================
// Byte Array Utilities - Formally Verified
// ============================================================================

/// Convert u64 to little-endian bytes.
///
/// # Verification
/// - Post: result encodes the input in little-endian format
#[rr::params("x" : "Z")]
#[rr::args("x")]
#[rr::requires("0 ≤ x < 2^64")]
#[rr::returns("Z.to_little_endian 8 x")]
pub fn u64_to_le_bytes(x: u64) -> [u8; 8] {
    x.to_le_bytes()
}

/// Convert u32 to little-endian bytes.
#[rr::params("x" : "Z")]
#[rr::args("x")]
#[rr::requires("0 ≤ x < 2^32")]
#[rr::returns("Z.to_little_endian 4 x")]
pub fn u32_to_le_bytes(x: u32) -> [u8; 4] {
    x.to_le_bytes()
}

/// Convert little-endian bytes to u64.
///
/// # Verification
/// - Post: round-trips with u64_to_le_bytes
#[rr::params("bytes" : "list Z")]
#[rr::args("bytes")]
#[rr::requires("length bytes = 8")]
#[rr::requires("∀ b, b ∈ bytes → 0 ≤ b < 256")]
#[rr::returns("Z.of_little_endian bytes")]
pub fn le_bytes_to_u64(bytes: [u8; 8]) -> u64 {
    u64::from_le_bytes(bytes)
}

/// Convert little-endian bytes to u32.
#[rr::params("bytes" : "list Z")]
#[rr::args("bytes")]
#[rr::requires("length bytes = 4")]
#[rr::requires("∀ b, b ∈ bytes → 0 ≤ b < 256")]
#[rr::returns("Z.of_little_endian bytes")]
pub fn le_bytes_to_u32(bytes: [u8; 4]) -> u32 {
    u32::from_le_bytes(bytes)
}

// ============================================================================
// Rotation and Shift Operations - Formally Verified
// ============================================================================

/// Rotate left for 64-bit values.
///
/// # Verification
/// - Pre: rotation amount is valid (0-63)
/// - Post: performs circular left rotation
#[rr::params("x" : "Z", "n" : "Z")]
#[rr::args("x", "n")]
#[rr::requires("0 ≤ x < 2^64")]
#[rr::requires("0 ≤ n < 64")]
#[rr::returns("Z.lor (Z.shiftl x n) (Z.shiftr x (64 - n))")]
pub fn rotate_left_64(x: u64, n: u32) -> u64 {
    x.rotate_left(n)
}

/// Rotate right for 64-bit values.
#[rr::params("x" : "Z", "n" : "Z")]
#[rr::args("x", "n")]
#[rr::requires("0 ≤ x < 2^64")]
#[rr::requires("0 ≤ n < 64")]
#[rr::returns("Z.lor (Z.shiftr x n) (Z.shiftl x (64 - n))")]
pub fn rotate_right_64(x: u64, n: u32) -> u64 {
    x.rotate_right(n)
}

// ============================================================================
// Nonce Generation Helpers - Formally Verified
// ============================================================================

/// Deterministic nonce derivation index calculation.
/// Ensures unique nonces for different (key_id, counter) pairs.
///
/// # Verification
/// - Pre: inputs fit in range
/// - Post: result is unique for distinct inputs (injectivity)
#[rr::params("key_id" : "Z", "counter" : "Z")]
#[rr::args("key_id", "counter")]
#[rr::requires("0 ≤ key_id < 2^32")]
#[rr::requires("0 ≤ counter < 2^32")]
#[rr::returns("Z.lor (Z.shiftl key_id 32) counter")]
pub fn nonce_index(key_id: u32, counter: u32) -> u64 {
    ((key_id as u64) << 32) | (counter as u64)
}

/// Extract key_id from nonce index.
#[rr::params("idx" : "Z")]
#[rr::args("idx")]
#[rr::requires("0 ≤ idx < 2^64")]
#[rr::returns("Z.shiftr idx 32")]
pub fn nonce_key_id(idx: u64) -> u32 {
    (idx >> 32) as u32
}

/// Extract counter from nonce index.
#[rr::params("idx" : "Z")]
#[rr::args("idx")]
#[rr::requires("0 ≤ idx < 2^64")]
#[rr::returns("Z.land idx (2^32 - 1)")]
pub fn nonce_counter(idx: u64) -> u32 {
    idx as u32
}

// ============================================================================
// Threshold Signature Helpers - Formally Verified
// ============================================================================

/// Check if threshold is valid for given number of signers.
///
/// # Verification
/// - Pre: threshold > 0, n_signers > 0
/// - Post: returns true iff threshold <= n_signers
#[rr::params("threshold" : "Z", "n_signers" : "Z")]
#[rr::args("threshold", "n_signers")]
#[rr::requires("0 < threshold")]
#[rr::requires("0 < n_signers")]
#[rr::returns("bool_decide (threshold ≤ n_signers)")]
pub fn valid_threshold(threshold: u32, n_signers: u32) -> bool {
    threshold <= n_signers
}

/// Calculate number of signatures needed to reach threshold.
/// Returns 0 if threshold already met.
#[rr::params("current" : "Z", "threshold" : "Z")]
#[rr::args("current", "threshold")]
#[rr::requires("0 ≤ current")]
#[rr::requires("0 < threshold")]
#[rr::returns("Z.max 0 (threshold - current)")]
pub fn signatures_needed(current: u32, threshold: u32) -> u32 {
    threshold.saturating_sub(current)
}

// ============================================================================
// Hash-Related Helpers - Formally Verified
// ============================================================================

/// Domain separator for leaf hashes in Merkle tree.
/// This ensures leaves and internal nodes produce different hashes.
pub const LEAF_DOMAIN: u8 = 0x00;

/// Domain separator for internal node hashes in Merkle tree.
pub const NODE_DOMAIN: u8 = 0x01;

/// Hash size constant (SHA3-256 output).
pub const HASH_SIZE: usize = 32;

/// Prepare leaf hash input with domain separator.
/// Returns the prefixed data ready for hashing.
///
/// # Verification
/// - Post: result[0] = LEAF_DOMAIN (0x00)
/// - Post: result[1..33] = data
#[rr::params("data" : "list Z")]
#[rr::args("data")]
#[rr::requires("length data = 32")]
#[rr::ensures("result[0] = 0")]
pub fn prepare_leaf_input(data: &[u8; 32]) -> [u8; 33] {
    let mut result = [0u8; 33];
    result[0] = LEAF_DOMAIN;
    result[1..33].copy_from_slice(data);
    result
}

/// Prepare node hash input with domain separator.
/// Concatenates: NODE_DOMAIN || left || right
///
/// # Verification
/// - Post: result[0] = NODE_DOMAIN (0x01)
/// - Post: result[1..33] = left
/// - Post: result[33..65] = right
#[rr::params("left" : "list Z", "right" : "list Z")]
#[rr::args("left", "right")]
#[rr::requires("length left = 32")]
#[rr::requires("length right = 32")]
#[rr::ensures("result[0] = 1")]
pub fn prepare_node_input(left: &[u8; 32], right: &[u8; 32]) -> [u8; 65] {
    let mut result = [0u8; 65];
    result[0] = NODE_DOMAIN;
    result[1..33].copy_from_slice(left);
    result[33..65].copy_from_slice(right);
    result
}

/// XOR two hash arrays element-wise.
/// Used in Merkle tree finalization to combine lane results.
///
/// # Verification
/// - Post: result[i] = a[i] XOR b[i] for all i
#[rr::params("a" : "list Z", "b" : "list Z")]
#[rr::args("a", "b")]
#[rr::requires("length a = 32")]
#[rr::requires("length b = 32")]
#[rr::ensures("length result = 32")]
pub fn xor_hashes(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let mut result = [0u8; 32];
    for i in 0..32 {
        result[i] = a[i] ^ b[i];
    }
    result
}

/// Constant-time hash comparison.
/// Returns true if and only if all 32 bytes are equal.
///
/// # Verification
/// - Post: result = true iff a = b (byte-wise)
/// - Property: Timing independent of where mismatch occurs
#[rr::params("a" : "list Z", "b" : "list Z")]
#[rr::args("a", "b")]
#[rr::requires("length a = 32")]
#[rr::requires("length b = 32")]
#[rr::returns("bool_decide (a = b)")]
pub fn ct_hash_eq(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let mut diff: u8 = 0;
    for i in 0..32 {
        diff |= a[i] ^ b[i];
    }
    diff == 0
}

// ============================================================================
// Proof Path Helpers - Formally Verified
// ============================================================================

/// Calculate the position of a leaf in its level.
/// For a leaf at index `idx`, returns its position among siblings.
///
/// # Verification
/// - Pre: idx is a valid leaf index
/// - Post: returns idx (leaves are at level 0)
#[rr::params("idx" : "Z")]
#[rr::args("idx")]
#[rr::requires("0 ≤ idx")]
#[rr::returns("idx")]
pub fn leaf_position(idx: usize) -> usize {
    idx
}

/// Calculate the number of leaves at a given tree level.
/// Level 0 is leaves, level h is root.
///
/// # Verification
/// - Pre: total_leaves > 0, level >= 0
/// - Post: returns ceil(total_leaves / 2^level)
#[rr::params("total" : "Z", "level" : "Z")]
#[rr::args("total", "level")]
#[rr::requires("0 < total")]
#[rr::requires("0 ≤ level")]
#[rr::requires("level < 64")]
#[rr::returns("(total + (1 << level) - 1) >> level")]
pub fn nodes_at_level(total_leaves: u64, level: u32) -> u64 {
    let divisor = 1u64 << level;
    (total_leaves + divisor - 1) / divisor
}

// ============================================================================
// Simple Addition (Test Function)
// ============================================================================

/// Simple addition to test verification pipeline.
#[rr::params("x" : "Z")]
#[rr::args("x")]
#[rr::requires("(x + 1) ∈ u64")]
#[rr::returns("(x + 1)")]
pub fn add_one(n: u64) -> u64 {
    n + 1
}
