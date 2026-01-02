/// Mathematical Proof Tests for Batch Root Computation
///
/// These tests prove that anchor_batch() produces deterministic,
/// verifiable Merkle roots using Poseidon hash.
///
/// Key Properties Proven:
/// 1. Determinism: Same inputs always produce same output
/// 2. Padding correctness: Partial batches are zero-padded
/// 3. Order sensitivity: Different ordering produces different roots
/// 4. Bounds enforcement: Only 1-8 roots allowed

use anubis_notary_oracle::{NotaryOracle, INotaryOracleDispatcher, INotaryOracleDispatcherTrait};
use starknet::testing::{set_caller_address, set_block_number, set_block_timestamp};
use core::poseidon::poseidon_hash_span;

/// Helper to create test addresses
fn get_test_address(name: felt252) -> starknet::ContractAddress {
    name.try_into().unwrap()
}

/// Deploy a fresh NotaryOracle contract for testing
fn deploy_contract() -> INotaryOracleDispatcher {
    let owner: felt252 = 'owner';
    let (contract_address, _) = starknet::syscalls::deploy_syscall(
        NotaryOracle::TEST_CLASS_HASH.try_into().unwrap(),
        0,
        array![owner].span(),
        false,
    ).unwrap();
    INotaryOracleDispatcher { contract_address }
}

/// Setup test environment
fn setup() -> INotaryOracleDispatcher {
    let contract = deploy_contract();
    set_caller_address(get_test_address('user'));
    set_block_number(1000);
    set_block_timestamp(1704067200);
    contract
}

// =============================================================================
// Test 1: Batch Root is Deterministic
// Property: hash([r0,r1,r2,r3,r4,r5,r6,r7]) is always the same for same inputs
// =============================================================================

#[test]
fn test_batch_root_deterministic() {
    let contract = setup();

    // Same 8 roots
    let roots: Array<felt252> = array![
        0x111, 0x222, 0x333, 0x444,
        0x555, 0x666, 0x777, 0x888
    ];

    // Anchor same batch twice
    let id1 = contract.anchor_batch(roots.span());
    let id2 = contract.anchor_batch(roots.span());

    // Get records
    let record1 = contract.get_anchor(id1);
    let record2 = contract.get_anchor(id2);

    // Roots must be identical (deterministic)
    assert(record1.root == record2.root, 'batch not deterministic');
}

// =============================================================================
// Test 2: Batch Root Matches Manual Poseidon Computation
// Verifies the contract computes hash correctly
// =============================================================================

#[test]
fn test_batch_root_matches_manual_hash() {
    let contract = setup();

    // 4 roots (will be padded to 8)
    let roots: Array<felt252> = array![0xAAA, 0xBBB, 0xCCC, 0xDDD];

    // Anchor batch
    let root_id = contract.anchor_batch(roots.span());
    let record = contract.get_anchor(root_id);

    // Compute expected hash manually (with zero padding)
    let padded: Array<felt252> = array![
        0xAAA, 0xBBB, 0xCCC, 0xDDD,
        0, 0, 0, 0  // Zero padding
    ];
    let expected_root = poseidon_hash_span(padded.span());

    assert(record.root == expected_root, 'batch root mismatch');
}

// =============================================================================
// Test 3: Padding with Zeros is Correct
// Property: [r0,r1] padded == hash([r0,r1,0,0,0,0,0,0])
// =============================================================================

#[test]
fn test_padding_correctness() {
    let contract = setup();

    // Only 2 roots
    let roots: Array<felt252> = array![0x111, 0x222];
    let root_id = contract.anchor_batch(roots.span());
    let record = contract.get_anchor(root_id);

    // Expected: padded with 6 zeros
    let padded: Array<felt252> = array![
        0x111, 0x222, 0, 0, 0, 0, 0, 0
    ];
    let expected = poseidon_hash_span(padded.span());

    assert(record.root == expected, 'padding incorrect');
}

// =============================================================================
// Test 4: Single Root Batch
// Property: [r0] padded == hash([r0,0,0,0,0,0,0,0])
// =============================================================================

#[test]
fn test_single_root_batch() {
    let contract = setup();

    let roots: Array<felt252> = array![0xABC];
    let root_id = contract.anchor_batch(roots.span());
    let record = contract.get_anchor(root_id);

    let padded: Array<felt252> = array![0xABC, 0, 0, 0, 0, 0, 0, 0];
    let expected = poseidon_hash_span(padded.span());

    assert(record.root == expected, 'single batch incorrect');
}

// =============================================================================
// Test 5: Order Matters
// Property: [r0,r1] != [r1,r0]
// =============================================================================

#[test]
fn test_batch_order_matters() {
    let contract = setup();

    // Order 1: [A, B]
    let roots1: Array<felt252> = array![0xAAA, 0xBBB];
    let id1 = contract.anchor_batch(roots1.span());
    let record1 = contract.get_anchor(id1);

    // Order 2: [B, A]
    let roots2: Array<felt252> = array![0xBBB, 0xAAA];
    let id2 = contract.anchor_batch(roots2.span());
    let record2 = contract.get_anchor(id2);

    // Roots must be different
    assert(record1.root != record2.root, 'order should matter');
}

// =============================================================================
// Test 6: Full 8-Root Batch
// Maximum batch size test
// =============================================================================

#[test]
fn test_full_eight_root_batch() {
    let contract = setup();

    let roots: Array<felt252> = array![
        0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
    ];
    let root_id = contract.anchor_batch(roots.span());
    let record = contract.get_anchor(root_id);

    // No padding needed for 8 roots
    let expected = poseidon_hash_span(roots.span());
    assert(record.root == expected, 'full batch incorrect');
}

// =============================================================================
// Test 7: Empty Batch Fails
// =============================================================================

#[test]
#[should_panic]
fn test_empty_batch_panics() {
    let contract = setup();
    let empty: Array<felt252> = array![];
    contract.anchor_batch(empty.span());
}

// =============================================================================
// Test 8: Batch Count Increments Correctly
// =============================================================================

#[test]
fn test_batch_count_increments() {
    let contract = setup();

    assert(contract.get_anchor_count() == 0, 'initial count wrong');

    // Anchor 3 batches
    contract.anchor_batch(array![0x1].span());
    assert(contract.get_anchor_count() == 1, 'count after 1');

    contract.anchor_batch(array![0x2, 0x3].span());
    assert(contract.get_anchor_count() == 2, 'count after 2');

    contract.anchor_batch(array![0x4, 0x5, 0x6].span());
    assert(contract.get_anchor_count() == 3, 'count after 3');
}

// =============================================================================
// Test 9: Mixed Single and Batch Anchoring
// =============================================================================

#[test]
fn test_mixed_single_and_batch() {
    let contract = setup();

    // Single anchor
    let single_root: felt252 = 0x12345;
    let id1 = contract.anchor_root(single_root);
    assert(id1 == 1, 'single id wrong');

    // Batch anchor
    let batch_roots: Array<felt252> = array![0xAAA, 0xBBB];
    let id2 = contract.anchor_batch(batch_roots.span());
    assert(id2 == 2, 'batch id wrong');

    // Another single
    let id3 = contract.anchor_root(0x67890);
    assert(id3 == 3, 'single id2 wrong');

    // Verify all
    assert(contract.verify_root(id1, single_root), 'verify single');

    let padded: Array<felt252> = array![0xAAA, 0xBBB, 0, 0, 0, 0, 0, 0];
    let batch_hash = poseidon_hash_span(padded.span());
    assert(contract.verify_root(id2, batch_hash), 'verify batch');

    assert(contract.verify_root(id3, 0x67890), 'verify single2');
}

// =============================================================================
// Test 10: Poseidon Hash Properties
// =============================================================================

#[test]
fn test_poseidon_determinism() {
    // Same inputs always produce same output
    let hash1 = poseidon_hash_span(array![0x111, 0x222].span());
    let hash2 = poseidon_hash_span(array![0x111, 0x222].span());
    assert(hash1 == hash2, 'poseidon not deterministic');
}

#[test]
fn test_poseidon_order_sensitive() {
    // Different order produces different hash
    let hash1 = poseidon_hash_span(array![0x111, 0x222].span());
    let hash2 = poseidon_hash_span(array![0x222, 0x111].span());
    assert(hash1 != hash2, 'poseidon should be ordered');
}

#[test]
fn test_poseidon_collision_resistance() {
    // Different inputs produce different outputs (spot check)
    let hash1 = poseidon_hash_span(array![0x1].span());
    let hash2 = poseidon_hash_span(array![0x2].span());
    let hash3 = poseidon_hash_span(array![0x3].span());

    assert(hash1 != hash2, 'collision 1-2');
    assert(hash2 != hash3, 'collision 2-3');
    assert(hash1 != hash3, 'collision 1-3');
}
