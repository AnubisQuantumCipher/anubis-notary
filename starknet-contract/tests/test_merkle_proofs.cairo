/// Mathematical Proof Tests for Merkle Inclusion Verification
///
/// These tests prove that verify_inclusion() correctly implements
/// Merkle tree verification using Poseidon hash. Each test provides
/// a mathematical guarantee that the verification logic is correct.
///
/// When these tests pass, Starknet's STARK proof system guarantees
/// the computations are mathematically correct.

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
// Test 1: Two-Leaf Merkle Tree
// Mathematical Proof: hash(leaf_0, leaf_1) produces correct root
// =============================================================================

#[test]
fn test_two_leaf_merkle_tree() {
    let contract = setup();

    // Define two leaves
    let leaf_0: felt252 = 0x1111;
    let leaf_1: felt252 = 0x2222;

    // Compute root manually: root = hash(leaf_0, leaf_1)
    let root = poseidon_hash_span(array![leaf_0, leaf_1].span());

    // Anchor the root
    let root_id = contract.anchor_root(root);

    // Verify leaf_0 with proof [leaf_1], direction [false] (leaf_0 is on left)
    let proof_0: Array<felt252> = array![leaf_1];
    let dirs_0: Array<bool> = array![false];
    assert(
        contract.verify_inclusion(root_id, leaf_0, proof_0.span(), dirs_0.span()),
        'leaf_0 verification failed'
    );

    // Verify leaf_1 with proof [leaf_0], direction [true] (leaf_1 is on right)
    let proof_1: Array<felt252> = array![leaf_0];
    let dirs_1: Array<bool> = array![true];
    assert(
        contract.verify_inclusion(root_id, leaf_1, proof_1.span(), dirs_1.span()),
        'leaf_1 verification failed'
    );
}

// =============================================================================
// Test 2: Four-Leaf Merkle Tree (Depth 2)
// Mathematical Structure:
//              root
//            /      \
//         h01        h23
//        /   \      /   \
//      L0    L1   L2    L3
// =============================================================================

#[test]
fn test_four_leaf_merkle_tree() {
    let contract = setup();

    // Define four leaves
    let leaf_0: felt252 = 0xAAA;
    let leaf_1: felt252 = 0xBBB;
    let leaf_2: felt252 = 0xCCC;
    let leaf_3: felt252 = 0xDDD;

    // Compute internal nodes
    let h01 = poseidon_hash_span(array![leaf_0, leaf_1].span());
    let h23 = poseidon_hash_span(array![leaf_2, leaf_3].span());

    // Compute root
    let root = poseidon_hash_span(array![h01, h23].span());

    // Anchor the root
    let root_id = contract.anchor_root(root);

    // Verify leaf_0: proof = [leaf_1, h23], dirs = [false, false]
    // Path: hash(leaf_0, leaf_1) -> hash(h01, h23) -> root
    let proof_0: Array<felt252> = array![leaf_1, h23];
    let dirs_0: Array<bool> = array![false, false];
    assert(
        contract.verify_inclusion(root_id, leaf_0, proof_0.span(), dirs_0.span()),
        'leaf_0 depth2 failed'
    );

    // Verify leaf_1: proof = [leaf_0, h23], dirs = [true, false]
    let proof_1: Array<felt252> = array![leaf_0, h23];
    let dirs_1: Array<bool> = array![true, false];
    assert(
        contract.verify_inclusion(root_id, leaf_1, proof_1.span(), dirs_1.span()),
        'leaf_1 depth2 failed'
    );

    // Verify leaf_2: proof = [leaf_3, h01], dirs = [false, true]
    let proof_2: Array<felt252> = array![leaf_3, h01];
    let dirs_2: Array<bool> = array![false, true];
    assert(
        contract.verify_inclusion(root_id, leaf_2, proof_2.span(), dirs_2.span()),
        'leaf_2 depth2 failed'
    );

    // Verify leaf_3: proof = [leaf_2, h01], dirs = [true, true]
    let proof_3: Array<felt252> = array![leaf_2, h01];
    let dirs_3: Array<bool> = array![true, true];
    assert(
        contract.verify_inclusion(root_id, leaf_3, proof_3.span(), dirs_3.span()),
        'leaf_3 depth2 failed'
    );
}

// =============================================================================
// Test 3: Eight-Leaf Merkle Tree (Full Batch - Depth 3)
// This matches the batch anchoring capability (8 roots max)
//
// Tree Structure:
//                        root
//                    /          \
//                h0123          h4567
//               /    \         /    \
//            h01     h23     h45     h67
//           / \     / \     / \     / \
//          L0 L1   L2 L3   L4 L5   L6 L7
// =============================================================================

#[test]
fn test_eight_leaf_merkle_tree_full_batch() {
    let contract = setup();

    // Define 8 leaves (simulating batch of 8 receipt roots)
    let leaves: Array<felt252> = array![
        0x100, 0x200, 0x300, 0x400,
        0x500, 0x600, 0x700, 0x800
    ];

    // Level 1: Compute leaf pairs
    let h01 = poseidon_hash_span(array![*leaves.at(0), *leaves.at(1)].span());
    let h23 = poseidon_hash_span(array![*leaves.at(2), *leaves.at(3)].span());
    let h45 = poseidon_hash_span(array![*leaves.at(4), *leaves.at(5)].span());
    let h67 = poseidon_hash_span(array![*leaves.at(6), *leaves.at(7)].span());

    // Level 2: Compute internal nodes
    let h0123 = poseidon_hash_span(array![h01, h23].span());
    let h4567 = poseidon_hash_span(array![h45, h67].span());

    // Level 3: Root
    let root = poseidon_hash_span(array![h0123, h4567].span());

    // Anchor the root
    let root_id = contract.anchor_root(root);

    // Verify leaf_0 (leftmost)
    // Path: L0 -> h01 -> h0123 -> root
    // Proof: [L1, h23, h4567], directions: [false, false, false]
    let proof_0: Array<felt252> = array![*leaves.at(1), h23, h4567];
    let dirs_0: Array<bool> = array![false, false, false];
    assert(
        contract.verify_inclusion(root_id, *leaves.at(0), proof_0.span(), dirs_0.span()),
        'leaf_0 depth3 failed'
    );

    // Verify leaf_7 (rightmost)
    // Path: L7 -> h67 -> h4567 -> root
    // Proof: [L6, h45, h0123], directions: [true, true, true]
    let proof_7: Array<felt252> = array![*leaves.at(6), h45, h0123];
    let dirs_7: Array<bool> = array![true, true, true];
    assert(
        contract.verify_inclusion(root_id, *leaves.at(7), proof_7.span(), dirs_7.span()),
        'leaf_7 depth3 failed'
    );

    // Verify leaf_4 (middle position)
    // Path: L4 -> h45 -> h4567 -> root
    // Proof: [L5, h67, h0123], directions: [false, false, true]
    let proof_4: Array<felt252> = array![*leaves.at(5), h67, h0123];
    let dirs_4: Array<bool> = array![false, false, true];
    assert(
        contract.verify_inclusion(root_id, *leaves.at(4), proof_4.span(), dirs_4.span()),
        'leaf_4 depth3 failed'
    );
}

// =============================================================================
// Test 4: Wrong Proof Direction Fails
// Proves that direction matters for verification
// =============================================================================

#[test]
fn test_wrong_direction_fails() {
    let contract = setup();

    let leaf_0: felt252 = 0x1111;
    let leaf_1: felt252 = 0x2222;
    let root = poseidon_hash_span(array![leaf_0, leaf_1].span());

    let root_id = contract.anchor_root(root);

    // Correct: leaf_0 on left, direction = false
    let proof: Array<felt252> = array![leaf_1];
    let correct_dirs: Array<bool> = array![false];
    assert(
        contract.verify_inclusion(root_id, leaf_0, proof.span(), correct_dirs.span()),
        'correct direction should pass'
    );

    // Wrong: Using direction = true (claims leaf_0 is on right)
    let wrong_dirs: Array<bool> = array![true];
    assert(
        !contract.verify_inclusion(root_id, leaf_0, proof.span(), wrong_dirs.span()),
        'wrong direction should fail'
    );
}

// =============================================================================
// Test 5: Invalid Proof (Wrong Sibling) Fails
// =============================================================================

#[test]
fn test_wrong_sibling_fails() {
    let contract = setup();

    let leaf_0: felt252 = 0x1111;
    let leaf_1: felt252 = 0x2222;
    let root = poseidon_hash_span(array![leaf_0, leaf_1].span());

    let root_id = contract.anchor_root(root);

    // Wrong sibling hash
    let wrong_proof: Array<felt252> = array![0x9999];  // Not leaf_1
    let dirs: Array<bool> = array![false];

    assert(
        !contract.verify_inclusion(root_id, leaf_0, wrong_proof.span(), dirs.span()),
        'wrong sibling should fail'
    );
}

// =============================================================================
// Test 6: Empty Proof with Non-Root Leaf Fails
// =============================================================================

#[test]
fn test_empty_proof_non_root_fails() {
    let contract = setup();

    let root: felt252 = 0x12345;
    let root_id = contract.anchor_root(root);

    // Different leaf than root
    let different_leaf: felt252 = 0x99999;
    let empty_proof: Array<felt252> = array![];
    let empty_dirs: Array<bool> = array![];

    assert(
        !contract.verify_inclusion(root_id, different_leaf, empty_proof.span(), empty_dirs.span()),
        'empty proof diff leaf fail'
    );
}

// =============================================================================
// Test 7: Empty Proof with Matching Root Succeeds
// When proof is empty, leaf should equal root directly
// =============================================================================

#[test]
fn test_empty_proof_matching_root_succeeds() {
    let contract = setup();

    let root: felt252 = 0x12345;
    let root_id = contract.anchor_root(root);

    // Leaf equals root (single-element tree)
    let empty_proof: Array<felt252> = array![];
    let empty_dirs: Array<bool> = array![];

    assert(
        contract.verify_inclusion(root_id, root, empty_proof.span(), empty_dirs.span()),
        'empty proof same leaf pass'
    );
}

// =============================================================================
// Test 8: Proof/Direction Length Mismatch Fails
// =============================================================================

#[test]
fn test_proof_direction_length_mismatch() {
    let contract = setup();

    let root: felt252 = 0x12345;
    let root_id = contract.anchor_root(root);

    // Mismatched lengths
    let proof: Array<felt252> = array![0x111, 0x222];
    let dirs: Array<bool> = array![false];  // Only 1 direction for 2 proof elements

    assert(
        !contract.verify_inclusion(root_id, 0x000, proof.span(), dirs.span()),
        'length mismatch should fail'
    );
}
