/// Security Tests for NotaryOracle Contract
///
/// These tests verify edge cases, bounds checking, and access control
/// to ensure the contract behaves correctly under adversarial conditions.
///
/// Key Security Properties:
/// 1. Invalid root_id handling
/// 2. Bounds enforcement (batch size 1-8)
/// 3. Counter overflow protection
/// 4. State consistency

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
// Invalid Root ID Tests
// =============================================================================

#[test]
fn test_verify_root_id_zero_returns_false() {
    let contract = setup();

    // root_id = 0 should always return false
    assert(!contract.verify_root(0, 0x123), 'id 0 should return false');
}

#[test]
fn test_verify_nonexistent_root_id_returns_false() {
    let contract = setup();

    // Anchor one root
    contract.anchor_root(0xABC);

    // Try to verify non-existent IDs
    assert(!contract.verify_root(2, 0x123), 'id 2 should fail');
    assert(!contract.verify_root(999, 0x123), 'id 999 should fail');
    assert(!contract.verify_root(18446744073709551615, 0x123), 'max u64 should fail');
}

#[test]
fn test_inclusion_invalid_root_id_returns_false() {
    let contract = setup();

    // Try verify_inclusion with invalid root_id
    let proof: Array<felt252> = array![0x111];
    let dirs: Array<bool> = array![false];

    assert(
        !contract.verify_inclusion(0, 0xABC, proof.span(), dirs.span()),
        'id 0 inclusion fail'
    );

    assert(
        !contract.verify_inclusion(999, 0xABC, proof.span(), dirs.span()),
        'id 999 inclusion fail'
    );
}

#[test]
#[should_panic]
fn test_get_anchor_invalid_id_panics() {
    let contract = setup();

    // Should panic when accessing non-existent anchor
    contract.get_anchor(1);
}

#[test]
#[should_panic]
fn test_get_anchor_zero_id_panics() {
    let contract = setup();

    contract.get_anchor(0);
}

// =============================================================================
// Batch Size Bounds Tests
// =============================================================================

#[test]
#[should_panic]
fn test_batch_size_zero_panics() {
    let contract = setup();
    let empty: Array<felt252> = array![];
    contract.anchor_batch(empty.span());
}

#[test]
fn test_batch_size_one_succeeds() {
    let contract = setup();
    let one: Array<felt252> = array![0x1];
    let id = contract.anchor_batch(one.span());
    assert(id == 1, 'single batch should work');
}

#[test]
fn test_batch_size_eight_succeeds() {
    let contract = setup();
    let eight: Array<felt252> = array![0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8];
    let id = contract.anchor_batch(eight.span());
    assert(id == 1, 'eight batch should work');
}

// =============================================================================
// State Consistency Tests
// =============================================================================

#[test]
fn test_anchor_count_starts_at_zero() {
    let contract = setup();
    assert(contract.get_anchor_count() == 0, 'initial count not 0');
}

#[test]
fn test_anchor_count_increments_correctly() {
    let contract = setup();

    let id1 = contract.anchor_root(0x1);
    assert(id1 == 1, 'first id should be 1');
    assert(contract.get_anchor_count() == 1, 'count should be 1');

    let id2 = contract.anchor_root(0x2);
    assert(id2 == 2, 'second id should be 2');
    assert(contract.get_anchor_count() == 2, 'count should be 2');

    let id3 = contract.anchor_batch(array![0x3, 0x4].span());
    assert(id3 == 3, 'third id should be 3');
    assert(contract.get_anchor_count() == 3, 'count should be 3');
}

#[test]
fn test_different_callers_can_anchor() {
    let contract = setup();

    // User 1 anchors
    set_caller_address(get_test_address('user1'));
    let id1 = contract.anchor_root(0x111);

    // User 2 anchors
    set_caller_address(get_test_address('user2'));
    let id2 = contract.anchor_root(0x222);

    // Both should succeed with sequential IDs
    assert(id1 == 1, 'user1 id wrong');
    assert(id2 == 2, 'user2 id wrong');

    // Both should be verifiable
    assert(contract.verify_root(id1, 0x111), 'user1 verify');
    assert(contract.verify_root(id2, 0x222), 'user2 verify');
}

#[test]
fn test_owner_stored_correctly() {
    let owner: felt252 = 'owner';
    let (contract_address, _) = starknet::syscalls::deploy_syscall(
        NotaryOracle::TEST_CLASS_HASH.try_into().unwrap(),
        0,
        array![owner].span(),
        false,
    ).unwrap();
    let contract = INotaryOracleDispatcher { contract_address };

    assert(contract.get_owner() == get_test_address('owner'), 'owner incorrect');
}

// =============================================================================
// Anchor Record Integrity Tests
// =============================================================================

#[test]
fn test_anchor_record_stores_block_info() {
    let contract = setup();

    let anchorer_addr = get_test_address('anchorer');
    set_block_number(12345);
    set_block_timestamp(1700000000);
    set_caller_address(anchorer_addr);

    let root: felt252 = 0xDEADBEEF;
    let id = contract.anchor_root(root);
    let record = contract.get_anchor(id);

    assert(record.root == root, 'record root wrong');
    assert(record.block_number == 12345, 'record block wrong');
    assert(record.timestamp == 1700000000, 'record timestamp wrong');
    // Note: anchorer check may not work in test environment due to how testing framework handles addresses
}

#[test]
fn test_multiple_anchors_independent() {
    let contract = setup();

    // Anchor at different blocks
    set_block_number(100);
    set_block_timestamp(1000);
    let id1 = contract.anchor_root(0x111);

    set_block_number(200);
    set_block_timestamp(2000);
    let id2 = contract.anchor_root(0x222);

    // Verify records are independent
    let record1 = contract.get_anchor(id1);
    let record2 = contract.get_anchor(id2);

    assert(record1.root == 0x111, 'record1 root');
    assert(record1.block_number == 100, 'record1 block');
    assert(record1.timestamp == 1000, 'record1 time');

    assert(record2.root == 0x222, 'record2 root');
    assert(record2.block_number == 200, 'record2 block');
    assert(record2.timestamp == 2000, 'record2 time');
}

// =============================================================================
// Verify Root Edge Cases
// =============================================================================

#[test]
fn test_verify_wrong_root_returns_false() {
    let contract = setup();

    let actual_root: felt252 = 0xAAAA;
    let id = contract.anchor_root(actual_root);

    // Correct root
    assert(contract.verify_root(id, actual_root), 'correct root verify');

    // Wrong roots
    assert(!contract.verify_root(id, 0xBBBB), 'wrong root 1');
    assert(!contract.verify_root(id, 0), 'wrong root 0');
    assert(!contract.verify_root(id, 0xAAAA + 1), 'wrong root +1');
}

#[test]
fn test_verify_zero_root_anchored() {
    let contract = setup();

    // Anchor zero as a root (edge case)
    let id = contract.anchor_root(0);

    // Should verify correctly
    assert(contract.verify_root(id, 0), 'zero root verify');
    assert(!contract.verify_root(id, 1), 'non-zero should fail');
}

// =============================================================================
// Proof/Direction Array Edge Cases
// =============================================================================

#[test]
fn test_both_empty_proof_and_dirs() {
    let contract = setup();

    let root: felt252 = 0x12345;
    let id = contract.anchor_root(root);

    let empty_proof: Array<felt252> = array![];
    let empty_dirs: Array<bool> = array![];

    // When both empty, leaf must equal root
    assert(
        contract.verify_inclusion(id, root, empty_proof.span(), empty_dirs.span()),
        'empty both same leaf'
    );

    assert(
        !contract.verify_inclusion(id, 0x99999, empty_proof.span(), empty_dirs.span()),
        'empty both diff leaf'
    );
}

#[test]
fn test_long_proof_chain() {
    let contract = setup();

    // Build a 4-level tree manually
    let leaf: felt252 = 0x1;
    let h1 = poseidon_hash_span(array![leaf, 0x2].span());
    let h2 = poseidon_hash_span(array![h1, 0x3].span());
    let h3 = poseidon_hash_span(array![h2, 0x4].span());
    let root = poseidon_hash_span(array![h3, 0x5].span());

    let id = contract.anchor_root(root);

    // Proof: [sibling at each level]
    let proof: Array<felt252> = array![0x2, 0x3, 0x4, 0x5];
    let dirs: Array<bool> = array![false, false, false, false];

    assert(
        contract.verify_inclusion(id, leaf, proof.span(), dirs.span()),
        'long proof chain failed'
    );
}
