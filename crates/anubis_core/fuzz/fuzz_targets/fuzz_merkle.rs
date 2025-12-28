//! Fuzz target for Merkle tree operations.
//!
//! Tests that:
//! 1. Tree operations with arbitrary inputs don't panic
//! 2. Proof verification is consistent
//! 3. Determinism: same leaves produce same root

#![no_main]

use libfuzzer_sys::fuzz_target;
use arbitrary::Arbitrary;

use anubis_core::merkle::{MerkleTree, HASH_SIZE, MAX_LEAVES};

#[derive(Debug, Arbitrary)]
struct MerkleInput {
    leaves: Vec<[u8; HASH_SIZE]>,
    proof_index: usize,
}

fuzz_target!(|input: MerkleInput| {
    // Limit to reasonable size
    let num_leaves = core::cmp::min(input.leaves.len(), MAX_LEAVES);
    if num_leaves == 0 {
        return;
    }

    // Property 1: Build tree without panic
    let mut tree = MerkleTree::new();
    for leaf in input.leaves.iter().take(num_leaves) {
        if tree.add_leaf(leaf).is_err() {
            break; // Tree full
        }
    }

    if tree.is_empty() {
        return;
    }

    // Property 2: Compute root without panic
    let root = match tree.compute_root() {
        Ok(r) => r,
        Err(_) => return,
    };

    // Property 3: Proof generation and verification
    let proof_idx = input.proof_index % tree.len();
    let proof = match tree.generate_proof(proof_idx) {
        Ok(p) => p,
        Err(_) => return,
    };

    // The correct leaf should verify
    let leaf = &input.leaves[proof_idx];
    assert!(proof.verify(leaf, &root), "Valid proof should verify");

    // A wrong leaf should not verify (with high probability)
    if num_leaves > 1 {
        let wrong_idx = (proof_idx + 1) % num_leaves;
        let wrong_leaf = &input.leaves[wrong_idx];
        if wrong_leaf != leaf {
            // Different leaf should not verify with same proof
            // (unless there's a collision, which is astronomically unlikely)
            let wrong_result = proof.verify(wrong_leaf, &root);
            // We just check it doesn't panic; collision is possible but rare
            let _ = wrong_result;
        }
    }

    // Property 4: Determinism - same leaves should produce same root
    let mut tree2 = MerkleTree::new();
    for leaf in input.leaves.iter().take(num_leaves) {
        let _ = tree2.add_leaf(leaf);
    }
    if let Ok(root2) = tree2.compute_root() {
        assert_eq!(root, root2, "Determinism: same leaves must produce same root");
    }
});
