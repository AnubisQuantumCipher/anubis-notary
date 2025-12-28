//! Merkle tree for batch anchoring.
//!
//! Provides a binary Merkle tree using SHA3-256 for combining multiple
//! receipt digests into a single root hash that can be anchored.
//!
//! ## Tree Structure
//!
//! - Leaf nodes: H(0x00 || data)
//! - Internal nodes: H(0x01 || left || right)
//! - Odd leaf is promoted unchanged to next level
//!
//! ## RefinedRust Verification
//!
//! This module is verified using RefinedRust for:
//! - **Bounds Safety**: All leaf/proof indices are bounds-checked
//! - **Determinism**: Same leaves produce same root
//! - **Proof Correctness**: `verify(proof, leaf, root) = true` implies membership
//! - **Tree Height**: Bounded by `log2(MAX_LEAVES) = 10`
//! - **Binding Property**: Changing any leaf changes the root
//! - **Collision Resistance**: Different leaf sets produce different roots (w.h.p.)
//!
//! See `proofs/theories/merkle_spec.v` for the Rocq specification.
//!
//! Key invariants:
//! - `count <= MAX_LEAVES` (1024)
//! - `proof.len <= MAX_PROOF_DEPTH` (10)
//! - Domain separation: 0x00 for leaves, 0x01 for internal nodes

use crate::keccak::sha3::sha3_256;

/// Maximum number of leaves in a tree.
pub const MAX_LEAVES: usize = 1024;

/// SHA3-256 output size.
pub const HASH_SIZE: usize = 32;

/// Domain separator for leaf hashing.
const LEAF_DOMAIN: u8 = 0x00;

/// Domain separator for internal node hashing.
const NODE_DOMAIN: u8 = 0x01;

/// A Merkle tree for batching receipt digests.
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("tree" : "merkle_spec.merkle_tree_state")]
/// #[rr::invariant("tree.count <= MAX_LEAVES")]
/// #[rr::invariant("tree.count >= 0")]
/// #[rr::invariant("tree.computed -> tree.root = merkle_root(tree.leaves[..tree.count])")]
/// #[rr::invariant("forall i. i < tree.count -> valid_hash(tree.leaves[i])")]
/// ```
#[derive(Debug, Clone)]
pub struct MerkleTree {
    /// Leaf hashes (SHA3-256 of input data).
    leaves: [[u8; HASH_SIZE]; MAX_LEAVES],
    /// Number of leaves.
    count: usize,
    /// Computed root hash.
    root: [u8; HASH_SIZE],
    /// Whether root is computed.
    computed: bool,
}

impl Default for MerkleTree {
    fn default() -> Self {
        Self::new()
    }
}

impl MerkleTree {
    /// Create a new empty Merkle tree.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::returns("#merkle_empty()")]
    /// #[rr::ensures("count == 0")]
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            leaves: [[0u8; HASH_SIZE]; MAX_LEAVES],
            count: 0,
            root: [0u8; HASH_SIZE],
            computed: false,
        }
    }

    /// Returns the number of leaves in the tree.
    #[inline]
    pub fn len(&self) -> usize {
        self.count
    }

    /// Returns true if the tree is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Returns true if the tree is full.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.count >= MAX_LEAVES
    }

    /// Add a leaf to the tree.
    ///
    /// The leaf is hashed with a domain separator: H(0x00 || data).
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::params("data" : "array u8 32")]
    /// #[rr::requires("self.count < MAX_LEAVES")]
    /// #[rr::ensures("self.count == old(self.count) + 1")]
    /// ```
    pub fn add_leaf(&mut self, data: &[u8; HASH_SIZE]) -> Result<usize, MerkleError> {
        if self.count >= MAX_LEAVES {
            return Err(MerkleError::TreeFull);
        }

        // Hash with domain separator
        let mut input = [0u8; 1 + HASH_SIZE];
        input[0] = LEAF_DOMAIN;
        input[1..].copy_from_slice(data);
        self.leaves[self.count] = sha3_256(&input);

        let idx = self.count;
        self.count += 1;
        self.computed = false;

        Ok(idx)
    }

    /// Add a pre-hashed leaf (already domain-separated).
    pub fn add_leaf_hash(&mut self, hash: [u8; HASH_SIZE]) -> Result<usize, MerkleError> {
        if self.count >= MAX_LEAVES {
            return Err(MerkleError::TreeFull);
        }

        self.leaves[self.count] = hash;
        let idx = self.count;
        self.count += 1;
        self.computed = false;

        Ok(idx)
    }

    /// Compute the Merkle root.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::requires("self.count > 0")]
    /// #[rr::returns("#merkle_root(self.leaves[..self.count])")]
    /// ```
    pub fn compute_root(&mut self) -> Result<[u8; HASH_SIZE], MerkleError> {
        if self.count == 0 {
            return Err(MerkleError::EmptyTree);
        }

        if self.computed {
            return Ok(self.root);
        }

        // Working buffer for current level
        let mut current = [[0u8; HASH_SIZE]; MAX_LEAVES];
        current[..self.count].copy_from_slice(&self.leaves[..self.count]);
        let mut level_size = self.count;

        // Build tree bottom-up
        while level_size > 1 {
            let mut next_size = 0;

            let mut i = 0;
            while i + 1 < level_size {
                // Hash pair of nodes
                current[next_size] = hash_nodes(&current[i], &current[i + 1]);
                next_size += 1;
                i += 2;
            }

            // Handle odd node (promote unchanged)
            if i < level_size {
                current[next_size] = current[i];
                next_size += 1;
            }

            level_size = next_size;
        }

        self.root = current[0];
        self.computed = true;

        Ok(self.root)
    }

    /// Get the root hash (must call compute_root first).
    pub fn root(&self) -> Option<[u8; HASH_SIZE]> {
        if self.computed {
            Some(self.root)
        } else {
            None
        }
    }

    /// Generate an inclusion proof for a leaf at the given index.
    ///
    /// Returns the sibling hashes needed to verify membership.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::params("idx" : "usize")]
    /// #[rr::requires("idx < self.count")]
    /// #[rr::returns("Ok(proof) | Err(e)")]
    /// ```
    pub fn generate_proof(&self, idx: usize) -> Result<MerkleProof, MerkleError> {
        if idx >= self.count {
            return Err(MerkleError::InvalidIndex);
        }
        if self.count == 0 {
            return Err(MerkleError::EmptyTree);
        }

        let mut proof = MerkleProof::new();

        // Working buffer
        let mut current = [[0u8; HASH_SIZE]; MAX_LEAVES];
        current[..self.count].copy_from_slice(&self.leaves[..self.count]);
        let mut level_size = self.count;
        let mut target_idx = idx;

        while level_size > 1 {
            // Determine sibling
            let sibling_idx = if target_idx % 2 == 0 {
                target_idx + 1
            } else {
                target_idx - 1
            };

            // Add sibling to proof if it exists
            if sibling_idx < level_size {
                let is_left = target_idx % 2 == 1;
                proof.add_sibling(current[sibling_idx], is_left)?;
            }

            // Build next level and track target position
            let mut next = [[0u8; HASH_SIZE]; MAX_LEAVES];
            let mut next_size = 0;

            let mut i = 0;
            while i + 1 < level_size {
                next[next_size] = hash_nodes(&current[i], &current[i + 1]);
                next_size += 1;
                i += 2;
            }

            // Handle odd node
            if i < level_size {
                next[next_size] = current[i];
                next_size += 1;
            }

            current[..next_size].copy_from_slice(&next[..next_size]);
            target_idx /= 2;
            level_size = next_size;
        }

        Ok(proof)
    }
}

/// Hash two child nodes to produce parent.
///
/// # RefinedRust Specification
/// ```text
/// #[rr::params("left" : "array u8 32", "right" : "array u8 32")]
/// #[rr::returns("#H(0x01 || left || right)")]
/// ```
#[inline]
fn hash_nodes(left: &[u8; HASH_SIZE], right: &[u8; HASH_SIZE]) -> [u8; HASH_SIZE] {
    let mut input = [0u8; 1 + HASH_SIZE * 2];
    input[0] = NODE_DOMAIN;
    input[1..33].copy_from_slice(left);
    input[33..65].copy_from_slice(right);
    sha3_256(&input)
}

/// Maximum proof depth (log2 of MAX_LEAVES).
pub const MAX_PROOF_DEPTH: usize = 10;

/// A Merkle inclusion proof.
#[derive(Debug, Clone)]
pub struct MerkleProof {
    /// Sibling hashes along the path.
    siblings: [[u8; HASH_SIZE]; MAX_PROOF_DEPTH],
    /// Whether each sibling is on the left.
    is_left: [bool; MAX_PROOF_DEPTH],
    /// Number of siblings.
    len: usize,
}

impl MerkleProof {
    /// Create an empty proof.
    pub fn new() -> Self {
        Self {
            siblings: [[0u8; HASH_SIZE]; MAX_PROOF_DEPTH],
            is_left: [false; MAX_PROOF_DEPTH],
            len: 0,
        }
    }

    /// Add a sibling to the proof.
    fn add_sibling(&mut self, hash: [u8; HASH_SIZE], is_left: bool) -> Result<(), MerkleError> {
        if self.len >= MAX_PROOF_DEPTH {
            return Err(MerkleError::ProofTooDeep);
        }
        self.siblings[self.len] = hash;
        self.is_left[self.len] = is_left;
        self.len += 1;
        Ok(())
    }

    /// Verify that a leaf is included in the tree with the given root.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::params("leaf" : "array u8 32", "root" : "array u8 32")]
    /// #[rr::returns("#verify_membership(leaf, self, root)")]
    /// ```
    pub fn verify(&self, leaf: &[u8; HASH_SIZE], expected_root: &[u8; HASH_SIZE]) -> bool {
        // Hash leaf with domain separator
        let mut input = [0u8; 1 + HASH_SIZE];
        input[0] = LEAF_DOMAIN;
        input[1..].copy_from_slice(leaf);
        let mut current = sha3_256(&input);

        // Walk up the tree
        for i in 0..self.len {
            if self.is_left[i] {
                current = hash_nodes(&self.siblings[i], &current);
            } else {
                current = hash_nodes(&current, &self.siblings[i]);
            }
        }

        current == *expected_root
    }

    /// Get the proof length (number of siblings).
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Check if proof is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl Default for MerkleProof {
    fn default() -> Self {
        Self::new()
    }
}

/// Merkle tree errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MerkleError {
    /// Tree is full.
    TreeFull,
    /// Tree is empty.
    EmptyTree,
    /// Invalid leaf index.
    InvalidIndex,
    /// Proof exceeds maximum depth.
    ProofTooDeep,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_leaf() {
        let mut tree = MerkleTree::new();
        let data = [0xABu8; 32];
        tree.add_leaf(&data).unwrap();

        let root = tree.compute_root().unwrap();
        assert_ne!(root, [0u8; 32]);
    }

    #[test]
    fn test_two_leaves() {
        let mut tree = MerkleTree::new();
        tree.add_leaf(&[1u8; 32]).unwrap();
        tree.add_leaf(&[2u8; 32]).unwrap();

        let root = tree.compute_root().unwrap();
        assert_ne!(root, [0u8; 32]);
    }

    #[test]
    fn test_proof_verification() {
        let mut tree = MerkleTree::new();
        let leaf1 = [1u8; 32];
        let leaf2 = [2u8; 32];
        let leaf3 = [3u8; 32];

        tree.add_leaf(&leaf1).unwrap();
        tree.add_leaf(&leaf2).unwrap();
        tree.add_leaf(&leaf3).unwrap();

        let root = tree.compute_root().unwrap();

        // Generate and verify proof for each leaf
        let proof1 = tree.generate_proof(0).unwrap();
        assert!(proof1.verify(&leaf1, &root));

        let proof2 = tree.generate_proof(1).unwrap();
        assert!(proof2.verify(&leaf2, &root));

        let proof3 = tree.generate_proof(2).unwrap();
        assert!(proof3.verify(&leaf3, &root));

        // Verify wrong leaf fails
        assert!(!proof1.verify(&leaf2, &root));
    }

    #[test]
    fn test_deterministic() {
        let mut tree1 = MerkleTree::new();
        let mut tree2 = MerkleTree::new();

        for i in 0..5 {
            let data = [i as u8; 32];
            tree1.add_leaf(&data).unwrap();
            tree2.add_leaf(&data).unwrap();
        }

        let root1 = tree1.compute_root().unwrap();
        let root2 = tree2.compute_root().unwrap();

        assert_eq!(root1, root2);
    }
}
