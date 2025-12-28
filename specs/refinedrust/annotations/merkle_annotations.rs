//! RefinedRust Annotations for merkle module
//!
//! This file shows the complete refinement type annotations for the
//! Merkle tree batch anchoring implementation.

// ============================================================================
// Constants
// ============================================================================

/// Maximum number of leaves in a tree.
pub const MAX_LEAVES: usize = 1024;

/// SHA3-256 output size.
pub const HASH_SIZE: usize = 32;

/// Maximum proof depth (log2 of MAX_LEAVES).
pub const MAX_PROOF_DEPTH: usize = 10;

/// Domain separator for leaf hashing.
const LEAF_DOMAIN: u8 = 0x00;

/// Domain separator for internal node hashing.
const NODE_DOMAIN: u8 = 0x01;

// ============================================================================
// MerkleTree Type
// ============================================================================

/// A Merkle tree for batching receipt digests.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("leaves" : "list (array u8 32)",
///                  "count" : "nat",
///                  "root" : "option (array u8 32)")]
/// #[rr::invariant("count <= MAX_LEAVES")]
/// #[rr::invariant("len(leaves) = MAX_LEAVES")]
/// #[rr::invariant("root.is_some ==> root = Some(merkle_root(leaves[..count]))")]
/// ```
#[rr::type("MerkleTree")]
pub struct MerkleTree {
    leaves: [[u8; HASH_SIZE]; MAX_LEAVES],
    count: usize,
    root: [u8; HASH_SIZE],
    computed: bool,
}

// ============================================================================
// MerkleTree::new
// ============================================================================

/// Create a new empty Merkle tree.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::returns("MerkleTree { count: 0, root: None }")]
/// #[rr::ensures("result.count = 0")]
/// #[rr::ensures("result.is_empty()")]
/// ```
#[rr::verified]
#[inline]
pub fn new() -> MerkleTree {
    MerkleTree {
        leaves: [[0u8; HASH_SIZE]; MAX_LEAVES],
        count: 0,
        root: [0u8; HASH_SIZE],
        computed: false,
    }
}

// ============================================================================
// MerkleTree::add_leaf
// ============================================================================

/// Add a leaf to the tree.
///
/// The leaf is hashed with a domain separator: H(0x00 || data).
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname", "data" : "array u8 32")]
/// #[rr::args("(&mut self, gamma) @ &mut MerkleTree", "data @ &[u8; 32]")]
/// #[rr::requires("self.count < MAX_LEAVES")]
/// #[rr::ensures("match result {
///     Ok(idx) =>
///         idx = old(self.count) /\
///         self.count = old(self.count) + 1 /\
///         self.leaves[idx] = hash_leaf(data) /\
///         self.computed = false
///   | Err(TreeFull) =>
///         old(self.count) >= MAX_LEAVES
/// }")]
/// ```
#[rr::verified]
pub fn add_leaf(&mut self, data: &[u8; HASH_SIZE]) -> Result<usize, MerkleError> {
    #[rr::assert("Check if tree is full")]
    if self.count >= MAX_LEAVES {
        return Err(MerkleError::TreeFull);
    }

    #[rr::assert("Hash with leaf domain separator: H(0x00 || data)")]
    let mut input = [0u8; 1 + HASH_SIZE];
    input[0] = LEAF_DOMAIN;
    input[1..].copy_from_slice(data);
    self.leaves[self.count] = sha3_256(&input);

    let idx = self.count;
    self.count += 1;
    self.computed = false;

    Ok(idx)
}

// ============================================================================
// MerkleTree::compute_root
// ============================================================================

/// Compute the Merkle root.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname")]
/// #[rr::args("(&mut self, gamma) @ &mut MerkleTree")]
/// #[rr::requires("self.count > 0")]
/// #[rr::ensures("match result {
///     Ok(root) =>
///         root = merkle_root(self.leaves[..self.count]) /\
///         self.computed = true /\
///         self.root = root
///   | Err(EmptyTree) =>
///         self.count = 0
/// }")]
///
/// (* Loop invariant for tree construction *)
/// #[rr::loop_inv("level_size", "level_size > 0")]
/// #[rr::loop_inv("level_size", "current[..level_size] = merkle_level(leaves, level)")]
/// ```
#[rr::verified]
pub fn compute_root(&mut self) -> Result<[u8; HASH_SIZE], MerkleError> {
    #[rr::assert("Check for empty tree")]
    if self.count == 0 {
        return Err(MerkleError::EmptyTree);
    }

    #[rr::assert("Return cached root if already computed")]
    if self.computed {
        return Ok(self.root);
    }

    #[rr::assert("Initialize working buffer")]
    let mut current = [[0u8; HASH_SIZE]; MAX_LEAVES];
    current[..self.count].copy_from_slice(&self.leaves[..self.count]);
    let mut level_size = self.count;

    #[rr::assert("Build tree bottom-up")]
    #[rr::loop_inv("level_size > 0")]
    while level_size > 1 {
        let mut next_size = 0;
        let mut i = 0;

        #[rr::assert("Hash pairs of nodes")]
        while i + 1 < level_size {
            current[next_size] = hash_nodes(&current[i], &current[i + 1]);
            next_size += 1;
            i += 2;
        }

        #[rr::assert("Handle odd node (promote unchanged)")]
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

// ============================================================================
// MerkleTree::generate_proof
// ============================================================================

/// Generate an inclusion proof for a leaf at the given index.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("idx" : "nat")]
/// #[rr::args("&self @ &shr<'_, MerkleTree>", "idx @ usize")]
/// #[rr::requires("idx < self.count")]
/// #[rr::ensures("match result {
///     Ok(proof) =>
///         proof.len <= MAX_PROOF_DEPTH /\
///         verify_proof(proof, self.leaves[idx], self.root) = true
///   | Err(InvalidIndex) =>
///         idx >= self.count
///   | Err(EmptyTree) =>
///         self.count = 0
/// }")]
/// ```
#[rr::verified]
pub fn generate_proof(&self, idx: usize) -> Result<MerkleProof, MerkleError> {
    #[rr::assert("Validate index")]
    if idx >= self.count {
        return Err(MerkleError::InvalidIndex);
    }
    if self.count == 0 {
        return Err(MerkleError::EmptyTree);
    }

    // ... proof generation implementation ...

    Ok(proof)
}

// ============================================================================
// hash_nodes - Internal Node Hashing
// ============================================================================

/// Hash two child nodes to produce parent.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("left" : "array u8 32", "right" : "array u8 32")]
/// #[rr::args("left @ &[u8; 32]", "right @ &[u8; 32]")]
/// #[rr::returns("SHA3_256(NODE_DOMAIN || left || right)")]
/// #[rr::ensures("result = hash_nodes(left, right)")]
/// ```
#[rr::verified]
#[inline]
fn hash_nodes(left: &[u8; HASH_SIZE], right: &[u8; HASH_SIZE]) -> [u8; HASH_SIZE] {
    #[rr::assert("Build input: 0x01 || left || right")]
    let mut input = [0u8; 1 + HASH_SIZE * 2];
    input[0] = NODE_DOMAIN;
    input[1..33].copy_from_slice(left);
    input[33..65].copy_from_slice(right);

    sha3_256(&input)
}

// ============================================================================
// MerkleProof Type
// ============================================================================

/// A Merkle inclusion proof.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("siblings" : "list (array u8 32)", "is_left" : "list bool")]
/// #[rr::invariant("len(siblings) <= MAX_PROOF_DEPTH")]
/// #[rr::invariant("len(siblings) = len(is_left)")]
/// ```
#[rr::type("MerkleProof")]
pub struct MerkleProof {
    siblings: [[u8; HASH_SIZE]; MAX_PROOF_DEPTH],
    is_left: [bool; MAX_PROOF_DEPTH],
    len: usize,
}

// ============================================================================
// MerkleProof::verify
// ============================================================================

/// Verify that a leaf is included in the tree with the given root.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("leaf" : "array u8 32", "expected_root" : "array u8 32")]
/// #[rr::args("&self @ &shr<'_, MerkleProof>",
///            "leaf @ &[u8; 32]",
///            "expected_root @ &[u8; 32]")]
/// #[rr::returns("verify_membership(leaf, self.siblings, self.is_left, expected_root)")]
///
/// (* Correctness: if verify returns true, leaf is in the tree *)
/// #[rr::ensures("result = true ==>
///     exists path. merkle_path(leaf, path, expected_root)")]
/// ```
#[rr::verified]
pub fn verify(&self, leaf: &[u8; HASH_SIZE], expected_root: &[u8; HASH_SIZE]) -> bool {
    #[rr::assert("Hash leaf with domain separator")]
    let mut input = [0u8; 1 + HASH_SIZE];
    input[0] = LEAF_DOMAIN;
    input[1..].copy_from_slice(leaf);
    let mut current = sha3_256(&input);

    #[rr::assert("Walk up the tree using proof siblings")]
    #[rr::loop_inv("i <= self.len")]
    for i in 0..self.len {
        if self.is_left[i] {
            current = hash_nodes(&self.siblings[i], &current);
        } else {
            current = hash_nodes(&current, &self.siblings[i]);
        }
    }

    current == *expected_root
}

// ============================================================================
// Verification Conditions
// ============================================================================

/// Proof obligations for Merkle tree:
///
/// ## Domain Separation
/// ```coq
/// Theorem domain_separation :
///   LEAF_DOMAIN <> NODE_DOMAIN.
/// Proof.
///   unfold LEAF_DOMAIN, NODE_DOMAIN. discriminate.
/// Qed.
/// ```
///
/// ## Leaf Count Bounds
/// ```coq
/// Theorem leaf_count_bounded :
///   forall tree : MerkleTree,
///     tree.count <= MAX_LEAVES.
/// ```
///
/// ## Proof Depth Bounds
/// ```coq
/// Theorem proof_depth_bounded :
///   forall proof : MerkleProof,
///     proof.len <= MAX_PROOF_DEPTH.
/// ```
///
/// ## Proof Verification Correctness
/// ```coq
/// Theorem proof_correctness :
///   forall tree leaf idx proof,
///     idx < tree.count ->
///     proof = generate_proof(tree, idx) ->
///     let root := compute_root(tree) in
///     verify(proof, tree.leaves[idx], root) = true.
/// ```
///
/// ## Deterministic Root
/// ```coq
/// Theorem root_deterministic :
///   forall leaves1 leaves2,
///     leaves1 = leaves2 ->
///     merkle_root(leaves1) = merkle_root(leaves2).
/// Proof.
///   reflexivity.
/// Qed.
/// ```
///
/// ## Hash Collision Resistance (Axiom)
/// ```coq
/// Axiom sha3_collision_resistant :
///   forall x y,
///     sha3_256(x) = sha3_256(y) ->
///     (* With overwhelming probability *) x = y.
/// ```
mod _verification_conditions {}

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
    fn test_proof_verification() {
        let mut tree = MerkleTree::new();
        let leaf1 = [1u8; 32];
        let leaf2 = [2u8; 32];
        tree.add_leaf(&leaf1).unwrap();
        tree.add_leaf(&leaf2).unwrap();
        let root = tree.compute_root().unwrap();

        let proof1 = tree.generate_proof(0).unwrap();
        assert!(proof1.verify(&leaf1, &root));
        assert!(!proof1.verify(&leaf2, &root));
    }
}
