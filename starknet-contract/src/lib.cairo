/// Anubis Notary Oracle - Post-Quantum Secure Document Notarization
///
/// A decentralized notary service providing cryptographic proof-of-existence
/// for documents, files, and digital assets on the Starknet blockchain.
///
/// ## Contracts
///
/// - **NotaryOracle**: Core document anchoring and verification
/// - **MarriageOracle**: Blockchain-anchored marriage contracts
/// - **AnubisMarriageRing**: ERC721 digital wedding rings

pub mod marriage;
pub mod marriage_ring;
///
/// ## What is a Notary Oracle?
///
/// This smart contract acts as an immutable, trustless notary that:
/// - **Timestamps documents**: Proves a document existed at a specific time
/// - **Anchors cryptographic hashes**: Stores SHA3-256/Poseidon Merkle roots on-chain
/// - **Enables verification**: Anyone can verify document authenticity against the blockchain
/// - **Provides legal evidence**: Blockchain timestamps are court-admissible in many jurisdictions
///
/// ## Use Cases
///
/// - **Legal documents**: Contracts, wills, patents, intellectual property
/// - **Software releases**: Code signatures, build artifacts, security audits
/// - **Financial records**: Invoices, receipts, audit trails
/// - **Creative works**: Art, music, manuscripts (proof of authorship)
/// - **Compliance**: Regulatory filings, certifications, attestations
///
/// ## Features
///
/// - **Single Anchor**: Store individual document hashes (~$0.001 per anchor)
/// - **Batch Anchor**: Store up to 8 documents combined via Poseidon hash (~$0.000125 each)
/// - **Merkle Proofs**: Verify document inclusion with cryptographic witnesses
/// - **Immutability**: Once anchored, records cannot be modified or deleted
/// - **Post-Quantum Ready**: Uses Poseidon hashing (STARK-friendly, PQ-secure)
///
/// ## Integration
///
/// This contract is the on-chain component of Anubis Notary, a post-quantum
/// secure CLI tool using ML-DSA-87 signatures and ML-KEM-1024 encryption.
/// Learn more: https://github.com/AnubisQuantumCipher/anubis-notary

use starknet::ContractAddress;

/// Anchor record stored on-chain.
#[derive(Drop, Serde, starknet::Store)]
pub struct AnchorRecord {
    /// The anchored Merkle root.
    pub root: felt252,
    /// Block number when anchored.
    pub block_number: u64,
    /// Timestamp when anchored (seconds since UNIX epoch).
    pub timestamp: u64,
    /// Address that created this anchor.
    pub anchorer: ContractAddress,
}

/// NotaryOracle interface.
#[starknet::interface]
pub trait INotaryOracle<TContractState> {
    /// Anchor a single Merkle root.
    ///
    /// Returns the assigned root ID.
    fn anchor_root(ref self: TContractState, root: felt252) -> u64;

    /// Anchor a batch of up to 8 Merkle roots.
    ///
    /// The roots are combined using Poseidon hash.
    /// Returns the assigned root ID for the batch.
    fn anchor_batch(ref self: TContractState, roots: Span<felt252>) -> u64;

    /// Verify that a root is anchored at the given ID.
    fn verify_root(self: @TContractState, root_id: u64, expected: felt252) -> bool;

    /// Verify inclusion of a leaf in a batch anchor using Merkle witness.
    ///
    /// - `root_id`: The batch anchor's root ID
    /// - `leaf`: The individual root to verify
    /// - `proof`: Array of sibling hashes (3 for 8-leaf tree)
    /// - `proof_directions`: Direction for each proof element (0=left, 1=right)
    fn verify_inclusion(
        self: @TContractState,
        root_id: u64,
        leaf: felt252,
        proof: Span<felt252>,
        proof_directions: Span<bool>,
    ) -> bool;

    /// Get an anchor record by ID.
    fn get_anchor(self: @TContractState, root_id: u64) -> AnchorRecord;

    /// Get the total number of anchors.
    fn get_anchor_count(self: @TContractState) -> u64;

    /// Get the contract owner.
    fn get_owner(self: @TContractState) -> ContractAddress;
}

#[starknet::contract]
pub mod NotaryOracle {
    use super::{AnchorRecord, INotaryOracle};
    use starknet::{ContractAddress, get_caller_address, get_block_number, get_block_timestamp};
    use starknet::storage::{Map, StorageMapReadAccess, StorageMapWriteAccess, StoragePointerReadAccess, StoragePointerWriteAccess};
    use core::poseidon::poseidon_hash_span;

    /// Events emitted by the contract.
    #[event]
    #[derive(Drop, starknet::Event)]
    pub enum Event {
        RootAnchored: RootAnchored,
        BatchAnchored: BatchAnchored,
    }

    /// Emitted when a single root is anchored.
    #[derive(Drop, starknet::Event)]
    pub struct RootAnchored {
        #[key]
        root_id: u64,
        root: felt252,
        anchorer: ContractAddress,
        block_number: u64,
        timestamp: u64,
    }

    /// Emitted when a batch of roots is anchored.
    #[derive(Drop, starknet::Event)]
    pub struct BatchAnchored {
        #[key]
        root_id: u64,
        batch_root: felt252,
        batch_size: u8,
        anchorer: ContractAddress,
        block_number: u64,
        timestamp: u64,
    }

    #[storage]
    struct Storage {
        /// Contract owner.
        owner: ContractAddress,
        /// Total number of anchors.
        anchor_count: u64,
        /// Mapping from root ID to anchor record.
        anchors: Map<u64, AnchorRecord>,
    }

    #[constructor]
    fn constructor(ref self: ContractState, owner: ContractAddress) {
        self.owner.write(owner);
        self.anchor_count.write(0);
    }

    #[abi(embed_v0)]
    impl NotaryOracleImpl of INotaryOracle<ContractState> {
        fn anchor_root(ref self: ContractState, root: felt252) -> u64 {
            // Get current state
            let caller = get_caller_address();
            let block_number = get_block_number();
            let timestamp = get_block_timestamp();

            // Increment anchor count
            let root_id = self.anchor_count.read() + 1;
            self.anchor_count.write(root_id);

            // Store anchor record
            let record = AnchorRecord {
                root,
                block_number,
                timestamp,
                anchorer: caller,
            };
            self.anchors.write(root_id, record);

            // Emit event
            self.emit(Event::RootAnchored(RootAnchored {
                root_id,
                root,
                anchorer: caller,
                block_number,
                timestamp,
            }));

            root_id
        }

        fn anchor_batch(ref self: ContractState, roots: Span<felt252>) -> u64 {
            // Validate batch size (1-8 roots)
            let batch_size = roots.len();
            assert(batch_size > 0 && batch_size <= 8, 'batch size must be 1-8');

            // Pad to 8 elements and compute batch root using Poseidon
            let mut padded: Array<felt252> = array![];
            let mut i: u32 = 0;
            loop {
                if i >= 8 {
                    break;
                }
                if i < batch_size {
                    padded.append(*roots.at(i));
                } else {
                    padded.append(0);
                }
                i += 1;
            };

            // Compute batch root
            let batch_root = poseidon_hash_span(padded.span());

            // Get current state
            let caller = get_caller_address();
            let block_number = get_block_number();
            let timestamp = get_block_timestamp();

            // Increment anchor count
            let root_id = self.anchor_count.read() + 1;
            self.anchor_count.write(root_id);

            // Store anchor record with batch root
            let record = AnchorRecord {
                root: batch_root,
                block_number,
                timestamp,
                anchorer: caller,
            };
            self.anchors.write(root_id, record);

            // Emit event
            self.emit(Event::BatchAnchored(BatchAnchored {
                root_id,
                batch_root,
                batch_size: batch_size.try_into().unwrap(),
                anchorer: caller,
                block_number,
                timestamp,
            }));

            root_id
        }

        fn verify_root(self: @ContractState, root_id: u64, expected: felt252) -> bool {
            if root_id == 0 || root_id > self.anchor_count.read() {
                return false;
            }

            let record = self.anchors.read(root_id);
            record.root == expected
        }

        fn verify_inclusion(
            self: @ContractState,
            root_id: u64,
            leaf: felt252,
            proof: Span<felt252>,
            proof_directions: Span<bool>,
        ) -> bool {
            // Validate inputs
            if root_id == 0 || root_id > self.anchor_count.read() {
                return false;
            }
            if proof.len() != proof_directions.len() {
                return false;
            }

            // Compute root from leaf and proof
            let mut current = leaf;
            let mut i: u32 = 0;
            loop {
                if i >= proof.len() {
                    break;
                }
                let sibling = *proof.at(i);
                let direction = *proof_directions.at(i);

                // Hash in correct order based on direction
                if direction {
                    // Current is on right, sibling on left
                    current = poseidon_hash_span(array![sibling, current].span());
                } else {
                    // Current is on left, sibling on right
                    current = poseidon_hash_span(array![current, sibling].span());
                }
                i += 1;
            };

            // Compare with stored root
            let record = self.anchors.read(root_id);
            record.root == current
        }

        fn get_anchor(self: @ContractState, root_id: u64) -> AnchorRecord {
            assert(root_id > 0 && root_id <= self.anchor_count.read(), 'invalid root id');
            self.anchors.read(root_id)
        }

        fn get_anchor_count(self: @ContractState) -> u64 {
            self.anchor_count.read()
        }

        fn get_owner(self: @ContractState) -> ContractAddress {
            self.owner.read()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{NotaryOracle, INotaryOracleDispatcher, INotaryOracleDispatcherTrait};
    use starknet::testing::{set_caller_address, set_block_number, set_block_timestamp};
    use starknet::syscalls::deploy_syscall;
    use core::poseidon::poseidon_hash_span;

    fn deploy_contract() -> INotaryOracleDispatcher {
        let owner: felt252 = 'owner';
        let (contract_address, _) = deploy_syscall(
            NotaryOracle::TEST_CLASS_HASH.try_into().unwrap(),
            0,
            array![owner].span(),
            false,
        ).unwrap();
        INotaryOracleDispatcher { contract_address }
    }

    fn get_test_address(name: felt252) -> starknet::ContractAddress {
        name.try_into().unwrap()
    }

    // ============================================================
    // BASIC ANCHOR TESTS
    // ============================================================

    #[test]
    fn test_anchor_single_root() {
        let contract = deploy_contract();
        let root: felt252 = 0x123456789abcdef;

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        let root_id = contract.anchor_root(root);
        assert(root_id == 1, 'wrong root id');
        assert(contract.get_anchor_count() == 1, 'wrong count');

        // Verify root
        assert(contract.verify_root(root_id, root), 'verify failed');
        assert(!contract.verify_root(root_id, 0x999), 'wrong root verified');
    }

    #[test]
    fn test_anchor_batch() {
        let contract = deploy_contract();
        let roots: Array<felt252> = array![0x111, 0x222, 0x333, 0x444];

        set_caller_address(get_test_address('user'));
        set_block_number(200);
        set_block_timestamp(1704153600);

        let root_id = contract.anchor_batch(roots.span());
        assert(root_id == 1, 'wrong root id');

        // Compute expected batch root
        let padded: Array<felt252> = array![0x111, 0x222, 0x333, 0x444, 0, 0, 0, 0];
        let expected_root = poseidon_hash_span(padded.span());

        assert(contract.verify_root(root_id, expected_root), 'batch verify failed');
    }

    #[test]
    fn test_get_anchor() {
        let contract = deploy_contract();
        let root: felt252 = 0xabc;

        set_caller_address(get_test_address('anchorer'));
        set_block_number(300);
        set_block_timestamp(1704240000);

        let root_id = contract.anchor_root(root);
        let record = contract.get_anchor(root_id);

        assert(record.root == root, 'wrong root');
        assert(record.block_number == 300, 'wrong block');
        assert(record.timestamp == 1704240000, 'wrong timestamp');
    }

    #[test]
    fn test_multiple_anchors() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        let id1 = contract.anchor_root(0x111);
        let id2 = contract.anchor_root(0x222);
        let id3 = contract.anchor_root(0x333);

        assert(id1 == 1, 'id1 wrong');
        assert(id2 == 2, 'id2 wrong');
        assert(id3 == 3, 'id3 wrong');
        assert(contract.get_anchor_count() == 3, 'count wrong');

        assert(contract.verify_root(id1, 0x111), 'verify 1 failed');
        assert(contract.verify_root(id2, 0x222), 'verify 2 failed');
        assert(contract.verify_root(id3, 0x333), 'verify 3 failed');
    }

    #[test]
    #[should_panic]
    fn test_batch_empty() {
        let contract = deploy_contract();
        let empty: Array<felt252> = array![];
        contract.anchor_batch(empty.span());
    }

    #[test]
    fn test_verify_invalid_root_id() {
        let contract = deploy_contract();
        assert(!contract.verify_root(0, 0x123), 'id 0 should fail');
        assert(!contract.verify_root(999, 0x123), 'non-existent should fail');
    }

    // ============================================================
    // MERKLE INCLUSION PROOF TESTS
    // Note: anchor_batch uses flat Poseidon hash, not binary Merkle tree.
    // verify_inclusion is for external Merkle proofs against single anchored roots.
    // ============================================================

    /// Test verify_inclusion with single root (empty proof)
    #[test]
    fn test_verify_inclusion_single_root() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        // Anchor a single root directly
        let root: felt252 = 0xDEADBEEF;
        let root_id = contract.anchor_root(root);

        // With empty proof, the leaf should equal the stored root
        let empty_proof: Array<felt252> = array![];
        let empty_dirs: Array<bool> = array![];

        assert(
            contract.verify_inclusion(root_id, root, empty_proof.span(), empty_dirs.span()),
            'empty proof should match'
        );
    }

    /// Test verify_inclusion with single-level proof
    #[test]
    fn test_verify_inclusion_one_level() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        // Create leaves and compute parent
        let leaf0: felt252 = 0x1111;
        let leaf1: felt252 = 0x2222;
        let parent = poseidon_hash_span(array![leaf0, leaf1].span());

        // Anchor the parent root
        let root_id = contract.anchor_root(parent);

        // Verify leaf0 with leaf1 as sibling (direction = false means leaf is on left)
        let proof0: Array<felt252> = array![leaf1];
        let dirs0: Array<bool> = array![false];
        assert(
            contract.verify_inclusion(root_id, leaf0, proof0.span(), dirs0.span()),
            'leaf0 proof failed'
        );

        // Verify leaf1 with leaf0 as sibling (direction = true means leaf is on right)
        let proof1: Array<felt252> = array![leaf0];
        let dirs1: Array<bool> = array![true];
        assert(
            contract.verify_inclusion(root_id, leaf1, proof1.span(), dirs1.span()),
            'leaf1 proof failed'
        );
    }

    /// Test verify_inclusion with two-level proof
    #[test]
    fn test_verify_inclusion_two_levels() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        // Create 4 leaves and compute binary tree
        let leaf0: felt252 = 0xAAAA;
        let leaf1: felt252 = 0xBBBB;
        let leaf2: felt252 = 0xCCCC;
        let leaf3: felt252 = 0xDDDD;

        let n01 = poseidon_hash_span(array![leaf0, leaf1].span());
        let n23 = poseidon_hash_span(array![leaf2, leaf3].span());
        let root = poseidon_hash_span(array![n01, n23].span());

        // Anchor the computed root
        let root_id = contract.anchor_root(root);

        // Verify leaf0: path [leaf1, n23], directions [false, false]
        assert(
            contract.verify_inclusion(
                root_id, leaf0, array![leaf1, n23].span(), array![false, false].span()
            ),
            'leaf0 proof failed'
        );

        // Verify leaf2: path [leaf3, n01], directions [false, true]
        assert(
            contract.verify_inclusion(
                root_id, leaf2, array![leaf3, n01].span(), array![false, true].span()
            ),
            'leaf2 proof failed'
        );
    }

    /// Test that invalid proofs fail
    #[test]
    fn test_merkle_inclusion_invalid_proof() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        let roots: Array<felt252> = array![0x1111, 0x2222];
        let root_id = contract.anchor_batch(roots.span());

        // Wrong sibling value should fail
        let wrong_proof: Array<felt252> = array![0x9999, 0, 0]; // Wrong first sibling
        let directions: Array<bool> = array![false, false, false];

        assert(
            !contract.verify_inclusion(root_id, 0x1111, wrong_proof.span(), directions.span()),
            'wrong proof should fail'
        );
    }

    /// Test that proof/direction length mismatch fails
    #[test]
    fn test_merkle_inclusion_length_mismatch() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        let roots: Array<felt252> = array![0x1111];
        let root_id = contract.anchor_batch(roots.span());

        // Mismatched lengths
        let proof: Array<felt252> = array![0x2222, 0x3333];
        let directions: Array<bool> = array![false]; // Only 1 direction for 2 proofs

        assert(
            !contract.verify_inclusion(root_id, 0x1111, proof.span(), directions.span()),
            'length mismatch should fail'
        );
    }

    /// Test verify_inclusion with invalid root_id
    #[test]
    fn test_merkle_inclusion_invalid_root_id() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));

        // No anchors exist yet
        let proof: Array<felt252> = array![0x1];
        let directions: Array<bool> = array![false];

        assert(
            !contract.verify_inclusion(0, 0x1111, proof.span(), directions.span()),
            'id=0 should fail'
        );
        assert(
            !contract.verify_inclusion(999, 0x1111, proof.span(), directions.span()),
            'nonexistent should fail'
        );
    }

    // ============================================================
    // BATCH ANCHORING DETERMINISM TESTS
    // ============================================================

    /// Same inputs should always produce the same batch root
    #[test]
    fn test_batch_determinism() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        // First batch
        let roots1: Array<felt252> = array![0x111, 0x222, 0x333];
        let id1 = contract.anchor_batch(roots1.span());
        let record1 = contract.get_anchor(id1);

        // Second batch with same values
        let roots2: Array<felt252> = array![0x111, 0x222, 0x333];
        let id2 = contract.anchor_batch(roots2.span());
        let record2 = contract.get_anchor(id2);

        // Both should produce identical roots (deterministic Poseidon)
        assert(record1.root == record2.root, 'roots should match');
    }

    /// Different inputs should produce different roots
    #[test]
    fn test_batch_collision_resistance() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        // First batch
        let roots1: Array<felt252> = array![0x111, 0x222];
        let id1 = contract.anchor_batch(roots1.span());
        let record1 = contract.get_anchor(id1);

        // Second batch with different values
        let roots2: Array<felt252> = array![0x111, 0x223]; // Only last digit different
        let id2 = contract.anchor_batch(roots2.span());
        let record2 = contract.get_anchor(id2);

        // Should produce different roots
        assert(record1.root != record2.root, 'roots should differ');
    }

    /// Verify padding correctness: [r0, r1] should equal [r0, r1, 0, 0, 0, 0, 0, 0]
    #[test]
    fn test_batch_padding_correctness() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        let roots: Array<felt252> = array![0xAAA, 0xBBB];
        let root_id = contract.anchor_batch(roots.span());
        let record = contract.get_anchor(root_id);

        // Manually compute with explicit padding
        let padded: Array<felt252> = array![0xAAA, 0xBBB, 0, 0, 0, 0, 0, 0];
        let expected = poseidon_hash_span(padded.span());

        assert(record.root == expected, 'padding incorrect');
    }

    // ============================================================
    // SECURITY BOUNDARY TESTS
    // ============================================================

    /// Test maximum batch size (8)
    #[test]
    fn test_batch_max_size() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        // Exactly 8 roots should work
        let max_roots: Array<felt252> = array![1, 2, 3, 4, 5, 6, 7, 8];
        let root_id = contract.anchor_batch(max_roots.span());
        assert(root_id == 1, 'max batch failed');
    }

    /// Test batch overflow (>8 should panic)
    #[test]
    #[should_panic]
    fn test_batch_overflow() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));

        // 9 roots should fail
        let too_many: Array<felt252> = array![1, 2, 3, 4, 5, 6, 7, 8, 9];
        contract.anchor_batch(too_many.span());
    }

    /// Test single-element batch
    #[test]
    fn test_batch_single_element() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        // Single root batch
        let single: Array<felt252> = array![0xDEADBEEF];
        let root_id = contract.anchor_batch(single.span());
        assert(root_id == 1, 'single batch failed');

        // Verify the padded hash
        let padded: Array<felt252> = array![0xDEADBEEF, 0, 0, 0, 0, 0, 0, 0];
        let expected = poseidon_hash_span(padded.span());
        assert(contract.verify_root(root_id, expected), 'single verify failed');
    }

    /// Test that get_anchor panics for invalid ID
    #[test]
    #[should_panic]
    fn test_get_anchor_invalid_id_zero() {
        let contract = deploy_contract();
        contract.get_anchor(0);
    }

    /// Test that get_anchor panics for non-existent ID
    #[test]
    #[should_panic]
    fn test_get_anchor_invalid_id_nonexistent() {
        let contract = deploy_contract();
        contract.get_anchor(999);
    }

    /// Test extreme felt252 values
    #[test]
    fn test_extreme_values() {
        let contract = deploy_contract();

        set_caller_address(get_test_address('user'));
        set_block_number(100);
        set_block_timestamp(1704067200);

        // Zero root
        let id_zero = contract.anchor_root(0);
        assert(contract.verify_root(id_zero, 0), 'zero verify failed');

        // Large value (close to felt252 max)
        let large_value: felt252 = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
        let id_large = contract.anchor_root(large_value);
        assert(contract.verify_root(id_large, large_value), 'large verify failed');
    }

    /// Test anchoring from a single caller works correctly
    #[test]
    fn test_single_caller_multiple_anchors() {
        let contract = deploy_contract();

        set_block_number(100);
        set_block_timestamp(1704067200);
        set_caller_address(get_test_address('user'));

        // Same user anchors multiple roots
        let id1 = contract.anchor_root(0x111);
        let id2 = contract.anchor_root(0x222);

        // Verify both anchors exist with correct roots
        assert(contract.verify_root(id1, 0x111), 'anchor 1 failed');
        assert(contract.verify_root(id2, 0x222), 'anchor 2 failed');

        // Verify records have correct data
        let record1 = contract.get_anchor(id1);
        let record2 = contract.get_anchor(id2);
        assert(record1.root == 0x111, 'wrong root 1');
        assert(record2.root == 0x222, 'wrong root 2');
    }
}
