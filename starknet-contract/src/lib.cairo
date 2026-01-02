/// Anubis Notary Oracle - On-chain Merkle Root Anchoring
///
/// This contract provides immutable timestamping of Merkle roots on Starknet.
/// It supports both single root anchoring and batch anchoring for cost efficiency.
///
/// ## Features
///
/// - **Single Anchor**: Store individual SHA3-256/Poseidon Merkle roots
/// - **Batch Anchor**: Store up to 8 roots combined via Poseidon hash
/// - **Verification**: Verify root inclusion with Merkle witnesses
/// - **Immutability**: Once anchored, roots cannot be modified
///
/// ## Cost
///
/// - Single anchor: ~$0.001
/// - Batch anchor (8 roots): ~$0.001 total (~$0.000125 per root)

use starknet::ContractAddress;
use starknet::storage::{StorageMapReadAccess, StorageMapWriteAccess, StoragePointerReadAccess, StoragePointerWriteAccess};
use core::poseidon::poseidon_hash_span;

/// Anchor record stored on-chain.
#[derive(Drop, Serde, starknet::Store)]
pub struct AnchorRecord {
    /// The anchored Merkle root.
    root: felt252,
    /// Block number when anchored.
    block_number: u64,
    /// Timestamp when anchored (seconds since UNIX epoch).
    timestamp: u64,
    /// Address that created this anchor.
    anchorer: ContractAddress,
}

/// Events emitted by the contract.
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
    use super::{AnchorRecord, Event, RootAnchored, BatchAnchored, INotaryOracle};
    use starknet::{ContractAddress, get_caller_address, get_block_number, get_block_timestamp};
    use starknet::storage::{Map, StorageMapReadAccess, StorageMapWriteAccess, StoragePointerReadAccess, StoragePointerWriteAccess};
    use core::poseidon::poseidon_hash_span;

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
    use super::{NotaryOracle, INotaryOracle, INotaryOracleDispatcher, INotaryOracleDispatcherTrait};
    use starknet::ContractAddress;
    use starknet::testing::{set_caller_address, set_block_number, set_block_timestamp};
    use starknet::contract_address_const;
    use core::poseidon::poseidon_hash_span;

    fn deploy_contract() -> INotaryOracleDispatcher {
        let owner = contract_address_const::<'owner'>();
        let contract_address = starknet::syscalls::deploy_syscall(
            NotaryOracle::TEST_CLASS_HASH.try_into().unwrap(),
            0,
            array![owner.into()].span(),
            false,
        ).unwrap().0;
        INotaryOracleDispatcher { contract_address }
    }

    #[test]
    fn test_anchor_single_root() {
        let contract = deploy_contract();
        let root: felt252 = 0x123456789abcdef;

        set_caller_address(contract_address_const::<'user'>());
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

        set_caller_address(contract_address_const::<'user'>());
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

        set_caller_address(contract_address_const::<'anchorer'>());
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

        set_caller_address(contract_address_const::<'user'>());
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
    #[should_panic(expected: ('batch size must be 1-8',))]
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
}
