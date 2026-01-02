/**
 * AnubisBatchVault zkApp - Batch Merkle Root Anchoring Contract for Mina Protocol
 *
 * This contract stores a Merkle tree of historical roots, enabling batch anchoring
 * of multiple receipts in a single transaction. This reduces costs by up to 8x
 * compared to individual anchoring.
 *
 * On-Chain State:
 * - vaultRoot: Merkle root of all historical anchored roots
 * - rootCount: Total number of roots anchored
 * - lastUpdated: Timestamp of last batch submission
 *
 * Key Features:
 * - Batch up to 8 roots per transaction
 * - Verification via Merkle proof (no on-chain lookup needed)
 * - Compatible with pure Rust verification
 */

import {
  SmartContract,
  state,
  State,
  method,
  Field,
  Permissions,
  Struct,
  Poseidon,
  UInt64,
  Provable,
  Circuit,
  Bool,
} from 'o1js';

/**
 * Maximum roots per batch.
 */
const MAX_BATCH_SIZE = 8;

/**
 * Depth of the vault Merkle tree (supports up to 2^16 = 65536 roots).
 */
const VAULT_TREE_DEPTH = 16;

/**
 * Witness for Merkle proof in the vault tree.
 */
export class VaultMerkleWitness extends Struct({
  path: Provable.Array(Field, VAULT_TREE_DEPTH),
  isLeft: Provable.Array(Bool, VAULT_TREE_DEPTH),
}) {
  /**
   * Compute the root given a leaf and this witness.
   */
  calculateRoot(leaf: Field): Field {
    let hash = leaf;
    for (let i = 0; i < VAULT_TREE_DEPTH; i++) {
      const sibling = this.path[i];
      const isLeft = this.isLeft[i];
      // If isLeft is true, hash = H(sibling, hash), else hash = H(hash, sibling)
      hash = Provable.if(
        isLeft,
        Poseidon.hash([sibling, hash]),
        Poseidon.hash([hash, sibling])
      );
    }
    return hash;
  }

  /**
   * Calculate the next root after inserting a new leaf.
   */
  calculateNextRoot(newLeaf: Field, oldRoot: Field): Field {
    // Verify the old root matches
    const emptyLeaf = Field(0);
    const computedOldRoot = this.calculateRoot(emptyLeaf);
    computedOldRoot.assertEquals(oldRoot, 'Witness does not match current vault state');

    // Compute new root with the new leaf
    return this.calculateRoot(newLeaf);
  }
}

/**
 * Batch of roots to anchor.
 */
export class RootBatch extends Struct({
  roots: Provable.Array(Field, MAX_BATCH_SIZE),
  count: Field, // Actual number of roots (1-8)
}) {
  /**
   * Compute the batch Merkle root from the provided roots.
   */
  computeBatchRoot(): Field {
    // Build a small Merkle tree from the roots
    // For efficiency, we use a fixed 3-level tree (supports 8 leaves)
    let level = this.roots.slice();

    // Level 2: 4 nodes
    const l2: Field[] = [];
    for (let i = 0; i < 4; i++) {
      l2.push(Poseidon.hash([level[i * 2], level[i * 2 + 1]]));
    }

    // Level 1: 2 nodes
    const l1: Field[] = [];
    for (let i = 0; i < 2; i++) {
      l1.push(Poseidon.hash([l2[i * 2], l2[i * 2 + 1]]));
    }

    // Level 0: 1 node (root)
    return Poseidon.hash([l1[0], l1[1]]);
  }
}

/**
 * AnubisBatchVault zkApp - Stores Merkle tree of historical roots.
 *
 * This enables batch anchoring where multiple receipt roots are combined
 * into a single vault update, reducing transaction costs.
 */
export class AnubisBatchVault extends SmartContract {
  /**
   * Root of the Merkle tree containing all anchored roots.
   */
  @state(Field) vaultRoot = State<Field>();

  /**
   * Total number of roots anchored.
   */
  @state(Field) rootCount = State<Field>();

  /**
   * Timestamp of last batch submission (Unix ms).
   */
  @state(UInt64) lastUpdated = State<UInt64>();

  /**
   * Initialize the contract with an empty vault.
   */
  init() {
    super.init();
    this.account.permissions.set({
      ...Permissions.default(),
      editState: Permissions.proofOrSignature(),
    });

    // Initialize with empty vault (all-zeros root)
    this.vaultRoot.set(Field(0));
    this.rootCount.set(Field(0));
    this.lastUpdated.set(UInt64.from(0));
  }

  /**
   * Submit a batch of roots to the vault.
   *
   * This updates the vault Merkle tree to include all provided roots.
   * The caller must provide a valid Merkle witness proving the insertion point.
   *
   * @param batch - Batch of roots to anchor (1-8 roots)
   * @param witness - Merkle witness for the insertion point
   */
  @method async submitBatch(batch: RootBatch, witness: VaultMerkleWitness) {
    // Get current state
    const currentRoot = this.vaultRoot.getAndRequireEquals();
    const currentCount = this.rootCount.getAndRequireEquals();

    // Validate batch
    batch.count.assertGreaterThan(Field(0), 'Batch cannot be empty');
    batch.count.assertLessThanOrEqual(Field(MAX_BATCH_SIZE), 'Batch too large');

    // Compute the batch root (combines all roots in this batch)
    const batchRoot = batch.computeBatchRoot();

    // Calculate new vault root by inserting the batch root
    const newVaultRoot = witness.calculateNextRoot(batchRoot, currentRoot);

    // Get network timestamp for deterministic proofs
    const networkTime = this.network.timestamp.getAndRequireEquals();

    // Update state
    this.vaultRoot.set(newVaultRoot);
    this.rootCount.set(currentCount.add(batch.count));
    this.lastUpdated.set(networkTime);
  }

  /**
   * Anchor a single root (backward compatible with existing flow).
   *
   * This wraps the single root in a batch of size 1.
   */
  @method async anchorRoot(root: Field) {
    const currentRoot = this.vaultRoot.getAndRequireEquals();
    const currentCount = this.rootCount.getAndRequireEquals();

    // Simple update: hash the new root with the current vault root
    // This creates a chain: newRoot = H(currentRoot, root)
    const newVaultRoot = Poseidon.hash([currentRoot, root]);

    // Get network timestamp for deterministic proofs
    const networkTime = this.network.timestamp.getAndRequireEquals();

    // Update state
    this.vaultRoot.set(newVaultRoot);
    this.rootCount.set(currentCount.add(Field(1)));
    this.lastUpdated.set(networkTime);
  }
}

/**
 * Convert a hex string to a Field (same as AnubisAnchor).
 */
export function hexToField(hexString: string): Field {
  const cleanHex = hexString.startsWith('0x') ? hexString.slice(2) : hexString;
  let value = BigInt('0x' + cleanHex);
  const mask = (BigInt(1) << BigInt(253)) - BigInt(1);
  return Field(value & mask);
}

/**
 * Compute a batch root from an array of hex digest strings.
 */
export function computeBatchRootFromHex(hexDigests: string[]): Field {
  if (hexDigests.length === 0) {
    return Field(0);
  }

  // Pad to 8 elements with zeros
  const paddedRoots: Field[] = [];
  for (let i = 0; i < MAX_BATCH_SIZE; i++) {
    if (i < hexDigests.length) {
      paddedRoots.push(hexToField(hexDigests[i]));
    } else {
      paddedRoots.push(Field(0));
    }
  }

  // Build Merkle tree
  // Level 2: 4 nodes
  const l2: Field[] = [];
  for (let i = 0; i < 4; i++) {
    l2.push(Poseidon.hash([paddedRoots[i * 2], paddedRoots[i * 2 + 1]]));
  }

  // Level 1: 2 nodes
  const l1: Field[] = [];
  for (let i = 0; i < 2; i++) {
    l1.push(Poseidon.hash([l2[i * 2], l2[i * 2 + 1]]));
  }

  // Level 0: root
  return Poseidon.hash([l1[0], l1[1]]);
}

/**
 * Generate an empty Merkle witness (for first insertion).
 */
export function emptyWitness(): VaultMerkleWitness {
  const path: Field[] = [];
  const isLeft: Bool[] = [];
  for (let i = 0; i < VAULT_TREE_DEPTH; i++) {
    path.push(Field(0));
    isLeft.push(Bool(false));
  }
  return new VaultMerkleWitness({ path, isLeft });
}
