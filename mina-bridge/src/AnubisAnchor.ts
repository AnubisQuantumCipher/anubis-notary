/**
 * AnubisAnchor zkApp - Merkle Root Anchoring Contract for Mina Protocol
 */

import {
  SmartContract,
  state,
  State,
  method,
  Field,
  Permissions,
} from 'o1js';

/**
 * AnubisAnchor zkApp - Stores Merkle roots on-chain.
 */
export class AnubisAnchor extends SmartContract {
  @state(Field) merkleRoot = State<Field>();
  @state(Field) anchorCount = State<Field>();

  init() {
    super.init();
    this.account.permissions.set({
      ...Permissions.default(),
      editState: Permissions.proofOrSignature(),
    });
  }

  @method async anchorRoot(root: Field) {
    const count = this.anchorCount.getAndRequireEquals();
    this.merkleRoot.set(root);
    this.anchorCount.set(count.add(1));
  }
}

/**
 * Convert a hex string to a Field.
 */
export function hexToField(hexString: string): Field {
  const cleanHex = hexString.startsWith('0x') ? hexString.slice(2) : hexString;
  let value = BigInt('0x' + cleanHex);
  const mask = (BigInt(1) << BigInt(253)) - BigInt(1);
  return Field(value & mask);
}
