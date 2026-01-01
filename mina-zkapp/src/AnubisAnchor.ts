/**
 * AnubisAnchor zkApp - Merkle Root Anchoring Contract for Mina Protocol
 *
 * This zkApp provides on-chain timestamping and anchoring for Anubis Notary.
 * It stores Merkle roots on the Mina blockchain, enabling verifiable
 * proof-of-existence without revealing the underlying data.
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

  init() {
    super.init();
    this.merkleRoot.set(Field(0));
    this.account.permissions.set({
      ...Permissions.default(),
      editState: Permissions.proofOrSignature(),
    });
  }

  @method
  async anchorRoot(root: Field) {
    this.merkleRoot.set(root);
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
