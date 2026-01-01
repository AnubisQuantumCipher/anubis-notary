/**
 * AnubisAnchor zkApp - Merkle Root Anchoring Contract for Mina Protocol
 *
 * This zkApp provides on-chain timestamping and anchoring for Anubis Notary.
 * It stores Merkle roots on the Mina blockchain, enabling verifiable
 * proof-of-existence without revealing the underlying data.
 */
var __decorate = (this && this.__decorate) || function (decorators, target, key, desc) {
    var c = arguments.length, r = c < 3 ? target : desc === null ? desc = Object.getOwnPropertyDescriptor(target, key) : desc, d;
    if (typeof Reflect === "object" && typeof Reflect.decorate === "function") r = Reflect.decorate(decorators, target, key, desc);
    else for (var i = decorators.length - 1; i >= 0; i--) if (d = decorators[i]) r = (c < 3 ? d(r) : c > 3 ? d(target, key, r) : d(target, key)) || r;
    return c > 3 && r && Object.defineProperty(target, key, r), r;
};
var __metadata = (this && this.__metadata) || function (k, v) {
    if (typeof Reflect === "object" && typeof Reflect.metadata === "function") return Reflect.metadata(k, v);
};
import { SmartContract, state, State, method, Field, Permissions, } from 'o1js';
/**
 * AnubisAnchor zkApp - Stores Merkle roots on-chain.
 */
export class AnubisAnchor extends SmartContract {
    constructor() {
        super(...arguments);
        this.merkleRoot = State();
    }
    init() {
        super.init();
        this.merkleRoot.set(Field(0));
        this.account.permissions.set({
            ...Permissions.default(),
            editState: Permissions.proofOrSignature(),
        });
    }
    async anchorRoot(root) {
        this.merkleRoot.set(root);
    }
}
__decorate([
    state(Field),
    __metadata("design:type", Object)
], AnubisAnchor.prototype, "merkleRoot", void 0);
__decorate([
    method,
    __metadata("design:type", Function),
    __metadata("design:paramtypes", [Field]),
    __metadata("design:returntype", Promise)
], AnubisAnchor.prototype, "anchorRoot", null);
/**
 * Convert a hex string to a Field.
 */
export function hexToField(hexString) {
    const cleanHex = hexString.startsWith('0x') ? hexString.slice(2) : hexString;
    let value = BigInt('0x' + cleanHex);
    const mask = (BigInt(1) << BigInt(253)) - BigInt(1);
    return Field(value & mask);
}
//# sourceMappingURL=AnubisAnchor.js.map