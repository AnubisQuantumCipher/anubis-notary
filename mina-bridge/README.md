# Anubis Mina Bridge

TypeScript/o1js integration for anchoring Anubis Notary receipts to the Mina Protocol blockchain.

## Overview

The Mina Bridge provides:
- **AnubisAnchor zkApp** - Smart contract for storing Merkle roots on-chain
- **mina-bridge.js** - Node.js subprocess bridge for the Rust CLI
- **Mainnet deployment** - Production zkApp on Mina mainnet

## Architecture

```
┌──────────────────┐     JSON/stdin/stdout     ┌──────────────────┐
│   Rust CLI       │ ◄───────────────────────► │   mina-bridge.js │
│  (anubis-notary) │                           │     (Node.js)    │
└──────────────────┘                           └────────┬─────────┘
                                                        │
                                                        │ o1js
                                                        ▼
                                               ┌──────────────────┐
                                               │   Mina Network   │
                                               │   (mainnet/dev)  │
                                               └──────────────────┘
```

## zkApp Contract

The `AnubisAnchor` zkApp stores Merkle roots on-chain:

```typescript
class AnubisAnchor extends SmartContract {
  @state(Field) merkleRoot = State<Field>();

  @method async anchorRoot(root: Field) {
    this.merkleRoot.set(root);
  }
}
```

## Deployed Contract

| Property | Value |
|----------|-------|
| **Network** | Mina Mainnet |
| **zkApp Address** | `B62qmddzKWzKQmNYsxxJRU6kTHtKxBaCwECEGUtdsz1DCTTK57XFceW` |
| **Deployment TX** | `5JuEBor5pLcfd2moQwFmACfscAn8JXdjYe1Nndjaqou8mfmug3WK` |

## Bridge Protocol

The bridge communicates via JSON over stdin/stdout:

### Commands

| Command | Description |
|---------|-------------|
| `anchor` | Anchor a Merkle root to the blockchain |
| `verify` | Verify a root exists on-chain |
| `time` | Get current blockchain time and height |
| `balance` | Get wallet balance |
| `keygen` | Generate a new Mina keypair |
| `deploy` | Deploy the zkApp contract |
| `networkinfo` | Get network configuration |
| `shutdown` | Gracefully shutdown the bridge |

### Example: Anchor

Request:
```json
{"cmd": "anchor", "root": "0123456789abcdef..."}
```

Response:
```json
{"ok": true, "tx": "5Jv...", "address": "B62q...", "timestamp": 1704067200}
```

## Development

### Build

```bash
npm install
npm run build
```

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `MINA_NETWORK` | `mainnet`, `devnet`, or `local` | `devnet` |
| `MINA_PRIVATE_KEY` | Wallet private key (Base58) | - |
| `MINA_ZKAPP_ADDRESS` | zkApp contract address | - |
| `MINA_FEE` | Transaction fee (nanomina) | `100000000` |
| `MINA_DEBUG` | Enable debug logging | `0` |

### Testing

```bash
# Start bridge
MINA_DEBUG=1 node mina-bridge.js

# Send commands via stdin
{"cmd": "time"}
{"cmd": "networkinfo"}
```

## License

MIT
