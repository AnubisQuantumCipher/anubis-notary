# Anubis Notary Architecture

## Overview

Anubis Notary is a post-quantum secure notary CLI built with a layered architecture that separates cryptographic primitives, I/O operations, and user interface concerns.

```
┌─────────────────────────────────────────────────────────────────┐
│                         anubis_cli                               │
│                    (Command-Line Interface)                      │
├─────────────────────────────────────────────────────────────────┤
│                         anubis_io                                │
│              (Keystore, Seal, Mina, Rate Limiting)               │
├─────────────────────────────────────────────────────────────────┤
│                        anubis_core                               │
│                  (Cryptographic Primitives)                      │
└─────────────────────────────────────────────────────────────────┘
```

## Crate Hierarchy

### anubis_core

The foundational cryptographic library. All primitives are formally verified or use verified implementations (libcrux).

| Module | Purpose | Standard |
|--------|---------|----------|
| `mldsa` | Post-quantum digital signatures | FIPS 204 (ML-DSA-87) |
| `mlkem` | Post-quantum key encapsulation | FIPS 203 (ML-KEM-1024) |
| `keccak` | SHA3-256, SHAKE256 hashing | FIPS 202 |
| `aead` | Authenticated encryption | RFC 8439 (ChaCha20Poly1305) |
| `kdf` | Memory-hard key derivation | RFC 9106 (Argon2id) |
| `merkle` | Merkle tree construction | - |
| `cbor` | Canonical binary encoding | RFC 8949 |
| `ct` | Constant-time operations | - |
| `nonce` | Deterministic nonce derivation | - |
| `recovery` | Shamir secret sharing | - |
| `private_batch` | ML-KEM encrypted batch anchoring | - |
| `receipt` | Timestamped attestations | - |
| `license` | Software licensing | - |
| `multisig` | Multi-signature governance | - |
| `streaming` | Large file operations | - |
| `hsm` | Hardware security module support | PKCS#11 |

### anubis_io

I/O operations and external integrations.

| Module | Purpose |
|--------|---------|
| `lib.rs` | Keystore management (create, load, rotate) |
| `seal.rs` | Sealed file encryption with ML-KEM |
| `mina.rs` | Mina Protocol client |
| `anchor.rs` | Blockchain anchoring abstraction |
| `rate_limit.rs` | API rate limiting |

### anubis_cli

User-facing command-line interface. Parses arguments, orchestrates operations, handles errors.

## Data Flow

### Signing a Document

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│  User    │───▶│  CLI     │───▶│  IO      │───▶│  Core    │
│  Input   │    │  Parse   │    │  Load    │    │  Sign    │
│          │    │  Args    │    │  Keystore│    │  ML-DSA  │
└──────────┘    └──────────┘    └──────────┘    └──────────┘
                                                      │
                                                      ▼
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│  Output  │◀───│  CLI     │◀───│  IO      │◀───│  CBOR    │
│  .sig    │    │  Write   │    │  Write   │    │  Encode  │
│  File    │    │  Result  │    │  File    │    │  Sig     │
└──────────┘    └──────────┘    └──────────┘    └──────────┘
```

### Private Batch Creation

```
┌─────────────────────────────────────────────────────────────────┐
│                    Private Batch Flow                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────┐                                                     │
│  │ Receipts│──┐                                                  │
│  └─────────┘  │                                                  │
│               ▼                                                  │
│         ┌──────────┐    ┌──────────┐    ┌──────────┐            │
│         │ Generate │───▶│ Encrypt  │───▶│ Build    │            │
│         │ Session  │    │ Leaves   │    │ Merkle   │            │
│         │ Key (32B)│    │ ChaCha20 │    │ Tree     │            │
│         └──────────┘    └──────────┘    └──────────┘            │
│               │                               │                  │
│               ▼                               ▼                  │
│         ┌──────────┐                    ┌──────────┐            │
│         │ Shamir   │                    │ Merkle   │            │
│         │ Split    │                    │ Root     │            │
│         │ (t-of-n) │                    │ (Anchor) │            │
│         └──────────┘                    └──────────┘            │
│               │                                                  │
│               ▼                                                  │
│  ┌─────────────────────────────────────────────────────┐        │
│  │           For Each Recipient (ML-KEM-1024)          │        │
│  ├─────────────────────────────────────────────────────┤        │
│  │  ┌──────────┐    ┌──────────┐    ┌──────────┐      │        │
│  │  │ Load     │───▶│ Encaps   │───▶│ Encrypt  │      │        │
│  │  │ Pub Key  │    │ Shared   │    │ Share    │      │        │
│  │  │          │    │ Secret   │    │ ChaCha20 │      │        │
│  │  └──────────┘    └──────────┘    └──────────┘      │        │
│  └─────────────────────────────────────────────────────┘        │
│               │                                                  │
│               ▼                                                  │
│         ┌──────────┐                                            │
│         │ Zeroize  │                                            │
│         │ Session  │                                            │
│         │ Key      │                                            │
│         └──────────┘                                            │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Mina Blockchain Anchoring

```
┌─────────────────────────────────────────────────────────────────┐
│                    Mina Anchor Flow                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐      │
│  │ Receipt │───▶│ Extract │───▶│ Rust    │───▶│ Node.js │      │
│  │ File    │    │ SHA3    │    │ CLI     │    │ Bridge  │      │
│  │         │    │ Digest  │    │         │    │         │      │
│  └─────────┘    └─────────┘    └─────────┘    └─────────┘      │
│                                                     │            │
│                                                     ▼            │
│                                               ┌─────────┐        │
│                                               │ o1js    │        │
│                                               │ zkApp   │        │
│                                               │ SDK     │        │
│                                               └─────────┘        │
│                                                     │            │
│                                                     ▼            │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐      │
│  │ TX Hash │◀───│ Parse   │◀───│ JSON    │◀───│ Mina    │      │
│  │ Output  │    │ Response│    │ Response│    │ Network │      │
│  │         │    │         │    │         │    │         │      │
│  └─────────┘    └─────────┘    └─────────┘    └─────────┘      │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## Keystore Structure

```
~/.anubis/                    # Default ANUBIS_HOME
├── key.sealed               # Encrypted ML-DSA-87 private key
├── key.pub                  # ML-DSA-87 public key (2592 bytes)
├── mina-config.json         # Mina configuration
└── mina-bridge/             # Mina bridge installation
    ├── mina-bridge.js       # Bridge script
    ├── build/               # Compiled zkApp
    └── node_modules/        # Dependencies
```

### Key Sealing

Private keys are encrypted using:

1. **Argon2id** (1-4 GiB memory) derives 32-byte key from password
2. **ChaCha20Poly1305** encrypts the ML-DSA-87 secret key
3. **CBOR** encodes the sealed structure

```
Sealed Key = CBOR({
  salt: [u8; 32],           # Argon2id salt
  nonce: [u8; 12],          # ChaCha20 nonce
  ciphertext: [u8; N],      # Encrypted secret key
  memory_kib: u32,          # Argon2id memory (1048576 or 4194304)
})
```

## Receipt Format

Receipts are CBOR-encoded attestations:

```
Receipt = CBOR({
  alg: "ML-DSA-87",         # Signature algorithm
  hash: "sha3-256",         # Hash algorithm
  digest: [u8; 32],         # SHA3-256 of document
  created: u64,             # Unix timestamp (seconds)
  sig: [u8; 4627],          # ML-DSA-87 signature
  anchor: AnchorType,       # Optional blockchain anchor
})

AnchorType = None | Local { timestamp } | Mina { zkapp, tx, block, time }
```

## Private Batch Format

```
PrivateBatch = CBOR({
  batch_id: [u8; 32],       # Unique batch identifier
  merkle_root: [u8; 32],    # Root of encrypted leaf tree
  created_at: u64,          # Creation timestamp
  leaves: [EncryptedLeaf],  # Encrypted receipt leaves
  key_envelope: KeyShareEnvelope,  # ML-KEM encrypted shares
})

EncryptedLeaf = {
  index: u32,               # Leaf position
  commitment: [u8; 32],     # SHA3-256(plaintext) for verification
  nonce: [u8; 12],          # ChaCha20 nonce
  ciphertext: [u8; N],      # Encrypted receipt
}

KeyShareEnvelope = {
  batch_id: [u8; 32],
  threshold: u8,            # Required shares (t)
  total_shares: u8,         # Total shares (n)
  recipient_shares: [RecipientKeyShare],
}

RecipientKeyShare = {
  recipient_fingerprint: [u8; 32],  # SHA3-256(ML-KEM pubkey)
  kem_ciphertext: [u8; 1568],       # ML-KEM-1024 ciphertext
  encrypted_share: [u8; N],          # ChaCha20 encrypted Shamir share
  nonce: [u8; 12],
}
```

## Security Model

### Threat Model

| Threat | Mitigation |
|--------|------------|
| Quantum computer attacks | ML-DSA-87, ML-KEM-1024 (NIST Level 5) |
| Password brute force | Argon2id (1-4 GiB memory-hard) |
| Timing attacks | Constant-time comparisons (ct module) |
| Memory disclosure | Zeroization on drop |
| Replay attacks | Timestamps, nonces |
| Tampering | Digital signatures, Merkle proofs |

### Trust Boundaries

```
┌─────────────────────────────────────────────────────────────────┐
│                      UNTRUSTED ZONE                              │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │  Network, Filesystem, User Input                          │  │
│  └───────────────────────────────────────────────────────────┘  │
├─────────────────────────────────────────────────────────────────┤
│                      TRUST BOUNDARY                              │
├─────────────────────────────────────────────────────────────────┤
│                      TRUSTED ZONE                                │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │  Cryptographic Operations (anubis_core)                   │  │
│  │  - All inputs validated before processing                 │  │
│  │  - Constant-time operations for secrets                   │  │
│  │  - Zeroization of sensitive data                          │  │
│  └───────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

## Dependencies

### Cryptographic Libraries

| Library | Purpose | Verification |
|---------|---------|--------------|
| libcrux | ML-DSA, ML-KEM, ChaCha20, SHA3 | hax/F* formal proofs |
| argon2 | Key derivation | Reference implementation |
| ciborium | CBOR encoding | - |

### Blockchain

| Library | Purpose |
|---------|---------|
| o1js | Mina Protocol zkApp SDK |
| ureq | HTTP client for Mina RPC |

## Performance Characteristics

| Operation | Time | Memory |
|-----------|------|--------|
| Key generation | ~100ms | 1-4 GiB (Argon2id) |
| Sign (ML-DSA-87) | ~5ms | ~10 MB |
| Verify (ML-DSA-87) | ~2ms | ~5 MB |
| ML-KEM encapsulate | ~1ms | ~2 MB |
| ML-KEM decapsulate | ~1ms | ~2 MB |
| SHA3-256 (1 MB) | ~5ms | ~1 KB |
| Mina anchor (first) | 40-120s | ~500 MB (zkApp proof) |
| Mina anchor (cached) | ~1s | ~100 MB (cached artifacts) |

## Mina Bridge Caching

The Mina bridge uses o1js's built-in caching to dramatically improve performance on subsequent runs.

### How Caching Works

```
┌──────────────────────────────────────────────────────────────────────┐
│                    zkApp Compilation Cache                            │
├──────────────────────────────────────────────────────────────────────┤
│                                                                       │
│  First Run (~175s):                                                   │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐       │
│  │ Parse    │───▶│ Compile  │───▶│ Generate │───▶│ Save to  │       │
│  │ Contract │    │ Circuits │    │ Prover   │    │ ~/.cache │       │
│  │          │    │          │    │ Keys     │    │ /o1js    │       │
│  └──────────┘    └──────────┘    └──────────┘    └──────────┘       │
│                                                                       │
│  Cached Run (~1s):                                                    │
│  ┌──────────┐    ┌──────────┐                                        │
│  │ Load     │───▶│ Ready    │                                        │
│  │ Cache    │    │ to Prove │                                        │
│  │          │    │          │                                        │
│  └──────────┘    └──────────┘                                        │
│                                                                       │
└──────────────────────────────────────────────────────────────────────┘
```

### Cache Location

| OS | Cache Directory |
|----|-----------------|
| Linux/macOS | `~/.cache/o1js/` |
| Windows | `%LOCALAPPDATA%/o1js/` |

### Cache Contents

The o1js cache stores:
- **SRS (Structured Reference String)**: Shared across all o1js projects
- **Circuit artifacts**: Compiled constraint systems
- **Prover keys**: Keys for generating proofs
- **Verification keys**: Keys for verifying proofs

### Performance Impact

| Scenario | Time | Improvement |
|----------|------|-------------|
| First run (no cache) | ~175s | - |
| Cached run | ~1s | **175x faster** |
| After circuit change | ~175s | Auto-invalidates |

### Environment Variables

```bash
# Force recompilation (bypass cache)
export MINA_FORCE_RECOMPILE=1

# Enable debug logging
export MINA_DEBUG=1
```

### Clearing Cache

```bash
# Clear o1js cache (forces recompilation)
rm -rf ~/.cache/o1js

# Next anchor command will recompile (~175s)
anubis-notary anchor mina anchor receipt.anb
```

## Extension Points

### Adding New Algorithms

1. Create module in `anubis_core/src/<algorithm>/`
2. Implement traits in `mod.rs`
3. Add to `lib.rs` exports
4. Update CLI in `anubis_cli/src/main.rs`

### Adding New Anchor Backends

1. Implement client in `anubis_io/src/<backend>.rs`
2. Add variant to `AnchorType` enum
3. Update CLI anchor subcommand
