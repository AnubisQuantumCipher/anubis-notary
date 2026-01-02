# Anubis Notary

**Post-Quantum Secure Notary CLI with Formal Proofs and Blockchain Anchoring**

A command-line tool for cryptographic signing, timestamping, licensing, and multi-signature governance using NIST-approved post-quantum algorithms with optional Mina Protocol blockchain anchoring.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Rust](https://img.shields.io/badge/rust-1.75+-orange.svg)](https://www.rust-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-Rocq%2FCoq-blue.svg)](https://coq.inria.fr/)
[![Mina](https://img.shields.io/badge/blockchain-Mina%20Protocol-9B4DCA.svg)](https://minaprotocol.com)
[![Starknet](https://img.shields.io/badge/blockchain-Starknet-EC796B.svg)](https://starknet.io)

## Features

### Core Cryptography
- **ML-DSA-87** (FIPS 204) - Post-quantum digital signatures (NIST Level 5)
- **ML-KEM-1024** (FIPS 203) - Post-quantum key encapsulation & private batches (NIST Level 5)
- **SHA3-256/SHAKE256** (FIPS 202) - Cryptographic hashing
- **ChaCha20Poly1305** (RFC 8439) - Authenticated encryption
- **Argon2id** (RFC 9106) - Memory-hard key derivation (1-4 GiB)
- **Shamir Secret Sharing** - Information-theoretic threshold cryptography
- **CBOR** (RFC 8949) - Canonical binary encoding

### Privacy-Preserving Collaborative Anchoring
- **Forward-Secure Batches** - Ephemeral ML-KEM keys protect past batches
- **Threshold Decryption** - t-of-n parties required to unlock encrypted receipts
- **Merkle Proofs** - Verifiable proofs work on encrypted data
- **Zeroization** - All session keys securely cleared from memory

### Blockchain Integration
- **Mina Protocol** - zkApp-based Merkle root anchoring on mainnet (~$0.08/tx)
- **Starknet** - STARK-private batch anchoring with Cairo contracts (~$0.001/tx)
- **Batch Anchoring** - 8x cost savings with queue-based batch submissions
- **Native Rust Clients** - Fast RPC/GraphQL clients (no Node.js for reads)
- **Timestamping** - Immutable blockchain-backed timestamps
- **Proof Verification** - On-chain verification of document integrity

### Formal Verification
- **Rocq/Coq Proofs** - Mathematical proofs for critical properties
- **RefinedRust Specs** - Separation logic specifications
- **Iris Framework** - Advanced separation logic proofs

## Download

### One-Click Download (v0.3.6)

Pre-built binaries - no compilation required:

| Platform | Download | Size |
|----------|----------|------|
| **Linux x86_64** | [**anubis-notary-linux-x86_64**](https://github.com/AnubisQuantumCipher/anubis-notary/releases/download/v0.3.6/anubis-notary-linux-x86_64) | ~5 MB |
| **macOS ARM64** (Apple Silicon) | [**anubis-notary-darwin-aarch64**](https://github.com/AnubisQuantumCipher/anubis-notary/releases/download/v0.3.6/anubis-notary-darwin-aarch64) | ~4 MB |

[**View All Releases**](https://github.com/AnubisQuantumCipher/anubis-notary/releases)

```bash
# After downloading, make executable and run:
chmod +x anubis-notary-*
./anubis-notary --version
# Output: anubis-notary 0.3.6
./anubis-notary --help
```

---

## Quick Start

### Build from Source

```bash
# Clone repository
git clone https://github.com/AnubisQuantumCipher/anubis-notary.git
cd anubis-notary

# Build release binary
cargo build --release

# Run
./target/release/anubis-notary --help
```

## Usage

### Initialize Keystore

```bash
# Create a new keystore with ML-DSA-87 signing key
anubis-notary key init

# Low-memory mode (1 GiB instead of 4 GiB Argon2id)
anubis-notary key init --low-memory

# Show public key
anubis-notary key show
```

### Sign & Verify Files

```bash
# Sign a file
anubis-notary sign document.pdf -o document.sig

# Verify signature
anubis-notary verify --sig document.sig document.pdf
```

### Create Timestamped Attestations

```bash
# Create receipt with timestamp
anubis-notary attest document.pdf --receipt document.receipt

# Verify receipt
anubis-notary check document.receipt document.pdf
```

### Streaming Operations (Large Files)

```bash
# Hash large files efficiently
anubis-notary stream hash large-file.iso

# Stream sign
anubis-notary stream sign large-file.iso -o large-file.sig

# Stream verify
anubis-notary stream verify --sig large-file.sig large-file.iso
```

### Software Licensing

```bash
# Issue a license
anubis-notary license issue \
  --product "MyApp" \
  --user "user@example.com" \
  --expiry "2025-12-31" \
  --features "pro,enterprise" \
  -o license.bin

# Verify license
anubis-notary license verify --license license.bin
```

### Multi-Signature Governance

```bash
# Initialize 2-of-3 multisig
anubis-notary multisig init \
  --threshold 2 \
  --signers signer1.pub,signer2.pub,signer3.pub \
  -o multisig.config

# Create proposal
anubis-notary multisig propose \
  --config multisig.config \
  --proposal-type authorize-action \
  --data <hex-data> \
  -o proposal.bin

# Sign proposal
anubis-notary multisig sign --config multisig.config --proposal proposal.bin

# Execute when threshold met
anubis-notary multisig execute --config multisig.config --proposal proposal.bin
```

### Key Rotation

```bash
# Rotate keys (archives old key)
anubis-notary key rotate
```

## Privacy-Preserving Collaborative Anchoring (ML-KEM-1024)

Anubis Notary supports **forward-secure, threshold-decryption batch anchoring** using ML-KEM-1024 for ephemeral key encapsulation and Shamir secret sharing. This allows multiple parties to collaboratively control access to encrypted receipts.

### How It Works

```
+---------------------------------------------------------------------+
|                    Private Batch Creation                            |
+---------------------------------------------------------------------+
| 1. Generate ephemeral session key (32 bytes)                        |
| 2. Encrypt each receipt leaf with ChaCha20Poly1305                  |
| 3. Build Merkle tree over encrypted leaf hashes                     |
| 4. Split session key using Shamir (t-of-n)                          |
| 5. For each recipient:                                              |
|    - ML-KEM-1024 encapsulate -> ephemeral shared secret             |
|    - Encrypt Shamir share with shared secret                        |
| 6. Anchor Merkle root to blockchain/log                             |
| 7. Zeroize session key                                              |
+---------------------------------------------------------------------+
```

### Generate Recipient Keypairs

```bash
# Generate ML-KEM-1024 keypairs for each recipient
anubis-notary private-batch keygen -o alice
anubis-notary private-batch keygen -o bob
anubis-notary private-batch keygen -o carol

# Creates: alice.mlkem.pub, alice.mlkem.sec (and same for bob, carol)
```

### Create Private Batch

```bash
# Create a 2-of-3 threshold encrypted batch
anubis-notary private-batch create receipt1.anb receipt2.anb \
    -r alice.mlkem.pub \
    -r bob.mlkem.pub \
    -r carol.mlkem.pub \
    -t 2 \
    -o batch.private

# View batch information
anubis-notary private-batch info batch.private
```

### Collaborative Decryption

```bash
# Each recipient decrypts their share (run by each party)
anubis-notary private-batch decrypt-share batch.private \
    -k alice.mlkem.sec -o alice.share

anubis-notary private-batch decrypt-share batch.private \
    -k carol.mlkem.sec -o carol.share

# Coordinator combines shares (only needs t shares)
anubis-notary private-batch combine batch.private \
    -s alice.share -s carol.share \
    -o decrypted/
```

### Security Properties

| Property | Description |
|----------|-------------|
| **Forward Secrecy** | Ephemeral ML-KEM keys ensure past batches remain secure even if long-term keys are compromised |
| **Privacy** | Encrypted leaves hide receipt contents while Merkle proofs still work |
| **Threshold Access** | t-of-n recipients must collaborate to decrypt |
| **Information-Theoretic Security** | t-1 shares reveal absolutely nothing (Shamir) |
| **Post-Quantum Security** | ML-KEM-1024 provides NIST Level 5 security against quantum attacks |
| **Zeroization** | All session keys and shares are securely cleared from memory |

### Use Cases

- **Multi-party escrow** - Legal documents requiring multiple parties to unlock
- **Corporate governance** - Board approval for sensitive documents
- **Dead man's switch** - Time-locked inheritance with trusted parties
- **Regulatory compliance** - Audit trails with controlled disclosure
- **Collaborative research** - Shared access to confidential data

## Mina Blockchain Anchoring

Anubis Notary integrates with [Mina Protocol](https://minaprotocol.com) for immutable blockchain timestamping. The official zkApp is **already deployed on mainnet** - you just need a Mina wallet with ~0.1 MINA to anchor documents.

### Quick Start (3 Steps)

```bash
# 1. One-time setup (installs Mina bridge)
anubis-notary anchor mina setup

# 2. Get a Mina wallet (or use existing)
anubis-notary anchor mina keygen
# Fund with ~0.1 MINA from any exchange

# 3. Anchor your documents!
export MINA_PRIVATE_KEY="your-key-from-step-2"
anubis-notary attest document.pdf --receipt document.receipt
anubis-notary anchor mina anchor document.receipt
```

**Cost:** ~0.1 MINA per anchor (~0.0125 with batch anchoring)

### Batch Anchoring (8x Cost Savings)

Queue multiple receipts and submit in a single transaction:

```bash
# Add receipts to the batch queue
anubis-notary anchor mina queue receipt1.receipt
anubis-notary anchor mina queue receipt2.receipt
# ... add up to 8 receipts

# Check queue status
anubis-notary anchor mina queue-status

# Submit batch when ready (auto-submits at 8, or use --force)
anubis-notary anchor mina flush

# Force submit with fewer than 8 receipts
anubis-notary anchor mina flush --force
```

### Detailed Usage

```bash
# Show configuration (pre-configured for mainnet)
anubis-notary anchor mina config --show

# Create a receipt for a document
anubis-notary attest document.pdf --receipt document.receipt

# Anchor the receipt to blockchain
export MINA_PRIVATE_KEY="your-mina-private-key"
anubis-notary anchor mina anchor document.receipt

# Get current blockchain time
anubis-notary anchor mina time

# Check your wallet balance
anubis-notary anchor mina balance
```

### Official zkApp (Pre-Configured)

The AnubisAnchor zkApp is deployed on Mina mainnet and configured by default:

| Property | Value |
|----------|-------|
| **zkApp Address** | `B62qnHLXkWxxJ4NwKgT8zwJ2JKZ8nymgrUyK7R7k5fm7ELPRgeEH8E3` |
| **Network** | Mina Mainnet |
| **Anchor Fee** | ~0.1 MINA |
| **Deployment TX** | [View on Minascan](https://minascan.io/mainnet/tx/5JvH2AvfsQDwXu41yAWJHosgadAtzEcqrRCeRYraSu43nriKoKe7) |

### Environment Variables

| Variable | Description | Required |
|----------|-------------|----------|
| `MINA_PRIVATE_KEY` | Your Mina wallet private key (Base58) | **Yes** |
| `MINA_NETWORK` | Network: `mainnet`, `devnet`, or `local` | No (default: mainnet) |
| `MINA_ZKAPP_ADDRESS` | Custom zkApp address | No (default: official) |
| `MINA_FEE` | Transaction fee in nanomina | No (default: 100000000) |

## Starknet Blockchain Anchoring

Anubis Notary also supports [Starknet](https://starknet.io) for ultra-low-cost anchoring using ZK-STARK validity proofs and Poseidon hashing.

### Quick Start

```bash
# Show network info and costs
anubis-notary anchor starknet info

# Generate a Starknet keypair
anubis-notary anchor starknet keygen

# Configure contract (after deployment)
anubis-notary anchor starknet config --contract 0x...

# Anchor a receipt
anubis-notary anchor starknet anchor document.receipt
```

### Batch Anchoring (8x Cost Savings)

```bash
# Queue receipts for batch submission
anubis-notary anchor starknet queue receipt1.receipt
anubis-notary anchor starknet queue receipt2.receipt
# ... add up to 8 receipts

# Check queue status
anubis-notary anchor starknet queue-status

# Submit batch
anubis-notary anchor starknet flush
```

### Cost Comparison

| Chain | Single Anchor | Batch (8 receipts) | Per Receipt |
|-------|---------------|---------------------|-------------|
| **Starknet** | ~$0.001 | ~$0.001 | ~$0.000125 |
| **Mina** | ~$0.08 | ~$0.08 | ~$0.01 |

### Cairo Smart Contract

The NotaryOracle Cairo contract is included in `starknet-contract/`:

```bash
# Build with Scarb
cd starknet-contract
scarb build

# Deploy (requires Starknet CLI)
starknet declare --contract target/dev/anubis_notary_oracle_NotaryOracle.json
starknet deploy --class-hash <HASH> --inputs <OWNER>
```

### Environment Variables

| Variable | Description | Required |
|----------|-------------|----------|
| `STARKNET_PRIVATE_KEY` | Account private key (hex) | For transactions |
| `STARKNET_ACCOUNT` | Account address (hex) | For balance queries |

## Environment Variables

For CI/CD pipelines and automated workflows:

| Variable | Description |
|----------|-------------|
| `ANUBIS_HOME` | Keystore directory (default: `~/.anubis`) |
| `ANUBIS_PASSWORD` | Password for non-interactive operations |
| `ANUBIS_PASSWORD_FILE` | Path to file containing password |

Example CI/CD usage:

```bash
export ANUBIS_HOME=/path/to/keystore
export ANUBIS_PASSWORD="secure-password"

# Non-interactive key initialization
anubis-notary key init --low-memory

# Sign files in automation
anubis-notary sign document.pdf -o document.sig
```

See [docs/MULTISIG.md](docs/MULTISIG.md) for multi-signature governance workflows.

## Formal Verification

This project includes Rocq/Coq proofs for critical cryptographic properties.

### Run Proofs with Docker (Recommended - Zero Setup)

```bash
# One-command proof verification (requires Docker installed)
docker run -it ghcr.io/anubisquantumcipher/anubis-proofs

# Inside container, verify proofs:
make all          # Build everything
make core         # Core crypto proofs
make refinedrust  # Separation logic specs
```

Or build locally:

```bash
./docker/run-proofs.sh
```

### Build Proofs Manually (Without Docker)

Requires Rocq/Coq 8.19+ with Iris:

```bash
opam install coq-iris coq-stdpp coq-equations
cd proofs
make all
```

### What's Proven

- **Nonce injectivity** - Different inputs produce different nonces
- **CBOR totality** - All valid inputs parse correctly
- **Merkle tree correctness** - Proof verification is sound
- **AEAD correctness** - Decrypt(Encrypt(m)) = m
- **Signature properties** - Verify(Sign(m)) = true
- **Constant-time comparisons** - No timing side-channels

## Project Structure

```
anubis-notary/
├── crates/
│   ├── anubis_core/           # Core cryptographic primitives
│   │   ├── aead/              # ChaCha20Poly1305 authenticated encryption
│   │   ├── cbor/              # CBOR encoding/decoding (RFC 8949)
│   │   ├── ct/                # Constant-time operations
│   │   ├── kdf/               # Argon2id key derivation (RFC 9106)
│   │   ├── keccak/            # SHA3-256/SHAKE256 (FIPS 202)
│   │   ├── merkle/            # Merkle tree construction & proofs
│   │   ├── mldsa/             # ML-DSA-87 signatures (FIPS 204)
│   │   ├── mlkem/             # ML-KEM-1024 key encapsulation (FIPS 203)
│   │   ├── private_batch/     # Privacy-preserving collaborative anchoring
│   │   │   ├── encrypted_leaf.rs    # ChaCha20Poly1305 encrypted leaves
│   │   │   ├── key_envelope.rs      # ML-KEM key share envelopes
│   │   │   ├── private_batch.rs     # Batch orchestration
│   │   │   └── collaborative.rs     # Threshold decryption
│   │   ├── recovery/          # Shamir secret sharing
│   │   ├── license/           # Software licensing
│   │   ├── multisig/          # Multi-signature governance
│   │   ├── receipt/           # Timestamped attestation receipts
│   │   ├── nonce/             # Deterministic nonce derivation
│   │   ├── streaming/         # Large file streaming operations
│   │   └── hsm/               # Hardware security module support
│   ├── anubis_cli/            # Command-line interface
│   │   └── src/main.rs        # CLI commands & subcommands
│   └── anubis_io/             # I/O operations
│       ├── lib.rs             # Keystore management
│       ├── seal.rs            # Sealed file encryption
│       ├── mina.rs            # Mina Protocol client
│       ├── mina_graphql.rs    # Pure Rust GraphQL client (10-20x faster)
│       ├── batch_queue.rs     # Batch anchoring queue system
│       ├── starknet.rs        # Starknet Protocol client
│       ├── anchor.rs          # Blockchain anchoring
│       └── rate_limit.rs      # API rate limiting
├── starknet-contract/         # Starknet Cairo smart contract
│   ├── Scarb.toml             # Cairo project config
│   └── src/lib.cairo          # NotaryOracle contract
├── mina-zkapp/                # Mina zkApp (TypeScript/o1js)
│   └── src/AnubisAnchor.ts    # On-chain anchor contract
├── mina-bridge/               # Node.js bridge for Rust CLI
│   ├── src/                   # Bridge source
│   │   ├── AnubisAnchor.ts    # Single anchor contract
│   │   └── AnubisBatchVault.ts # Batch vault contract (8x savings)
│   └── mina-bridge.js         # Compiled bridge script
├── proofs/                    # Rocq/Coq formal proofs
│   └── theories/              # Proof files (.v)
├── specs/                     # RefinedRust specifications
├── fuzz/                      # Fuzzing targets
├── benches/                   # Performance benchmarks
├── docker/                    # Docker setup for proofs
└── docs/                      # Documentation
```

## Security

### Cryptographic Standards

| Algorithm | Standard | Security Level |
|-----------|----------|----------------|
| ML-DSA-87 | FIPS 204 | NIST Level 5 (256-bit) |
| ML-KEM-1024 | FIPS 203 | NIST Level 5 (256-bit) |
| SHA3-256 | FIPS 202 | 256-bit |
| SHAKE256 | FIPS 202 | Arbitrary |
| ChaCha20Poly1305 | RFC 8439 | 256-bit |
| Argon2id | RFC 9106 | Memory-hard |

### Security Features

- **Constant-time operations** for secret data
- **Zeroization** of all sensitive memory
- **Memory-hard KDF** (Argon2id with 1-4 GiB)
- **Atomic file operations** (fsync + rename)
- **Formal proofs** for critical properties
- **Blockchain anchoring** for tamper-evident timestamps

### Reporting Vulnerabilities

Please report security issues to: **sic.tau@pm.me**

All reports are treated with strict confidentiality. We aim to respond within 48 hours.

## Development

### Run Tests

```bash
cargo test --all
```

### Run Clippy

```bash
cargo clippy --all -- -D warnings
```

### Run Fuzzing

```bash
cd fuzz
cargo +nightly fuzz run fuzz_cbor
```

### Run Benchmarks

```bash
cargo bench
```

### Mina Bridge Development

```bash
cd mina-bridge
npm install
npm run build
```

## Documentation

| Document | Description |
|----------|-------------|
| [Architecture Guide](docs/ARCHITECTURE.md) | System design, data flows, security model |
| [Deployment Guide](docs/DEPLOYMENT.md) | Server setup, Docker, CI/CD, Mina configuration |
| [Troubleshooting](docs/TROUBLESHOOTING.md) | Common issues and solutions |
| [Multi-Signature Guide](docs/MULTISIG.md) | Governance and multi-party signing |

## License

MIT License - see [LICENSE](LICENSE)

## Contributing

Contributions welcome! Please read [CONTRIBUTING.md](CONTRIBUTING.md) first.

### Supporting Development

This project is developed independently for advancing post-quantum cryptography research and open-source security tooling. If you find this work valuable, consider supporting continued development:

| Network | Address |
|---------|---------|
| **Bitcoin (BTC)** | `bc1qum8pp56ahlkrvcurrfmryyg0hxtay5jzfrlx9s` |
| **Cardano (ADA)** | `addr1qxx5zwas6p53hnmnweua2ngdqx4x52ugatyqatcrn3yfjvmm99tf343tw7ldxg746f87cll4gfq5nc0dcm7f5f8mwq0qfwsl93` |
| **Monero (XMR)** | `43SQ1nkaFybf8zQ1JFG2xphKxkf3QUZeEQ6q1rgrrL1g6PSYFqzJ8XEEzNTGEAVpjh9pSF4hEihkt3w2yHobJbMy496H19D` |
| **Mina (MINA)** | `B62qidUYaNWRhTYdxx9djDBxMKSwqL9487MjX1x59bfGmeq4wq5sA1d` |

Contributions support:
- Ongoing security audits and formal verification efforts
- Post-quantum cryptography research and testing infrastructure
- Blockchain integration development and zkApp maintenance
- Documentation, tooling, and community resources

## Acknowledgments

- [libcrux](https://github.com/cryspen/libcrux) - ML-DSA and ML-KEM implementations
- [Rocq/Coq](https://coq.inria.fr/) - Proof assistant
- [Iris](https://iris-project.org/) - Separation logic framework
- [o1js](https://github.com/o1-labs/o1js) - Mina Protocol zkApp framework
- [Mina Protocol](https://minaprotocol.com) - Blockchain infrastructure
