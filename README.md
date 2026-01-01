# Anubis Notary

**Post-Quantum Secure Notary CLI with Formal Proofs and Blockchain Anchoring**

A command-line tool for cryptographic signing, timestamping, licensing, and multi-signature governance using NIST-approved post-quantum algorithms with optional Mina Protocol blockchain anchoring.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Rust](https://img.shields.io/badge/rust-1.75+-orange.svg)](https://www.rust-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-Rocq%2FCoq-blue.svg)](https://coq.inria.fr/)
[![Mina](https://img.shields.io/badge/blockchain-Mina%20Protocol-9B4DCA.svg)](https://minaprotocol.com)

## Features

### Core Cryptography
- **ML-DSA-87** (FIPS 204) - Post-quantum digital signatures (NIST Level 5)
- **ML-KEM-1024** (FIPS 203) - Post-quantum key encapsulation (NIST Level 5)
- **SHA3-256/SHAKE256** (FIPS 202) - Cryptographic hashing
- **ChaCha20Poly1305** (RFC 8439) - Authenticated encryption
- **Argon2id** (RFC 9106) - Memory-hard key derivation (1-4 GiB)
- **CBOR** (RFC 8949) - Canonical binary encoding

### Blockchain Integration
- **Mina Protocol** - zkApp-based Merkle root anchoring on mainnet
- **Timestamping** - Immutable blockchain-backed timestamps
- **Proof Verification** - On-chain verification of document integrity

### Formal Verification
- **Rocq/Coq Proofs** - Mathematical proofs for critical properties
- **RefinedRust Specs** - Separation logic specifications
- **Iris Framework** - Advanced separation logic proofs

## Quick Start

### One-Click Download (Recommended)

Download pre-built binaries from [Releases](https://github.com/AnubisQuantumCipher/anubis-notary/releases):

| Platform | Download |
|----------|----------|
| Linux (x86_64) | `anubis-notary-linux-x86_64` |
| macOS (Apple Silicon) | `anubis-notary-darwin-aarch64` |
| macOS (Intel) | `anubis-notary-darwin-x86_64` |

```bash
# Make executable (Linux/macOS)
chmod +x anubis-notary-*
./anubis-notary --help
```

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

## Mina Blockchain Anchoring

Anubis Notary integrates with [Mina Protocol](https://minaprotocol.com) for immutable blockchain timestamping using a deployed zkApp smart contract.

### Setup Mina Integration

```bash
# Initialize Mina bridge (downloads o1js, compiles zkApp)
anubis-notary anchor mina setup

# Generate a Mina keypair for transactions
anubis-notary anchor mina keygen

# Show network information and costs
anubis-notary anchor mina info
```

### Configure Mina

```bash
# Set zkApp address and network
anubis-notary anchor mina config \
  --zkapp "B62qmEptuweVvBJbv6dLBXC7QoVJqyUuQ8dkB4PZdjUyrxFUWhSnXBg" \
  --network mainnet

# Show current configuration
anubis-notary anchor mina config --show
```

### Anchor Documents to Blockchain

```bash
# Create a receipt first
anubis-notary attest document.pdf --receipt document.receipt

# Anchor receipt's Merkle root to Mina blockchain
export MINA_PRIVATE_KEY="your-mina-private-key"
anubis-notary anchor mina anchor document.receipt

# Get current blockchain time
anubis-notary anchor mina time
```

### Deployed zkApp (Mainnet)

The AnubisAnchor zkApp is deployed on Mina mainnet:

| Property | Value |
|----------|-------|
| **zkApp Address** | `B62qmEptuweVvBJbv6dLBXC7QoVJqyUuQ8dkB4PZdjUyrxFUWhSnXBg` |
| **Network** | Mina Mainnet |
| **Deployment TX** | `5JvLVr1VrwarXoUFQcb3LWhZbGUTcDAFzMF8xxbBNK8VSLVQ6C8S` |
| **Explorer** | [View on Minascan](https://minascan.io/mainnet/tx/5JvLVr1VrwarXoUFQcb3LWhZbGUTcDAFzMF8xxbBNK8VSLVQ6C8S) |

### Mina Environment Variables

| Variable | Description |
|----------|-------------|
| `MINA_PRIVATE_KEY` | Your Mina wallet private key (Base58) |
| `MINA_NETWORK` | Network: `mainnet`, `devnet`, or `local` |
| `MINA_ZKAPP_ADDRESS` | zkApp contract address |
| `MINA_FEE` | Transaction fee in nanomina (default: 100000000) |

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
│   ├── anubis_core/     # Core cryptographic primitives
│   ├── anubis_cli/      # Command-line interface
│   └── anubis_io/       # I/O operations (keystore, seal)
├── mina-bridge/         # Mina Protocol integration (TypeScript/o1js)
│   ├── src/             # zkApp source (AnubisAnchor.ts)
│   └── mina-bridge.js   # Node.js bridge for Rust CLI
├── proofs/              # Rocq/Coq formal proofs
│   └── theories/        # Proof files (.v)
├── specs/               # RefinedRust specifications
├── fuzz/                # Fuzzing targets
├── benches/             # Performance benchmarks
├── docker/              # Docker setup for proofs
└── docs/                # Documentation
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
| **Mina (MINA)** | `B62qpxzahqwoTULNHKegn4ExZ95XpprhjRMQGDPDhknkovTr45Migte` |

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
