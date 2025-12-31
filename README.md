# Anubis Notary

**Post-Quantum Secure Notary CLI with Formal Proofs**

A command-line tool for cryptographic signing, timestamping, licensing, and multi-signature governance using NIST-approved post-quantum algorithms.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Rust](https://img.shields.io/badge/rust-1.75+-orange.svg)](https://www.rust-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-Rocq%2FCoq-blue.svg)](https://coq.inria.fr/)

## Features

- **ML-DSA-87** (FIPS 204) - Post-quantum digital signatures
- **ML-KEM-1024** (FIPS 203) - Post-quantum key encapsulation
- **SHA3-256/SHAKE256** (FIPS 202) - Cryptographic hashing
- **ChaCha20Poly1305** (RFC 8439) - Authenticated encryption
- **Argon2id** (RFC 9106) - Memory-hard key derivation (1-4 GiB)
- **CBOR** (RFC 8949) - Canonical binary encoding
- **Formal Proofs** - Rocq/Coq proofs for critical properties

## Quick Start

### One-Click Download (Recommended)

Download pre-built binaries from [Releases](https://github.com/AnubisQuantumCipher/anubis-notary/releases):

| Platform | Download |
|----------|----------|
| Linux (x86_64) | `anubis-notary-linux-x86_64` |
| macOS (Intel) | `anubis-notary-darwin-x86_64` |
| macOS (Apple Silicon) | `anubis-notary-darwin-aarch64` |
| Windows | `anubis-notary-windows-x86_64.exe` |

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

## Formal Verification

This project includes Rocq/Coq proofs for critical cryptographic properties.

### Run Proofs with Docker (Recommended)

```bash
# One-command proof verification
docker run -it ghcr.io/anubisquantumcipher/anubis-proofs make prove

# Or build locally
cd docker
./run-proofs.sh
```

### Build Proofs Manually

Requires Rocq 9.0+ with coq-iris, coq-stdpp:

```bash
cd proofs
make all
```

### What's Proven

- **Nonce injectivity** - Different inputs produce different nonces
- **CBOR totality** - All valid inputs parse correctly
- **Merkle tree correctness** - Proof verification is sound
- **AEAD correctness** - Decrypt(Encrypt(m)) = m
- **Signature properties** - Verify(Sign(m)) = true

## Project Structure

```
anubis-notary/
├── crates/
│   ├── anubis_core/     # Core cryptographic primitives
│   ├── anubis_cli/      # Command-line interface
│   └── anubis_io/       # I/O operations (keystore, seal)
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
- **No unsafe code** without SAFETY comments

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

## License

MIT License - see [LICENSE](LICENSE)

## Contributing

Contributions welcome! Please read [CONTRIBUTING.md](CONTRIBUTING.md) first.

### Supporting Development

This project is developed independently for advancing post-quantum cryptography research and open-source security tooling. If you find this work valuable for your research, testing, or production use, consider supporting continued development:

| Network | Address |
|---------|---------|
| **Bitcoin (BTC)** | `bc1qum8pp56ahlkrvcurrfmryyg0hxtay5jzfrlx9s` |
| **Cardano (ADA)** | `addr1qxx5zwas6p53hnmnweua2ngdqx4x52ugatyqatcrn3yfjvmm99tf343tw7ldxg746f87cll4gfq5nc0dcm7f5f8mwq0qfwsl93` |
| **Monero (XMR)** | `43SQ1nkaFybf8zQ1JFG2xphKxkf3QUZeEQ6q1rgrrL1g6PSYFqzJ8XEEzNTGEAVpjh9pSF4hEihkt3w2yHobJbMy496H19D` |

Contributions support:
- Ongoing security audits and formal verification efforts
- Post-quantum cryptography research and testing infrastructure
- Documentation, tooling, and community resources
- Hardware security module (HSM) integration development

## Acknowledgments

- [libcrux](https://github.com/cryspen/libcrux) - ML-DSA and ML-KEM implementations
- [Rocq/Coq](https://coq.inria.fr/) - Proof assistant
- [Iris](https://iris-project.org/) - Separation logic framework
