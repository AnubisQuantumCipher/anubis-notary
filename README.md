# Anubis Notary

**Post-Quantum Secure Notary CLI with Formal Proofs and Blockchain Anchoring**

A command-line tool for cryptographic signing, timestamping, licensing, and multi-signature governance using NIST-approved post-quantum algorithms with optional blockchain anchoring.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Rust](https://img.shields.io/badge/rust-1.75+-orange.svg)](https://www.rust-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-Rocq%2FCoq-blue.svg)](https://coq.inria.fr/)
[![Mina](https://img.shields.io/badge/blockchain-Mina%20Protocol-9B4DCA.svg)](https://minaprotocol.com)
[![Starknet](https://img.shields.io/badge/blockchain-Starknet-EC796B.svg)](https://starknet.io)
[![Ztarknet](https://img.shields.io/badge/blockchain-Ztarknet-F4B728.svg)](https://ztarknet.cash)

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
- **Ztarknet** - Privacy-preserving anchoring with Zcash L1 settlement (~$0.0005/tx)
- **Pedersen Commitments** - Hide document hashes on-chain (ZK proofs of existence)
- **Batch Anchoring** - 8x cost savings with queue-based batch submissions
- **Native Rust Clients** - Fast RPC/GraphQL clients (no Node.js for reads)
- **Timestamping** - Immutable blockchain-backed timestamps
- **Proof Verification** - On-chain verification of document integrity

### Formal Verification
- **Rocq/Coq Proofs** - Mathematical proofs for critical properties
- **RefinedRust Specs** - Separation logic specifications
- **Iris Framework** - Advanced separation logic proofs

## Download

### One-Click Download (v0.4.0)

Pre-built binaries - no compilation required:

| Platform | Architecture | Download |
|----------|--------------|----------|
| **Linux** | x86_64 | [anubis-notary-linux-x86_64](https://github.com/AnubisQuantumCipher/anubis-notary/releases/download/v0.4.0/anubis-notary-linux-x86_64) |
| **Linux** | ARM64 | [anubis-notary-linux-aarch64](https://github.com/AnubisQuantumCipher/anubis-notary/releases/download/v0.4.0/anubis-notary-linux-aarch64) |
| **macOS** | Apple Silicon | [anubis-notary-darwin-aarch64](https://github.com/AnubisQuantumCipher/anubis-notary/releases/download/v0.4.0/anubis-notary-darwin-aarch64) |
| **macOS** | Intel | [anubis-notary-darwin-x86_64](https://github.com/AnubisQuantumCipher/anubis-notary/releases/download/v0.4.0/anubis-notary-darwin-x86_64) |
| **Windows** | x86_64 | [anubis-notary-windows-x86_64.exe](https://github.com/AnubisQuantumCipher/anubis-notary/releases/download/v0.4.0/anubis-notary-windows-x86_64.exe) |

[**View All Releases**](https://github.com/AnubisQuantumCipher/anubis-notary/releases) | [SHA256 Checksums](https://github.com/AnubisQuantumCipher/anubis-notary/releases/download/v0.4.0/SHA256SUMS.txt)

```bash
# Linux/macOS: Download, make executable, and run
curl -LO https://github.com/AnubisQuantumCipher/anubis-notary/releases/download/v0.4.0/anubis-notary-linux-x86_64
chmod +x anubis-notary-linux-x86_64
./anubis-notary-linux-x86_64 --version
# Output: anubis-notary 0.4.0

# Verify checksum (optional but recommended)
sha256sum anubis-notary-linux-x86_64
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

### Blockchain-Anchored Marriage System

Create legally binding, post-quantum secure marriage contracts on the blockchain with NFT wedding rings.

```bash
# Initialize marriage document (monogamy or polygamy template)
anubis-notary marriage init \
  --template monogamy \
  --parties "Alice,Bob" \
  --jurisdiction "US-CA" \
  -o marriage.json

# Each party signs with optional vows
anubis-notary marriage sign marriage.json --party 0 --vows "I take thee..."
anubis-notary marriage sign marriage.json --party 1 --vows "With this ring..."

# Verify all signatures
anubis-notary marriage verify marriage.json

# Create on-chain marriage with NFT rings
anubis-notary marriage create marriage.json --network mainnet --mint-rings

# Manage NFT rings
anubis-notary marriage rings supply --network mainnet
anubis-notary marriage rings show 1000 --network mainnet

# Divorce (burns rings automatically)
anubis-notary marriage divorce --marriage-id 1 --reason "Mutual consent"
```

**Features:**
- **Multi-party consent**: All parties must sign before blockchain creation
- **Personal vows**: SHA3-256 hashed vows stored on-chain in NFT metadata
- **Polygamy support**: Up to 10 parties (template: `polygamy`)
- **NFT wedding rings**: ERC721 tokens minted for each party
- **Automatic ring burning**: Rings burned on divorce
- **Post-quantum security**: ML-DSA-87 signatures

**Templates:** `simple`, `monogamy`, `polygamy`

### Single-User File Encryption (ML-KEM-1024)

Encrypt files for yourself or a single recipient using post-quantum ML-KEM-1024 key encapsulation with ChaCha20Poly1305 symmetric encryption.

```bash
# Generate ML-KEM-1024 keypair
anubis-notary private-batch keygen --out mykey
# Creates: mykey.mlkem.pub (public key) and mykey.mlkem.sec (secret key)

# Seal (encrypt) a file to a recipient's public key
anubis-notary seal document.pdf --recipient mykey.mlkem.pub --out document.sealed

# Unseal (decrypt) with your secret key
anubis-notary unseal document.sealed --secret-key mykey.mlkem.sec --out document-decrypted.pdf
```

**Sealed File Format:**
- 4 bytes: Magic ("ANU1")
- 1568 bytes: ML-KEM-1024 ciphertext (encapsulated shared secret)
- 12 bytes: ChaCha20Poly1305 nonce
- N bytes: Encrypted file + 16-byte authentication tag

**Security:** Only the holder of the corresponding secret key can unseal the file. Uses NIST Level 5 post-quantum security.

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

Anubis Notary supports [Starknet](https://starknet.io) for ultra-low-cost anchoring using ZK-STARK validity proofs and Poseidon hashing.

**Full documentation**: [docs/STARKNET.md](docs/STARKNET.md) | [docs/MAINNET.md](docs/MAINNET.md)

### Quick Start (3 Steps)

```bash
# 1. Install Starknet Foundry
curl -L https://raw.githubusercontent.com/foundry-rs/starknet-foundry/master/scripts/install.sh | sh

# 2. Create and fund an account
sncast account create --name myaccount --network sepolia
# Fund via https://starknet-faucet.vercel.app/
sncast account deploy --name myaccount --network sepolia

# 3. Anchor your documents!
export STARKNET_ACCOUNT_NAME="myaccount"
anubis-notary anchor starknet config --contract 0x04aa72f8dc65247389378621b6ff3e61852d56ddf571b522d03f02dc7f827606
anubis-notary attest document.pdf --receipt document.receipt
anubis-notary anchor starknet anchor document.receipt
```

**Cost**: ~$0.001 per anchor (~$0.000125 with batch anchoring)

### Batch Anchoring (8x Cost Savings)

```bash
# Queue receipts for batch submission
anubis-notary anchor starknet queue receipt1.receipt
anubis-notary anchor starknet queue receipt2.receipt

# Submit batch
anubis-notary anchor starknet flush
```

### Pre-Deployed Contracts

**NotaryOracle (Timestamping & Anchoring):**

| Network | Contract | Explorer |
|---------|----------|----------|
| **Mainnet** | `0x01dc1e7ebd8383c27e4620bb724409e2b9258d50ed33d60ce0fcaa4e169c93dc` | [View on Starkscan](https://starkscan.co/contract/0x01dc1e7ebd8383c27e4620bb724409e2b9258d50ed33d60ce0fcaa4e169c93dc) |
| **Sepolia** | `0x04aa72f8dc65247389378621b6ff3e61852d56ddf571b522d03f02dc7f827606` | [View on Voyager](https://sepolia.voyager.online/contract/0x04aa72f8dc65247389378621b6ff3e61852d56ddf571b522d03f02dc7f827606) |

**MarriageOracle (Marriage Contracts):**

| Network | Contract | Explorer |
|---------|----------|----------|
| **Mainnet** | `0x005d0a4cc5757e6d63dd6f7835c11a373af002e4c2603f040e2f5bf702a71ff8` | [View on Starkscan](https://starkscan.co/contract/0x005d0a4cc5757e6d63dd6f7835c11a373af002e4c2603f040e2f5bf702a71ff8) |
| **Sepolia** | `0x0457be1c094b09a3f27690388b8a4d70c908fec9b7de45bfb5d152488acd2181` | [View on Voyager](https://sepolia.voyager.online/contract/0x0457be1c094b09a3f27690388b8a4d70c908fec9b7de45bfb5d152488acd2181) |

**AnubisMarriageRing (NFT Wedding Rings):**

| Network | Contract | Explorer |
|---------|----------|----------|
| **Mainnet** | `0x00884842791e3542c42140d581edd7ab0327bf6ec276ca9d6201c9168c9f63d3` | [View on Starkscan](https://starkscan.co/contract/0x00884842791e3542c42140d581edd7ab0327bf6ec276ca9d6201c9168c9f63d3) |
| **Sepolia** | `0x07f579e725cbd8dbac8974245d05824f1024bc0c041d98e0a6133dbd5cdc7090` | [View on Voyager](https://sepolia.voyager.online/contract/0x07f579e725cbd8dbac8974245d05824f1024bc0c041d98e0a6133dbd5cdc7090) |

### Cost Comparison

| Chain | Single Anchor | Per Receipt (Batch) |
|-------|---------------|---------------------|
| **Starknet** | ~$0.001 | ~$0.000125 |
| **Mina** | ~$0.08 | ~$0.01 |

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `STARKNET_ACCOUNT_NAME` | sncast account name | `anubis-deployer` |
| `STARKNET_NETWORK` | `mainnet`, `sepolia`, `devnet` | `mainnet` |

## Ztarknet Privacy-Preserving Anchoring

Anubis Notary supports [Ztarknet](https://ztarknet.cash) for **privacy-preserving blockchain anchoring**. Ztarknet is a Starknet-compatible L2 that settles to Zcash L1, inheriting native shielded pool privacy.

### Privacy Modes

| Mode | Description | Use Case |
|------|-------------|----------|
| **Public** | Document hash visible on-chain | Open-source attestations, public records |
| **Selective** | Viewing key required to see hash | Regulatory compliance, audited documents |
| **Committed** | Only Pedersen commitment on-chain (ZK) | Trade secrets, NDAs, confidential contracts |

### Quick Start

```bash
# 1. Configure Ztarknet
anubis-notary anchor ztarknet config --network testnet --contract 0x01dc...

# 2. Anchor with privacy (committed mode - hash hidden)
anubis-notary attest document.pdf --receipt document.anb
anubis-notary anchor ztarknet anchor document.anb --mode committed

# Output:
# Commitment ID: 42
# Blinding Factor: 05b99557... (SAVE THIS!)

# 3. Later: Reveal if needed
anubis-notary anchor ztarknet reveal \
  --commitment-id 42 \
  --blinding 05b99557... \
  --original-hash <hash>

# 4. Or grant time-limited disclosure to auditor
anubis-notary anchor ztarknet disclose \
  --commitment-id 42 \
  --recipient 0x123... \
  --duration 86400  # 24 hours
```

### Commands

| Command | Description |
|---------|-------------|
| `config` | Configure Ztarknet connection |
| `anchor` | Anchor receipt with privacy mode |
| `verify` | Verify anchor or commitment |
| `reveal` | Reveal committed anchor (makes hash public) |
| `disclose` | Grant time-limited disclosure to auditor |
| `revoke` | Revoke a disclosure token |
| `commitment` | Get commitment info by ID |
| `time` | Get current blockchain time |
| `balance` | Get account balance |
| `info` | Show network info and privacy features |

### How Pedersen Commitments Work

```
Document Hash: H = SHA3-256(document)
Blinding Factor: r = random 32 bytes
Commitment: C = Poseidon(H, r)

On-chain: Only C is stored (hash H is hidden)
To verify: Prover reveals (H, r), verifier checks Poseidon(H, r) == C
```

**Properties:**
- **Binding**: Cannot change H after committing (computationally infeasible)
- **Hiding**: C reveals nothing about H (information-theoretic)
- **Cairo-compatible**: Uses Poseidon hash for Starknet/Ztarknet compatibility

### Cost Comparison

| Chain | Public Anchor | Committed Anchor | Reveal |
|-------|---------------|------------------|--------|
| **Ztarknet** | ~$0.0005 | ~$0.0008 | ~$0.0005 |
| **Starknet** | ~$0.001 | N/A | N/A |
| **Mina** | ~$0.08 | N/A | N/A |

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `ZTARKNET_ACCOUNT` | Account address for signing | - |
| `ZTARKNET_NETWORK` | `mainnet` or `testnet` | `mainnet` |

### Network Status

Ztarknet is currently in development. The CLI is ready and will work when the network launches.

| Network | RPC URL | L1 Settlement |
|---------|---------|---------------|
| **Mainnet** | `https://rpc.ztarknet.cash` | Zcash mainnet |
| **Testnet** | `https://testnet-rpc.ztarknet.cash` | Zcash testnet |

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
│       ├── ztarknet.rs        # Ztarknet privacy-preserving client
│       ├── anchor.rs          # Blockchain anchoring
│       └── rate_limit.rs      # API rate limiting
├── starknet-contract/         # Starknet/Ztarknet Cairo smart contracts
│   ├── Scarb.toml             # Cairo project config
│   └── src/
│       ├── lib.cairo          # NotaryOracle contract
│       └── privacy_oracle.cairo # PrivacyOracle for Ztarknet commitments
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
| [Starknet Anchoring](docs/STARKNET.md) | Complete Starknet blockchain anchoring guide |
| [Mainnet Deployment](docs/MAINNET.md) | Production deployment for Starknet & Mina |
| [Architecture Guide](docs/ARCHITECTURE.md) | System design, data flows, security model |
| [Deployment Guide](docs/DEPLOYMENT.md) | Server setup, Docker, CI/CD configuration |
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
