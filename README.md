# Anubis Notary

A CLI-only notary and licensing tool with post-quantum cryptography.

## Verification Status

| Component | Verified By | Status |
|-----------|-------------|--------|
| ML-DSA-87 signatures | Cryspen (libcrux) | ✓ Formally verified (hax/F*) |
| ML-KEM-1024 encapsulation | Cryspen (libcrux) | ✓ Formally verified (hax/F*) |
| ChaCha20Poly1305 | Cryspen (libcrux) | ✓ Formally verified (hax/F*) |
| Our wrapper code | Us | ✗ NOT verified (tested only) |
| Keccak/SHA3 | Us | ✗ NOT verified (NIST KAT tested) |
| CBOR codec | Us | ✗ NOT verified (tested only) |

**Note**: RefinedRust-style specifications exist as documentation but have NOT been machine-checked. See [VERIFICATION.md](VERIFICATION.md) for honest details.

## Features

- **Receipts & Signatures** for any file/directory (ML-DSA-87 post-quantum)
- **Deterministic, auditable timestamps** (local, RFC3161, or offline anchor receipts)
- **Licenses** (CBOR tokens) - offline-verifiable for your paid tools
- **Optional anchoring** to public logs (batch/Merkle) for monetization

## Non-Negotiables

- **Verified cryptographic primitives**: ML-DSA-87/ML-KEM from formally verified libcrux
- **PQ by default**: ML-DSA-87 signatures; HKDF(SHAKE256); AEAD = ChaCha20Poly1305
- **Deterministic nonces** derived from `(header_counter, entry_id, domain)`
- **CLI only**, works fully offline; macOS/Linux friendly

## Installation

```bash
cargo install --path crates/anubis_cli
```

## Quick Start

```bash
# Initialize keystore
anubis-notary key init --keystore ~/.anubis

# Sign a file
anubis-notary sign document.pdf --out document.sig

# Verify a signature
anubis-notary verify document.pdf --sig document.sig --json

# Create attestation receipt
anubis-notary attest ./project --recursive --receipt project.receipt

# Issue a license
anubis-notary license issue --product myapp --user user@example.com \
    --expiry 2025-12-31 --features "pro,team5" --out user.lic

# Verify a license
anubis-notary license verify --license user.lic --json
```

## CLI Reference

### Key Management

```bash
anubis-notary key init     # Initialize new keystore
anubis-notary key show     # Show public key
anubis-notary key rotate   # Rotate keys
```

### Signing & Verification

```bash
anubis-notary sign FILE --out FILE.sig
anubis-notary verify FILE --sig SIG --json
anubis-notary attest PATH --recursive --receipt out.receipt
anubis-notary check RECEIPT FILE --json
```

### Licenses

```bash
anubis-notary license issue --product X --user U --expiry YYYY-MM-DD \
                            --features "offline,team5" --out U.lic
anubis-notary license verify --license U.lic --json
anubis-notary license list --keystore ~/.anubis
```

### Anchoring (Optional, Paid)

```bash
anubis-notary anchor queue add out.receipt
anubis-notary anchor submit --provider btc --batch 512
anubis-notary anchor status <id> --json
```

## Cryptographic Profile

| Component | Algorithm | Standard |
|-----------|-----------|----------|
| Hash/XOF | SHA3-256, SHAKE256 | FIPS 202 |
| Signatures | ML-DSA-87 | FIPS 204 |
| KDF | Argon2id + HKDF(SHAKE256) | RFC 9106 |
| AEAD | Ascon-128a | NIST LWC |
| Nonces | Deterministic derivation | Injective |

## Project Structure

```
anubis-notary/
  crates/
    anubis_core/     # no_std, no I/O, core cryptographic library
      ct/            # constant-time helpers
      bytes/         # LE load/store, zeroize types
      keccak/        # SHA3/SHAKE (our implementation)
      kdf/           # Argon2id + HKDF
      aead/          # ChaCha20Poly1305 (libcrux wrapper)
      nonce/         # deterministic nonce derivation
      cbor/          # canonical CBOR codec
      license/       # license schema
      receipt/       # receipt schema
      merkle/        # batch anchoring tree
      mldsa/         # ML-DSA-87 (libcrux wrapper)
    anubis_io/       # FS, time sources, RFC3161 client
    anubis_cli/      # clap-based CLI
  specs/
    refinedrust/     # Aspirational specifications (NOT verified)
      theories/      # Coq specifications (unlinked to code)
      annotations/   # RefinedRust annotations (documentation only)
```

## Formal Verification Status

**Honest assessment**: Most of our code is NOT formally verified.

**What IS verified** (by Cryspen, not us):
- ML-DSA-87 via libcrux-ml-dsa (hax/F* proofs)
- ML-KEM-1024 via libcrux-ml-kem (hax/F* proofs)
- ChaCha20Poly1305 via libcrux (hax/F* proofs)

**What is NOT verified** (our code):
- 135 Verification Conditions are DOCUMENTED, not proven
- RefinedRust annotations exist but no proofs link them to code
- Specifications in `specs/refinedrust/theories/` are aspirational

See [VERIFICATION.md](VERIFICATION.md) for detailed honest assessment.

## Building

```bash
# Build all crates
cargo build --all

# Run tests
cargo test --all

# Run KAT tests
cargo test -p anubis_core --release -- keccak aead mldsa cbor

# Build documentation
cargo doc --all --no-deps
```

## Specifications (Not Proofs)

```bash
cd specs/refinedrust
make theories    # Build Coq specifications (NOT linked to Rust code)
```

**Note**: These specifications compile but do NOT verify the Rust code. There is no RefinedRust toolchain integration.

## Security

See [SECURITY.md](SECURITY.md) for security policy and reporting vulnerabilities.

See [THREATMODEL.md](THREATMODEL.md) for the threat model.

## License

Licensed under Apache-2.0 OR MIT at your option.

## References

- [RefinedRust Paper](https://plv.mpi-sws.org/refinedrust/)
- [FIPS 202: SHA-3 Standard](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf)
- [FIPS 204: ML-DSA Standard](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf)
- [Ascon AEAD](https://ascon.iaik.tugraz.at/)
- [RFC 9106: Argon2](https://www.rfc-editor.org/rfc/rfc9106.html)
