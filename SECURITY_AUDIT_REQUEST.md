# Security Audit Request - v0.3.4

## Audit Scope

This PR requests a comprehensive security audit of the entire Anubis Notary codebase using CodeRabbit Pro's advanced features.

## Areas to Review

### 1. Core Cryptography (`crates/anubis_core/`)
- ML-DSA-87 signature implementation (FIPS 204)
- ML-KEM-1024 key encapsulation (FIPS 203)
- SHA3-256/SHAKE256 hashing (FIPS 202)
- ChaCha20Poly1305 AEAD (RFC 8439)
- Argon2id KDF (RFC 9106)
- Shamir Secret Sharing
- CBOR encoding/decoding

### 2. Private Batch Module (`crates/anubis_core/src/private_batch/`)
- Ephemeral key-share encryption
- ML-KEM key envelope implementation
- Encrypted leaf encryption/decryption
- Collaborative decryption coordinator
- Threshold cryptography implementation

### 3. I/O Operations (`crates/anubis_io/`)
- Keystore management
- Mina Protocol GraphQL client
- Batch queue system
- Sealed file encryption

### 4. CLI Security (`crates/anubis_cli/`)
- Input validation
- Password handling
- File operations

### 5. Mina Bridge (`mina-bridge/`)
- zkApp implementation
- Node.js bridge security

### 6. Formal Proofs (`proofs/`)
- Coq/Rocq proof completeness
- Specification correctness

## Security Checks Required

- [ ] Constant-time operations for secrets
- [ ] Zeroization on all code paths
- [ ] No timing side-channels
- [ ] Proper error handling
- [ ] No unwrap() on crypto ops
- [ ] Memory safety in unsafe code
- [ ] Input validation
- [ ] FIPS/RFC compliance

## CodeRabbit Configuration

Using `.coderabbit.yaml` with:
- Maximum scrutiny profile
- All static analysis tools enabled
- Custom security checks
- Path-specific instructions

@coderabbitai full review
