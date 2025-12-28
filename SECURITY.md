# Security Policy

## Cryptographic Dependencies Audit Status

This document provides an **honest assessment** of the security audit status for all
cryptographic dependencies used in Anubis Notary. We believe in transparency about
what has and has not been independently verified.

### Legend

| Status | Meaning |
|--------|---------|
| **Audited** | Independent third-party security audit completed |
| **Formally Verified** | Mathematical proofs of correctness using formal methods |
| **Production-Proven** | Widely deployed in production (millions of downloads, major users) |
| **NIST KAT Tested** | Passes official NIST Known Answer Test vectors |
| **Unaudited** | No independent audit; use with informed consent |

---

## Dependency Matrix

### AEAD (Authenticated Encryption)

| Component | Crate | Audit Status | Details |
|-----------|-------|--------------|---------|
| ChaCha20Poly1305 | `chacha20poly1305` | **Audited** | NCC Group audit (Feb 2020), funded by MobileCoin. No significant vulnerabilities found. [Report](https://research.nccgroup.com/2020/02/26/public-report-rustcrypto-aes-gcm-and-chacha20poly1305-implementation-review/) |
| XChaCha20Poly1305 | `chacha20poly1305` | **Audited** | Same audit as above |
| Ascon-128a | Custom | **Unaudited** | Custom implementation with RefinedRust annotations. Uses `subtle` crate for constant-time operations. Not independently audited. |

### Hash Functions

| Component | Crate | Audit Status | Details |
|-----------|-------|--------------|---------|
| SHA3-256/512 | `sha3` (RustCrypto) | **Production-Proven** | 3.7M+ downloads/month. Extensive community review. NIST test vector validated. Not formally audited but widely trusted. |
| SHAKE128/256 | `sha3` (RustCrypto) | **Production-Proven** | Same as above |
| Custom Keccak | Custom | **Unaudited** | Available via `sha3-custom` feature. Has RefinedRust annotations but not independently audited. Use `sha3-audited` feature (default) for production. |

### Post-Quantum Cryptography

| Component | Crate | Audit Status | Details |
|-----------|-------|--------------|---------|
| ML-KEM-1024 | `libcrux-ml-kem` | **Formally Verified** | Cryspen's libcrux verified using hax/F* toolchain. Proven properties: panic freedom, functional correctness, secret independence (constant-time). [Verification Report](https://cryspen.com/post/ml-kem-verification/) |
| ML-DSA-87 | `libcrux-ml-dsa` | **Formally Verified** | Cryspen's libcrux verified using hax/F* toolchain. Same verification methodology as ML-KEM: panic freedom, functional correctness, secret independence. FIPS 204 compliant. [GitHub](https://github.com/cryspen/libcrux) |

### Serialization

| Component | Crate | Audit Status | Details |
|-----------|-------|--------------|---------|
| CBOR | `ciborium` | **Production-Proven** | Used by Google (coset/COSE), AWS (aws-smithy-types), Android platform, Criterion (132M+ downloads). RFC 8949 compliant. |

### Supporting Cryptography

| Component | Crate | Audit Status | Details |
|-----------|-------|--------------|---------|
| Constant-time ops | `subtle` | **Audited** | Part of the dalek-cryptography ecosystem. Audited alongside curve25519-dalek. |
| Memory zeroization | `zeroize` | **Production-Proven** | RustCrypto standard. Widely deployed. |

---

## Risk Assessment

### High Confidence (Recommended for Production)

1. **ChaCha20Poly1305** - NCC Group audited, no findings
2. **ML-KEM-1024** - Formally verified (Cryspen libcrux) for panic freedom, correctness, and constant-time execution
3. **ML-DSA-87** - Formally verified (Cryspen libcrux) using same hax/F* methodology as ML-KEM
4. **SHA3 (via `sha3` crate)** - Massive adoption, extensive review

### Medium Confidence (Acceptable with Monitoring)

1. **CBOR (ciborium)** - Production-proven but not formally audited
2. **Constant-time operations (subtle)** - Audited as part of dalek ecosystem

### Lower Confidence (Use with Informed Consent)

1. **Custom Ascon-128a** - Has RefinedRust annotations but unaudited
   - Mitigation: Uses `subtle` for constant-time comparisons
   - Mitigation: Feature-gated; ChaCha20 is the default
   - Recommendation: Use `chacha` feature (default) for production

---

## Feature Flag Recommendations

For production use, we recommend the default features:

```toml
[dependencies]
anubis_core = { version = "0.1", features = ["chacha", "sha3-audited"] }
```

This ensures you use:
- ChaCha20Poly1305 (NCC Group audited)
- RustCrypto sha3 (production-proven, 3.7M downloads/month)

Avoid these features in production unless you understand the risks:
- `ascon` - Custom Ascon-128a (unaudited)

---

## Formal Verification Status

### RefinedRust Annotations

The codebase contains RefinedRust annotations for formal verification.
These annotations specify:
- Refinement types with safety invariants
- Separation logic ownership predicates
- Functional correctness specifications
- Loop invariants for termination

**Important**: While annotations exist, full verification with RefinedRust/Coq/Iris requires:
1. Running the RefinedRust extraction toolchain
2. Discharging proof obligations in Coq
3. Auditing the trusted computing base

Current status: **Annotations written, proofs in progress**

### Coq/Iris Specifications

Formal specifications exist in `specs/refinedrust/theories/`:
- `keccak_spec.v` - Keccak permutation correctness
- `ascon_spec.v` - Ascon AEAD security properties
- `mldsa_spec.v` - ML-DSA signature properties
- `cbor_spec.v` - CBOR encoding canonicity

---

## Supported Versions

| Version | Supported |
|---------|-----------|
| 1.0.x   | Yes       |
| < 1.0   | No        |

## Reporting a Vulnerability

If you discover a security vulnerability in Anubis Notary, please report it responsibly:

1. **Do NOT** open a public GitHub issue for security vulnerabilities
2. Send details to: security@anubis-notary.io (or create private security advisory)
3. Include:
   - Description of the vulnerability
   - Steps to reproduce
   - Affected versions
   - Potential impact
   - Any suggested fixes (optional)

### Response Timeline

- **Initial response**: Within 48 hours
- **Status update**: Within 7 days
- **Fix timeline**: Depends on severity (critical: < 7 days, high: < 30 days)

## Security Measures

### Cryptographic Choices

| Component | Algorithm | Security Level | Audit Status |
|-----------|-----------|----------------|--------------|
| Signatures | ML-DSA-87 | NIST Level 5 (post-quantum) | **Formally Verified** |
| Key Exchange | ML-KEM-1024 | NIST Level 5 (post-quantum) | **Formally Verified** |
| Hash | SHA3-256 | 128-bit collision resistance | Production-Proven |
| XOF | SHAKE256 | Adjustable security | Production-Proven |
| AEAD (default) | ChaCha20Poly1305 | 256-bit key | **Audited (NCC Group)** |
| AEAD (optional) | Ascon-128a | 128-bit security | Unaudited |

### Constant-Time Discipline

The following operations are implemented with constant-time primitives via `subtle` crate:

- `ct_eq` - byte comparison
- `ct_select` - conditional selection
- `ct_lt_u64` - unsigned comparison
- Tag verification in AEAD
- Signature verification in ML-DSA

### Key Protection

- Secret keys are zeroized on drop using `SecretBytes` wrapper
- Keystores are encrypted with AEAD after Argon2id KDF
- KDF parameters enforce minimum security floors

### Nonce Safety

- Nonces are deterministically derived from `(counter, entry_id, domain)`
- Injectivity is formally proven for bounded inputs
- No random nonce generation (eliminates RNG failure modes)

## Known Limitations

### Not Protected Against

- **Physical side channels**: Power analysis, EM emanation, cache timing at CPU level
- **Compiler bugs**: We trust rustc + LLVM
- **OS/hardware vulnerabilities**: Ring-0 attacks, firmware bugs
- **Cryptographic breaks**: If ML-DSA, Keccak, or Ascon are broken
- **Social engineering**: User credential theft

### Validated Via (Not Proven)

- **Cryptographic hardness**: Validated through NIST KAT vectors
- **Reference implementation cross-checks**: Compared against official test vectors
- **Optional timing analysis**: dudect or similar for gross outliers

## Secure Usage Guidelines

### Key Management

1. **Backup recovery phrases** using split knowledge (printed, stored separately)
2. **Never export secret keys** - only `key export --pub` is supported
3. **Rotate keys periodically** - use `key rotate` command
4. **Use strong passphrases** for keystore encryption

### File Operations

1. All file writes are **atomic** (temp file + rename)
2. Receipts are **detached** from original files
3. Original files are **never modified** during signing

### License Verification

1. Always verify licenses **before** granting access
2. Check expiration with `license verify --json`
3. Validate feature flags against required features

## Audit History

| Date | Auditor | Scope | Status |
|------|---------|-------|--------|
| 2024-12-24 | - | Upgraded ML-DSA to formally verified libcrux-ml-dsa | Complete |
| 2024-12-24 | - | Added audited dependencies | Complete |
| TBD | - | Full codebase audit | Pending |

## Disclosure Policy

We follow responsible disclosure:

1. Report received and acknowledged
2. Vulnerability confirmed and severity assessed
3. Fix developed and tested
4. Security advisory prepared
5. Fix released with coordinated disclosure
6. Public advisory published after users have time to update

---

## References

1. [NCC Group ChaCha20Poly1305 Audit](https://research.nccgroup.com/2020/02/26/public-report-rustcrypto-aes-gcm-and-chacha20poly1305-implementation-review/)
2. [Cryspen ML-KEM Verification](https://cryspen.com/post/ml-kem-verification/)
3. [Cryspen libcrux (ML-KEM & ML-DSA)](https://github.com/cryspen/libcrux) - Formally verified cryptographic library
4. [NIST FIPS 203 (ML-KEM)](https://csrc.nist.gov/pubs/fips/203/final)
5. [NIST FIPS 204 (ML-DSA)](https://csrc.nist.gov/pubs/fips/204/final)
6. [RFC 8949 (CBOR)](https://www.rfc-editor.org/rfc/rfc8949.html)
