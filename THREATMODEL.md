# Threat Model

## Overview

Anubis Notary is a CLI-based notary and licensing tool designed for:
- File/directory attestation with post-quantum signatures
- Offline-verifiable license tokens
- Optional timestamp anchoring to public logs

This document describes the security properties, threat boundaries, and mitigations.

## Security Objectives

### Primary Goals

| Objective | Description | Mechanism |
|-----------|-------------|-----------|
| **Integrity** | Receipts/licenses unforgeable without secret key | ML-DSA-87 signatures |
| **Authenticity** | Receipts prove origin from specific key holder | Signature verification |
| **Non-repudiation** | Signer cannot deny creating valid signature | Deterministic signatures |
| **Freshness** | Timestamps are verifiable | Local/RFC3161/OTS anchors |

### Secondary Goals

| Objective | Description | Mechanism |
|-----------|-------------|-----------|
| **Key Confidentiality** | Secret keys protected at rest | Argon2id + AEAD encryption |
| **Nonce Safety** | No nonce reuse | Deterministic derivation with injectivity proof |
| **Side-Channel Resistance** | Timing-independent operations | Constant-time primitives |

## Threat Actors

### In-Scope Threats

| Actor | Capability | Motivation |
|-------|------------|------------|
| **Remote Attacker** | Network access, malformed inputs | Forge signatures, bypass licenses |
| **Local Attacker** | File system access | Steal keys, tamper with receipts |
| **Quantum Adversary** | Future quantum computer | Break classical signatures |

### Out-of-Scope Threats

| Actor | Reason |
|-------|--------|
| **Physical Attacker** | Power/EM analysis beyond CT discipline |
| **Compromised OS** | Ring-0 access bypasses all user-space protections |
| **Insider Threat** | Key holder acting maliciously |
| **Nation-State** | Compiler/hardware implants |

## Attack Surface

### Input Vectors

| Vector | Format | Validation |
|--------|--------|------------|
| Files to sign | Arbitrary bytes | Hashed, not parsed |
| Receipts | CBOR | Total decoder, canonical form |
| Licenses | CBOR | Total decoder, schema validation |
| CLI arguments | UTF-8 strings | Clap parsing |
| Keystore | Encrypted CBOR | AEAD + Argon2id |

### Trust Boundaries

```
┌─────────────────────────────────────────────────────────┐
│                    Untrusted Zone                        │
│  - Network (RFC3161, anchor providers)                  │
│  - User input (CLI, files)                              │
│  - Malformed CBOR data                                  │
└───────────────────────┬─────────────────────────────────┘
                        │ Validation
                        ▼
┌─────────────────────────────────────────────────────────┐
│                    anubis_io                             │
│  - File I/O (path validation)                           │
│  - Time sources (untrusted, recorded)                   │
│  - Network clients (TLS, timeout)                       │
└───────────────────────┬─────────────────────────────────┘
                        │ Sanitized data
                        ▼
┌─────────────────────────────────────────────────────────┐
│                    anubis_core (Verified)               │
│  - CBOR parsing (total decoders)                        │
│  - Cryptographic operations (CT, proven bounds)         │
│  - Schema validation (type-safe)                        │
└─────────────────────────────────────────────────────────┘
```

## Threat Analysis

### T1: Signature Forgery

**Threat**: Attacker creates valid receipt/license without secret key.

**Mitigations**:
- ML-DSA-87 provides NIST Level 5 security (post-quantum)
- 4627-byte signatures with 256-bit security margin
- Deterministic signing eliminates RNG failure modes

**Residual Risk**: Cryptographic break of ML-DSA (unlikely before 2040+).

### T2: Malformed Input Exploitation

**Threat**: Attacker sends crafted CBOR to cause crash/UB.

**Mitigations**:
- Total decoders: every input maps to `Ok(v)` or `Err(e)`
- Formally verified bounds checking (135 VCs proven)
- No unsafe code in parsing paths
- Closed error enums (no catch-all handlers)

**Residual Risk**: Compiler bugs generating incorrect code.

### T3: Key Extraction

**Threat**: Attacker steals secret key from keystore.

**Mitigations**:
- Argon2id KDF with floors: m >= 1 GiB, t >= 3, p >= 1
- Ascon-128a AEAD encryption
- Keys zeroized on drop (`SecretBytes` wrapper)
- No key export command (only public key export)

**Residual Risk**: Memory dump while key is in use; weak passphrase.

### T4: Nonce Reuse

**Threat**: Reusing nonces enables forgery attacks.

**Mitigations**:
- Deterministic nonce derivation from `(counter, entry_id, domain)`
- Injectivity formally proven for bounded inputs
- Counter stored persistently in keystore
- No random nonce generation

**Residual Risk**: Counter rollback via keystore tampering.

### T5: Timing Side Channels

**Threat**: Attacker measures execution time to extract secrets.

**Mitigations**:
- `ct_eq`, `ct_select`, `ct_lt_u64` primitives
- Tag comparison in AEAD is constant-time
- No secret-dependent branching in signature verification
- Audited for CT compliance

**Residual Risk**: Microarchitectural timing (cache, speculation).

### T6: Replay Attacks

**Threat**: Attacker replays old valid receipt/license.

**Mitigations**:
- Receipts include creation timestamp
- Licenses include expiration field
- Anchored receipts have immutable timestamps
- Applications should check freshness

**Residual Risk**: Application fails to check expiration.

### T7: License Feature Bypass

**Threat**: Attacker modifies license to add features.

**Mitigations**:
- Signature covers entire signable portion
- Canonical CBOR encoding (deterministic)
- Feature list is signed data

**Residual Risk**: Application incorrectly parses features.

### T8: Denial of Service

**Threat**: Attacker causes resource exhaustion.

**Mitigations**:
- Bounded recursion depth in CBOR parser
- Maximum sizes for all fields (documented)
- No unbounded allocation in core

**Residual Risk**: Large file hashing (expected behavior).

## Data Flow Security

### Receipt Creation

```
File → SHA3-256 → digest
                     ↓
Key + digest + metadata → ML-DSA Sign → signature
                                          ↓
                        CBOR Encode → Receipt
```

**Security Properties**:
- Digest binds receipt to specific file content
- Signature binds receipt to key holder
- Canonical CBOR prevents encoding ambiguity

### License Verification

```
License CBOR → Decode → {fields, signature}
                           ↓
    Extract signable portion → Verify(pubkey, signable, sig)
                                         ↓
                           Check expiry, features
```

**Security Properties**:
- Total decoder handles all inputs safely
- Signature verification is constant-time
- Expiration checked with provided timestamp

## Cryptographic Assumptions

### Hardness Assumptions

| Primitive | Assumption | Standard |
|-----------|------------|----------|
| ML-DSA-87 | Module-LWE hardness | FIPS 204 |
| SHA3-256 | Collision resistance | FIPS 202 |
| SHAKE256 | PRF security | FIPS 202 |
| Ascon-128a | Related-key security | NIST LWC |
| Argon2id | Memory-hardness | RFC 9106 |

### Validated (Not Proven)

- Cryptographic primitives match reference implementations
- NIST KAT vectors pass for all algorithms
- No known attacks on chosen algorithms

## Formal Verification Coverage

| Property | Modules | Method | Status |
|----------|---------|--------|--------|
| A.R.E. | All core | RefinedRust | 135 VCs proven |
| Total parsing | CBOR, License, Receipt | Postconditions | Proven |
| Nonce injectivity | nonce | Model lemma | Proven |
| CT discipline | ct, aead, mldsa | Annotations | Audited |
| Bounds safety | All | Refinement types | Proven |

## Recommendations

### For Users

1. Use strong, unique passphrases for keystores
2. Store keystore backups securely (encrypted, offline)
3. Verify receipts/licenses before trusting
4. Check expiration timestamps on licenses
5. Keep software updated

### For Integrators

1. Always verify signatures before processing
2. Check license expiration with accurate clock
3. Validate feature flags against requirements
4. Handle verification failures gracefully
5. Log verification attempts for audit

### For Auditors

1. Focus on boundary between `anubis_io` and `anubis_core`
2. Review constant-time discipline in CT-marked functions
3. Check for timing leaks in comparison operations
4. Verify CBOR parser handles all edge cases
5. Test with malformed/adversarial inputs

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | TBD | Initial threat model |
