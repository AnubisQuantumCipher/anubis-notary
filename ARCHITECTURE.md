# Anubis Notary Architecture

## Overview

Anubis Notary is a post-quantum secure CLI tool for digital signing, timestamping, and licensing. All cryptographic primitives are formally verified using the Cryspen libcrux library (hax/F* proofs).

## System Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              ANUBIS NOTARY CLI                              │
│                           (anubis_cli crate)                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────────────┐  │
│   │  key    │  │  sign   │  │  attest │  │ license │  │     anchor      │  │
│   │ init/   │  │ verify  │  │  check  │  │ issue/  │  │  queue/submit/  │  │
│   │ rotate  │  │         │  │         │  │ verify  │  │     status      │  │
│   └────┬────┘  └────┬────┘  └────┬────┘  └────┬────┘  └────────┬────────┘  │
│        │            │            │            │                 │           │
└────────┼────────────┼────────────┼────────────┼─────────────────┼───────────┘
         │            │            │            │                 │
         ▼            ▼            ▼            ▼                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           ANUBIS I/O LAYER                                  │
│                          (anubis_io crate)                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────────────────┐ │
│   │    Keystore     │  │   File I/O      │  │      Anchor Service         │ │
│   │                 │  │                 │  │                             │ │
│   │  • Seal/Unseal  │  │  • Atomic write │  │  • Queue management         │ │
│   │  • Key archive  │  │  • Hash file    │  │  • Merkle batching          │ │
│   │  • Revocation   │  │  • Hash dir     │  │  • Transparency logs        │ │
│   │  • Rate limit   │  │                 │  │                             │ │
│   └────────┬────────┘  └────────┬────────┘  └─────────────┬───────────────┘ │
│            │                    │                         │                 │
└────────────┼────────────────────┼─────────────────────────┼─────────────────┘
             │                    │                         │
             ▼                    ▼                         ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                        ANUBIS CRYPTOGRAPHIC CORE                            │
│                         (anubis_core crate)                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                    POST-QUANTUM CRYPTOGRAPHY                         │   │
│  │           (Formally Verified via Cryspen libcrux)                    │   │
│  │                                                                      │   │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌────────────────┐  │   │
│  │  │  ML-DSA-87 │  │ ML-KEM-1024│  │  SHA3-256  │  │ ChaCha20Poly   │  │   │
│  │  │  (FIPS204) │  │  (FIPS203) │  │  SHAKE256  │  │    1305        │  │   │
│  │  │            │  │            │  │            │  │                │  │   │
│  │  │  Sign/     │  │  Encap/    │  │  Hash/     │  │  Encrypt/      │  │   │
│  │  │  Verify    │  │  Decap     │  │  XOF       │  │  Decrypt       │  │   │
│  │  └────────────┘  └────────────┘  └────────────┘  └────────────────┘  │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                      KEY DERIVATION & SEALING                        │   │
│  │                                                                      │   │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────────────┐  │   │
│  │  │   Argon2id     │  │ HKDF(SHAKE256) │  │   Nonce Derivation     │  │   │
│  │  │                │  │                │  │                        │  │   │
│  │  │  Auto-tiered:  │  │  Salt-based    │  │  Injective counter-    │  │   │
│  │  │  • High: 4GiB  │  │  key expansion │  │  based derivation      │  │   │
│  │  │  • Med:  1GiB  │  │                │  │                        │  │   │
│  │  │  • Low: 512MiB │  │                │  │                        │  │   │
│  │  └────────────────┘  └────────────────┘  └────────────────────────┘  │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                        DATA STRUCTURES                               │   │
│  │                                                                      │   │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌────────────────┐  │   │
│  │  │  Receipt   │  │  License   │  │   Merkle   │  │     CBOR       │  │   │
│  │  │            │  │            │  │   Tree     │  │                │  │   │
│  │  │  Signed    │  │  Product/  │  │            │  │  Canonical     │  │   │
│  │  │  timestamp │  │  Feature   │  │  Batch     │  │  encoding      │  │   │
│  │  │  attestat- │  │  tokens    │  │  anchoring │  │  (RFC 8949)    │  │   │
│  │  │  ions      │  │            │  │            │  │                │  │   │
│  │  └────────────┘  └────────────┘  └────────────┘  └────────────────┘  │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Crate Structure

```
anubis-notary/
├── crates/
│   ├── anubis_core/          # Pure cryptographic library (no I/O)
│   │   ├── aead/             # ChaCha20Poly1305 (libcrux)
│   │   ├── bytes/            # LE load/store, SecretBytes
│   │   ├── cbor/             # Canonical CBOR encoder/decoder
│   │   ├── ct/               # Constant-time ops (subtle)
│   │   ├── error/            # Unified error types
│   │   ├── kdf/              # Argon2id params, HKDF
│   │   ├── keccak/           # SHA3-256, SHAKE256 (libcrux)
│   │   ├── license/          # License token schema
│   │   ├── merkle/           # Merkle tree for batching
│   │   ├── mldsa/            # ML-DSA-87 signatures (libcrux)
│   │   ├── mlkem/            # ML-KEM-1024 KEM (libcrux)
│   │   ├── nonce/            # Deterministic nonce derivation
│   │   └── receipt/          # Receipt attestation schema
│   │
│   ├── anubis_io/            # I/O layer (filesystem, time, network)
│   │   ├── anchor/           # Transparency log integration
│   │   ├── keystore/         # Encrypted key storage
│   │   ├── rate_limit/       # Brute-force protection
│   │   └── seal/             # Key sealing with Argon2id
│   │
│   └── anubis_cli/           # CLI binary
│       └── main.rs           # Command dispatch
│
├── proofs/                   # Formal verification
│   └── theories/             # Rocq/Coq proofs
│       ├── argon2_spec.v     # Argon2id correctness
│       └── memory_tier_spec.v # Auto memory selection
│
└── tests/
    └── integration_test.rs   # End-to-end workflow tests
```

## Data Flow

### 1. Key Generation & Storage

```
                    ┌─────────────────────────────┐
                    │       User Password         │
                    └──────────────┬──────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────┐
│                      KEY SEALING FLOW                       │
│                                                             │
│  ┌─────────────┐    ┌──────────────┐    ┌───────────────┐  │
│  │ OS CSPRNG   │───▶│ ML-DSA-87    │───▶│  Secret Key   │  │
│  │ (getrandom) │    │ KeyGen       │    │  (4864 bytes) │  │
│  └─────────────┘    └──────────────┘    └───────┬───────┘  │
│                                                  │          │
│  ┌─────────────┐    ┌──────────────┐            │          │
│  │ OS CSPRNG   │───▶│ 256-bit Salt │────────────┼──────┐   │
│  └─────────────┘    └──────────────┘            │      │   │
│                                                  │      │   │
│  ┌─────────────┐    ┌──────────────┐            │      │   │
│  │ OS CSPRNG   │───▶│ 96-bit Nonce │────────────┼──────┤   │
│  └─────────────┘    └──────────────┘            │      │   │
│                                                  ▼      ▼   │
│  Password ─────▶┌──────────────────────────────────────────┐│
│                 │           Argon2id                       ││
│                 │  (auto-tiered: 512MiB - 4GiB)           ││
│                 └──────────────────┬───────────────────────┘│
│                                    │                        │
│                                    ▼ 256-bit key            │
│                          ┌─────────────────────┐            │
│                          │  ChaCha20Poly1305   │            │
│                          │     Encrypt         │            │
│                          └──────────┬──────────┘            │
│                                     │                       │
└─────────────────────────────────────┼───────────────────────┘
                                      ▼
                           ┌──────────────────────┐
                           │   ~/.anubis/         │
                           │   ├── key.sealed     │
                           │   └── key.pub        │
                           └──────────────────────┘
```

### 2. Sign & Verify Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              SIGNING FLOW                                   │
│                                                                             │
│   ┌──────────┐                                                              │
│   │  File    │                                                              │
│   │ (input)  │                                                              │
│   └────┬─────┘                                                              │
│        │                                                                    │
│        ▼                                                                    │
│   ┌──────────┐    ┌───────────────┐    ┌─────────────────────────────────┐  │
│   │ SHA3-256 │───▶│ 32-byte hash  │───▶│  ML-DSA-87 Sign(sk, hash)       │  │
│   └──────────┘    └───────────────┘    │                                 │  │
│                                        │  1. Expand secret key           │  │
│                                        │  2. Sample noise polynomials    │  │
│                                        │  3. Compute commitment          │  │
│                                        │  4. Generate signature          │  │
│                                        │     (4627 bytes)                │  │
│                                        └────────────────┬────────────────┘  │
│                                                         │                   │
│                                                         ▼                   │
│                                              ┌───────────────────┐          │
│                                              │   file.sig        │          │
│                                              │   (4627 bytes)    │          │
│                                              └───────────────────┘          │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│                            VERIFICATION FLOW                                │
│                                                                             │
│  ┌──────────┐   ┌──────────┐   ┌────────────┐                               │
│  │  File    │   │ Signature│   │ Public Key │                               │
│  └────┬─────┘   └────┬─────┘   └─────┬──────┘                               │
│       │              │               │                                      │
│       ▼              │               │                                      │
│  ┌──────────┐        │               │                                      │
│  │ SHA3-256 │        │               │                                      │
│  └────┬─────┘        │               │                                      │
│       │              │               │                                      │
│       ▼              ▼               ▼                                      │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                    ML-DSA-87 Verify(pk, hash, sig)                   │   │
│  │                                                                      │   │
│  │  1. Decode signature into (c̃, z, hint)                              │   │
│  │  2. Expand public key matrix A                                       │   │
│  │  3. Recompute w' = Az - ct₁·2^d                                      │   │
│  │  4. Verify c̃ = H(μ || w')                                           │   │
│  │  5. Check ||z||∞ < γ₁ - β                                            │   │
│  │                                                                      │   │
│  └──────────────────────────────────┬───────────────────────────────────┘   │
│                                     │                                       │
│                                     ▼                                       │
│                          ┌────────────────────┐                             │
│                          │  Valid / Invalid   │                             │
│                          └────────────────────┘                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3. Attest & Check Flow (Receipts)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           ATTESTATION FLOW                                  │
│                                                                             │
│  ┌──────────┐    ┌──────────┐    ┌──────────────────────────────────────┐   │
│  │  File    │───▶│ SHA3-256 │───▶│  Receipt (CBOR)                      │   │
│  └──────────┘    └──────────┘    │  {                                   │   │
│                                  │    "v": 1,                           │   │
│  ┌──────────┐                    │    "alg": "ML-DSA-87",               │   │
│  │ Timestamp│───────────────────▶│    "h": "sha3-256",                  │   │
│  └──────────┘                    │    "digest": <32 bytes>,             │   │
│                                  │    "created": <unix_timestamp>,      │   │
│                                  │    "time": ["local"],                │   │
│                                  │    "anchor": ["none"],               │   │
│                                  │    "sig": <4627 bytes>               │   │
│                                  │  }                                   │   │
│                                  └───────────────────┬──────────────────┘   │
│                                                      │                      │
│                                                      ▼                      │
│                                           ┌──────────────────┐              │
│                                           │  file.receipt    │              │
│                                           └──────────────────┘              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│                              CHECK FLOW                                     │
│                                                                             │
│  ┌──────────┐    ┌──────────────┐                                           │
│  │  File    │───▶│ SHA3-256     │──┐                                        │
│  └──────────┘    └──────────────┘  │                                        │
│                                    ▼                                        │
│  ┌──────────────┐           ┌────────────┐                                  │
│  │ file.receipt │──────────▶│  Compare   │                                  │
│  └──────────────┘           │  digests   │                                  │
│                             └─────┬──────┘                                  │
│                                   │                                         │
│  ┌──────────────┐                 ▼                                         │
│  │  Public Key  │──────────▶┌────────────────────┐                          │
│  └──────────────┘           │ Verify ML-DSA-87   │                          │
│                             │ signature over     │                          │
│                             │ receipt            │                          │
│                             └─────────┬──────────┘                          │
│                                       │                                     │
│                                       ▼                                     │
│                          ┌───────────────────────────┐                      │
│                          │  ✓ Content matches        │                      │
│                          │  ✓ Signature valid        │                      │
│                          │  ✓ Timestamp: 2025-01-01  │                      │
│                          └───────────────────────────┘                      │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 4. License Issuance Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         LICENSE ISSUANCE FLOW                               │
│                                                                             │
│  Inputs:                                                                    │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐                    │
│  │ User email    │  │ Product code  │  │ Expiration    │                    │
│  │ (subject)     │  │               │  │ timestamp     │                    │
│  └───────┬───────┘  └───────┬───────┘  └───────┬───────┘                    │
│          │                  │                  │                            │
│          └──────────────────┼──────────────────┘                            │
│                             │                                               │
│                             ▼                                               │
│                    ┌──────────────────────────────────────────┐             │
│                    │  License (CBOR)                          │             │
│                    │  {                                       │             │
│                    │    "v": 1,                               │             │
│                    │    "sub": "user@example.com",            │             │
│                    │    "prod": "anubis-pro",                 │             │
│                    │    "exp": 1767225600,                    │             │
│                    │    "feat": ["offline-mode", "team-sync"],│             │
│                    │    "sig": <ML-DSA-87 signature>          │             │
│                    │  }                                       │             │
│                    └──────────────────┬───────────────────────┘             │
│                                       │                                     │
│                                       ▼                                     │
│                            ┌───────────────────┐                            │
│                            │  license.bin      │                            │
│                            │  (distribute to   │                            │
│                            │   customer)       │                            │
│                            └───────────────────┘                            │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│                       LICENSE VERIFICATION FLOW                             │
│                                                                             │
│  ┌────────────────┐   ┌────────────────┐   ┌────────────────┐               │
│  │  license.bin   │   │ Issuer PubKey  │   │ Current Time   │               │
│  └───────┬────────┘   └───────┬────────┘   └───────┬────────┘               │
│          │                    │                    │                        │
│          ▼                    │                    │                        │
│  ┌────────────────┐           │                    │                        │
│  │ Decode CBOR    │           │                    │                        │
│  └───────┬────────┘           │                    │                        │
│          │                    │                    │                        │
│          ▼                    ▼                    ▼                        │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                        VALIDATION CHECKS                             │   │
│  │                                                                      │   │
│  │  1. Verify ML-DSA-87 signature with issuer public key                │   │
│  │  2. Check: current_time <= expiration                                │   │
│  │  3. Extract and return feature flags                                 │   │
│  │                                                                      │   │
│  └──────────────────────────────┬───────────────────────────────────────┘   │
│                                 │                                           │
│                                 ▼                                           │
│                    ┌────────────────────────────┐                           │
│                    │  ✓ Valid until 2025-12-31  │                           │
│                    │  ✓ Features: offline-mode  │                           │
│                    │             team-sync      │                           │
│                    └────────────────────────────┘                           │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Threat Model

### Assets to Protect

| Asset | Sensitivity | Protection Mechanism |
|-------|-------------|---------------------|
| ML-DSA-87 Secret Key | **Critical** | Argon2id + ChaCha20Poly1305 encryption, 0o600 permissions |
| Password | **Critical** | Never stored; derived key zeroized immediately after use |
| Signatures | Integrity | ML-DSA-87 (NIST FIPS 204, post-quantum secure) |
| Receipts | Integrity | Canonical CBOR + ML-DSA-87 signature |
| Licenses | Integrity | ML-DSA-87 signature + expiration validation |

### Threat Categories

#### 1. Cryptanalytic Attacks

| Threat | Mitigation |
|--------|------------|
| Quantum computer attacks on signatures | ML-DSA-87 (NIST PQC standard, 192-bit post-quantum security) |
| Quantum attacks on encryption | ChaCha20Poly1305 (256-bit symmetric, quantum-resistant) |
| Hash collisions | SHA3-256 (256-bit security, no known attacks) |

#### 2. Password/Key Extraction

| Threat | Mitigation |
|--------|------------|
| Brute-force password attack | Argon2id with 512MiB-4GiB memory, exponential rate limiting |
| Memory scraping | Zeroize all sensitive data, SecretBytes with Drop impl |
| Cold boot attack | Argon2id's memory-hardness increases attack cost |
| Timing side-channels | Constant-time operations via `subtle` crate |

#### 3. File System Attacks

| Threat | Mitigation |
|--------|------------|
| Key file theft | Argon2id encryption (4+ GiB memory-hard) |
| Key file tampering | ChaCha20Poly1305 AEAD (authentication tag) |
| TOCTOU race conditions | Atomic writes (temp file + rename + fsync) |
| Permission escalation | 0o600 for secrets, 0o644 for public keys |

#### 4. Signature Attacks

| Threat | Mitigation |
|--------|------------|
| Signature forgery | ML-DSA-87 (EUF-CMA secure) |
| Key substitution | Public key fingerprints (SHA3-256 of pubkey) |
| Replay attacks | Timestamps in receipts, expiration in licenses |
| Revoked key usage | Local revocation list + signed revocation lists |

#### 5. Implementation Attacks

| Threat | Mitigation |
|--------|------------|
| Buffer overflows | Rust memory safety, `#![forbid(unsafe_code)]` |
| Integer overflows | Explicit overflow checks, bounded arithmetic |
| Format string attacks | Rust's type-safe formatting |
| Injection attacks | Strongly-typed CBOR encoding, no string interpolation |

### Security Boundaries

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          TRUST BOUNDARY                                     │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                     TRUSTED COMPONENTS                                │  │
│  │                                                                       │  │
│  │  • anubis_core (pure crypto, formally verified dependencies)          │  │
│  │  • libcrux (hax/F* verified ML-DSA, ML-KEM, SHA3, ChaCha20)          │  │
│  │  • subtle (audited constant-time operations)                          │  │
│  │  • zeroize (audited secure memory clearing)                           │  │
│  │                                                                       │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                   SEMI-TRUSTED COMPONENTS                             │  │
│  │                                                                       │  │
│  │  • anubis_io (filesystem, network - attack surface)                   │  │
│  │  • OS CSPRNG (getrandom - must be properly seeded)                    │  │
│  │  • System clock (can be spoofed if attacker has root)                 │  │
│  │                                                                       │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                      UNTRUSTED INPUTS                                 │  │
│  │                                                                       │  │
│  │  • User-provided files (arbitrary content)                            │  │
│  │  • User passwords (may be weak)                                       │  │
│  │  • External signatures/receipts/licenses (may be forged)              │  │
│  │  • Network responses (transparency logs, TSA)                         │  │
│  │                                                                       │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Key Lifecycle

### State Machine

```
                                    ┌─────────────┐
                                    │             │
                              ┌─────│  UNINITIALIZED
                              │     │             │
                              │     └─────────────┘
                              │
                              │ key init
                              ▼
┌─────────────┐         ┌─────────────┐         ┌─────────────┐
│             │         │             │         │             │
│  ARCHIVED   │◀────────│   ACTIVE    │────────▶│   REVOKED   │
│             │ rotate  │             │ revoke  │             │
└─────────────┘         └─────────────┘         └─────────────┘
      │                       │                       │
      │                       │                       │
      │                       ▼                       │
      │               ┌─────────────┐                 │
      │               │             │                 │
      └──────────────▶│  DESTROYED  │◀────────────────┘
         (optional)   │             │
                      └─────────────┘
```

### Lifecycle Operations

#### 1. Key Generation (`key init`)

```bash
$ anubis-notary key init
Enter password: ********
Confirm password: ********

Key generated successfully.
  Fingerprint: 7a3b9c2d...
  Algorithm: ML-DSA-87
  Storage: ~/.anubis/key.sealed
```

**What happens:**
1. Generate 32 bytes from OS CSPRNG → ML-DSA-87 seed
2. KeyGen(seed) → (secret_key, public_key)
3. Generate 32-byte salt, 12-byte nonce from CSPRNG
4. Argon2id(password, salt) → 256-bit encryption key
5. ChaCha20Poly1305.Encrypt(enc_key, nonce, secret_key) → ciphertext
6. Write `~/.anubis/key.sealed` = version || salt || nonce || ciphertext || tag
7. Write `~/.anubis/key.pub` = public_key bytes
8. Zeroize password, enc_key, secret_key from memory

#### 2. Key Rotation (`key rotate`)

```bash
$ anubis-notary key rotate
Enter current password: ********
Enter new password: ********
Confirm new password: ********

Key rotated successfully.
  Old key archived as: 1735689600
  New fingerprint: 8b4c0d3e...
```

**What happens:**
1. Unseal current key with old password
2. Generate new ML-DSA-87 keypair
3. Sign rotation certificate: `rotate(old_pk, new_pk, timestamp)`
4. Archive: `~/.anubis/archived/1735689600.pub`, `*.sealed`, `*.rotation`
5. Seal new key with new password
6. Overwrite `~/.anubis/key.sealed` and `key.pub`

#### 3. Key Revocation (`key revoke`)

```bash
$ anubis-notary key revoke --reason "compromised device"
Enter password: ********

Key revoked successfully.
  Fingerprint: 7a3b9c2d...
  Reason: compromised device
  Revocation time: 2025-01-15T12:00:00Z
```

**What happens:**
1. Compute fingerprint = SHA3-256(public_key)[..32 hex chars]
2. Append to `~/.anubis/revoked.list`: `fingerprint:timestamp:reason`
3. Optionally sign revocation list → `revoked.signed`
4. Key is **not deleted** (can verify old signatures, but won't sign new)

#### 4. Key Unsealing (on every sign/attest operation)

```
Password ──────┐
               │
               ▼
          ┌─────────┐     ┌─────────────────┐
Sealed ──▶│ Argon2id│────▶│ ChaCha20Poly1305│────▶ Secret Key
Key       │         │     │     Decrypt     │
          └─────────┘     └─────────────────┘
               │
               └── Rate Limited (exponential backoff after failures)
```

### Key Storage Layout

```
~/.anubis/                          # Linux: ~/.local/share/anubis/
├── key.sealed                      # Encrypted ML-DSA-87 secret key (0o600)
├── key.pub                         # ML-DSA-87 public key (0o644)
├── revoked.list                    # Plaintext revocation list
├── revoked.signed                  # Signed revocation list (CBOR + ML-DSA)
│
├── archived/                       # Rotated keys (0o700)
│   ├── 1735689600.pub             # Archived public key
│   ├── 1735689600.sealed          # Archived sealed key (for decryption)
│   └── 1735689600.rotation        # Rotation certificate
│
├── anchor_queue/                   # Pending receipts for anchoring
│   └── <digest>.queued
│
├── anchors/                        # Completed anchor records
│   └── <merkle_root>.anchor
│
└── licenses/                       # Issued licenses
    ├── <license_id>.license
    └── <license_id>.meta
```

## Cryptographic Parameter Summary

| Component | Algorithm | Security Level | Key/Output Size |
|-----------|-----------|---------------|-----------------|
| Signatures | ML-DSA-87 (FIPS 204) | 192-bit PQ | PK: 2592B, SK: 4864B, Sig: 4627B |
| KEM | ML-KEM-1024 (FIPS 203) | 192-bit PQ | PK: 1568B, SK: 3168B, CT: 1568B |
| AEAD | ChaCha20Poly1305 | 256-bit classical | Key: 32B, Nonce: 12B, Tag: 16B |
| Hash | SHA3-256 | 128-bit classical | 32B |
| XOF | SHAKE256 | 256-bit classical | Variable |
| KDF (password) | Argon2id | Configurable | 512MiB-4GiB memory |
| KDF (key expansion) | HKDF-SHAKE256 | 256-bit | Variable |

## Formal Verification Status

| Component | Verification Method | Status |
|-----------|---------------------|--------|
| ML-DSA-87 | hax/F* (Cryspen libcrux) | **Verified** |
| ML-KEM-1024 | hax/F* (Cryspen libcrux) | **Verified** |
| SHA3-256/SHAKE256 | hax/F* (Cryspen libcrux) | **Verified** |
| ChaCha20Poly1305 | hax/F* (Cryspen libcrux) | **Verified** |
| HKDF | hax/F* (Cryspen libcrux) | **Verified** |
| Constant-time ops | Quarkslab audit (subtle) | **Audited** |
| Memory zeroization | Mozilla/Google audit | **Audited** |
| Argon2id memory tiers | Rocq/Coq proofs | **Proven** |

## References

- [NIST FIPS 204](https://csrc.nist.gov/pubs/fips/204/final) - ML-DSA (Dilithium)
- [NIST FIPS 203](https://csrc.nist.gov/pubs/fips/203/final) - ML-KEM (Kyber)
- [RFC 9106](https://www.rfc-editor.org/rfc/rfc9106) - Argon2
- [RFC 8949](https://www.rfc-editor.org/rfc/rfc8949) - CBOR
- [Cryspen libcrux](https://github.com/cryspen/libcrux) - Formally verified crypto
