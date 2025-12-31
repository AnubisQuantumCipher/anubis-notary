# Anubis Notary - Project Status

**Last Updated:** December 2024

---

## Executive Summary

Anubis Notary is a post-quantum cryptographic CLI tool for digital signing, timestamping, and licensing. The project has a working Rust implementation using formally verified cryptographic primitives, with partial Coq/Rocq proofs for specification and property verification.

---

## Implementation Status

### Rust Codebase

| Component | Status | Notes |
|-----------|--------|-------|
| **anubis_core** | Compiles | Core crypto library |
| **anubis_io** | Compiles | I/O layer for keystore, files |
| **anubis_cli** | Compiles | CLI with signature verification |

### Cryptographic Primitives

| Primitive | Size Constants | Verification |
|-----------|---------------|--------------|
| ML-DSA-87 | pk=2592, sk=4896, sig=4627 | libcrux (hax/F* verified) |
| ML-KEM-1024 | pk=1568, sk=3168 | libcrux (hax/F* verified) |
| SHA3-256 / SHAKE256 | 32 bytes output | libcrux (hax/F* verified) |
| ChaCha20Poly1305 | key=32, nonce=12, tag=16 | libcrux (hax/F* verified) |
| Argon2id | configurable | rust-argon2 (not formally verified) |

### Security Features

| Feature | Status | Location |
|---------|--------|----------|
| Signature verification | Implemented | `pk.verify()` in CLI at 4 locations |
| Constant-time ops | Implemented | `ct/mod.rs` using `subtle` crate |
| Zeroization | Implemented | `Zeroize` trait on all secret types |
| Domain separation | Implemented | Distinct ASCII prefixes per operation |
| Bounds checking | Implemented | `MAX_SIGNERS`, `MAX_NESTING_DEPTH` |

---

## Formal Verification Status

### Coq/Rocq Proofs

**Structure:**
- `proofs/theories/` - Core specifications
- `specs/refinedrust/theories/` - RefinedRust-style specs
- `specs/coq/` - Additional property proofs

### Proof Statistics

| Metric | Count | Notes |
|--------|-------|-------|
| Admitted proofs | 33 | Documented with rationale |
| Vacuous `:= True` | 0 | All fixed |
| `exact I.` in case splits | 7 | Legitimate (impossible branches) |

### What IS Proven

1. **Timing invariance** (`ct_bridge.v`)
   - `ct_select_timing_invariant_holds`
   - `ct_eq_timing_invariant_holds`
   - `ct_lt_timing_invariant_holds`
   - `all_ct_ops_timing_safe`

2. **Domain separation** (`crypto_model.v`)
   - `domains_distinct` - All domain prefixes are pairwise distinct
   - Concrete ASCII byte definitions for each domain

3. **Size invariants** (multiple files)
   - Key sizes match FIPS 204/203
   - Signature bounds enforced

4. **Merkle tree properties** (`merkle_spec.v`)
   - `domain_separation` for leaf vs internal nodes
   - Index bounds preservation

5. **AEAD correctness** (`aead_spec.v`)
   - RFC 8439 ChaCha20Poly1305 construction modeled
   - `seal_output_length` - ciphertext = plaintext + 16 bytes
   - `open_rejects_short` - short inputs rejected
   - `bp_aead_no_plaintext_leak_on_failure` - zeroization on auth failure
   - Poly1305 unforgeability axiom for MAC security

### What Is Admitted (Requires External Verification)

| Category | Examples | Reason |
|----------|----------|--------|
| Cryptographic reductions | `system_security`, `euf_cma_secure` | Requires probabilistic framework |
| Bit-level proofs | `le_bytes_injective` | Computational complexity |
| Hash properties | `keccak_f_bijection` | Requires ~500 lines of inverse proof |

---

## Architecture

### Verification Layers

1. **Rust Implementation** - Uses formally verified libcrux
2. **Detailed Coq Specs** - `proofs/theories/mldsa_spec.v` with full FIPS 204 steps
3. **Abstract Models** - `specs/coq/` for property proofs (documented as models)

### CLI Signature Verification

The CLI verifies signatures at:
- Line 911: `pk.verify()` for file verification
- Line 1089: `pk.verify()` for receipt checking
- Line 1314: `pk.verify()` for execute command
- Line 2206: `pk.verify()` for multisig

All use libcrux-ml-dsa which is formally verified via hax/F*.

---

## Honest Assessment

| Claim | Status |
|-------|--------|
| Cryptographic primitives verified | YES (via libcrux/Cryspen) |
| Constant-time operations | YES (proven in ct_bridge.v) |
| Domain separation | YES (proven in crypto_model.v) |
| Size invariants | YES (consistent across codebase) |
| CLI verifies signatures | YES (4 locations) |
| Full functional correctness | PARTIAL (33 Admitted) |
| Memory safety proofs | PARTIAL (requires RefinedRust completion) |

---

## For Security Auditors

1. **Cryptographic security** relies on libcrux (externally verified by Cryspen)
2. **Admitted proofs** are documented - focus audit on those areas
3. **Abstract models** in `specs/coq/` are for property proofs, not crypto verification
4. **Constant-time** implementation uses `subtle` crate (audited by Quarkslab)

---

## Version

- Rust crate version: 0.1.0
- Verification status: **Partial** (33 Admitted, 0 vacuous)
