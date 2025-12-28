# Formal Verification Coverage for anubis_core

## Overview

The `anubis_core` crate provides RefinedRust-verified cryptographic primitives for
the Anubis Notary system. This document describes the formal verification methodology,
coverage, and assurance levels.

## Verification Methodology

We employ a multi-layered verification approach:

1. **RefinedRust/Coq Specifications** - Formal specs in `specs/refinedrust/theories/`
2. **Property-Based Testing** - Proptest tests for algebraic properties
3. **Fuzzing** - cargo-fuzz targets for crash safety
4. **Benchmarks** - Criterion benchmarks with timing analysis

## Module Verification Status

| Module | Memory Safety | Functional | Timing | KAT | Fuzz |
|--------|---------------|------------|--------|-----|------|
| ct | Proven | Proven | Proven | N/A | N/A |
| bytes | Proven | Proven | Partial | N/A | N/A |
| keccak | Proven | Proven | Model | Pass | Yes |
| sha3 | Proven | Proven | Model | Pass | Yes |
| shake | Proven | Proven | Model | Pass | Yes |
| aead | Proven | Tested | Trusted | Pass | Yes |
| kdf | Proven | Tested | N/A | N/A | N/A |
| nonce | Proven | Proven | N/A | N/A | N/A |
| merkle | Proven | Tested | N/A | N/A | Yes |
| cbor | Proven | Tested | N/A | N/A | Yes |
| mldsa | Trusted | Trusted | External | Pending | N/A |

**Legend:**
- **Proven** - Verified with Coq/Iris proofs
- **Tested** - Property-based tests + unit tests
- **Trusted** - Uses audited external libraries
- **Model** - Timing independence via execution model
- **External** - Security relies on external crate

## Security Properties

### Constant-Time Operations (`ct` module)

All CT primitives are verified timing-independent:

```
ct_eq(a, b)      : timing ∝ len(a)      (not contents)
ct_select(c,x,y) : timing = O(1)        (independent of c)
ct_lt_u64(a, b)  : timing = O(1)        (no branches)
ct_lookup(t, i)  : timing ∝ len(t)      (touches all entries)
```

**Coq Spec**: `specs/refinedrust/theories/ct_spec.v`

### Memory Safety

All array accesses are bounds-checked:

- Keccak state: `∀ x y. x < 5 → y < 5 → x + 5*y < 25`
- Rotation offsets: `∀ i. RHO[i] < 64`
- Buffer positions: `buffer_pos ≤ RATE`

**Coq Spec**: `specs/refinedrust/theories/keccak_spec.v`

### Cryptographic Correctness

Functional specifications for all cryptographic functions:

- **SHA3-256**: Matches FIPS 202 specification
- **SHAKE256**: Correct sponge construction
- **HKDF-SHAKE256**: Correct extract-then-expand
- **Ascon-128a**: Correct permutation and padding
- **ML-DSA-87**: Uses RustCrypto `ml-dsa` crate (FIPS 204)

## Property-Based Tests

Located in `tests/property_tests.rs`:

### Byte Operations (7 properties)
- `le32_roundtrip`: store then load is identity
- `le64_roundtrip`: store then load is identity
- `try_load_le32_totality`: safe variants return None for short slices
- `try_load_le64_totality`: safe variants return None for short slices
- `rotation_inverse`: rotl ∘ rotr = id
- `xor_self_inverse`: x ⊕ x = 0
- `xor_double_identity`: (x ⊕ k) ⊕ k = x

### Constant-Time Operations (9 properties)
- `ct_eq_reflexive`: ct_eq(a, a) = true
- `ct_eq_symmetric`: ct_eq(a, b) = ct_eq(b, a)
- `ct_select_true`: ct_select(true, a, b) = a
- `ct_select_false`: ct_select(false, a, b) = b
- `ct_select_u64_true/false`: 64-bit variants
- `ct_lt_matches_std`: ct_lt_u64 = standard comparison
- `ct_cmov_false_preserves`: dst unchanged when false
- `ct_cmov_true_updates`: dst = src when true

### Keccak/SHA3/SHAKE (6 properties)
- `sha3_output_length`: Always 32 bytes
- `sha3_deterministic`: Same input → same output
- `sha3_streaming_equivalence`: Streaming = one-shot
- `sha3_split_streaming`: Split update = single update
- `shake_deterministic`: Same input → same output
- `shake_prefix_consistency`: Shorter output is prefix of longer

### KDF (3 properties)
- `hkdf_deterministic`: Same inputs → same output
- `hkdf_info_separation`: Different info → different output
- `hkdf_ikm_separation`: Different IKM → different output

### Nonce Derivation (4 properties)
- `nonce_deterministic`: Same inputs → same nonce
- `nonce_counter_separation`: Different counter → different nonce
- `nonce_entry_separation`: Different entry_id → different nonce
- `nonce_overflow_rejected`: Counter overflow returns error

### AEAD (3 properties)
- `aead_roundtrip`: Decrypt(Encrypt(pt)) = pt
- `aead_tamper_detection`: Tampered ciphertext rejected
- `aead_wrong_aad_rejected`: Wrong AAD rejected

### CBOR (5 properties)
- `cbor_uint_roundtrip`: Decode(Encode(n)) = n
- `cbor_int_roundtrip`: Signed integer roundtrip
- `cbor_bytes_roundtrip`: Byte string roundtrip
- `cbor_text_roundtrip`: Text string roundtrip
- `cbor_bool_roundtrip`: Boolean roundtrip

### Merkle Tree (3 properties)
- `merkle_deterministic`: Same leaves → same root
- `merkle_proof_valid`: Generated proofs verify correctly
- `merkle_collision_resistance`: Different leaves → different roots

**Total: 41 property-based tests**

## Fuzzing Targets

Located in `fuzz/fuzz_targets/`:

| Target | Purpose | Properties Tested |
|--------|---------|-------------------|
| `fuzz_cbor` | CBOR parsing | No panics, roundtrip |
| `fuzz_aead` | Ascon-128a | No panics, roundtrip, tamper detection |
| `fuzz_keccak` | SHA3/SHAKE | No panics, streaming equivalence |
| `fuzz_merkle` | Merkle tree | No panics, proof verification |

## Benchmarks

Located in `benches/crypto_bench.rs`:

- SHA3-256 throughput (32B - 16KB)
- SHAKE256 squeeze performance
- Ascon-128a encryption (64B - 4KB)
- HKDF-SHAKE256 derivation
- Nonce derivation
- Merkle tree building and proof generation
- ML-DSA-87 keygen/sign/verify (reduced sample size)

## Known Limitations

1. **ML-DSA Stack Usage**: ML-DSA-87 uses large stack temporaries for polynomial
   vectors and NTT workspaces. The `.cargo/config.toml` configures 32 MiB stack
   for test threads automatically.

2. **Unaudited Dependencies**: The `ml-dsa` crate has not been independently audited.
   For highest assurance, consider HSM-backed signatures.

3. **Side-Channel Resistance**: While CT operations are timing-independent by design,
   hardware-specific side channels (power analysis, cache timing) require physical
   countermeasures.

4. **Argon2id Memory Floor**: 4 GiB minimum memory cost may be impractical for
   resource-constrained environments.

## Verification Files

```
specs/refinedrust/
├── theories/
│   ├── aead_spec.v          # Ascon-128a AEAD spec
│   ├── bytes_spec.v         # Byte manipulation spec
│   ├── cbor_spec.v          # CBOR codec spec
│   ├── ct_spec.v            # Constant-time ops spec
│   ├── kdf_spec.v           # HKDF spec
│   ├── keccak_model.v       # Pure Keccak model
│   ├── keccak_spec.v        # Keccak implementation spec
│   ├── license_spec.v       # License token spec
│   ├── merkle_spec.v        # Merkle tree spec
│   ├── mldsa_spec.v         # ML-DSA-87 spec
│   ├── nonce_spec.v         # Nonce derivation spec
│   ├── receipt_spec.v       # Receipt format spec
│   ├── sha3_spec.v          # SHA3-256 spec
│   ├── shake_spec.v         # SHAKE256 spec
│   └── timing_model.v       # CT execution model
├── proofs/
│   └── proof_obligations.v  # Consolidated proofs
└── annotations/
    └── *.rs                 # RefinedRust annotations
```

## Running Verification

```bash
# Run all tests (stack configured via .cargo/config.toml)
cargo test -p anubis_core

# Run property tests only
cargo test -p anubis_core --test property_tests

# Run benchmarks
cargo bench -p anubis_core

# Run fuzzing (requires cargo-fuzz)
cd crates/anubis_core && cargo +nightly fuzz run fuzz_cbor
```

## References

- [RefinedRust](https://plv.mpi-sws.org/refinedrust/)
- [FIPS 202: SHA-3](https://csrc.nist.gov/pubs/fips/202/final)
- [FIPS 204: ML-DSA](https://csrc.nist.gov/pubs/fips/204/final)
- [Ascon](https://ascon.iaik.tugraz.at/)
- [subtle crate](https://docs.rs/subtle/)
