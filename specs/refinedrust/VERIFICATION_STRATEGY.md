# RefinedRust Verification Strategy for Anubis Core

## Executive Summary

This document outlines the formal verification strategy for the cryptographic
primitives in `anubis_core` using RefinedRust methodology. The verification
covers three core modules:

1. **ct** - Constant-time primitives
2. **bytes** - Byte manipulation utilities
3. **keccak** - Keccak-f[1600] permutation and sponge constructions

## Verification Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Rust Source Code                         │
│    ct/mod.rs    bytes/mod.rs    keccak/{mod,sha3,shake}.rs │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼ RefinedRust Frontend
┌─────────────────────────────────────────────────────────────┐
│                   Radium IR + Annotations                   │
│         #[rr::requires], #[rr::ensures], #[rr::loop_inv]   │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼ Type Derivation
┌─────────────────────────────────────────────────────────────┐
│               Coq/Iris Proof Obligations                    │
│    theories/{ct,bytes,keccak,sha3,shake}_spec.v            │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼ Lithium Automation
┌─────────────────────────────────────────────────────────────┐
│                   Verified Properties                       │
│     NRTE + Functional Correctness + Security Properties    │
└─────────────────────────────────────────────────────────────┘
```

## Module Specifications

### 1. Constant-Time Module (`ct`)

**Source**: `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/ct/mod.rs`

**Specification**: `theories/ct_spec.v`

**Key Functions**:
| Function | Specification | Security |
|----------|--------------|----------|
| `ct_eq` | `result = (a = b)` | Timing independent of contents |
| `ct_select` | `result = if choice then a else b` | Timing independent of choice |
| `ct_lt_u64` | `result = if a < b then 1 else 0` | No secret-dependent branches |
| `ct_lookup` | `result = table[index mod len]` | Accesses all entries |

**Proof Obligations**:
- PO-CT-1: `ct_eq` returns true iff slices are equal
- PO-CT-2: `ct_select` implements conditional selection
- PO-CT-3: `ct_ne_byte` correctly detects inequality
- PO-CT-4: `ct_lt_u64` correctly computes less-than
- PO-CT-5: All operations are timing-independent

### 2. Bytes Module (`bytes`)

**Source**: `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/bytes/mod.rs`

**Specification**: `theories/bytes_spec.v`

**Key Functions**:
| Function | Specification |
|----------|--------------|
| `load_le64` | `result = sum(bytes[i] * 2^(8*i))` |
| `store_le64` | `bytes[0..8] = le_encoding(word)` |
| `rotl64` | `result = (word << n) \| (word >> (64-n))` |
| `rotr64` | `result = (word >> n) \| (word << (64-n))` |

**Proof Obligations**:
- PO-BYTES-1: Little-endian encoding is correct
- PO-BYTES-2: `load_le64 . store_le64 = id` (round-trip)
- PO-BYTES-3: Rotations satisfy mathematical definition
- PO-BYTES-4: `rotr(rotl(x, n), n) = x` (inverse property)
- PO-BYTES-5: Zeroization clears all bytes

### 3. Keccak Module (`keccak`)

**Source**: `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/keccak/mod.rs`

**Specification**: `theories/keccak_spec.v`, `theories/keccak_model.v`

**Key Functions**:
| Function | Specification |
|----------|--------------|
| `keccak_f1600` | `state' = keccak_f(state)` (FIPS 202) |
| `keccak_absorb` | XOR block, then permute |
| `keccak_squeeze` | Extract output bytes from state |

**Proof Obligations**:
- PO-KECCAK-1: All state indices in 0..25
- PO-KECCAK-2: All rotation offsets < 64
- PO-KECCAK-3: Round constant accesses valid
- PO-KECCAK-4: State length = 25 preserved
- PO-KECCAK-5: Functional correctness vs FIPS 202
- PO-KECCAK-6: Keccak-f is a bijection

### 4. SHA3-256 (`keccak/sha3.rs`)

**Specification**: `theories/sha3_spec.v`

**Key Properties**:
- Output is exactly 32 bytes
- Streaming: `update(a); update(b) = update(a ++ b)`
- Padding: Domain byte (0x06) and 0x80 correctly placed
- KAT: Matches NIST test vectors

### 5. SHAKE256 (`keccak/shake.rs`)

**Specification**: `theories/shake_spec.v`

**Key Properties**:
- State machine: Cannot absorb after squeezing
- Prefix consistency: Shorter output is prefix of longer
- Arbitrary output length supported
- Incremental squeeze works correctly

## Index Safety Proofs

The most critical NRTE obligations involve array index bounds:

### Keccak State Access
```coq
Theorem keccak_state_indices_safe : forall x y,
  x < 5 -> y < 5 -> x + 5 * y < 25.
Proof. lia. Qed.
```

### Rotation Offset Bounds
```coq
Theorem keccak_rho_offsets_safe : forall i,
  i < 24 -> RHO[i] < 64.
```
All 24 values in the RHO table are < 64 (max is 62).

### Pi Permutation Bounds
```coq
Theorem keccak_pi_indices_safe : forall i,
  i < 24 -> 1 <= PI[i] <= 24.
```
PI table values are in range [1, 24], all valid state indices.

## Loop Invariants

### Keccak Round Loop
```rust
#[rr::loop_inv("0 <= round <= 24")]
#[rr::loop_inv("state' = keccak_f_rounds(state, round)")]
for round in 0..24 { ... }
```

### Theta Column Parity
```rust
#[rr::loop_inv("0 <= x <= 5")]
#[rr::loop_inv("forall i. i < x ==> c[i] = column_parity(state, i)")]
for x in 0..5 { c[x] = state[x] ^ state[x+5] ^ ... }
```

### SHA3 Update Loop
```rust
#[rr::loop_inv("offset <= data.len()")]
#[rr::loop_inv("buffer_pos <= RATE")]
while offset + RATE <= data.len() { ... }
```

## Verification Workflow

### Phase 1: Type Checking (Automated)
1. Run RefinedRust frontend on Rust sources
2. Generate Radium IR with annotations
3. Extract typing derivations

### Phase 2: VC Generation (Automated)
1. Lithium generates verification conditions from types
2. Simple VCs discharged automatically
3. Complex VCs extracted for manual proof

### Phase 3: Manual Proofs (As Needed)
1. Index bounds: Usually `lia` suffices
2. Functional correctness: Model comparison
3. Security properties: Timing model

### Phase 4: Integration Testing
1. Run KAT vectors for SHA3/SHAKE
2. Property-based tests for round-trips
3. Timing tests for CT operations

## File Inventory

```
specs/refinedrust/
├── README.md
├── VERIFICATION_STRATEGY.md (this file)
├── theories/
│   ├── timing_model.v       # CT execution model
│   ├── ct_spec.v            # CT module spec
│   ├── bytes_spec.v         # Bytes module spec
│   ├── keccak_model.v       # Pure Keccak model
│   ├── keccak_spec.v        # Keccak implementation spec
│   ├── sha3_spec.v          # SHA3-256 spec
│   └── shake_spec.v         # SHAKE256 spec
├── annotations/
│   ├── ct_annotations.rs    # RefinedRust annotations for ct
│   └── keccak_annotations.rs # RefinedRust annotations for keccak
└── proofs/
    └── proof_obligations.v  # Consolidated proof obligations
```

## Status Summary

| Module | NRTE | Functional | Security | KAT |
|--------|------|------------|----------|-----|
| ct | Complete | Partial | Trusted | N/A |
| bytes | Complete | Partial | Complete | N/A |
| keccak | Complete | Admitted | N/A | Pending |
| sha3 | Complete | Admitted | N/A | Partial |
| shake | Complete | Admitted | N/A | Partial |

## Next Steps

1. **Complete functional correctness proofs** for Keccak-f[1600]
   - Prove each step (theta, rho, pi, chi, iota) matches model
   - Prove composition equals full permutation

2. **Add more KAT vectors** for SHA3 and SHAKE
   - NIST test vectors
   - Edge cases (empty input, long input, multi-block)

3. **Formalize timing model** for CT operations
   - Define cost model in Iris
   - Prove timing independence properties

4. **Extract and run Lithium proofs**
   - Set up RefinedRust toolchain
   - Generate and discharge VCs
   - Document any manual proof steps

## References

- [RefinedRust Paper](https://plv.mpi-sws.org/refinedrust/)
- [FIPS 202: SHA-3 Standard](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf)
- [Keccak Reference](https://keccak.team/keccak.html)
- [subtle crate documentation](https://docs.rs/subtle/)
