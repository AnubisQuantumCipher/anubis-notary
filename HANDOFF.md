# Anubis Notary Build Handoff

## Mission
Build **Anubis Notary** - a RefinedRust-verified, post-quantum CLI for signing, timestamping, licensing, and revenue generation. Follow the blueprint at `/Users/sicarii/Desktop/one-document blueprint.md` **exactly**.

---

## Three RefinedRust Agents to Use

You have THREE custom agents available. Use ALL of them in parallel:

### 1. `anubis-notary-architect` (Opus)
**Role**: Principal architect for crypto primitives, crate structure, CBOR schemas
**Use for**:
- Building Keccak-f[1600], SHA3-256, SHAKE256
- Building Ascon-128a AEAD
- Designing Receipt and License CBOR schemas
- Implementing ML-DSA-87 and ML-KEM-1024 wrappers
- CLI architecture with clap

### 2. `refined-rust-verifier` (Opus)
**Role**: RefinedRust type system expert, ownership verification
**Use for**:
- Adding `#[rr::params(...)]`, `#[rr::requires(...)]`, `#[rr::ensures(...)]` annotations
- Borrow name annotations for mutable references
- Place type mechanics
- Unsafe code verification
- Ownership transfer specifications

### 3. `refinedrust-verification-expert` (Opus)
**Role**: Formal verification strategy, Iris separation logic, proof methodology
**Use for**:
- Loop invariant design
- Representation invariants
- Proof obligation analysis
- Invariant strengthening strategies
- Creating VERIFICATION.md

---

## Current State (What's Done)

1. ✅ Directory structure created at `/Users/sicarii/Desktop/anubis-notary/`
2. ✅ Blueprint read and understood
3. ✅ Agents configured and ready (restart session to activate)
4. ❌ No code written yet - all files need to be created

---

## What Needs to Be Built

### Phase 1: Workspace Structure

Create these files:

```
/Users/sicarii/Desktop/anubis-notary/
├── Cargo.toml                    # Workspace root
├── VERIFICATION.md               # Proof strategy document
├── crates/
│   ├── anubis_core/
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs            # Module declarations
│   │       ├── ct/mod.rs         # Constant-time helpers
│   │       ├── bytes/mod.rs      # LE load/store, zeroize
│   │       ├── keccak/
│   │       │   ├── mod.rs        # Keccak-f[1600] permutation
│   │       │   ├── sha3.rs       # SHA3-256
│   │       │   └── shake.rs      # SHAKE256 XOF
│   │       ├── aead/mod.rs       # Ascon-128a
│   │       ├── kdf/mod.rs        # HKDF(SHAKE256), Argon2id params
│   │       ├── nonce/mod.rs      # Deterministic derivation
│   │       ├── cbor/mod.rs       # Canonical CBOR codec
│   │       ├── receipt/mod.rs    # Receipt schema
│   │       ├── license/mod.rs    # License schema
│   │       └── merkle/mod.rs     # Merkle tree batching
│   ├── anubis_io/
│   │   ├── Cargo.toml
│   │   └── src/lib.rs            # FS, time, network
│   └── anubis_cli/
│       ├── Cargo.toml
│       └── src/main.rs           # CLI with clap
```

---

## Technical Specifications (From Blueprint)

### Cryptographic Profile

| Component | Algorithm | Details |
|-----------|-----------|---------|
| Hash | SHA3-256 | Keccak-f[1600], LE lane loads |
| XOF | SHAKE256 | Rate = 136 bytes, domain = 0x1F |
| AEAD | Ascon-128a | 128-bit key/nonce, 12/8 rounds |
| Signatures | ML-DSA-87 | NIST Level 3 |
| KEM | ML-KEM-1024 | NIST Level 5 |
| KDF | HKDF(SHAKE256) | + Argon2id with floors |
| Nonces | Deterministic | HKDF(ctr, id, dom), injective |

### Argon2id Parameter Floors (Non-negotiable)
- m_cost ≥ 1 GiB
- t_cost ≥ 3
- p ≥ 1

### Data Formats (CBOR, Canonical)

**Receipt v1:**
```
{
  "v": 1,
  "alg": "ML-DSA-87",
  "h": "sha3-256",
  "digest": bstr(32),
  "created": int,
  "time": ["local"|"rfc3161"|"ots", meta],
  "anchor": ["none"|"btc"|"http-log", meta],
  "sig": bstr
}
```

**License v1:**
```
{
  "v": 1,
  "sub": tstr,
  "prod": tstr,
  "exp": int,
  "feat": [tstr*],
  "sig": bstr
}
```

### CLI Surface

```bash
# Keys
anubis-notary key init --keystore ~/.anubis --kdf argon2id:m=4G,t=3,p=1
anubis-notary key show --pub
anubis-notary key rotate

# Sign/Verify
anubis-notary sign FILE --out FILE.sig
anubis-notary verify FILE --sig SIG --json
anubis-notary attest PATH --recursive --receipt out.receipt
anubis-notary check RECEIPT FILE --json

# Licenses
anubis-notary license issue --product X --user U --expiry YYYY-MM-DD --features "..." --out U.lic
anubis-notary license verify --license U.lic --json

# Anchoring (paid)
anubis-notary anchor queue add out.receipt
anubis-notary anchor submit --provider btc --batch 512
anubis-notary anchor status <id> --json
```

---

## RefinedRust Verification Requirements (Section 5 of Blueprint)

### Must Prove:

1. **A.R.E. (Absence of Runtime Errors)** for all `anubis_core` modules
   - Array bounds
   - Shifts/rotates
   - Arithmetic overflow
   - Division by zero

2. **Keccak Sponge Correctness**:
   - Lane layout: `i = x + 5*y`
   - LE loads/stores at boundaries
   - ρ rotates LEFT with canonical offsets
   - π mapping: `(x,y) → (y, 2x+3y mod 5)`
   - Squeeze never exceeds rate bytes per permutation

3. **Total Decoders** (CBOR, License, Receipt):
   - Every input → `Ok(v)` or `Err(e)`
   - Closed error set
   - No partial state on error

4. **Nonce Injectivity**:
   - `derive_nonce(ctr, id, dom)` injective for `ctr < 2^48, id < 2^32`
   - Prove: `(ctr ≠ ctr' ∨ id ≠ id' ∨ dom ≠ dom') ⇒ nonce ≠ nonce'`

5. **AEAD State Machine** (Ascon-128a):
   - On failure: no plaintext exposure, state unchanged
   - On success: `open(seal(m)) = m`

6. **Argon2id Floors**:
   - Refinements ensure params ≥ floors
   - Output length exact

7. **Constant-Time Discipline**:
   - No secret-dependent branching
   - No secret-dependent indexing
   - Mask-select primitives only

---

## RefinedRust Annotation Patterns

Use these exact patterns:

```rust
// Basic function spec
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::args("#x", "#y")]
#[rr::requires("x > 0 && y > 0")]
#[rr::ensures("result == x + y")]
fn add(x: i32, y: i32) -> i32;

// Injectivity proof
#[rr::params("ctr" : "Z", "id" : "Z", "dom" : "Z")]
#[rr::returns("#(derive_nonce(ctr, id, dom))")]
#[rr::ensures("(ctr ≠ ctr' ∨ id ≠ id' ∨ dom ≠ dom') ⇒ Res ≠ Res'")]
fn derive_nonce(ctr: u64, id: u32, dom: u8) -> [u8; 32];

// AEAD round-trip
#[rr::ensures("decrypt(k, n, ad, ct || tag) = Some(msg)")]
#[rr::ensures("∀ k' ≠ k, decrypt(k', n, ad, ct || tag) = None")]
fn ascon_seal(...);

// Total parser
#[rr::returns("Ok(v) | Err(e)")]
#[rr::ensures("on_error: no_partial_state_mutation")]
fn decode_receipt(...);

// Mutable reference with borrow name
#[rr::params("γ" : "gname")]
#[rr::args("(#val, γ) @ &mut T")]
#[rr::ensures("Res γ(new_val)")]
fn update_in_place(...);

// Loop invariant
#[rr::loop_inv("0 <= i <= n")]
#[rr::loop_inv("sum == partial_sum(arr, i)")]
while i < n { ... }
```

---

## Keccak-f[1600] Implementation Details

### Round Constants (24 values)
```rust
const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
    0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];
```

### Rotation Offsets (25 values)
```rust
const RHO: [u32; 25] = [
     0,  1, 62, 28, 27,
    36, 44,  6, 55, 20,
     3, 10, 43, 25, 39,
    41, 45, 15, 21,  8,
    18,  2, 61, 56, 14,
];
```

### π Permutation Table
```rust
const PI: [usize; 25] = [
     0, 6, 12, 18, 24,
     3, 9, 10, 16, 22,
     1, 7, 13, 19, 20,
     4, 5, 11, 17, 23,
     2, 8, 14, 15, 21,
];
```

---

## Ascon-128a Implementation Details

### Permutation Constants
- 12 rounds for initialization and finalization
- 8 rounds for processing associated data and plaintext
- State: 320 bits (5 × 64-bit words)

### Round Constant Addition
```rust
const RC: [u64; 12] = [
    0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5,
    0x96, 0x87, 0x78, 0x69, 0x5a, 0x4b,
];
```

---

## How to Execute the Build

### Step 1: Launch all three agents in parallel

```
<Task anubis-notary-architect>
Build the complete anubis_core crate with all cryptographic primitives.
Read /Users/sicarii/Desktop/one-document blueprint.md for specifications.
Write to /Users/sicarii/Desktop/anubis-notary/crates/anubis_core/
Include: ct, bytes, keccak (with sha3, shake), aead, cbor, nonce, receipt, license, merkle, kdf
Use #![no_std], depend on subtle and zeroize only.
</Task>

<Task refined-rust-verifier>
Add RefinedRust annotations to all anubis_core modules.
Focus on: ownership types, borrow names, unsafe verification.
Annotate: ct operations, AEAD seal/open, nonce derivation, all decoders.
</Task>

<Task refinedrust-verification-expert>
Create VERIFICATION.md with complete proof strategy.
Design loop invariants for: Keccak rounds, CBOR parsing, Merkle construction.
Define representation invariants for all data structures.
List all VCs that must be discharged.
</Task>
```

### Step 2: Build I/O and CLI

After core is complete, build:
- `anubis_io`: Filesystem operations, time sources, keystore
- `anubis_cli`: Full CLI with all commands from blueprint

### Step 3: Verification

Run RefinedRust verification pipeline on completed code.

---

## Quality Gates (From Blueprint)

Before marking any component complete:

- [ ] RefinedRust annotations compile and type-check
- [ ] All public functions have Pre/Post conditions
- [ ] Loops have invariants sufficient for NRTE proofs
- [ ] Test vectors pass (NIST, RFC)
- [ ] No secret-dependent branches (audit constant-time)
- [ ] CBOR encoding is canonical (sorted keys, no duplicates)
- [ ] Error handling is total (closed error enum)

---

## Files to Create (Ordered)

1. `/Users/sicarii/Desktop/anubis-notary/Cargo.toml` - Workspace
2. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/Cargo.toml`
3. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/lib.rs`
4. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/ct/mod.rs`
5. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/bytes/mod.rs`
6. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/keccak/mod.rs`
7. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/keccak/sha3.rs`
8. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/keccak/shake.rs`
9. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/aead/mod.rs`
10. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/kdf/mod.rs`
11. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/nonce/mod.rs`
12. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/cbor/mod.rs`
13. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/receipt/mod.rs`
14. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/license/mod.rs`
15. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_core/src/merkle/mod.rs`
16. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_io/Cargo.toml`
17. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_io/src/lib.rs`
18. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_cli/Cargo.toml`
19. `/Users/sicarii/Desktop/anubis-notary/crates/anubis_cli/src/main.rs`
20. `/Users/sicarii/Desktop/anubis-notary/VERIFICATION.md`

---

## Command to Start Next Session

```bash
# Exit current session
/exit

# Start fresh session
claude

# Then say:
"Read /Users/sicarii/Desktop/anubis-notary/HANDOFF.md and continue building Anubis Notary using all three RefinedRust agents in parallel. Build everything to completion."
```

---

## Definition of Done (v1)

From blueprint Section 0:

> v1 produces verifiable receipts, issues/validates licenses, passes KATs, ships with proofs (A.R.E., total decoders, nonce injectivity), and a stable CLI.

The project is DONE when:
1. All 20 files listed above are created with complete, compilable code
2. RefinedRust annotations cover all verification requirements
3. VERIFICATION.md documents the complete proof strategy
4. `cargo build` succeeds
5. All proof obligations are documented

---

*Handoff created: December 24, 2024*
*Blueprint: /Users/sicarii/Desktop/one-document blueprint.md*
*Project: /Users/sicarii/Desktop/anubis-notary/*
