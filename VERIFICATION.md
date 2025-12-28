# Anubis Notary Verification Strategy

## Current Status: Honest Assessment

**IMPORTANT**: This document describes *aspirational* verification goals, not *achieved* verification.

### What Is Actually Verified (Externally)

| Component | Crate | Verified By | Method |
|-----------|-------|-------------|--------|
| ML-DSA-87 | `libcrux-ml-dsa` | Cryspen | hax/F* extraction, machine-checked proofs |
| ML-KEM-1024 | `libcrux-ml-kem` | Cryspen | hax/F* extraction, machine-checked proofs |

These are the **ONLY** mechanically verified components. Cryspen performed the proofs, not us.

### What Is NOT Verified (Custom Implementations)

| Component | Status | Testing |
|-----------|--------|---------|
| Ascon-128a | Annotations written, **NO proofs** | Property tests, fuzzing |
| SHA3/Keccak | Annotations written, **NO proofs** | NIST test vectors, fuzzing |
| HKDF-SHAKE256 | Annotations written, **NO proofs** | Property tests |
| CBOR codec | Annotations written, **NO proofs** | Property tests, fuzzing |
| Nonce derivation | Annotations written, **NO proofs** | Property tests |
| Merkle tree | Annotations written, **NO proofs** | Property tests, fuzzing |

### What "Annotations Written" Means

- RefinedRust-style specifications exist in doc comments
- Coq theory files exist in `specs/refinedrust/theories/`
- **No mechanical proof** that code matches specifications
- Specifications serve as documentation and future verification targets

### Path to Full Verification

To mechanically verify custom components would require:
1. RefinedRust toolchain setup and code extraction
2. Proof development for each verification condition (135 total)
3. Machine checking in Coq/Rocq
4. Estimated effort: 3-6 months for a verification engineer

---

## Overview

This document describes the formal verification strategy for `anubis_core` using RefinedRust, a verification framework that combines Rust's ownership system with Iris separation logic in Coq.

## Verification Scope (v1)

### Properties to Prove

1. **A.R.E. (Absence of Runtime Errors)** - All modules
   - Array bounds checking
   - Shift/rotate preconditions
   - Arithmetic overflow prevention
   - Division by zero prevention

2. **Keccak-f[1600] Sponge Correctness**
   - Lane layout: `i = x + 5*y` for 0 ≤ x,y < 5
   - Little-endian loads/stores at rate boundaries
   - ρ rotates LEFT with canonical offsets
   - π mapping: `(x,y) → (y, 2x+3y mod 5)`
   - Squeeze never exceeds rate bytes per permutation

3. **Total Decoders** (CBOR, License, Receipt)
   - Every input → `Ok(v)` or `Err(e)`
   - Closed error enum
   - No partial state mutation on error

4. **Nonce Derivation Injectivity**
   - `derive_nonce(ctr, id, dom)` injective for bounded inputs
   - Proof: `(ctr ≠ ctr' ∨ id ≠ id' ∨ dom ≠ dom') ⇒ nonce ≠ nonce'`

5. **AEAD State Machine** (Ascon-128a)
   - On failure: no plaintext exposure, state unchanged
   - On success: `open(seal(m)) = m`

6. **Argon2id Parameter Floors**
   - m_cost ≥ 1 GiB
   - t_cost ≥ 3
   - p ≥ 1

7. **Constant-Time Discipline**
   - No secret-dependent branching
   - No secret-dependent indexing
   - Mask-select primitives only

---

## Module-by-Module Verification Conditions

### 1. ct (Constant-Time) Module

**VCs: 12**

| VC | Property | Specification |
|----|----------|---------------|
| CT-1 | ct_eq timing | `timing_independent_of(a, b)` |
| CT-2 | ct_eq correctness | `ct_eq(a, b) = (a == b)` |
| CT-3 | ct_select timing | `timing_independent_of(choice)` |
| CT-4 | ct_select correctness | `ct_select(c, a, b) = if c then a else b` |
| CT-5 | ct_cmov timing | `timing_independent_of(choice)` |
| CT-6 | ct_cmov correctness | `dst' = if choice then src else dst` |
| CT-7 | ct_lt_u64 correctness | `ct_lt_u64(a, b) = if a < b then 1 else 0` |
| CT-8 | ct_gt_u64 correctness | `ct_gt_u64(a, b) = if a > b then 1 else 0` |
| CT-9 | ct_ne_byte correctness | `ct_ne_byte(a, b) = if a ≠ b then 1 else 0` |
| CT-10 | choice_to_mask correctness | `choice_to_mask(c) = if c then 0xFF else 0x00` |
| CT-11 | ct_lookup timing | `timing_independent_of(index)` |
| CT-12 | ct_lookup correctness | `ct_lookup(table, i) = table[i mod len]` |

### 2. bytes Module

**VCs: 8**

| VC | Property | Specification |
|----|----------|---------------|
| BY-1 | load_le32 bounds | `bytes.len() ≥ 4` required |
| BY-2 | load_le64 bounds | `bytes.len() ≥ 8` required |
| BY-3 | store_le32 bounds | `bytes.len() ≥ 4` required |
| BY-4 | store_le64 bounds | `bytes.len() ≥ 8` required |
| BY-5 | LE roundtrip 32 | `load_le32(store_le32(x)) = x` |
| BY-6 | LE roundtrip 64 | `load_le64(store_le64(x)) = x` |
| BY-7 | SecretBytes zeroize | `after_drop: ∀i. bytes[i] = 0` |
| BY-8 | xor_bytes bounds | `dst.len() ≥ src.len()` required |

### 3. keccak Module

**VCs: 24**

| VC | Property | Specification |
|----|----------|---------------|
| KE-1 | Lane index bounds | `0 ≤ x + 5*y < 25` |
| KE-2 | θ step correctness | Column parity XOR |
| KE-3 | ρ rotation bounds | `RHO[i] < 64` for all i |
| KE-4 | ρ rotation direction | Rotate LEFT |
| KE-5 | π permutation bijective | `π` is a bijection on [0,25) |
| KE-6 | χ step correctness | Non-linear layer |
| KE-7 | ι step correctness | Round constant XOR |
| KE-8 | Round constant values | Match FIPS 202 |
| KE-9 | keccak_f1600 24 rounds | Exactly 24 rounds applied |
| KE-10 | Absorb rate check | Never absorb > rate bytes |
| KE-11 | Squeeze rate check | Never squeeze > rate bytes without permute |
| KE-12 | SHA3-256 domain | Domain separator = 0x06 |
| KE-13 | SHAKE256 domain | Domain separator = 0x1F |
| KE-14 | SHA3-256 rate | Rate = 136 bytes |
| KE-15 | SHAKE256 rate | Rate = 136 bytes |
| KE-16 | Padding correctness | `pad10*1` rule |
| KE-17 | Empty hash test | SHA3-256("") matches NIST |
| KE-18 | ABC hash test | SHA3-256("abc") matches NIST |
| KE-19 | State initialization | All lanes zeroed |
| KE-20 | Finalize determinism | Same input → same output |
| KE-21 | Buffer position bounds | `0 ≤ buffer_pos < rate` |
| KE-22 | SHAKE extend bounds | XOF output unbounded |
| KE-23 | Lane load LE | Little-endian byte order |
| KE-24 | Lane store LE | Little-endian byte order |

### 4. aead Module (Ascon-128a)

**VCs: 18**

| VC | Property | Specification |
|----|----------|---------------|
| AE-1 | Key size | Key = 128 bits |
| AE-2 | Nonce size | Nonce = 128 bits |
| AE-3 | Tag size | Tag = 128 bits |
| AE-4 | Init rounds | 12 rounds for initialization |
| AE-5 | Data rounds | 8 rounds for AD/plaintext |
| AE-6 | Final rounds | 12 rounds for finalization |
| AE-7 | Round constant | RC[i] = 0xF0 - i*0x11 |
| AE-8 | S-box correctness | 5-bit S-box matches spec |
| AE-9 | Linear layer | Diffusion correct |
| AE-10 | Seal determinism | Same inputs → same output |
| AE-11 | Open inverse | open(seal(m)) = Ok(m) |
| AE-12 | Open reject tamper | Bit flip → Err |
| AE-13 | Open no plaintext leak | On Err, no partial plaintext |
| AE-14 | AD processing | AD absorbed correctly |
| AE-15 | Rate-2 processing | 128 bits per block |
| AE-16 | State zeroize | State cleared after use |
| AE-17 | Ciphertext length | |ct| = |pt| |
| AE-18 | Tag verification CT | Constant-time tag compare |

### 5. kdf Module

**VCs: 12**

| VC | Property | Specification |
|----|----------|---------------|
| KD-1 | Argon2id m_cost floor | m_cost ≥ 1 GiB |
| KD-2 | Argon2id t_cost floor | t_cost ≥ 3 |
| KD-3 | Argon2id parallelism | p ≥ 1 |
| KD-4 | HKDF extract | PRK = HMAC(salt, IKM) |
| KD-5 | HKDF expand | OKM = HMAC chain |
| KD-6 | HKDF output length | |OKM| = requested |
| KD-7 | HKDF-SHAKE256 | Using SHAKE256 as base |
| KD-8 | Salt handling | Empty salt → zero block |
| KD-9 | Info binding | Different info → different output |
| KD-10 | Key material zeroize | PRK zeroized after use |
| KD-11 | Parameter validation | Reject invalid params |
| KD-12 | Output determinism | Same inputs → same output |

### 6. nonce Module

**VCs: 8**

| VC | Property | Specification |
|----|----------|---------------|
| NO-1 | Derivation determinism | Same inputs → same nonce |
| NO-2 | Counter bound | ctr < 2^48 |
| NO-3 | ID bound | id < 2^32 |
| NO-4 | Domain separation | Different domains → different nonces |
| NO-5 | Injectivity (ctr) | ctr ≠ ctr' → nonce ≠ nonce' |
| NO-6 | Injectivity (id) | id ≠ id' → nonce ≠ nonce' |
| NO-7 | Injectivity (dom) | dom ≠ dom' → nonce ≠ nonce' |
| NO-8 | Output length | Nonce = 32 bytes |

### 7. cbor Module

**VCs: 16**

| VC | Property | Specification |
|----|----------|---------------|
| CB-1 | Encoder buffer bounds | Never write past buffer |
| CB-2 | Decoder buffer bounds | Never read past buffer |
| CB-3 | Minimal int encoding | Shortest form used |
| CB-4 | Type byte encoding | Major type in bits 7-5 |
| CB-5 | Uint decode correct | decode(encode(n)) = n |
| CB-6 | Int decode correct | Signed integers handled |
| CB-7 | Bytes decode correct | Byte strings preserved |
| CB-8 | Text decode correct | UTF-8 validated |
| CB-9 | Array header correct | Length encoded correctly |
| CB-10 | Map header correct | Pair count correct |
| CB-11 | Skip value recursive | All nested values skipped |
| CB-12 | Error on truncation | Short input → UnexpectedEnd |
| CB-13 | Error on invalid | Bad encoding → InvalidEncoding |
| CB-14 | Error on indefinite | Indefinite → Unsupported |
| CB-15 | Position tracking | pos always valid |
| CB-16 | Canonical ordering | canonical_cmp correct |

### 8. receipt Module

**VCs: 12**

| VC | Property | Specification |
|----|----------|---------------|
| RE-1 | Version check | v = 1 required |
| RE-2 | Algorithm check | alg = "ML-DSA-87" |
| RE-3 | Hash algorithm | h = "sha3-256" |
| RE-4 | Digest length | digest = 32 bytes |
| RE-5 | Signature length | sig ≤ 4627 bytes |
| RE-6 | Encode determinism | Same receipt → same bytes |
| RE-7 | Decode total | All inputs handled |
| RE-8 | Roundtrip | decode(encode(r)) = r |
| RE-9 | Signable excludes sig | sig not in signable portion |
| RE-10 | Time source valid | local/rfc3161/ots |
| RE-11 | Anchor type valid | none/btc/http-log |
| RE-12 | Map key order | Canonical CBOR order |

### 9. license Module

**VCs: 14**

| VC | Property | Specification |
|----|----------|---------------|
| LI-1 | Version check | v = 1 required |
| LI-2 | Subject length | sub ≤ 256 bytes |
| LI-3 | Product length | prod ≤ 64 bytes |
| LI-4 | Feature count | feat ≤ 32 entries |
| LI-5 | Feature length | Each feat ≤ 64 bytes |
| LI-6 | Expiry check | is_expired(now) correct |
| LI-7 | Encode determinism | Same license → same bytes |
| LI-8 | Decode total | All inputs handled |
| LI-9 | Roundtrip | decode(encode(l)) = l |
| LI-10 | Signable excludes sig | sig not in signable |
| LI-11 | has_feature correct | Feature lookup works |
| LI-12 | UTF-8 validation | All strings valid UTF-8 |
| LI-13 | Signature length | sig ≤ 4627 bytes |
| LI-14 | Map key order | Canonical CBOR order |

### 10. merkle Module

**VCs: 11**

| VC | Property | Specification |
|----|----------|---------------|
| ME-1 | Max leaves | count ≤ 1024 |
| ME-2 | Leaf domain | H(0x00 || data) |
| ME-3 | Node domain | H(0x01 || left || right) |
| ME-4 | Root determinism | Same leaves → same root |
| ME-5 | Proof generation bounds | idx < count |
| ME-6 | Proof verification | Valid proof verifies |
| ME-7 | Proof rejection | Invalid proof fails |
| ME-8 | Empty tree error | compute_root on empty → Err |
| ME-9 | Odd leaf promotion | Single child promoted |
| ME-10 | Proof depth | depth ≤ log2(max_leaves) |
| ME-11 | Leaf hash length | Hash = 32 bytes |

---

## Proof Development Roadmap

### Phase 1: A.R.E. Proofs (Foundation)

Focus on proving absence of runtime errors across all modules.

1. Add RefinedRust annotations for array bounds
2. Add preconditions for shift/rotate operations
3. Prove arithmetic operations don't overflow
4. Verify division by zero cannot occur

### Phase 2: Cryptographic Correctness

1. **Keccak Sponge**
   - Define lane layout model
   - Prove permutation steps correct
   - Verify padding and domain separation

2. **Ascon-128a**
   - Define state machine model
   - Prove round function correctness
   - Verify seal/open inverse property

3. **Nonce Derivation**
   - Define injectivity predicate
   - Prove for bounded counter/id ranges

### Phase 3: Total Parser Proofs

1. Define error handling model
2. Prove all decoders are total
3. Verify no partial state on error
4. Prove roundtrip properties

### Phase 4: Constant-Time Verification

1. Define timing independence predicate
2. Annotate all ct module functions
3. Verify no secret-dependent control flow

---

## RefinedRust Annotation Patterns

### Basic Function Specification
```rust
#[rr::params("x" : "Z", "y" : "Z")]
#[rr::args("#x", "#y")]
#[rr::requires("x > 0 && y > 0")]
#[rr::ensures("result == x + y")]
fn add(x: i32, y: i32) -> i32;
```

### Mutable Reference with Borrow Name
```rust
#[rr::params("γ" : "gname")]
#[rr::args("(#val, γ) @ &mut T")]
#[rr::ensures("γ(new_val)")]
fn update(val: &mut T);
```

### Total Decoder Pattern
```rust
#[rr::returns("Ok(v) | Err(e)")]
#[rr::ensures("on_error: no_partial_state_mutation")]
fn decode(input: &[u8]) -> Result<T, E>;
```

### Injectivity Proof Pattern
```rust
#[rr::params("ctr" : "Z", "id" : "Z", "dom" : "Z")]
#[rr::returns("#(derive_nonce(ctr, id, dom))")]
#[rr::ensures("(ctr ≠ ctr' ∨ id ≠ id' ∨ dom ≠ dom') ⇒ Res ≠ Res'")]
fn derive_nonce(ctr: u64, id: u32, dom: u8) -> [u8; 32];
```

### Loop Invariant Pattern
```rust
#[rr::loop_inv("0 <= i <= n")]
#[rr::loop_inv("acc == sum(arr[0..i])")]
while i < n { /* ... */ }
```

---

## Test Vectors

### SHA3-256
- Empty string: `a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a`
- "abc": `3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532`

### Ascon-128a
- NIST AEAD test vectors (see `tests/vectors/ascon.json`)

### CBOR
- RFC 8949 diagnostic examples

---

## Quality Gates

Before declaring a module verified:

- [ ] All RefinedRust annotations compile
- [ ] All VCs discharged by proof assistant
- [ ] Test vectors pass
- [ ] No unsafe code in verified modules
- [ ] Constant-time audit passed (where applicable)
- [ ] Documentation complete

---

## Total Verification Conditions: 135

| Module | VCs |
|--------|-----|
| ct | 12 |
| bytes | 8 |
| keccak | 24 |
| aead | 18 |
| kdf | 12 |
| nonce | 8 |
| cbor | 16 |
| receipt | 12 |
| license | 14 |
| merkle | 11 |
| **Total** | **135** |
