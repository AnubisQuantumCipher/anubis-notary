# Anubis Notary - Formal Verification Strategy

> **⚠️ VERIFICATION STATUS: PLANNED**
>
> This document describes the *planned* RefinedRust verification approach for `anubis_core`.
> The Coq specifications and RefinedRust annotations exist in the codebase, but:
> - **Many Coq proofs use `Admitted`** (not yet proven)
> - **RefinedRust verification has not been run** (toolchain not yet integrated)
> - **The annotations serve as specifications** for future verification
>
> The cryptographic primitives themselves come from **libcrux** which IS formally verified
> using hax/F*. Our verification effort focuses on the glue code and higher-level protocols.

## Overview

This document describes the RefinedRust verification approach for `anubis_core`.
The goal is to prove **absence of runtime errors (A.R.E.)**, **functional correctness**, and
**security properties** for all cryptographic primitives and data structures.

## Verification Scope

### What We Prove

| Property | Modules | Technique |
|----------|---------|-----------|
| A.R.E. (no panics, OOB, UB) | All of `anubis_core` | RefinedRust refinement types |
| Functional correctness | Keccak, CBOR, Merkle | Iris separation logic |
| Total parsing | CBOR, License, Receipt | Refinement postconditions |
| Constant-time discipline | ct, aead, mldsa | `#[rr::ct]` markers + audit |
| Nonce injectivity | nonce | Model-level lemma |
| AEAD state machine | aead | Round-trip invariants |
| Zeroization completeness | bytes, mldsa | Volatile write postconditions |

### What We Do NOT Prove (Axioms)

- Cryptographic hardness of ML-DSA-87, Keccak, Ascon
- Side-channel resistance beyond CT discipline (power, EM, cache timing)
- Correct compilation (we trust rustc + LLVM)

These are validated via:
- NIST KAT vectors (Known Answer Tests)
- Reference implementation cross-checks
- Optional: dudect timing analysis

---

## Module-by-Module Verification

### 1. `ct` - Constant-Time Primitives

**File:** `src/ct/mod.rs`

**Properties:**
- `ct_select(a, b, flag)` returns `b` if `flag` else `a`
- `ct_eq(a, b)` returns `true` iff `a == b` (byte-wise)
- No secret-dependent branches or memory accesses

**Annotations:**
```rust
#[rr::ensures("result == if flag { b } else { a }")]
#[rr::ct]  // Constant-time marker
pub fn ct_select(a: u64, b: u64, flag: bool) -> u64
```

**Proof Obligations:**
- [ ] `ct_select` mask arithmetic is correct
- [ ] `ct_eq` accumulator XOR yields 0 iff equal
- [ ] `ct_lt_u64` comparison chain is sound

---

### 2. `bytes` - Byte Manipulation

**File:** `src/bytes/mod.rs`

**Properties:**
- `load_le64` correctly interprets 8 bytes as little-endian u64
- `store_le64` is the exact inverse of `load_le64`
- `rotr64(x, n)` equals `(x >> n) | (x << (64 - n))` for `n < 64`
- `SecretBytes` zeroizes on drop

**Annotations:**
```rust
#[rr::requires("bytes.len() >= 8")]
#[rr::ensures("result == sum(bytes[i] << (8*i) for i in 0..8)")]
pub fn load_le64(bytes: &[u8]) -> u64

#[rr::requires("n < 64")]
#[rr::ensures("result == ((x >> n) | (x << (64 - n)))")]
pub fn rotr64(x: u64, n: u32) -> u64
```

**Proof Obligations:**
- [x] `load_le64` bounds check (requires len >= 8)
- [x] `store_le64` inverse property
- [x] `rotr64` shift bounds (n < 64)
- [ ] `SecretBytes::drop` postcondition (all bytes == 0)

---

### 3. `keccak` - Keccak-f[1600] Permutation

**File:** `src/keccak/mod.rs`

**Properties:**
- State is 25 lanes of 64 bits (1600 bits total)
- Lane indexing: `i = x + 5*y` for `x,y in 0..5`
- Permutation applies θ → ρ → π → χ → ι in sequence
- Absorb XORs at most `rate/8` lanes
- Squeeze reads at most `rate/8` lanes

**Annotations:**
```rust
#[rr::loop_inv("0 <= round <= 24")]
#[rr::ensures("state is permuted per Keccak-f spec")]
pub fn keccak_f1600(state: &mut KeccakState)

#[rr::requires("block.len() == rate && rate % 8 == 0")]
#[rr::requires("rate / 8 <= 25")]
pub fn keccak_absorb(state: &mut KeccakState, block: &[u8], rate: usize)
```

**Proof Obligations:**
- [x] Lane index `i = x + 5*y` always in `0..25`
- [x] Rotation offsets in ρ step are all < 64
- [x] π permutation indices stay in bounds
- [x] χ step reads/writes only valid lanes
- [ ] Round constant table has exactly 24 entries
- [ ] Absorb never exceeds rate bytes
- [ ] Squeeze never exceeds rate bytes

---

### 4. `keccak::sha3` - SHA3-256

**File:** `src/keccak/sha3.rs`

**Properties:**
- Rate = 136 bytes (1088 bits)
- Domain separator = 0x06
- Output = 32 bytes
- Padding: `0x06 || 0x00* || 0x80`

**Annotations:**
```rust
#[rr::ensures("result.len() == 32")]
#[rr::ensures("result == SHA3-256(data) per FIPS 202")]
pub fn sha3_256(data: &[u8]) -> [u8; 32]
```

**Proof Obligations:**
- [x] Output length is exactly 32 bytes
- [x] Padding byte positions are correct
- [ ] Multi-block absorption is sequential

---

### 5. `keccak::shake` - SHAKE256 XOF

**File:** `src/keccak/shake.rs`

**Properties:**
- Rate = 136 bytes
- Domain separator = 0x1F
- Arbitrary output length
- Streaming: absorb*, then squeeze*

**Annotations:**
```rust
#[rr::requires("!self.squeezing")]
pub fn absorb(&mut self, data: &[u8])

#[rr::ensures("self.squeezing == true")]
#[rr::ensures("output filled with XOF bytes")]
pub fn squeeze(&mut self, output: &mut [u8])
```

**Proof Obligations:**
- [x] Cannot absorb after squeezing
- [x] Buffer position never exceeds RATE
- [x] Permute called between squeeze blocks
- [ ] Streaming equivalence: `absorb(a); absorb(b)` == `absorb(a||b)`

---

### 6. `aead` - Ascon-128a

**File:** `src/aead/mod.rs`

**Properties:**
- Key: 16 bytes, Nonce: 16 bytes, Tag: 16 bytes
- 12 rounds for init/finalize, 8 for data
- Seal/Open round-trip correctness
- Failed open reveals no plaintext

**Annotations:**
```rust
#[rr::requires("key.len() == 16 && nonce.len() == 16")]
#[rr::requires("ciphertext.len() >= plaintext.len() + 16")]
#[rr::ensures("open(key, nonce, ad, result) == Ok(plaintext)")]
#[rr::ct]
pub fn seal(&self, nonce: &[u8], ad: &[u8], plaintext: &[u8], ciphertext: &mut [u8])
    -> Result<usize, AeadError>

#[rr::ensures("result.is_err() ==> plaintext buffer is zeroized")]
#[rr::ct]
pub fn open(&self, nonce: &[u8], ad: &[u8], ciphertext: &[u8], plaintext: &mut [u8])
    -> Result<usize, AeadError>
```

**Proof Obligations:**
- [x] Key/nonce size validation
- [x] Output buffer size validation
- [x] Tag comparison is constant-time
- [x] Plaintext zeroized on auth failure
- [ ] State zeroized after use
- [ ] Permutation round counts correct

---

### 7. `cbor` - Canonical CBOR Codec

**File:** `src/cbor/mod.rs`

**Properties:**
- Canonical encoding (sorted keys, minimal integer encoding)
- Total decoder (all inputs map to Ok or Err, no panics)
- Round-trip: `decode(encode(x)) == Ok(x)`

**Annotations:**
```rust
#[rr::ensures("match result { Ok(_) => true, Err(_) => true }")]
#[rr::ensures("no partial state mutation on error")]
pub fn decode_map_header(&mut self) -> Result<usize, CborError>

#[rr::ensures("self.position() <= self.data.len()")]
pub fn skip_value(&mut self) -> Result<(), CborError>
```

**Proof Obligations:**
- [x] Decoder never reads past buffer end
- [x] All decode paths return Result (no panics)
- [x] Encoder produces canonical form
- [ ] Round-trip property for all supported types

---

### 8. `nonce` - Deterministic Nonce Derivation

**File:** `src/nonce/mod.rs`

**Properties:**
- Nonce = HKDF-Expand(SHAKE256, key_material, info || counter || entry_id || domain)
- Injectivity: distinct (counter, entry_id, domain) → distinct nonces

**Annotations:**
```rust
#[rr::requires("counter < 2^48")]
#[rr::ensures("(ctr1, id1, dom1) != (ctr2, id2, dom2) ==> result1 != result2")]
pub fn derive(&self, counter: u64, entry_id: u32, domain: u8) -> [u8; 16]
```

**Proof Obligations:**
- [x] Counter bounds check
- [ ] Injectivity lemma (model-level, assumes SHAKE256 collision resistance)
- [x] Output length is exactly 16 bytes

---

### 9. `license` - License Token Schema

**File:** `src/license/mod.rs`

**Properties:**
- CBOR encoding with 6 fields (sorted keys)
- Total decoder
- Signature covers canonical signable portion

**Annotations:**
```rust
#[rr::ensures("result.is_ok() ==> decode(encode(result)) == result")]
pub fn decode(data: &[u8]) -> Result<License, LicenseError>

#[rr::ensures("buffer[..n] is canonical CBOR")]
pub fn encode(&self, buffer: &mut [u8]) -> Result<usize, LicenseError>
```

**Proof Obligations:**
- [x] All field length checks
- [x] Feature count bounds
- [x] Signature length bounds
- [ ] Canonical key ordering in encode

---

### 10. `receipt` - Attestation Receipt Schema

**File:** `src/receipt/mod.rs`

**Properties:**
- Similar to License: CBOR with total parsing
- Digest is SHA3-256 of file/directory content
- Timestamp source is recorded

**Proof Obligations:**
- [x] Digest length is 32 bytes
- [x] All string length bounds
- [ ] Canonical encoding

---

### 11. `merkle` - Batch Anchoring Tree

**File:** `src/merkle/mod.rs`

**Properties:**
- Binary tree with SHA3-256 internal nodes
- Proof verification: recompute root from leaf + siblings
- Deterministic: same leaves → same root

**Annotations:**
```rust
#[rr::ensures("result == SHA3-256(left || right)")]
fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32]

#[rr::ensures("verify(proof, leaf, root) == true")]
pub fn prove(&self, index: usize) -> Option<MerkleProof>
```

**Proof Obligations:**
- [x] Index bounds in proof generation
- [x] Proof verification recomputes correct root
- [ ] Tree construction is deterministic

---

### 12. `mldsa` - ML-DSA-87 Signatures

**File:** `src/mldsa/mod.rs`

**Properties:**
- Public key: 2592 bytes
- Secret key: 4896 bytes (zeroized on drop)
- Signature: 4627 bytes
- Deterministic from seed

**Annotations:**
```rust
#[rr::ensures("keypair is deterministic from seed")]
#[rr::ensures("secret key zeroized on drop")]
pub fn from_seed(seed: &[u8]) -> Result<KeyPair, MlDsaError>

#[rr::ensures("verify(pk, msg, sign(sk, msg)) == true")]
#[rr::ct]
pub fn sign(&self, message: &[u8]) -> Result<Signature, MlDsaError>
```

**Proof Obligations:**
- [x] Key/signature size validation
- [x] Seed size validation
- [ ] SecretKey zeroization on drop
- [ ] Signature verification soundness

---

## Known Answer Tests (KATs)

| Algorithm | Source | Status |
|-----------|--------|--------|
| SHA3-256 | NIST CAVP | Implemented |
| SHAKE256 | NIST CAVP | Implemented |
| Ascon-128a | Ascon reference | Partial |
| ML-DSA-87 | NIST PQC | Placeholder |
| CBOR | RFC 8949 examples | Implemented |

---

## CI Integration

```yaml
# .github/workflows/verify.yml
jobs:
  prove:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install Coq + Iris + RefinedRust
        run: make setup-rr
      - name: Prove anubis_core
        run: make prove
      - name: Run KATs
        run: cargo test -p anubis_core --release
```

---

## Proof Reproduction

```bash
# Prerequisites
opam install coq=8.18 coq-iris

# Clone RefinedRust
git clone https://gitlab.mpi-sws.org/iris/refinedrust
cd refinedrust && make install

# Prove Anubis Notary
cd anubis-notary
make prove
```

---

## Threat Model

### In Scope
- Memory safety violations (buffer overflows, use-after-free)
- Logic errors in crypto implementations
- Timing side channels via secret-dependent branches
- Malformed input handling (parser crashes)
- Nonce reuse (prevented by deterministic derivation)

### Out of Scope
- Physical side channels (power, EM, cache)
- Compiler bugs
- OS/hardware vulnerabilities
- Social engineering
- Cryptographic breaks (e.g., quantum attacks on classical crypto)

---

## Verification Status

| Module | A.R.E. | Functional | CT | Coq Spec | Overall |
|--------|--------|------------|-----|----------|---------|
| ct | Planned | Planned | Audited | crypto_refinements.v | **Specified** |
| bytes | Planned | Planned | N/A | crypto_refinements.v | **Specified** |
| keccak | Planned | Planned | N/A | crypto_model.v | **Specified** |
| sha3 | Planned | Planned | N/A | crypto_model.v | **Specified** |
| shake | Planned | Planned | N/A | crypto_model.v | **Specified** |
| aead | Planned | Planned | Audited | aead_spec.v | **Specified** |
| cbor | Planned | Planned | N/A | cbor_spec.v | **Partial** |
| nonce | Planned | Planned | N/A | crypto_refinements.v | **Specified** |
| license | Planned | Planned | N/A | - | **Annotated** |
| receipt | Planned | Planned | N/A | - | **Annotated** |
| merkle | Planned | Partial | N/A | merkle_spec.v | **Partial** |
| mldsa | Planned | Planned | Audited | mldsa_spec.v | **Specified** |
| kdf | Planned | Planned | N/A | argon2_spec.v | **Specified** |

**Legend:**
- Planned: RefinedRust annotations exist, verification not yet run
- Partial: Some Coq proofs completed, others use `Admitted`
- Audited: Manual code review for constant-time discipline
- Specified: Full Coq/Iris specification written, proofs pending toolchain
- Annotated: RefinedRust comments in source, no separate spec file

---

## Coq Specification Files

Coq specifications are located in `proofs/theories/`:

| File | Description | Proof Status |
|------|-------------|--------------|
| `crypto_model.v` | Foundation types, axioms | Complete |
| `mldsa_spec.v` | ML-DSA-87 full spec | Mostly Admitted |
| `aead_spec.v` | ChaCha20Poly1305 | Mostly Admitted |
| `security_games.v` | EUF-CMA, IND-CPA, INT-CTXT | All Admitted |
| `merkle_spec.v` | Merkle tree properties | **Partially Proven** |
| `cbor_spec.v` | RFC 8949 canonical CBOR | Roundtrip proven |
| `argon2_spec.v` | KDF parameters | Proven |
| `xdg_spec.v` | XDG path specs | Complete |
| `crypto_refinements.v` | RefinedRust bindings | Type definitions |
| `crypto_tactics.v` | Proof automation | Complete |

**Proven Lemmas in merkle_spec.v:**
- `prefix_injective` - Domain separation proof
- `build_level_length` - Tree construction termination
- `build_level_nonempty` - Non-emptiness preservation
- `build_tree_aux_valid` - Recursive validity
- `batch_size_valid` - Full batch theorem

To check specifications (requires Coq 8.18+):
```bash
cd proofs
coqc -Q theories AnubisNotary theories/crypto_model.v
coqc -Q theories AnubisNotary theories/merkle_spec.v
# etc.
```

**Note:** The RefinedRust toolchain is not yet integrated. Annotations in Rust source
serve as specifications for future verification when the toolchain is available.

---

## RefinedRust Annotation Files

Complete RefinedRust annotations linking Rust source to Coq specifications are in
`specs/refinedrust/annotations/`:

| File | Module | Key Specifications |
|------|--------|-------------------|
| `ct_annotations.rs` | ct | ct_select, ct_eq, ct_lt_u64, constant-time discipline |
| `bytes_annotations.rs` | bytes | load_le64, store_le64, rotr64, SecretBytes zeroization |
| `keccak_annotations.rs` | keccak | KeccakState, keccak_f1600, theta/rho/pi/chi/iota steps |
| `aead_annotations.rs` | aead | Ascon128a, seal/open with round-trip correctness |
| `cbor_annotations.rs` | cbor | Encoder/Decoder totality, canonical encoding |
| `nonce_annotations.rs` | nonce | NonceDeriver, derive with injectivity guarantee |
| `mldsa_annotations.rs` | mldsa | PublicKey/SecretKey/Signature, zeroization on drop |
| `kdf_annotations.rs` | kdf | Argon2idParams validation, HKDF extract/expand |
| `merkle_annotations.rs` | merkle | MerkleTree, MerkleProof, domain separation |
| `license_annotations.rs` | license | License encode/decode, round-trip, canonical keys |
| `receipt_annotations.rs` | receipt | Receipt encode/decode, TimeSource, AnchorType |

**Total Annotation Files:** 11

Each annotation file contains:
- Type refinements (`#[rr::refined_by]`, `#[rr::invariant]`)
- Function specifications (`#[rr::requires]`, `#[rr::ensures]`)
- Loop invariants (`#[rr::loop_inv]`)
- Constant-time markers (`#[rr::ct]`)
- Verification conditions (Coq theorems to prove)
