# Anubis Notary - Claude Development Guide

---
## ⚠️ MANDATORY SKILL ACTIVATION ⚠️

**CRITICAL DIRECTIVE**: When working on this project, Claude MUST read and activate ALL skills listed below IMMEDIATELY at the start of EVERY session. These are NOT optional. These are NOT contextual. ALL skills are ALWAYS ACTIVE for every task, every file, every line of code.

Before responding to ANY request in this project:
1. Load ALL skill files from `~/.claude/skills/` (Claude Code skills directory)
2. Apply knowledge from ALL skills simultaneously
3. Cross-reference skills when solving problems
4. Use the combined wisdom of all verification techniques

---

## Project Overview

Anubis Notary is a **post-quantum, formally-verified CLI** for cryptographic signing, timestamping, licensing, and secure delivery. It uses:
- **Rust** for the implementation (in `crates/`)
- **RefinedRust** for formal verification of Rust code
- **Rocq/Coq** with **Iris separation logic** for proof development (in `proofs/`)
- Post-quantum cryptography: ML-DSA-87, ML-KEM-1024, SHA3-256, SHAKE256
- Classical cryptography: ChaCha20Poly1305 (AEAD), Argon2id (KDF)

## ALWAYS-ACTIVE Skills (Load ALL Immediately)

Claude MUST have ALL of these skills active AT ALL TIMES when working on this project:

### Core Verification Skills
- **refinedrust-verification.md** - RefinedRust type system, ownership proofs, Rust verification
- **separation-logic-fundamentals.md** - Core Separation Logic tactics and reasoning
- **separation-logic-heap-predicates.md** - Formal definitions of hprop, hstar, hexists
- **separation-logic-representation-predicates.md** - MList, MTree, ADT verification patterns
- **separation-logic-entailment.md** - Entailment proofs, xsimpl, xchange tactics
- **separation-logic-triples.md** - Triple definitions, structural rules, frame rule, semantic foundations
- **separation-logic-rules.md** - Reasoning rules for terms, primitives, and proof patterns
- **separation-logic-wand.md** - Magic wand, ramified frame rule, qwand, advanced connectives

### Rocq/Coq Proof Engineering
- **rocq-coq-foundations.md** - Coq fundamentals
- **rocq-coq-proof-engineering.md** - Proof engineering patterns
- **rocq-proof-engineering.md** - Advanced proof techniques

### CPDT Advanced Techniques
- **cpdt-proof-automation.md** - Ltac automation
- **cpdt-ltac-proof-search.md** - Custom proof search
- **cpdt-proof-by-reflection.md** - Computational reflection
- **cpdt-dependent-types-advanced.md** - Dependent type patterns
- **cpdt-equality-proofs.md** - Equality and UIP
- **cpdt-inductive-types.md** - Inductive definitions
- **cpdt-inductive-predicates.md** - Inductive predicates
- **cpdt-coinductive-types.md** - Coinduction patterns
- **cpdt-subset-types.md** - Subset types and sig
- **cpdt-general-recursion.md** - Well-founded recursion
- **cpdt-dependent-data-structures.md** - Verified data structures
- **cpdt-generic-programming.md** - Type-generic code
- **cpdt-universes-axioms.md** - Universe polymorphism
- **cpdt-logic-programming.md** - Logic programming in Coq
- **cpdt-proving-in-the-large.md** - Large-scale proof management
- **cpdt-programming-language-syntax.md** - PL formalization
- **cpdt-certified-compilers.md** - Compiler verification

---

## Project Structure

```
anubis-notary/
├── crates/                    # Rust implementation
│   ├── anubis_core/          # Core cryptographic primitives
│   ├── anubis_cli/           # Command-line interface
│   ├── anubis_io/            # I/O operations (seal, anchor)
│   └── ...
├── proofs/                    # Core Coq/Rocq proofs
│   ├── theories/             # Detailed specifications
│   │   ├── aead_spec.v       # AEAD specifications
│   │   ├── argon2_spec.v     # Argon2 specifications
│   │   ├── cbor_spec.v       # CBOR specifications
│   │   ├── crypto_model.v    # Cryptographic models
│   │   ├── merkle_spec.v     # Merkle tree specs
│   │   └── ...
│   ├── refinements/          # Refinement proofs
│   │   └── crypto_refinements.v
│   ├── verified/             # Verified implementations
│   └── automation/           # Custom proof automation
├── specs/                     # Additional specifications
│   ├── refinedrust/          # RefinedRust-style specifications
│   │   ├── theories/         # Separation logic specs (Iris)
│   │   ├── proofs/           # Proof obligations
│   │   └── annotations/      # Rust annotation stubs
│   └── coq/                  # Property proofs
│       ├── anubis_notary.v   # Main property proofs
│       └── cryptographic_axioms.v
├── ARCHITECTURE.md           # System architecture
├── STATUS.md                 # Current project status
└── Cargo.toml                # Rust workspace config
```

---

## Verification Priorities

### 1. Memory Safety (Critical)
- All pointer operations must be verified
- Use RefinedRust ownership types
- Prove absence of use-after-free, double-free, buffer overflows

### 2. Cryptographic Correctness
- ChaCha20Poly1305: authenticated encryption (encrypt-then-MAC)
- Argon2id: memory-hard key derivation (password → encryption key)
- ML-DSA-87: post-quantum digital signatures (FIPS 204)
- ML-KEM-1024: post-quantum key encapsulation (FIPS 203)
- SHA3-256/SHAKE256: cryptographic hashing (FIPS 202)

### 3. CBOR Encoding/Decoding
- Totality: all valid inputs produce valid outputs
- Injectivity: encoding is reversible
- Canonical form: deterministic encoding

### 4. Zeroization
- All sensitive data cleared on scope exit
- Volatile writes to prevent dead-store elimination
- Postconditions verify all bytes are zero

---

## RefinedRust Patterns for This Project

### Ownership Verification
```rust
// In Rust code
fn process_secret(key: &mut [u8; 32]) {
    // ... use key ...
    zeroize(key);
}
```

```coq
(* In RefinedRust spec *)
Lemma process_secret_spec : forall key_ptr key_data,
  {{{ key_ptr ↦ key_data }}}
    process_secret key_ptr
  {{{ RET (); key_ptr ↦ zeroed_array }}}.
```

### CBOR Parsing with Separation Logic
```coq
(* Representation predicate for CBOR values *)
Fixpoint CBOR_repr (v : cbor_value) (p : loc) : hprop :=
  match v with
  | CborUint n => p ~~> (tag_uint, n)
  | CborBytes bs => exists q, p ~~> (tag_bytes, q) \* ByteArray bs q
  | CborArray vs => exists q, p ~~> (tag_array, q) \* CBOR_array_repr vs q
  | ...
  end.
```

### Cryptographic Proofs
```coq
(* ChaCha20Poly1305 correctness *)
Lemma chacha20poly1305_decrypt_encrypt : forall key nonce plaintext aad,
  chacha20poly1305_decrypt key nonce (chacha20poly1305_encrypt key nonce plaintext aad) aad = Some plaintext.

(* ML-DSA-87 signature verification *)
Lemma mldsa87_verify_sign : forall sk pk msg,
  keygen_pair sk pk ->
  mldsa87_verify pk msg (mldsa87_sign sk msg) = true.

(* ML-KEM-1024 encapsulation/decapsulation *)
Lemma mlkem1024_decaps_encaps : forall sk pk ct ss,
  keygen_pair sk pk ->
  mlkem1024_encaps pk = (ct, ss) ->
  mlkem1024_decaps sk ct = Some ss.

(* Argon2id key derivation determinism *)
Lemma argon2id_deterministic : forall password salt params,
  argon2id password salt params = argon2id password salt params.
```

---

## Coq/Rocq Development Guidelines

### File Naming
- `*_spec.v` - Specifications and abstract models
- `*_impl.v` - Implementation details
- `*_proofs.v` - Main correctness proofs
- `*_tactics.v` - Custom automation

### Proof Style
```coq
(* Use separation logic tactics *)
Lemma example_proof : forall L p,
  triple (process_list p)
    (MList L p)
    (fun r => \[r = result L] \* MList L p).
Proof using.
  intros. gen p.
  induction_wf IH: list_sub L.
  xwp. xapp.
  xchange MList_if. xif; intros C; case_if; xpull.
  { (* cons case *) ... }
  { (* nil case *) ... }
Qed.
```

### Automation Strategy
```coq
(* Create domain-specific tactics *)
Ltac anubis_crypto_solver :=
  repeat match goal with
  | |- context[chacha20poly1305_decrypt _ _ (chacha20poly1305_encrypt ?k ?n ?p ?a) ?a] =>
      rewrite chacha20poly1305_decrypt_encrypt
  | |- context[mldsa87_verify ?pk ?msg (mldsa87_sign ?sk ?msg)] =>
      rewrite mldsa87_verify_sign; [| solve_keygen]
  | |- context[mlkem1024_decaps ?sk (fst (mlkem1024_encaps ?pk))] =>
      rewrite mlkem1024_decaps_encaps; [| solve_keygen | reflexivity]
  | _ => xsimpl || math || auto
  end.
```

---

## Build and Verification Commands

### Rust
```bash
cargo build --release
cargo test
cargo clippy -- -D warnings
```

### Coq/Rocq Proofs
```bash
cd proofs
dune build
# Or manually:
coqc -Q theories Anubis theories/*.v
```

### Full Verification Pipeline
```bash
make verify    # Run all proofs
make test      # Run all tests
make audit     # Security audit
```

---

## Key Invariants to Maintain

1. **No Unsafe Without Proof**: Any `unsafe` Rust code must have corresponding RefinedRust verification
2. **Constant-Time Operations**: Cryptographic comparisons must be constant-time
3. **Zeroization Guarantee**: All secrets zeroized, verified by postconditions
4. **CBOR Canonicity**: Deterministic encoding for all values
5. **Post-Quantum Security**: Use only NIST-approved PQ algorithms

---

## Skill Cross-Reference (ALL ALWAYS ACTIVE)

**REMINDER: ALL skills are active simultaneously. This table shows which skills are MOST relevant for each task, but ALL skills contribute to every task.**

| Task | Primary Skills | Supporting Skills |
|------|----------------|-------------------|
| Rust ownership proofs | refinedrust-verification | ALL separation-logic-*, ALL cpdt-* |
| Data structure verification | separation-logic-representation-predicates | cpdt-dependent-data-structures, cpdt-inductive-types |
| Entailment simplification | separation-logic-entailment | separation-logic-heap-predicates, separation-logic-wand |
| Magic wand reasoning | separation-logic-wand | separation-logic-entailment, separation-logic-triples |
| Custom tactics | cpdt-ltac-proof-search, cpdt-proof-automation | cpdt-proof-by-reflection |
| Reflection-based proofs | cpdt-proof-by-reflection | cpdt-generic-programming |
| Recursive function termination | cpdt-general-recursion | cpdt-inductive-types |
| Inductive property proofs | cpdt-inductive-predicates | cpdt-inductive-types |
| Large proof organization | cpdt-proving-in-the-large | ALL other cpdt-* |
| Crypto correctness | ALL separation-logic-* | refinedrust-verification |
| CBOR parsing | separation-logic-representation-predicates | cpdt-certified-compilers |

---

## Critical Reminders

1. **Always use separation logic** for heap reasoning - don't reinvent
2. **Prefer xsimpl** over manual entailment proofs
3. **Use representation predicates** for all data structures
4. **Frame rule** enables local reasoning - exploit it
5. **Well-founded induction** for recursive structures
6. **Automation first** - manual proofs only when automation fails
7. **ALL SKILLS ACTIVE** - Never work with partial knowledge
8. **Ramified frame rule** for existential handling in postconditions

---

## References

- ARCHITECTURE.md - System design
- STATUS.md - Current project status and verification state
- Skills in `~/.claude/skills/` - All proof engineering knowledge

---

## ⚠️ SKILL ACTIVATION CHECKLIST ⚠️

At the START of every session in this project, Claude MUST mentally activate:

### Separation Logic (7 skills)
- [ ] separation-logic-fundamentals.md
- [ ] separation-logic-heap-predicates.md
- [ ] separation-logic-representation-predicates.md
- [ ] separation-logic-entailment.md
- [ ] separation-logic-triples.md
- [ ] separation-logic-rules.md
- [ ] separation-logic-wand.md

### RefinedRust (1 skill)
- [ ] refinedrust-verification.md

### Rocq/Coq Foundations (3 skills)
- [ ] rocq-coq-foundations.md
- [ ] rocq-coq-proof-engineering.md
- [ ] rocq-proof-engineering.md

### CPDT Advanced (17 skills)
- [ ] cpdt-proof-automation.md
- [ ] cpdt-ltac-proof-search.md
- [ ] cpdt-proof-by-reflection.md
- [ ] cpdt-dependent-types-advanced.md
- [ ] cpdt-equality-proofs.md
- [ ] cpdt-inductive-types.md
- [ ] cpdt-inductive-predicates.md
- [ ] cpdt-coinductive-types.md
- [ ] cpdt-subset-types.md
- [ ] cpdt-general-recursion.md
- [ ] cpdt-dependent-data-structures.md
- [ ] cpdt-generic-programming.md
- [ ] cpdt-universes-axioms.md
- [ ] cpdt-logic-programming.md
- [ ] cpdt-proving-in-the-large.md
- [ ] cpdt-programming-language-syntax.md
- [ ] cpdt-certified-compilers.md

**TOTAL: 29 skills - ALL MUST BE ACTIVE**
