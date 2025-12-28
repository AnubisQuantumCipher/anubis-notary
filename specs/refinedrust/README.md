# RefinedRust Verification Strategy for Anubis Core

## Overview

This document describes the formal verification strategy for the `anubis_core` crate
using RefinedRust methodology. We provide Coq/Iris specifications, refinement type
annotations, and proof obligations for the cryptographic primitives.

## Verification Targets

1. **ct module** - Constant-time primitives (timing-independent operations)
2. **bytes module** - Byte manipulation with bounds safety
3. **keccak module** - Keccak-f[1600] permutation with full functional correctness

## Directory Structure

```
specs/refinedrust/
├── README.md                    # This file
├── theories/
│   ├── ct_spec.v               # Constant-time specifications
│   ├── bytes_spec.v            # Byte manipulation specifications
│   ├── keccak_spec.v           # Keccak permutation specifications
│   ├── keccak_model.v          # Pure functional Keccak model
│   ├── sha3_spec.v             # SHA3-256 specification
│   ├── shake_spec.v            # SHAKE256 XOF specification
│   └── timing_model.v          # Constant-time execution model
└── proofs/
    ├── ct_proofs.v             # CT module proof obligations
    ├── bytes_proofs.v          # Bytes module proofs
    ├── keccak_proofs.v         # Keccak functional correctness
    └── sponge_proofs.v         # Sponge construction proofs
```

## Verification Levels

### Level 1: Memory Safety (NRTE)
- No out-of-bounds array access
- No integer overflow in index computations
- No panic paths when preconditions hold

### Level 2: Functional Correctness
- Functions compute specified mathematical results
- Inverse relationships (load/store, encode/decode)
- State machine invariants (absorb before squeeze)

### Level 3: Security Properties
- Constant-time execution model
- Zeroization completeness
- No secret-dependent control flow

## Proof Automation Strategy

We use RefinedRust's Lithium tactic framework for automation:
1. Refinement type annotations generate verification conditions
2. Lithium discharges most VCs automatically
3. Residual obligations proved manually in Coq
