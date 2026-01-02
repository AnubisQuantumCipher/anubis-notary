# Contributing to Anubis Notary

Thank you for your interest in contributing to Anubis Notary. This document provides guidelines and information for contributors.

## Table of Contents

- [Code of Conduct](#code-of-conduct)
- [Getting Started](#getting-started)
- [Development Setup](#development-setup)
- [Making Contributions](#making-contributions)
- [Coding Standards](#coding-standards)
- [Testing Requirements](#testing-requirements)
- [Security Considerations](#security-considerations)
- [Pull Request Process](#pull-request-process)

## Code of Conduct

This project maintains a professional and inclusive environment. Contributors are expected to:

- Be respectful and constructive in all communications
- Focus on technical merit and project goals
- Accept constructive criticism gracefully
- Prioritize security and correctness over convenience

## Getting Started

### Prerequisites

- **Rust 1.75+** - Install via [rustup](https://rustup.rs/)
- **Rocq/Coq 9.0+** - For proof verification (optional for most contributions)
- **Docker** - For running proofs in isolation (optional)

### Fork and Clone

```bash
# Fork the repository on GitHub, then:
git clone https://github.com/YOUR_USERNAME/anubis-notary.git
cd anubis-notary
```

## Development Setup

### Building the Project

```bash
# Build in release mode
cargo build --release

# Run all tests
cargo test --all

# Run clippy lints
cargo clippy --all -- -D warnings
```

### Running Proofs (Optional)

```bash
# Using Docker (recommended)
cd docker
./run-proofs.sh make all

# Or manually with Coq installed
cd proofs
make all
```

### Mina Bridge Development

```bash
# Build the TypeScript zkApp contracts
cd mina-bridge
npm install
npm run build

# Key files:
# - src/AnubisAnchor.ts    - Single anchor contract
# - src/AnubisBatchVault.ts - Batch vault contract (8x savings)
# - mina-bridge.js         - Compiled bridge script
```

## Making Contributions

### Types of Contributions

We welcome the following types of contributions:

| Type | Description |
|------|-------------|
| **Bug Fixes** | Corrections to existing functionality |
| **Security Patches** | Fixes for security vulnerabilities (see [Security](#security-considerations)) |
| **Documentation** | Improvements to docs, comments, or examples |
| **Tests** | Additional test coverage |
| **Features** | New functionality (discuss first in an issue) |
| **Proofs** | Formal verification improvements |

### Before You Start

1. **Check existing issues** - Someone may already be working on it
2. **Open an issue first** - For significant changes, discuss before implementing
3. **Review the architecture** - Understand how your change fits

## Coding Standards

### Rust Code

```rust
// Use explicit error handling, no unwrap() in library code
fn process_data(data: &[u8]) -> Result<Output, Error> {
    // ...
}

// Document public APIs
/// Signs the provided message using ML-DSA-87.
///
/// # Arguments
/// * `message` - The message bytes to sign
///
/// # Returns
/// A 4,627-byte signature on success
pub fn sign(message: &[u8]) -> Result<Signature, SignError> {
    // ...
}

// Use SAFETY comments for any unsafe code
// SAFETY: pointer is valid and aligned, checked by caller
unsafe { ... }
```

### Style Guidelines

- **Formatting**: Run `cargo fmt` before committing
- **Lints**: Code must pass `cargo clippy -- -D warnings`
- **No warnings**: All code must compile without warnings
- **Comments**: Explain *why*, not *what*

### Commit Messages

Use clear, descriptive commit messages:

```
type(scope): brief description

- Detail 1
- Detail 2
```

Types: `feat`, `fix`, `docs`, `test`, `refactor`, `security`, `perf`

Examples:
```
fix(signing): handle empty message edge case
feat(cli): add --output flag to verify command
security(kdf): increase Argon2id iterations
docs(readme): update installation instructions
```

## Testing Requirements

### All Changes Must Include Tests

```bash
# Run the full test suite
cargo test --all

# Run specific tests
cargo test --package anubis_core

# Run with verbose output
cargo test --all -- --nocapture
```

### Test Categories

| Category | Location | Purpose |
|----------|----------|---------|
| Unit tests | `src/*.rs` | Function-level correctness |
| Integration tests | `tests/` | End-to-end workflows |
| Property tests | `tests/property_tests.rs` | Invariant verification |
| Fuzz tests | `fuzz/` | Input validation |

### Coverage Expectations

- New code should have >80% test coverage
- Security-critical paths require 100% coverage
- Edge cases must be explicitly tested

## Security Considerations

### Reporting Vulnerabilities

**Do NOT open public issues for security vulnerabilities.**

Report security issues privately to: **sic.tau@pm.me**

Include:
- Description of the vulnerability
- Steps to reproduce
- Potential impact assessment
- Suggested fix (if any)

### Security Requirements for Code

All contributions must adhere to:

1. **Constant-time operations** for secret data
2. **Zeroization** of all sensitive memory after use
3. **No panics** in library code (use `Result` types)
4. **Input validation** at all public API boundaries
5. **No `unsafe` code** without explicit SAFETY documentation

### Cryptographic Changes

Changes to cryptographic code require:

- Justification referencing relevant standards (FIPS, RFC, etc.)
- Additional review by maintainers
- Extended test coverage including known-answer tests
- Formal proof updates if applicable

## Pull Request Process

### 1. Prepare Your Changes

```bash
# Create a feature branch
git checkout -b feature/your-feature-name

# Make your changes, then:
cargo fmt
cargo clippy --all -- -D warnings
cargo test --all
```

### 2. Submit the Pull Request

- Fill out the PR template completely
- Link related issues
- Provide clear description of changes
- Include test results

### 3. Review Process

| Step | Description |
|------|-------------|
| **Automated checks** | CI runs tests, lints, and builds |
| **Code review** | Maintainer reviews for correctness and style |
| **Security review** | For security-sensitive changes |
| **Approval** | At least one maintainer approval required |

### 4. After Merge

- Delete your feature branch
- Verify the change in the next release

## Questions?

- Open a [GitHub Discussion](https://github.com/AnubisQuantumCipher/anubis-notary/discussions)
- Check existing [Issues](https://github.com/AnubisQuantumCipher/anubis-notary/issues)

---

Thank you for contributing to post-quantum cryptography and open-source security tooling.
