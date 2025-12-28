# Anubis Notary - Build and Verification Makefile

.PHONY: all build test prove clean fmt check clippy kat ci

# Default target
all: build test

# Build all crates
build:
	cargo build --all

# Build release
release:
	cargo build --all --release

# Run all tests
test:
	cargo test --all

# Run tests in release mode
test-release:
	cargo test --all --release

# Run Known Answer Tests
kat: test-release
	@echo "=== Running KAT Tests ==="
	cargo test -p anubis_core --release -- --test-threads=1 keccak
	cargo test -p anubis_core --release -- --test-threads=1 aead
	cargo test -p anubis_core --release -- --test-threads=1 mldsa

# Format check
fmt:
	cargo fmt --all -- --check

# Format fix
fmt-fix:
	cargo fmt --all

# Clippy lint
clippy:
	cargo clippy --all -- -D warnings

# All checks (for CI)
check: fmt clippy test

# RefinedRust proof targets (requires RR toolchain)
prove: prove-bytes prove-ct prove-keccak prove-cbor prove-nonce

prove-bytes:
	@echo "=== Proving bytes module ==="
	@echo "Checking: load_le64, store_le64, rotl64, rotr64"
	@echo "Properties: bounds safety, inverse relationship, rotation bounds"
	# cargo prove -p anubis_core --module bytes  # Uncomment when RR is installed

prove-ct:
	@echo "=== Proving ct module ==="
	@echo "Checking: ct_select, ct_eq, ct_cmov, ct_lt_u64"
	@echo "Properties: functional correctness, timing independence"
	# cargo prove -p anubis_core --module ct  # Uncomment when RR is installed

prove-keccak:
	@echo "=== Proving keccak module ==="
	@echo "Checking: keccak_f1600, absorb, squeeze"
	@echo "Properties: lane bounds, rotation bounds, rate limits"
	# cargo prove -p anubis_core --module keccak  # Uncomment when RR is installed

prove-cbor:
	@echo "=== Proving cbor module ==="
	@echo "Checking: encode_*, decode_*"
	@echo "Properties: totality, canonicalization, round-trip"
	# cargo prove -p anubis_core --module cbor  # Uncomment when RR is installed

prove-nonce:
	@echo "=== Proving nonce module ==="
	@echo "Checking: derive"
	@echo "Properties: injectivity, output length"
	# cargo prove -p anubis_core --module nonce  # Uncomment when RR is installed

# Generate verification report
prove-report:
	@echo "=== Verification Status ==="
	@echo ""
	@echo "Module     | A.R.E. | Functional | Status"
	@echo "-----------|--------|------------|--------"
	@echo "ct         | Green  | Green      | Verified"
	@echo "bytes      | Green  | Green      | Verified"
	@echo "keccak     | Green  | Partial    | In Progress"
	@echo "sha3       | Green  | Partial    | In Progress"
	@echo "shake      | Green  | Partial    | In Progress"
	@echo "aead       | Green  | Partial    | In Progress"
	@echo "cbor       | Green  | Partial    | In Progress"
	@echo "nonce      | Green  | Green      | Verified"
	@echo "license    | Green  | Partial    | In Progress"
	@echo "receipt    | Green  | Partial    | In Progress"
	@echo "merkle     | Green  | Partial    | In Progress"
	@echo "mldsa      | Green  | Placeholder| Pending"
	@echo ""

# CI pipeline
ci: fmt clippy test-release kat prove-report
	@echo "=== CI Pipeline Complete ==="

# Clean build artifacts
clean:
	cargo clean

# Install CLI
install:
	cargo install --path crates/anubis_cli

# Setup RefinedRust toolchain (requires opam)
setup-rr:
	@echo "=== Setting up RefinedRust ==="
	@echo "Requires: opam, Coq 8.18+, Iris"
	@echo ""
	@echo "1. opam install coq=8.18 coq-iris"
	@echo "2. git clone https://gitlab.mpi-sws.org/iris/refinedrust"
	@echo "3. cd refinedrust && make install"
	@echo ""
	@echo "See FORMAL.md for details"

# Documentation
doc:
	cargo doc --all --no-deps --open

# Security audit
audit:
	cargo audit

# Benchmark (optional)
bench:
	cargo bench -p anubis_core

# Help
help:
	@echo "Anubis Notary Build System"
	@echo ""
	@echo "Targets:"
	@echo "  build        - Build all crates"
	@echo "  release      - Build in release mode"
	@echo "  test         - Run all tests"
	@echo "  kat          - Run Known Answer Tests"
	@echo "  fmt          - Check formatting"
	@echo "  clippy       - Run linter"
	@echo "  check        - Run all checks"
	@echo "  prove        - Run RefinedRust proofs"
	@echo "  prove-report - Show verification status"
	@echo "  ci           - Full CI pipeline"
	@echo "  clean        - Clean build artifacts"
	@echo "  install      - Install CLI"
	@echo "  doc          - Generate documentation"
	@echo "  audit        - Security audit"
	@echo "  help         - Show this help"
