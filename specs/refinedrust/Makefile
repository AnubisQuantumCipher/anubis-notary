# Anubis Notary - RefinedRust Verification Makefile
#
# Prerequisites:
#   - Rocq 9.1+ (or Coq 8.19+)
#   - Iris separation logic library
#   - RefinedRust framework
#   - Caesium Rust semantics
#   - dune 3.16+
#
# Installation:
#   opam install coq-iris coq-stdpp coq-equations
#   # Then install RefinedRust from source
#
# Targets:
#   make all           - Build all proofs
#   make prove         - Run full proof checking
#   make extract       - Generate OCaml extraction
#   make rocqworkers   - Run proofs with rocqworkers
#   make report        - Generate verification report

.PHONY: all build clean check-deps theories proofs help prove extract rocqworkers report verify

# opam switch for RefinedRust
OPAM_SWITCH := refinedrust
OPAM_ENV := eval $$(opam env --switch=$(OPAM_SWITCH) --set-switch)

# Directories
THEORIES_DIR := theories
PROOFS_DIR := ../../verified/output/anubis_verified/proofs
BUILD_DIR := _build/default/theories

# Default target
all: theories

# Check dependencies are installed
check-deps:
	@echo "Checking Rocq/Coq installation..."
	@which coqc > /dev/null || which rocqc > /dev/null || \
		(echo "Error: coqc/rocqc not found. Install Rocq 9.1+" && exit 1)
	@echo "Rocq/Coq version: $$(coqc --version 2>/dev/null || rocqc --version 2>/dev/null | head -1)"
	@echo "Checking dune installation..."
	@which dune > /dev/null || (echo "Error: dune not found. Install dune" && exit 1)
	@echo "dune version: $$(dune --version)"
	@echo "Checking opam switch..."
	@opam switch show 2>/dev/null || echo "Warning: opam not configured"
	@echo "Dependencies check passed."

# Build all theory files
theories: check-deps
	@echo "Building Rocq specifications..."
	dune build

# Build with verbose output
theories-verbose: check-deps
	@echo "Building Rocq specifications (verbose)..."
	dune build --display=verbose

# Full proof checking with timing
prove: check-deps
	@echo "=== Full Proof Verification ==="
	@echo "Started: $$(date)"
	@time dune build --force 2>&1 | tee _build/prove.log
	@echo ""
	@echo "=== Verification Complete ==="
	@echo "Finished: $$(date)"
	@echo "Log: _build/prove.log"

# Run extraction to generate OCaml
extract: theories
	@echo "=== Running Extraction ==="
	@mkdir -p _build/extracted
	dune exec -- coqc -R $(BUILD_DIR) anubis_notary \
		$(THEORIES_DIR)/extraction.v \
		-set "Extraction Directory=\"_build/extracted\"" 2>/dev/null || \
	echo "Extraction runs during build; check _build/extracted/"
	@echo "Extracted files in _build/extracted/"

# Run rocqworkers if available
rocqworkers: check-deps
	@echo "=== Running rocqworkers ==="
	@if command -v rocqworkers >/dev/null 2>&1; then \
		rocqworkers prove --config rocqworkers.toml; \
	else \
		echo "rocqworkers not found, using dune instead"; \
		$(MAKE) prove; \
	fi

# Generate verification report
report: theories
	@echo "=== Generating Verification Report ==="
	@mkdir -p _build/reports
	@echo "# Anubis Notary Verification Report" > _build/reports/proof_report.md
	@echo "" >> _build/reports/proof_report.md
	@echo "Generated: $$(date)" >> _build/reports/proof_report.md
	@echo "" >> _build/reports/proof_report.md
	@echo "## Summary" >> _build/reports/proof_report.md
	@echo "" >> _build/reports/proof_report.md
	@echo "| Metric | Count |" >> _build/reports/proof_report.md
	@echo "|--------|-------|" >> _build/reports/proof_report.md
	@echo "| Theory files | $$(find $(THEORIES_DIR) -name '*.v' | wc -l | tr -d ' ') |" >> _build/reports/proof_report.md
	@echo "| Proof files | $$(find $(PROOFS_DIR) -name '*.v' 2>/dev/null | wc -l | tr -d ' ') |" >> _build/reports/proof_report.md
	@echo "| Completed proofs (Qed) | $$(grep -r 'Qed\.' $(THEORIES_DIR)/*.v 2>/dev/null | wc -l | tr -d ' ') |" >> _build/reports/proof_report.md
	@echo "| Admitted proofs | $$(grep -r 'Admitted\.' $(THEORIES_DIR)/*.v 2>/dev/null | wc -l | tr -d ' ') |" >> _build/reports/proof_report.md
	@echo "" >> _build/reports/proof_report.md
	@echo "## Verified Modules" >> _build/reports/proof_report.md
	@echo "" >> _build/reports/proof_report.md
	@for f in $(THEORIES_DIR)/*.v; do \
		name=$$(basename $$f .v); \
		echo "- **$$name**: $$(head -5 $$f | grep -o '\*\*.*\*\*' | head -1 || echo 'Specification module')" >> _build/reports/proof_report.md; \
	done
	@echo "" >> _build/reports/proof_report.md
	@echo "## Bridge Modules" >> _build/reports/proof_report.md
	@echo "" >> _build/reports/proof_report.md
	@echo "- merkle_bridge.v: Connects Merkle tree specs to RefinedRust" >> _build/reports/proof_report.md
	@echo "- ct_bridge.v: Connects constant-time specs to RefinedRust" >> _build/reports/proof_report.md
	@echo "" >> _build/reports/proof_report.md
	@echo "## Extraction" >> _build/reports/proof_report.md
	@echo "" >> _build/reports/proof_report.md
	@echo "- extraction.v: Generates OCaml code for test oracles" >> _build/reports/proof_report.md
	@echo "" >> _build/reports/proof_report.md
	@echo "Report written to _build/reports/proof_report.md"
	@cat _build/reports/proof_report.md

# Verify integration with Rust verified crate
verify: theories
	@echo "=== Verifying RefinedRust Integration ==="
	@echo ""
	@echo "Checking generated specs exist..."
	@if [ -f "$(PROOFS_DIR)/../generated/generated_specs_anubis_verified.v" ]; then \
		echo "  ✓ generated_specs_anubis_verified.v"; \
	else \
		echo "  ✗ generated_specs_anubis_verified.v (run refinedrust on verified/src/main.rs)"; \
	fi
	@if [ -f "$(PROOFS_DIR)/../generated/generated_code_anubis_verified.v" ]; then \
		echo "  ✓ generated_code_anubis_verified.v"; \
	else \
		echo "  ✗ generated_code_anubis_verified.v (run refinedrust on verified/src/main.rs)"; \
	fi
	@echo ""
	@echo "Checking proof files..."
	@for f in $(PROOFS_DIR)/proof_*.v 2>/dev/null; do \
		if [ -f "$$f" ]; then \
			name=$$(basename $$f); \
			echo "  ✓ $$name"; \
		fi \
	done || echo "  (no proof files found)"
	@echo ""
	@echo "=== Integration Status ==="
	@echo "Bridge modules connect abstract specifications to RefinedRust-generated code."
	@echo "Run 'make prove' to verify all proofs."

# Clean build artifacts
clean:
	@echo "=== Cleaning ==="
	dune clean
	rm -rf _build
	rm -f anubis_*.ml anubis_*.mli

# List all theory files
list-theories:
	@echo "Theory files:"
	@find theories -name "*.v" -type f | sort

# Count proof obligations
count-admitted:
	@echo "Proof obligations status:"
	@echo "========================="
	@echo "Admitted proofs:"
	@grep -r "Admitted\." theories/*.v 2>/dev/null | wc -l | xargs echo "  Count:"
	@echo ""
	@echo "Completed proofs (Qed):"
	@grep -r "Qed\." theories/*.v 2>/dev/null | wc -l | xargs echo "  Count:"
	@echo ""
	@echo "Admitted locations:"
	@grep -rn "Admitted\." theories/*.v 2>/dev/null || echo "  (none)"

# Summary of specifications
summary:
	@echo "Anubis Notary RefinedRust Specifications"
	@echo "========================================"
	@echo ""
	@echo "Core Cryptographic Modules:"
	@echo "  - timing_model.v    : Constant-time execution model"
	@echo "  - ct_spec.v         : Constant-time primitives (ct_select, ct_eq)"
	@echo "  - ct_bridge.v       : CT bridge to RefinedRust"
	@echo "  - bytes_spec.v      : Byte manipulation utilities"
	@echo "  - keccak_model.v    : Pure Keccak-f[1600] mathematical model"
	@echo "  - keccak_spec.v     : Keccak permutation Hoare specifications"
	@echo "  - sha3_spec.v       : SHA3-256 hash function"
	@echo "  - shake_spec.v      : SHAKE256 extendable output function"
	@echo "  - aead_spec.v       : Ascon-128a authenticated encryption"
	@echo ""
	@echo "Data Format Modules:"
	@echo "  - cbor_spec.v       : Canonical CBOR encoder/decoder"
	@echo "  - license_spec.v    : License token format"
	@echo "  - receipt_spec.v    : Receipt attestation format"
	@echo ""
	@echo "Cryptographic Building Blocks:"
	@echo "  - nonce_spec.v      : Deterministic nonce derivation"
	@echo "  - merkle_spec.v     : Merkle tree proofs"
	@echo "  - merkle_bridge.v   : Merkle bridge to RefinedRust"
	@echo "  - mldsa_spec.v      : ML-DSA-87 post-quantum signatures"
	@echo "  - mlkem_spec.v      : ML-KEM-1024 key encapsulation"
	@echo "  - kdf_spec.v        : HKDF key derivation"
	@echo ""
	@echo "Multi-Party & Resilience:"
	@echo "  - multisig_spec.v   : Threshold signature schemes"
	@echo "  - hsm_spec.v        : Hardware security module interface"
	@echo "  - fault_spec.v      : Fault tolerance specifications"
	@echo "  - streaming_spec.v  : Streaming hash interface"
	@echo ""
	@echo "Proof Infrastructure:"
	@echo "  - all_proofs.v      : Master proof module (imports all)"
	@echo "  - extraction.v      : OCaml extraction targets"
	@echo "  - proofs/*.v        : Individual function proofs"

# Help target
help:
	@echo "Anubis Notary Verification Makefile"
	@echo ""
	@echo "Primary Targets:"
	@echo "  all             - Build all theory files (default)"
	@echo "  prove           - Full proof verification with timing"
	@echo "  extract         - Generate OCaml extraction"
	@echo "  rocqworkers     - Run proofs with rocqworkers (if available)"
	@echo "  verify          - Check RefinedRust integration status"
	@echo "  report          - Generate verification report"
	@echo ""
	@echo "Build Targets:"
	@echo "  theories        - Build Rocq specifications"
	@echo "  theories-verbose- Build with verbose output"
	@echo "  clean           - Remove build artifacts"
	@echo ""
	@echo "Info Targets:"
	@echo "  check-deps      - Verify required tools are installed"
	@echo "  list-theories   - List all .v files"
	@echo "  count-admitted  - Count Admitted vs Qed proofs"
	@echo "  summary         - Show specification summary"
	@echo "  help            - Show this help message"
	@echo ""
	@echo "Prerequisites:"
	@echo "  - Rocq 9.1+ (or Coq 8.19+)"
	@echo "  - Iris separation logic"
	@echo "  - RefinedRust framework"
	@echo "  - Caesium Rust semantics"
	@echo "  - dune 3.16+"
