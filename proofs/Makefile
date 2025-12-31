# Anubis Notary - Proof Build Makefile
# Wrapper around Dune for Coq/Rocq proof compilation

.PHONY: all clean prove check

# Build all proofs
all:
	dune build

# Verify proofs (same as build for Coq)
prove: all

# Check proofs syntax
check:
	dune build @check

# Clean build artifacts
clean:
	dune clean

# Generate documentation
doc:
	dune build @doc

# Install locally
install:
	dune install

# Uninstall
uninstall:
	dune uninstall
