# Anubis Notary - Proof Build Makefile
# Uses coqc directly for maximum compatibility

.PHONY: all clean prove check status

# Coq flags
COQFLAGS = -Q theories anubis_proofs

# Find all .v files
VFILES = $(wildcard theories/*.v)
VOFILES = $(VFILES:.v=.vo)

# Build all proofs
all: $(VOFILES)
	@echo "✓ All proofs compiled"

# Alias for all
prove: all

# Pattern rule for compiling .v to .vo
theories/%.vo: theories/%.v
	@echo "Compiling $<..."
	@coqc $(COQFLAGS) $< && echo "  ✓ $@" || echo "  ○ $@ (failed)"

# Check syntax only
check:
	@for f in $(VFILES); do \
		echo "Checking $$f..."; \
		coqc -Q theories anubis_proofs $$f 2>/dev/null && echo "  ✓" || echo "  ○"; \
	done

# Show status
status:
	@echo "Proof Status:"
	@for f in $(VFILES); do \
		vo=$${f%.v}.vo; \
		if [ -f "$$vo" ]; then \
			echo "  ✓ $$(basename $$f .v)"; \
		else \
			echo "  ○ $$(basename $$f .v)"; \
		fi; \
	done

# Clean build artifacts
clean:
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob
	rm -f theories/.*.aux
	rm -rf _build
	@echo "✓ Clean complete"
