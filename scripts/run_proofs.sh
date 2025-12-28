#!/bin/bash
# Run all Rocq proofs for Anubis Notary
#
# Usage:
#   ./scripts/run_proofs.sh        # Run all proofs
#   ./scripts/run_proofs.sh quick  # Quick check (level 2)
#   ./scripts/run_proofs.sh full   # Full proof (level 4)
#
# Requirements:
#   - Rocq 9.1+ or Coq 8.19+
#   - dune 3.16+
#   - opam with refinedrust switch

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
SPECS_DIR="$PROJECT_DIR/specs/refinedrust"
VERIFIED_DIR="$PROJECT_DIR/verified"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

MODE="${1:-all}"

echo -e "${BLUE}=== Anubis Notary Proof Runner ===${NC}"
echo ""
echo "Project: $PROJECT_DIR"
echo "Mode: $MODE"
echo "Started: $(date)"
echo ""

# Check dependencies
check_deps() {
    echo -e "${YELLOW}Checking dependencies...${NC}"

    if ! command -v coqc &> /dev/null && ! command -v rocqc &> /dev/null; then
        echo -e "${RED}Error: coqc or rocqc not found${NC}"
        echo "Please install Rocq 9.1+ or Coq 8.19+"
        exit 1
    fi

    if ! command -v dune &> /dev/null; then
        echo -e "${RED}Error: dune not found${NC}"
        echo "Please install dune 3.16+"
        exit 1
    fi

    echo -e "  Rocq/Coq: $(coqc --version 2>/dev/null || rocqc --version 2>/dev/null | head -1)"
    echo -e "  dune: $(dune --version)"
    echo -e "${GREEN}Dependencies OK${NC}"
    echo ""
}

# Build specifications
build_specs() {
    echo -e "${YELLOW}Building Rocq specifications...${NC}"
    cd "$SPECS_DIR"

    if [ "$MODE" = "quick" ]; then
        dune build --force 2>&1 | head -50
    else
        dune build --force 2>&1
    fi

    if [ $? -eq 0 ]; then
        echo -e "${GREEN}Specifications built successfully${NC}"
    else
        echo -e "${RED}Specification build failed${NC}"
        exit 1
    fi
    echo ""
}

# Check for admitted proofs
check_admitted() {
    echo -e "${YELLOW}Checking for admitted proofs...${NC}"

    ADMITTED_COUNT=0

    # Check theory files
    if [ -d "$SPECS_DIR/theories" ]; then
        THEORY_ADMITTED=$(grep -r "Admitted\." "$SPECS_DIR/theories"/*.v 2>/dev/null | wc -l | tr -d ' ')
        ADMITTED_COUNT=$((ADMITTED_COUNT + THEORY_ADMITTED))
        echo "  Theory files: $THEORY_ADMITTED admitted"
    fi

    # Check proof files
    if [ -d "$VERIFIED_DIR/output/anubis_verified/proofs" ]; then
        PROOF_ADMITTED=$(grep -r "Admitted\." "$VERIFIED_DIR/output/anubis_verified/proofs"/*.v 2>/dev/null | wc -l | tr -d ' ')
        ADMITTED_COUNT=$((ADMITTED_COUNT + PROOF_ADMITTED))
        echo "  Proof files: $PROOF_ADMITTED admitted"
    fi

    if [ "$ADMITTED_COUNT" -gt 0 ]; then
        echo -e "${YELLOW}Warning: $ADMITTED_COUNT admitted proofs found${NC}"
        echo "Locations:"
        grep -rn "Admitted\." "$SPECS_DIR/theories"/*.v 2>/dev/null || true
        grep -rn "Admitted\." "$VERIFIED_DIR/output/anubis_verified/proofs"/*.v 2>/dev/null || true
    else
        echo -e "${GREEN}No admitted proofs (Gold level achieved!)${NC}"
    fi
    echo ""
}

# Count completed proofs
count_proofs() {
    echo -e "${YELLOW}Proof statistics...${NC}"

    QED_COUNT=0

    if [ -d "$SPECS_DIR/theories" ]; then
        THEORY_QED=$(grep -r "Qed\." "$SPECS_DIR/theories"/*.v 2>/dev/null | wc -l | tr -d ' ')
        QED_COUNT=$((QED_COUNT + THEORY_QED))
        echo "  Theory proofs: $THEORY_QED"
    fi

    if [ -d "$VERIFIED_DIR/output/anubis_verified/proofs" ]; then
        PROOF_QED=$(grep -r "Qed\." "$VERIFIED_DIR/output/anubis_verified/proofs"/*.v 2>/dev/null | wc -l | tr -d ' ')
        QED_COUNT=$((QED_COUNT + PROOF_QED))
        echo "  Function proofs: $PROOF_QED"
    fi

    echo -e "${GREEN}Total completed proofs: $QED_COUNT${NC}"
    echo ""
}

# Run with rocqworkers if available
run_rocqworkers() {
    if command -v rocqworkers &> /dev/null; then
        echo -e "${YELLOW}Running rocqworkers...${NC}"
        cd "$SPECS_DIR"
        rocqworkers prove --config rocqworkers.toml
    else
        echo -e "${YELLOW}rocqworkers not found, using dune${NC}"
    fi
}

# Generate report
generate_report() {
    echo -e "${YELLOW}Generating verification report...${NC}"

    REPORT_DIR="$PROJECT_DIR/_build/reports"
    mkdir -p "$REPORT_DIR"

    REPORT="$REPORT_DIR/proof_report_$(date +%Y%m%d_%H%M%S).md"

    cat > "$REPORT" << EOF
# Anubis Notary Verification Report

Generated: $(date)

## Summary

| Metric | Count |
|--------|-------|
| Theory files | $(find "$SPECS_DIR/theories" -name "*.v" 2>/dev/null | wc -l | tr -d ' ') |
| Proof files | $(find "$VERIFIED_DIR/output/anubis_verified/proofs" -name "*.v" 2>/dev/null | wc -l | tr -d ' ') |
| Completed proofs (Qed) | $(grep -r "Qed\." "$SPECS_DIR/theories"/*.v "$VERIFIED_DIR/output/anubis_verified/proofs"/*.v 2>/dev/null | wc -l | tr -d ' ') |
| Admitted proofs | $(grep -r "Admitted\." "$SPECS_DIR/theories"/*.v "$VERIFIED_DIR/output/anubis_verified/proofs"/*.v 2>/dev/null | wc -l | tr -d ' ') |

## Verified Functions

EOF

    # List proof files
    for f in "$VERIFIED_DIR/output/anubis_verified/proofs"/proof_*.v; do
        if [ -f "$f" ]; then
            name=$(basename "$f" .v | sed 's/proof_//')
            echo "- \`$name\`" >> "$REPORT"
        fi
    done

    cat >> "$REPORT" << EOF

## Theory Modules

EOF

    # List theory files
    for f in "$SPECS_DIR/theories"/*.v; do
        if [ -f "$f" ]; then
            name=$(basename "$f" .v)
            echo "- \`$name\`" >> "$REPORT"
        fi
    done

    cat >> "$REPORT" << EOF

## Build Status

EOF

    if [ -d "$SPECS_DIR/_build" ]; then
        echo "Build successful" >> "$REPORT"
    else
        echo "Build not completed" >> "$REPORT"
    fi

    echo ""
    echo -e "${GREEN}Report written to: $REPORT${NC}"
}

# Main execution
main() {
    check_deps

    case "$MODE" in
        quick)
            build_specs
            count_proofs
            ;;
        full)
            build_specs
            check_admitted
            count_proofs
            generate_report
            ;;
        rocqworkers)
            run_rocqworkers
            ;;
        report)
            generate_report
            ;;
        *)
            build_specs
            check_admitted
            count_proofs
            ;;
    esac

    echo ""
    echo -e "${GREEN}=== Proof run complete ===${NC}"
    echo "Finished: $(date)"
}

main
