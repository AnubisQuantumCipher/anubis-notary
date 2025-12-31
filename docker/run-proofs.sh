#!/bin/bash
# Anubis Notary - One-command proof verification
# Usage: ./run-proofs.sh [command]
#
# Examples:
#   ./run-proofs.sh              # Interactive shell
#   ./run-proofs.sh make all     # Build all proofs
#   ./run-proofs.sh make prove   # Verify proofs
#   ./run-proofs.sh --no-build   # Skip image rebuild

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

IMAGE_NAME="anubis-proofs"
SKIP_BUILD=false

# Parse arguments
if [ "$1" = "--no-build" ]; then
    SKIP_BUILD=true
    shift
fi

echo "=== Anubis Notary Proof Verification ==="
echo ""

# Check if Docker is installed
if ! command -v docker &> /dev/null; then
    echo "Error: Docker is not installed."
    echo "Please install Docker from https://docker.com"
    echo ""
    echo "Alternative: Install Rocq/Coq natively:"
    echo "  opam install coq.8.18 dune coq-stdpp coq-equations"
    echo "  cd proofs && make all"
    exit 1
fi

# Check if Docker daemon is running
if ! docker info &> /dev/null; then
    echo "Error: Docker daemon is not running."
    echo ""
    echo "Please start Docker Desktop or run:"
    echo "  sudo systemctl start docker  # Linux"
    echo "  open -a Docker                # macOS"
    echo ""
    echo "Alternative: Install Rocq/Coq natively:"
    echo "  opam install coq.8.18 dune coq-stdpp coq-equations"
    echo "  cd proofs && make all"
    exit 1
fi

# Build image if not exists or if requested
if [ "$SKIP_BUILD" = false ]; then
    echo "Building Docker image (this may take a few minutes on first run)..."
    docker build -t "$IMAGE_NAME" -f "$SCRIPT_DIR/Dockerfile" "$PROJECT_DIR"
    echo ""
fi

echo "Starting proof environment..."
echo ""

# Run container with writable volume for build artifacts
if [ $# -eq 0 ]; then
    # Interactive mode
    docker run -it --rm \
        -v "$PROJECT_DIR/proofs:/home/coq/anubis-notary/proofs" \
        -v "$PROJECT_DIR/specs:/home/coq/anubis-notary/specs:ro" \
        "$IMAGE_NAME"
else
    # Run specific command
    docker run -it --rm \
        -v "$PROJECT_DIR/proofs:/home/coq/anubis-notary/proofs" \
        -v "$PROJECT_DIR/specs:/home/coq/anubis-notary/specs:ro" \
        "$IMAGE_NAME" \
        bash -c "eval \$(opam env) && $*"
fi
