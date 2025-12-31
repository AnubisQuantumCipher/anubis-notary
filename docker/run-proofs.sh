#!/bin/bash
# Anubis Notary - One-command proof verification
#
# Usage:
#   ./run-proofs.sh              # Interactive shell
#   ./run-proofs.sh make all     # Build all proofs
#   ./run-proofs.sh make prove   # Verify proofs
#
# Inside container:
#   make prove                   # Runs coqc on all .v files
#   coqtop -I proofs/ -l merkle_spec.v  # Interactive proof checking

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

IMAGE_NAME="anubis-proofs"

echo "=== Anubis Notary Proof Verification ==="
echo ""

# Check if Docker is installed
if ! command -v docker &> /dev/null; then
    echo "Error: Docker is not installed."
    echo "Please install Docker from https://docker.com (free/one-time install)"
    echo ""
    echo "Alternative without Docker:"
    echo "  opam install coq-iris coq-stdpp coq-equations"
    echo "  cd proofs && make all"
    exit 1
fi

# Check if Docker daemon is running
if ! docker info &> /dev/null; then
    echo "Error: Docker daemon is not running."
    echo ""
    echo "Please start Docker:"
    echo "  Linux:  sudo systemctl start docker"
    echo "  macOS:  open -a Docker"
    echo ""
    exit 1
fi

# Build the Docker image
echo "Building Docker image (first run takes a few minutes)..."
docker build -t "$IMAGE_NAME" -f "$SCRIPT_DIR/Dockerfile" "$PROJECT_DIR"

echo ""
echo "Starting proof environment..."
echo ""

# Run container
if [ $# -eq 0 ]; then
    # Interactive mode
    docker run -it --rm "$IMAGE_NAME"
else
    # Run specific command
    docker run -it --rm "$IMAGE_NAME" bash -c "eval \$(opam env) && $*"
fi
