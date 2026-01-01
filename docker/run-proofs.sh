#!/bin/bash
# Anubis Notary - One-command proof verification
#
# Usage:
#   ./run-proofs.sh              # Interactive shell
#   ./run-proofs.sh make all     # Build all proofs
#   ./run-proofs.sh make prove   # Verify proofs
#
# Inside container:
#   make prove                   # Compile all proofs
#   make status                  # Show compilation status
#   coqtop                       # Interactive Coq toplevel

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

IMAGE_NAME="anubis-proofs"
NETWORK_FLAG=""

echo ""
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║       Anubis Notary - Formal Proof Verification              ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

# Check if Docker is installed
if ! command -v docker &> /dev/null; then
    echo "Error: Docker is not installed."
    echo ""
    echo "Please install Docker from https://docker.com (free/one-time install)"
    echo ""
    echo "Alternative without Docker:"
    echo "  opam install coq coq-stdpp coq-equations"
    echo "  cd proofs/theories"
    echo "  for f in *.v; do coqc -Q . anubis_proofs \"\$f\"; done"
    exit 1
fi

# Check if Docker daemon is running
if ! docker info &> /dev/null 2>&1; then
    echo "Error: Docker daemon is not running."
    echo ""
    echo "Please start Docker:"
    echo "  Linux:  sudo systemctl start docker"
    echo "  macOS:  open -a Docker"
    exit 1
fi

# Detect if we're in a containerized environment (Docker-in-Docker)
# This helps avoid iptables errors in nested containers
if [ -f "/.dockerenv" ] || grep -q docker /proc/1/cgroup 2>/dev/null; then
    echo "Note: Detected containerized environment, using --network=host"
    NETWORK_FLAG="--network=host"
fi

# Build the Docker image
echo "Building Docker image (first run takes a few minutes)..."
echo ""

if ! docker build $NETWORK_FLAG -t "$IMAGE_NAME" -f "$SCRIPT_DIR/Dockerfile" "$PROJECT_DIR"; then
    echo ""
    echo "Build failed. Trying with --network=host..."
    NETWORK_FLAG="--network=host"
    docker build $NETWORK_FLAG -t "$IMAGE_NAME" -f "$SCRIPT_DIR/Dockerfile" "$PROJECT_DIR"
fi

echo ""
echo "Starting proof environment..."
echo ""

# Run container
if [ $# -eq 0 ]; then
    # Interactive mode
    docker run -it --rm $NETWORK_FLAG "$IMAGE_NAME"
else
    # Run specific command
    docker run -it --rm $NETWORK_FLAG "$IMAGE_NAME" bash -c "eval \$(opam env) && $*"
fi
