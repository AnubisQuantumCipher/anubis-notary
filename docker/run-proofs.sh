#!/bin/bash
# Anubis Notary - One-command proof verification
# Usage: ./run-proofs.sh [command]
#
# Examples:
#   ./run-proofs.sh           # Interactive shell
#   ./run-proofs.sh make all  # Build all proofs
#   ./run-proofs.sh make prove # Verify proofs

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

IMAGE_NAME="anubis-proofs"

echo "=== Anubis Notary Proof Verification ==="
echo ""

# Check if Docker is installed
if ! command -v docker &> /dev/null; then
    echo "Error: Docker is not installed."
    echo "Please install Docker from https://docker.com"
    exit 1
fi

# Build image if not exists or if Dockerfile changed
echo "Building Docker image..."
docker build -t "$IMAGE_NAME" -f "$SCRIPT_DIR/Dockerfile" "$PROJECT_DIR"

echo ""
echo "Starting proof environment..."
echo ""

# Run container
if [ $# -eq 0 ]; then
    # Interactive mode
    docker run -it --rm \
        -v "$PROJECT_DIR/proofs:/home/coq/anubis-notary/proofs:ro" \
        "$IMAGE_NAME"
else
    # Run specific command
    docker run -it --rm \
        -v "$PROJECT_DIR/proofs:/home/coq/anubis-notary/proofs:ro" \
        "$IMAGE_NAME" \
        bash -c "eval \$(opam env) && $*"
fi
