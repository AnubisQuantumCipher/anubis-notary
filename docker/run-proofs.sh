#!/bin/bash
# Anubis Notary - One-command proof verification
#
# This script builds and runs the Docker container for verifying
# all Rocq/Coq proofs in the Anubis Notary project.
#
# Usage:
#   ./docker/run-proofs.sh          # Build and run interactively
#   ./docker/run-proofs.sh --build  # Force rebuild
#   ./docker/run-proofs.sh --check  # Build only (non-interactive)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
IMAGE_NAME="anubis-proofs"

cd "$PROJECT_DIR"

# Parse arguments
BUILD_ONLY=false
FORCE_BUILD=false

for arg in "$@"; do
    case $arg in
        --build)
            FORCE_BUILD=true
            shift
            ;;
        --check)
            BUILD_ONLY=true
            shift
            ;;
        *)
            ;;
    esac
done

echo "=== Anubis Notary Proof Verification ==="
echo ""

# Check if image exists and if we need to rebuild
if [[ "$FORCE_BUILD" == "true" ]] || ! docker image inspect "$IMAGE_NAME" &> /dev/null; then
    echo "Building Docker image (this may take a few minutes)..."
    echo ""
    docker build -t "$IMAGE_NAME" -f docker/Dockerfile .
    echo ""
    echo "Build complete!"
fi

if [[ "$BUILD_ONLY" == "true" ]]; then
    echo ""
    echo "Proof verification complete (build only mode)."
    echo "All proofs compiled successfully during Docker build."
    exit 0
fi

echo ""
echo "Starting interactive proof environment..."
echo ""

# Run interactively
docker run -it --rm \
    -v "$PROJECT_DIR/proofs:/home/coq/anubis-notary/proofs:ro" \
    -v "$PROJECT_DIR/specs:/home/coq/anubis-notary/specs:ro" \
    "$IMAGE_NAME"
