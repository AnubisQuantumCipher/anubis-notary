#!/bin/bash
# Clean build artifacts from the repository
# Run this script from the project root directory

set -e

echo "Cleaning build artifacts..."

# Remove _build directories
find . -type d -name "_build" -exec rm -rf {} + 2>/dev/null || true

# Remove Coq build outputs
find . -type f -name "*.vo" -delete 2>/dev/null || true
find . -type f -name "*.vok" -delete 2>/dev/null || true
find . -type f -name "*.vos" -delete 2>/dev/null || true
find . -type f -name "*.vio" -delete 2>/dev/null || true
find . -type f -name "*.glob" -delete 2>/dev/null || true
find . -type f -name "*.aux" -delete 2>/dev/null || true
find . -type f -name ".*.aux" -delete 2>/dev/null || true
find . -type f -name ".lia.cache" -delete 2>/dev/null || true
find . -type f -name ".coqdeps.d" -delete 2>/dev/null || true
find . -type f -name ".filesystem-clock" -delete 2>/dev/null || true
find . -type f -name ".lock" -delete 2>/dev/null || true

# Remove dune build metadata
find . -type d -name ".dune" -exec rm -rf {} + 2>/dev/null || true
find . -type f -name "*.d.*theory.d" -delete 2>/dev/null || true

# Remove editor backup files
find . -type f -name "*.bak" -delete 2>/dev/null || true
find . -type f -name "*.orig" -delete 2>/dev/null || true
find . -type f -name "*~" -delete 2>/dev/null || true

# Remove OS metadata
find . -type f -name ".DS_Store" -delete 2>/dev/null || true
find . -type f -name "._*" -delete 2>/dev/null || true

echo "Build artifacts cleaned."
echo ""
echo "If this is a git repository, also run:"
echo "  git rm -r --cached _build/"
echo "  git rm --cached '*.vo' '*.vok' '*.vos' '*.glob' '*.aux' '.*.aux' '.lia.cache'"
echo "  git add .gitignore"
echo "  git commit -m 'chore: remove build artifacts and update .gitignore'"
