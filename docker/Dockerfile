# Anubis Notary - Proof Verification Container
# Build: docker build -t anubis-proofs .
# Run:   docker run -it anubis-proofs
#
# One-command proof verification - no manual install needed!

FROM coqorg/coq:8.18

LABEL maintainer="AnubisQuantumCipher <sic.tau@pm.me>"
LABEL description="Anubis Notary formal proofs verification environment"

# Install system dependencies and SSL certificates
USER root
RUN apt-get update && apt-get install -y \
    make \
    m4 \
    time \
    ca-certificates \
    curl \
    && update-ca-certificates \
    && rm -rf /var/lib/apt/lists/*

USER coq

# Set up project directory
WORKDIR /home/coq/anubis-notary

# Copy proof files
COPY --chown=coq:coq proofs/ ./proofs/
COPY --chown=coq:coq docker/Makefile.proofs ./Makefile

# The base coqorg/coq:8.18 image already has Coq installed
# We skip opam install to avoid network issues
# The core proofs don't require external libraries

# Set working directory
WORKDIR /home/coq/anubis-notary

# Show help by default
CMD ["bash", "-c", "echo '' && echo '╔══════════════════════════════════════════════════════════════╗' && echo '║       Anubis Notary - Formal Proof Verification              ║' && echo '╚══════════════════════════════════════════════════════════════╝' && echo '' && echo 'Commands:' && echo '  make all      - Compile all proofs' && echo '  make status   - Show compilation status' && echo '  make clean    - Remove build artifacts' && echo '  coqtop        - Interactive Coq toplevel' && echo '' && exec bash"]
