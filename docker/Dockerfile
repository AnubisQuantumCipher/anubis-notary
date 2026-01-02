# Anubis Notary - Proof Verification Docker Image
# Provides a complete environment for verifying Rocq/Coq proofs
#
# Usage:
#   docker build -t anubis-proofs docker/
#   docker run -it anubis-proofs
#
# Or use the convenience script:
#   ./docker/run-proofs.sh

FROM coqorg/coq:8.19.0-ocaml-4.14.1-flambda

LABEL org.opencontainers.image.title="Anubis Notary Proofs"
LABEL org.opencontainers.image.description="Formal proof verification for Anubis Notary"
LABEL org.opencontainers.image.source="https://github.com/AnubisQuantumCipher/anubis-notary"
LABEL org.opencontainers.image.licenses="MIT"

# Install additional packages
USER root
RUN apt-get update && apt-get install -y \
    make \
    git \
    && rm -rf /var/lib/apt/lists/*

USER coq

# Install Iris and stdpp via opam
RUN opam update && \
    opam install -y coq-stdpp coq-iris && \
    opam clean -a -c -s --logs

# Set working directory
WORKDIR /home/coq/anubis-notary

# Copy proof files
COPY --chown=coq:coq proofs/ ./proofs/
COPY --chown=coq:coq specs/ ./specs/

# Build proofs
WORKDIR /home/coq/anubis-notary/proofs

# Verify all proofs on build
RUN eval $(opam env) && make all

# Default command shows status and starts interactive shell
CMD ["/bin/bash", "-c", "eval $(opam env) && echo '=== Anubis Notary Proof Verification ===' && make status && echo '' && echo 'Run \"make all\" to rebuild proofs' && echo 'Run \"make clean\" to clean artifacts' && /bin/bash"]
