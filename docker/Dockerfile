# Anubis Notary - Proof Verification Container
# Build: docker build -t anubis-proofs .
# Run:   docker run -it anubis-proofs
#
# One-command proof verification - no manual install needed!

FROM coqorg/coq:8.19

LABEL maintainer="AnubisQuantumCipher <sic.tau@pm.me>"
LABEL description="Anubis Notary formal proofs verification environment"

# Install system dependencies
USER root
RUN apt-get update && apt-get install -y \
    make \
    m4 \
    time \
    && rm -rf /var/lib/apt/lists/*

USER coq

# Install Coq libraries (Iris, stdpp, equations) via opam
RUN opam update && \
    opam install -y dune coq-iris coq-stdpp coq-equations && \
    opam clean -a -c -s --logs

# Set up project directory
WORKDIR /app

# Copy all project files
COPY --chown=coq:coq proofs/ ./proofs/
COPY --chown=coq:coq specs/ ./specs/
COPY --chown=coq:coq verified/output/ ./verified/output/
COPY --chown=coq:coq docker/Makefile.proofs ./Makefile

# Pre-build proofs (creates .vo files)
RUN eval $(opam env) && cd proofs && dune build 2>/dev/null || true

# Set working directory
WORKDIR /app

# Interactive shell for proof checking
CMD ["bash", "-c", "eval $(opam env) && make help && exec bash"]
