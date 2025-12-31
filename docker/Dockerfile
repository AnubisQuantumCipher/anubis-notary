# Anubis Notary - Proof Verification Container
# Build: docker build -t anubis-proofs .
# Run:   docker run -it anubis-proofs
#
# Proof Categories:
#   core        - Core cryptographic proofs (AEAD, CBOR, Merkle, ML-DSA)
#   refinedrust - Separation logic specs (nonce injectivity, constant-time)
#   properties  - High-level property proofs
#   verified    - Generated RefinedRust proofs

FROM coqorg/coq:8.18

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

# Install Coq libraries and dune via opam
RUN opam update && \
    opam install -y dune coq-stdpp coq-equations && \
    opam clean -a -c -s --logs

# Set up project directory
WORKDIR /home/coq/anubis-notary

# Copy all proof directories
COPY --chown=coq:coq proofs/ ./proofs/
COPY --chown=coq:coq specs/ ./specs/
COPY --chown=coq:coq verified/output/ ./verified/output/

# Copy the master Makefile
COPY --chown=coq:coq docker/Makefile.proofs ./Makefile

# Set working directory
WORKDIR /home/coq/anubis-notary

# Show help by default
CMD ["bash", "-c", "eval $(opam env) && make help && exec bash"]
