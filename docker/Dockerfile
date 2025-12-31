# Anubis Notary - Proof Verification Container
# Build: docker build -t anubis-proofs .
# Run:   docker run -it anubis-proofs

FROM coqorg/coq:8.18

# Set maintainer
LABEL maintainer="AnubisQuantumCipher"
LABEL description="Anubis Notary formal proofs verification environment"

# Install Rocq/Coq dependencies
USER root
RUN apt-get update && apt-get install -y \
    make \
    m4 \
    && rm -rf /var/lib/apt/lists/*

USER coq

# Install Coq libraries via opam
RUN opam update && \
    opam install -y coq-stdpp coq-equations && \
    opam clean -a -c -s --logs

# Copy proof files
WORKDIR /home/coq/anubis-notary
COPY --chown=coq:coq proofs/ ./proofs/
COPY --chown=coq:coq specs/ ./specs/

# Set working directory to proofs
WORKDIR /home/coq/anubis-notary/proofs

# Build proofs on image creation (optional - comment out for faster builds)
# RUN eval $(opam env) && make all

# Default command: interactive shell for proof verification
CMD ["bash", "-c", "eval $(opam env) && echo 'Anubis Notary Proofs Environment' && echo 'Run: make all    - Build all proofs' && echo 'Run: make prove  - Verify proofs' && echo 'Run: coqide      - Open Coq IDE' && exec bash"]
