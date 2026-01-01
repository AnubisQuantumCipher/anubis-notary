# Deployment Guide

## Quick Start

### Download Pre-built Binaries

```bash
# Linux (x86_64)
curl -LO https://github.com/AnubisQuantumCipher/anubis-notary/releases/latest/download/anubis-notary-linux-x86_64
chmod +x anubis-notary-linux-x86_64
sudo mv anubis-notary-linux-x86_64 /usr/local/bin/anubis-notary

# macOS (Apple Silicon)
curl -LO https://github.com/AnubisQuantumCipher/anubis-notary/releases/latest/download/anubis-notary-darwin-aarch64
chmod +x anubis-notary-darwin-aarch64
xattr -d com.apple.quarantine anubis-notary-darwin-aarch64
sudo mv anubis-notary-darwin-aarch64 /usr/local/bin/anubis-notary

# Verify installation
anubis-notary --version
```

### Build from Source

```bash
# Prerequisites
# - Rust 1.75+ (https://rustup.rs)
# - Node.js 18+ (for Mina integration)

# Clone and build
git clone https://github.com/AnubisQuantumCipher/anubis-notary.git
cd anubis-notary
cargo build --release

# Install
sudo cp target/release/anubis-notary /usr/local/bin/
```

---

## Server Deployment

### Systemd Service (Linux)

Create `/etc/systemd/system/anubis-notary.service`:

```ini
[Unit]
Description=Anubis Notary Service
After=network.target

[Service]
Type=oneshot
RemainAfterExit=yes
User=anubis
Group=anubis
Environment="ANUBIS_HOME=/var/lib/anubis"
Environment="ANUBIS_PASSWORD_FILE=/etc/anubis/password"
ExecStart=/usr/local/bin/anubis-notary key show
WorkingDirectory=/var/lib/anubis

# Security hardening
NoNewPrivileges=yes
ProtectSystem=strict
ProtectHome=yes
ReadWritePaths=/var/lib/anubis
PrivateTmp=yes
PrivateDevices=yes

[Install]
WantedBy=multi-user.target
```

Setup:

```bash
# Create user and directories
sudo useradd -r -s /bin/false anubis
sudo mkdir -p /var/lib/anubis /etc/anubis
sudo chown anubis:anubis /var/lib/anubis

# Store password securely
echo "your-secure-password" | sudo tee /etc/anubis/password
sudo chmod 600 /etc/anubis/password
sudo chown anubis:anubis /etc/anubis/password

# Initialize keystore
sudo -u anubis ANUBIS_HOME=/var/lib/anubis \
    ANUBIS_PASSWORD_FILE=/etc/anubis/password \
    anubis-notary key init --low-memory

# Enable service
sudo systemctl daemon-reload
sudo systemctl enable anubis-notary
```

### Docker Deployment

Create `Dockerfile`:

```dockerfile
FROM rust:1.75-slim as builder

WORKDIR /build
COPY . .
RUN cargo build --release

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    nodejs \
    npm \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /build/target/release/anubis-notary /usr/local/bin/

RUN useradd -r -s /bin/false anubis
USER anubis
WORKDIR /home/anubis

ENV ANUBIS_HOME=/home/anubis/.anubis

ENTRYPOINT ["anubis-notary"]
CMD ["--help"]
```

Build and run:

```bash
# Build
docker build -t anubis-notary .

# Initialize keystore
docker run -it -v anubis-data:/home/anubis/.anubis \
    -e ANUBIS_PASSWORD="your-password" \
    anubis-notary key init --low-memory

# Sign a file
docker run -v anubis-data:/home/anubis/.anubis \
    -v $(pwd):/data \
    -e ANUBIS_PASSWORD="your-password" \
    anubis-notary sign /data/document.pdf -o /data/document.sig
```

### Docker Compose

```yaml
version: '3.8'

services:
  anubis:
    image: anubis-notary
    build: .
    volumes:
      - anubis-keystore:/home/anubis/.anubis
      - ./documents:/data
    environment:
      - ANUBIS_PASSWORD_FILE=/run/secrets/anubis_password
      - MINA_PRIVATE_KEY_FILE=/run/secrets/mina_key
    secrets:
      - anubis_password
      - mina_key
    security_opt:
      - no-new-privileges:true
    read_only: true
    tmpfs:
      - /tmp:mode=1777,size=100M

volumes:
  anubis-keystore:

secrets:
  anubis_password:
    file: ./secrets/anubis_password.txt
  mina_key:
    file: ./secrets/mina_key.txt
```

---

## CI/CD Integration

### GitHub Actions

```yaml
name: Sign Release Artifacts

on:
  release:
    types: [published]

jobs:
  sign:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Download Anubis Notary
        run: |
          curl -LO https://github.com/AnubisQuantumCipher/anubis-notary/releases/latest/download/anubis-notary-linux-x86_64
          chmod +x anubis-notary-linux-x86_64
          sudo mv anubis-notary-linux-x86_64 /usr/local/bin/anubis-notary

      - name: Initialize Keystore
        env:
          ANUBIS_PASSWORD: ${{ secrets.ANUBIS_PASSWORD }}
        run: |
          anubis-notary key init --low-memory

      - name: Sign Artifacts
        env:
          ANUBIS_PASSWORD: ${{ secrets.ANUBIS_PASSWORD }}
        run: |
          for file in dist/*; do
            anubis-notary sign "$file" -o "$file.sig"
            anubis-notary attest "$file" --receipt "$file.receipt"
          done

      - name: Upload Signatures
        uses: actions/upload-artifact@v4
        with:
          name: signatures
          path: |
            dist/*.sig
            dist/*.receipt
```

### GitLab CI

```yaml
sign-release:
  stage: release
  image: debian:bookworm-slim
  before_script:
    - apt-get update && apt-get install -y curl
    - curl -LO https://github.com/AnubisQuantumCipher/anubis-notary/releases/latest/download/anubis-notary-linux-x86_64
    - chmod +x anubis-notary-linux-x86_64
    - mv anubis-notary-linux-x86_64 /usr/local/bin/anubis-notary
  script:
    - anubis-notary key init --low-memory
    - |
      for file in dist/*; do
        anubis-notary sign "$file" -o "$file.sig"
      done
  artifacts:
    paths:
      - dist/*.sig
  variables:
    ANUBIS_PASSWORD: $ANUBIS_PASSWORD
  only:
    - tags
```

### Jenkins Pipeline

```groovy
pipeline {
    agent any

    environment {
        ANUBIS_PASSWORD = credentials('anubis-password')
        ANUBIS_HOME = "${WORKSPACE}/.anubis"
    }

    stages {
        stage('Setup') {
            steps {
                sh '''
                    curl -LO https://github.com/AnubisQuantumCipher/anubis-notary/releases/latest/download/anubis-notary-linux-x86_64
                    chmod +x anubis-notary-linux-x86_64
                    ./anubis-notary-linux-x86_64 key init --low-memory
                '''
            }
        }

        stage('Sign') {
            steps {
                sh '''
                    for file in dist/*; do
                        ./anubis-notary-linux-x86_64 sign "$file" -o "$file.sig"
                    done
                '''
            }
        }
    }

    post {
        always {
            // Clean up keystore
            sh 'rm -rf ${ANUBIS_HOME}'
        }
    }
}
```

---

## Mina Blockchain Setup

### Prerequisites

```bash
# Node.js 18+ required
node --version  # Should be 18.x or higher

# Install Mina bridge
anubis-notary anchor mina setup
```

### Generate Wallet

```bash
# Generate new Mina keypair
anubis-notary anchor mina keygen

# Output:
# Private Key: EK...  (SAVE THIS SECURELY)
# Public Key:  B62q...
# Address:     B62q...
```

### Fund Wallet

1. Copy your address from keygen output
2. Send ~0.2 MINA from an exchange (Coinbase, Kraken, etc.)
3. Wait for confirmation (~10 minutes)

```bash
# Check balance
export MINA_PRIVATE_KEY="EK..."
anubis-notary anchor mina balance
```

### Anchor Documents

```bash
# Set credentials
export MINA_PRIVATE_KEY="EK..."
export MINA_NETWORK="mainnet"  # or "devnet" for testing

# Create receipt
anubis-notary attest document.pdf --receipt document.receipt

# Anchor to blockchain
anubis-notary anchor mina anchor document.receipt

# Output:
# Anchor submitted successfully!
#   Transaction: 5Jtu6Q...
#   Explorer: https://minascan.io/mainnet/tx/5Jtu6Q...
```

### Production Configuration

For production deployments, use environment files:

```bash
# /etc/anubis/mina.env
MINA_PRIVATE_KEY=EK...
MINA_NETWORK=mainnet
MINA_FEE=100000000
```

```bash
# Load and use
source /etc/anubis/mina.env
anubis-notary anchor mina anchor receipt.anb
```

---

## High Availability Setup

### Multiple Keystores

For redundancy, maintain keystores on multiple servers:

```bash
# Server 1: Initialize primary
anubis-notary key init
anubis-notary key show > /backup/server1.pub

# Server 2: Initialize backup (different key)
anubis-notary key init
anubis-notary key show > /backup/server2.pub

# Document both public keys for verification
```

### Key Rotation

Rotate keys periodically:

```bash
# Rotate (archives old key)
anubis-notary key rotate

# Verify new key
anubis-notary key show

# Old signatures remain valid with archived public key
```

### Backup Strategy

```bash
# Backup keystore (encrypted)
tar -czf anubis-backup-$(date +%Y%m%d).tar.gz ~/.anubis/

# Store backup securely (offline, encrypted storage)
gpg -c anubis-backup-*.tar.gz

# Test restoration periodically
mkdir /tmp/test-restore
tar -xzf anubis-backup-*.tar.gz -C /tmp/test-restore
ANUBIS_HOME=/tmp/test-restore/.anubis anubis-notary key show
```

---

## Security Hardening

### File Permissions

```bash
# Keystore directory
chmod 700 ~/.anubis
chmod 600 ~/.anubis/key.sealed
chmod 644 ~/.anubis/key.pub

# Password file
chmod 600 /etc/anubis/password
```

### Network Isolation

For Mina anchoring, only outbound HTTPS is required:

```bash
# Firewall rules (ufw example)
sudo ufw allow out 443/tcp  # HTTPS for Mina GraphQL
sudo ufw default deny incoming
sudo ufw default deny outgoing
sudo ufw allow out 53/udp   # DNS
sudo ufw enable
```

### Audit Logging

```bash
# Enable audit logging
sudo auditctl -w /usr/local/bin/anubis-notary -p x -k anubis
sudo auditctl -w /var/lib/anubis -p rwa -k anubis-keystore

# View audit logs
sudo ausearch -k anubis
```

---

## Monitoring

### Health Check Script

```bash
#!/bin/bash
# /usr/local/bin/anubis-healthcheck.sh

set -e

# Check binary exists
which anubis-notary > /dev/null

# Check keystore accessible
ANUBIS_PASSWORD_FILE=/etc/anubis/password anubis-notary key show > /dev/null

# Check Mina bridge (if used)
if [ -d ~/.anubis/mina-bridge ]; then
    anubis-notary anchor mina time > /dev/null
fi

echo "OK"
```

### Prometheus Metrics

Create wrapper script for metrics:

```bash
#!/bin/bash
# /usr/local/bin/anubis-metrics.sh

echo "# HELP anubis_keystore_accessible Keystore is accessible"
echo "# TYPE anubis_keystore_accessible gauge"
if ANUBIS_PASSWORD_FILE=/etc/anubis/password anubis-notary key show > /dev/null 2>&1; then
    echo "anubis_keystore_accessible 1"
else
    echo "anubis_keystore_accessible 0"
fi

echo "# HELP anubis_mina_block_height Current Mina block height"
echo "# TYPE anubis_mina_block_height gauge"
HEIGHT=$(anubis-notary --json anchor mina time 2>/dev/null | jq -r '.data.height // 0')
echo "anubis_mina_block_height $HEIGHT"
```

---

## Upgrading

### Binary Upgrade

```bash
# Download new version
curl -LO https://github.com/AnubisQuantumCipher/anubis-notary/releases/latest/download/anubis-notary-linux-x86_64

# Verify checksum (from release notes)
sha256sum anubis-notary-linux-x86_64

# Backup old binary
sudo mv /usr/local/bin/anubis-notary /usr/local/bin/anubis-notary.bak

# Install new version
chmod +x anubis-notary-linux-x86_64
sudo mv anubis-notary-linux-x86_64 /usr/local/bin/anubis-notary

# Verify
anubis-notary --version

# Test keystore access
anubis-notary key show
```

### Rollback

```bash
# If issues, rollback
sudo mv /usr/local/bin/anubis-notary.bak /usr/local/bin/anubis-notary
anubis-notary --version
```

---

## Environment Variables Reference

| Variable | Description | Default |
|----------|-------------|---------|
| `ANUBIS_HOME` | Keystore directory | `~/.anubis` |
| `ANUBIS_PASSWORD` | Keystore password | (prompt) |
| `ANUBIS_PASSWORD_FILE` | File containing password | - |
| `MINA_PRIVATE_KEY` | Mina wallet private key | - |
| `MINA_NETWORK` | Mina network | `mainnet` |
| `MINA_ZKAPP_ADDRESS` | Custom zkApp address | (official) |
| `MINA_FEE` | Transaction fee (nanomina) | `100000000` |
| `MINA_DEBUG` | Enable bridge debug logs | `0` |
| `RUST_LOG` | Rust logging level | - |
