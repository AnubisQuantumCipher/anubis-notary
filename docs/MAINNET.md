# Mainnet Deployment Guide

Production deployment guide for Anubis Notary blockchain anchoring.

## Overview

This guide covers deploying Anubis Notary anchoring infrastructure to production mainnet environments for both Starknet and Mina Protocol.

---

## Starknet Mainnet

### Prerequisites

1. **Production Account**: A funded Starknet mainnet account
2. **STRK Balance**: Minimum 10 STRK recommended for operations
3. **sncast**: Starknet Foundry CLI installed

### Step 1: Create Mainnet Account

```bash
# Create account for mainnet
sncast account create --name anubis-mainnet --network mainnet

# Output shows account address - fund it before deployment
# Address: 0x...

# Send 10 STRK to this address from an exchange (Binance, OKX, Bybit, Gate.io)
```

### Step 2: Deploy Account

```bash
# After funding, deploy the account contract
sncast account deploy --name anubis-mainnet --network mainnet
```

### Step 3: Build and Declare Contract

```bash
cd starknet-contract

# Build with release optimizations
scarb build

# Declare on mainnet
sncast --account anubis-mainnet declare \
  --contract-name NotaryOracle \
  --network mainnet

# Save the class hash
# CLASS_HASH=0x...
```

### Step 4: Deploy Contract Instance

```bash
# Get your account address
sncast account list

# Deploy with your account as owner
sncast --account anubis-mainnet deploy \
  --class-hash 0x<CLASS_HASH> \
  --constructor-calldata 0x<YOUR_ACCOUNT_ADDRESS> \
  --network mainnet

# Save the contract address
# CONTRACT=0x...
```

### Step 5: Verify Source Code

```bash
# Verify on Voyager for transparency
sncast verify \
  --contract-address 0x<CONTRACT> \
  --contract-name NotaryOracle \
  --verifier voyager \
  --network mainnet
```

### Step 6: Configure Anubis Notary

```bash
# Set mainnet as default
export STARKNET_NETWORK="mainnet"
export STARKNET_ACCOUNT_NAME="anubis-mainnet"

# Configure contract address
anubis-notary anchor starknet config --contract 0x<CONTRACT>

# Verify configuration
anubis-notary anchor starknet info
```

### Mainnet Costs (Estimated)

Gas fees on Starknet are paid in **STRK** (the native Starknet token).

| Operation | STRK Cost | USD (@ $1.20/STRK) |
|-----------|-----------|-------------------|
| Account Deployment | ~2 STRK | ~$2.40 |
| Contract Declaration | ~3 STRK | ~$3.60 |
| Contract Deployment | ~2 STRK | ~$2.40 |
| Single Anchor | ~0.8 STRK | ~$0.96 |
| Batch Anchor (8 roots) | ~0.8 STRK | ~$0.96 |
| **Per Receipt (batch)** | ~0.1 STRK | ~$0.12 |

---

## Mina Mainnet

### Prerequisites

1. **Mina Wallet**: With ~1 MINA for deployment + anchoring
2. **Node.js 18+**: For zkApp compilation
3. **Mina Bridge**: Installed and configured

### Step 1: Setup Mina Bridge

```bash
# Install dependencies
cd mina-bridge
npm install

# Build bridge
npm run build
```

### Step 2: Generate or Import Key

```bash
# Generate new keypair
anubis-notary anchor mina keygen

# Or use existing key
export MINA_PRIVATE_KEY="your-existing-private-key"
```

### Step 3: Fund Account

Purchase MINA from exchanges and send to your address:
- Binance, Kraken, OKX, Gate.io support MINA
- Minimum: 1 MINA (for deployment + initial anchors)

### Step 4: Configure for Mainnet

```bash
# The official zkApp is already deployed on mainnet
# Just set your private key
export MINA_PRIVATE_KEY="your-key"
export MINA_NETWORK="mainnet"

# Verify configuration
anubis-notary anchor mina config --show
```

### Pre-Deployed Mainnet Contract

The AnubisAnchor zkApp is deployed and ready to use:

| Property | Value |
|----------|-------|
| **Address** | `B62qnHLXkWxxJ4NwKgT8zwJ2JKZ8nymgrUyK7R7k5fm7ELPRgeEH8E3` |
| **Network** | Mina Mainnet |
| **Deployment TX** | [View on Minascan](https://minascan.io/mainnet/tx/5JvH2AvfsQDwXu41yAWJHosgadAtzEcqrRCeRYraSu43nriKoKe7) |

### Mainnet Costs

| Operation | MINA Cost | USD (@ $1/MINA) |
|-----------|-----------|-----------------|
| Single Anchor | ~0.1 | ~$0.10 |
| Batch Anchor (8 roots) | ~0.1 | ~$0.10 |
| **Per Receipt (batch)** | ~0.0125 | ~$0.0125 |

---

## Security Checklist

### Account Security

- [ ] Use dedicated accounts for anchoring (not personal wallets)
- [ ] Store private keys in secure environment (HSM, Vault, or encrypted storage)
- [ ] Never commit private keys to version control
- [ ] Use environment variables or secure secret management
- [ ] Enable 2FA on exchange accounts used for funding

### Operational Security

- [ ] Monitor account balances and set up alerts
- [ ] Implement rate limiting for anchoring operations
- [ ] Log all anchoring transactions for audit
- [ ] Set up alerts for unusual activity
- [ ] Regular key rotation schedule

### Contract Security

- [ ] Verify source code on block explorers
- [ ] Use multisig for contract ownership (if upgrading)
- [ ] Document admin functions and access controls
- [ ] Consider bug bounty program for critical deployments

---

## Infrastructure Setup

### Environment Variables

```bash
# Starknet Mainnet
export STARKNET_NETWORK="mainnet"
export STARKNET_ACCOUNT_NAME="anubis-mainnet"
export STARKNET_CONTRACT="0x..."  # Your deployed contract

# Mina Mainnet
export MINA_NETWORK="mainnet"
export MINA_PRIVATE_KEY="..."  # Secure storage recommended

# Anubis Configuration
export ANUBIS_HOME="/secure/path/to/keystore"
export ANUBIS_PASSWORD_FILE="/secure/path/to/password"
```

### Systemd Service (Linux)

```ini
# /etc/systemd/system/anubis-anchor.service
[Unit]
Description=Anubis Notary Anchor Service
After=network.target

[Service]
Type=simple
User=anubis
EnvironmentFile=/etc/anubis/env
ExecStart=/usr/local/bin/anubis-notary anchor starknet flush --force
Restart=on-failure
RestartSec=300

[Install]
WantedBy=multi-user.target
```

### Docker Deployment

```dockerfile
FROM rust:1.75-slim as builder
WORKDIR /app
COPY . .
RUN cargo build --release

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/anubis-notary /usr/local/bin/
ENTRYPOINT ["anubis-notary"]
```

```bash
# Build and run
docker build -t anubis-notary .
docker run -e STARKNET_NETWORK=mainnet \
           -e STARKNET_ACCOUNT_NAME=anubis-mainnet \
           -v /path/to/snfoundry:/root/.starknet \
           anubis-notary anchor starknet anchor receipt.anb
```

---

## Monitoring and Alerting

### Balance Monitoring

```bash
#!/bin/bash
# check-balance.sh

MIN_BALANCE="10000000000000000000"  # 10 STRK in FRI (smallest unit)

BALANCE=$(anubis-notary anchor starknet balance --json | jq -r '.balance_fri')

if [ "$BALANCE" -lt "$MIN_BALANCE" ]; then
    echo "WARNING: Low STRK balance: $BALANCE FRI"
    # Send alert (Slack, email, PagerDuty, etc.)
fi
```

### Transaction Monitoring

```bash
#!/bin/bash
# monitor-tx.sh

TX_HASH="$1"
MAX_WAIT=300  # 5 minutes

START=$(date +%s)
while true; do
    STATUS=$(sncast tx-status --transaction-hash "$TX_HASH" --network mainnet | jq -r '.finality_status')

    if [ "$STATUS" = "ACCEPTED_ON_L2" ] || [ "$STATUS" = "ACCEPTED_ON_L1" ]; then
        echo "Transaction confirmed: $TX_HASH"
        exit 0
    fi

    ELAPSED=$(($(date +%s) - START))
    if [ "$ELAPSED" -gt "$MAX_WAIT" ]; then
        echo "Transaction timeout: $TX_HASH"
        exit 1
    fi

    sleep 10
done
```

---

## Disaster Recovery

### Backup Procedures

1. **Keystore Backup**: Regular encrypted backups of `~/.anubis/`
2. **Account Keys**: Secure backup of sncast accounts in `~/.starknet/`
3. **Configuration**: Version control all config files
4. **Transaction Log**: Archive all transaction hashes for audit

### Recovery Steps

1. **Account Recovery**: Import from backup seed/private key
2. **Contract**: Redeploy if needed (roots are immutable once anchored)
3. **Configuration**: Restore from version control
4. **Verification**: Re-verify all pending anchors

---

## Support

- **Documentation**: [docs/TROUBLESHOOTING.md](./TROUBLESHOOTING.md)
- **GitHub Issues**: [github.com/AnubisQuantumCipher/anubis-notary/issues](https://github.com/AnubisQuantumCipher/anubis-notary/issues)
- **Security Issues**: sic.tau@pm.me

---

## See Also

- [Starknet Anchoring Guide](./STARKNET.md) - Detailed Starknet usage
- [Architecture Guide](./ARCHITECTURE.md) - System design
- [Troubleshooting Guide](./TROUBLESHOOTING.md) - Common issues
