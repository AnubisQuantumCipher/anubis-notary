# Multi-Signature Governance Guide

This guide explains how to use Anubis Notary's multi-signature (multisig) feature for governance and shared custody scenarios.

## Overview

Multi-signature governance allows multiple parties to collectively authorize actions. A threshold scheme (M-of-N) requires M signatures from N total signers to execute a proposal.

**Use Cases:**
- Corporate governance (board approvals)
- Shared custody of signing authority
- Multi-party authorization workflows
- Disaster recovery with distributed keys

## Quick Start

### 1. Export Public Keys

Each participant exports their public key:

```bash
# Participant 1
anubis-notary key show --pub-only > signer1.pub

# Participant 2
anubis-notary key show --pub-only > signer2.pub

# Participant 3
anubis-notary key show --pub-only > signer3.pub
```

### 2. Initialize Multisig Configuration

Create a 2-of-3 multisig (requires 2 signatures from 3 signers):

```bash
anubis-notary multisig init \
  --threshold 2 \
  --signers signer1.pub,signer2.pub,signer3.pub \
  -o governance.config
```

### 3. Create a Proposal

Any signer can create a proposal:

```bash
anubis-notary multisig propose \
  --config governance.config \
  --proposal-type authorize-action \
  --data "$(echo -n 'Approve budget Q1 2025' | xxd -p)" \
  -o proposal.bin
```

### 4. Sign the Proposal

Each signer reviews and signs:

```bash
# Signer 1
anubis-notary multisig sign \
  --config governance.config \
  --proposal proposal.bin

# Signer 2
anubis-notary multisig sign \
  --config governance.config \
  --proposal proposal.bin
```

### 5. Execute When Threshold Met

Once enough signatures are collected:

```bash
anubis-notary multisig execute \
  --config governance.config \
  --proposal proposal.bin
```

## Proposal Types

| Type | Description | Data Format |
|------|-------------|-------------|
| `authorize-action` | Generic authorization | Hex-encoded action description |
| `update-config` | Modify multisig settings | New configuration parameters |
| `rotate-signer` | Replace a signer's key | Old + new public key |
| `emergency-revoke` | Emergency key revocation | Key fingerprint to revoke |

## Environment Variables for CI/CD

For automated multisig workflows:

```bash
# Set keystore location
export ANUBIS_HOME=/path/to/keystore

# Set password (non-interactive)
export ANUBIS_PASSWORD="secure-password"

# Or use a password file
export ANUBIS_PASSWORD_FILE=/path/to/password.txt
```

## Example: Corporate Board Approval

### Setup (One-time)

```bash
# Each board member generates a key
anubis-notary key init --low-memory

# Export public keys
anubis-notary key show --pub-only > ceo.pub
anubis-notary key show --pub-only > cfo.pub
anubis-notary key show --pub-only > cto.pub

# Create 2-of-3 board config
anubis-notary multisig init \
  --threshold 2 \
  --signers ceo.pub,cfo.pub,cto.pub \
  -o board.config
```

### Approval Workflow

```bash
# 1. CEO creates proposal for major expenditure
anubis-notary multisig propose \
  --config board.config \
  --proposal-type authorize-action \
  --data "$(echo -n 'Approve $1M infrastructure investment' | xxd -p)" \
  -o expenditure-proposal.bin

# 2. CEO signs (as proposer)
anubis-notary multisig sign \
  --config board.config \
  --proposal expenditure-proposal.bin

# 3. CFO reviews and co-signs
anubis-notary multisig sign \
  --config board.config \
  --proposal expenditure-proposal.bin

# 4. Execute (threshold of 2 met)
anubis-notary multisig execute \
  --config board.config \
  --proposal expenditure-proposal.bin
```

## Example: Emergency Key Rotation

If a signer's key is compromised:

```bash
# Create emergency rotation proposal
anubis-notary multisig propose \
  --config governance.config \
  --proposal-type rotate-signer \
  --data "$(cat compromised.pub new-signer.pub | xxd -p)" \
  -o emergency-rotation.bin

# Remaining signers approve
anubis-notary multisig sign --config governance.config --proposal emergency-rotation.bin
anubis-notary multisig sign --config governance.config --proposal emergency-rotation.bin

# Execute rotation
anubis-notary multisig execute --config governance.config --proposal emergency-rotation.bin
```

## Security Considerations

### Key Storage
- Store private keys on separate, secure systems
- Use hardware security modules (HSMs) for high-value scenarios
- Never share private keys between signers

### Threshold Selection
| Signers | Recommended Threshold | Use Case |
|---------|----------------------|----------|
| 2 | 2-of-2 | Dual control (both required) |
| 3 | 2-of-3 | Standard governance |
| 5 | 3-of-5 | High security with redundancy |
| 7 | 4-of-7 | Enterprise governance |

### Proposal Review
- Always verify proposal contents before signing
- Use `--json` output for programmatic verification
- Implement out-of-band confirmation for critical actions

## JSON Output

For automation, use `--json` flag:

```bash
anubis-notary multisig propose \
  --config governance.config \
  --proposal-type authorize-action \
  --data "..." \
  -o proposal.bin \
  --json
```

Output:
```json
{
  "success": true,
  "data": {
    "proposal_id": "a1b2c3d4...",
    "proposal_type": "authorize-action",
    "threshold": 2,
    "total_signers": 3,
    "signatures_collected": 0,
    "status": "pending"
  }
}
```

## Troubleshooting

### "Threshold not met"
Not enough signatures collected. Check current status:
```bash
anubis-notary multisig status --config governance.config --proposal proposal.bin
```

### "Invalid signer"
The signing key is not in the multisig configuration. Verify with:
```bash
anubis-notary multisig list-signers --config governance.config
```

### "Proposal expired"
Proposals may have time limits. Create a new proposal.

### "Duplicate signature"
A signer already signed this proposal. Each signer can only sign once.

## Best Practices

1. **Distribute configuration** - All signers should have a copy of the config file
2. **Secure proposal transport** - Use encrypted channels to share proposals
3. **Verify before signing** - Always decode and verify proposal contents
4. **Backup configurations** - Store config files securely with other backups
5. **Regular key rotation** - Rotate signer keys periodically
6. **Audit trail** - Keep records of all proposals and executions

## Command Reference

| Command | Description |
|---------|-------------|
| `multisig init` | Create new multisig configuration |
| `multisig propose` | Create a new proposal |
| `multisig sign` | Add signature to proposal |
| `multisig execute` | Execute proposal (if threshold met) |
| `multisig status` | Check proposal status |
| `multisig list-signers` | List all signers in config |
| `multisig verify` | Verify proposal signatures |

## See Also

- [README.md](../README.md) - Main documentation
- [CONTRIBUTING.md](../CONTRIBUTING.md) - Contribution guidelines
