# Starknet Blockchain Anchoring Guide

Complete guide for anchoring Anubis Notary receipts to Starknet for immutable proof-of-existence.

## Overview

Starknet anchoring enables you to store cryptographic proof of your documents on-chain, providing:

- **Immutable Timestamps**: Blockchain-backed proof of when a document existed
- **Ultra-Low Cost**: ~$0.001 per anchor (100x cheaper than Ethereum L1)
- **ZK-STARK Proofs**: Native validity proofs ensure correctness
- **Post-Quantum Binding**: SHA3-256 receipts → Poseidon on-chain

### How It Works

```
┌─────────────────────────────────────────────────────────────────┐
│                    Anchoring Pipeline                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. Sign document with ML-DSA-87                                │
│     document.pdf → ML-DSA-87 → receipt.anb                      │
│                                                                  │
│  2. Receipt contains SHA3-256 hash of document                  │
│     sha3_256(document.pdf) = 0x31b1781...                       │
│                                                                  │
│  3. Convert to Poseidon felt252 for Starknet                    │
│     sha3_256 → split(16+16 bytes) → poseidon_hash_many()        │
│                                                                  │
│  4. Submit to NotaryOracle contract                             │
│     anchor_root(poseidon_root) → tx_hash                        │
│                                                                  │
│  5. Verify on-chain                                             │
│     verify_root(poseidon_root) → true/false                     │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Prerequisites

### 1. Install Starknet Foundry (sncast)

```bash
# Install snfoundry
curl -L https://raw.githubusercontent.com/foundry-rs/starknet-foundry/master/scripts/install.sh | sh

# Restart terminal, then verify
sncast --version
# Output: sncast 0.x.x
```

### 2. Create a Starknet Account

```bash
# Create a new account (generates keypair)
sncast account create --name myaccount --network sepolia

# Output shows your account address - fund it before deployment
# Address: 0x...

# Deploy the account (requires ~0.001 ETH for gas)
sncast account deploy --name myaccount --network sepolia
```

### 3. Fund Your Account

For **Sepolia testnet**:
- Use the [Starknet Faucet](https://starknet-faucet.vercel.app/) or
- Bridge ETH from Ethereum Sepolia via the [Starknet Bridge](https://sepolia.starkgate.starknet.io/)

For **Mainnet**:
- Bridge ETH from Ethereum mainnet via [StarkGate](https://starkgate.starknet.io/)
- Or purchase STRK via exchanges and bridge

### 4. Set Environment Variables

```bash
# Required for anchoring
export STARKNET_ACCOUNT_NAME="myaccount"

# Optional: Override network (default: mainnet)
export STARKNET_NETWORK="sepolia"  # or "mainnet"
```

---

## Configuration

### Show Current Configuration

```bash
anubis-notary anchor starknet info
```

Output:
```
Starknet Configuration
━━━━━━━━━━━━━━━━━━━━━
Network:    sepolia
RPC URL:    https://starknet-sepolia.drpc.org
Contract:   0x04aa72f8dc65247389378621b6ff3e61852d56ddf571b522d03f02dc7f827606

Current Block: 847123
Timestamp:     2024-01-15T14:32:18Z
```

### Set Contract Address

```bash
# Configure the NotaryOracle contract address
anubis-notary anchor starknet config --contract 0x04aa72f8dc65247389378621b6ff3e61852d56ddf571b522d03f02dc7f827606
```

### Official Deployed Contracts

| Network | Contract Address | Explorer |
|---------|------------------|----------|
| **Sepolia** | `0x04aa72f8dc65247389378621b6ff3e61852d56ddf571b522d03f02dc7f827606` | [View on Voyager](https://sepolia.voyager.online/contract/0x04aa72f8dc65247389378621b6ff3e61852d56ddf571b522d03f02dc7f827606) |
| **Mainnet** | *Deploy your own (see below)* | - |

---

## Single Anchor Workflow

### Step 1: Create a Receipt

```bash
# Initialize keystore (first time only)
anubis-notary key init

# Create a signed receipt for your document
anubis-notary attest document.pdf --receipt document.receipt
```

### Step 2: Anchor to Starknet

```bash
# Anchor the receipt
anubis-notary anchor starknet anchor document.receipt
```

Output:
```
Anchoring to Starknet...
━━━━━━━━━━━━━━━━━━━━━━━
Network:      sepolia
Contract:     0x04aa72f8...
Receipt Hash: 31b178155e575398381b43052c016d16216d2974...

Converting SHA3-256 → Poseidon felt252...
Poseidon Root: 0x2a8f9c1d3e4b5a6f7890...

Submitting transaction...
Transaction Hash: 0x0321919a1f8b...

Waiting for confirmation...
✓ Anchored successfully!

Block:     847456
Timestamp: 2024-01-15T14:35:42Z
Explorer:  https://sepolia.voyager.online/tx/0x0321919a1f8b...
```

### Step 3: Verify the Anchor

```bash
# Verify a receipt is anchored on-chain
anubis-notary anchor starknet verify document.receipt
```

Output:
```
Verifying anchor...
━━━━━━━━━━━━━━━━━
Receipt:      document.receipt
Poseidon Root: 0x2a8f9c1d3e4b5a6f7890...

Querying contract...
✓ Root verified on-chain!

Anchored at block 847456 (2024-01-15T14:35:42Z)
```

---

## Batch Anchoring (8x Cost Savings)

Batch anchoring combines multiple receipts into a single on-chain transaction using a Merkle tree. This provides 8x cost savings while maintaining individual verifiability.

### How Batch Anchoring Works

```
┌─────────────────────────────────────────────────────────────────┐
│                   Batch Merkle Tree                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│                        [Batch Root]                             │
│                       /            \                            │
│                    [H01]          [H23]                         │
│                   /    \         /    \                         │
│                [R0]   [R1]    [R2]   [R3]                       │
│                 │      │       │      │                         │
│               doc1   doc2    doc3   doc4                        │
│                                                                  │
│  Only the Batch Root is stored on-chain.                        │
│  Each receipt can prove inclusion via Merkle witness.           │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Queue Receipts

```bash
# Add receipts to the batch queue
anubis-notary anchor starknet queue receipt1.anb
anubis-notary anchor starknet queue receipt2.anb
anubis-notary anchor starknet queue receipt3.anb
anubis-notary anchor starknet queue receipt4.anb

# Check queue status
anubis-notary anchor starknet queue-status
```

Output:
```
Starknet Batch Queue
━━━━━━━━━━━━━━━━━━━
Queued receipts: 4/8
Estimated cost:  ~0.000125 ETH per receipt (vs 0.001 single)

Receipts:
  1. receipt1.anb (added 2024-01-15T14:30:00Z)
  2. receipt2.anb (added 2024-01-15T14:30:05Z)
  3. receipt3.anb (added 2024-01-15T14:30:10Z)
  4. receipt4.anb (added 2024-01-15T14:30:15Z)

Auto-flush at: 8 receipts
```

### Submit Batch

```bash
# Submit when queue reaches 8 (auto-flush), or force submit:
anubis-notary anchor starknet flush

# Force submit with fewer than 8 receipts:
anubis-notary anchor starknet flush --force
```

### Verify Individual Receipt in Batch

Each receipt can independently prove its inclusion in the batch:

```bash
anubis-notary anchor starknet verify receipt2.anb
```

Output:
```
Verifying batch inclusion...
━━━━━━━━━━━━━━━━━━━━━━━━━
Receipt:       receipt2.anb
Batch Root:    0x3c5d6e7f8a9b...
Merkle Index:  1
Witness Size:  3 nodes

Computing Merkle proof...
✓ Receipt verified in batch!

Batch anchored at block 847789 (2024-01-15T15:00:00Z)
```

---

## Cost Analysis

### Transaction Costs

| Operation | Sepolia (testnet) | Mainnet (est.) |
|-----------|-------------------|----------------|
| Single Anchor | ~0.0001 ETH | ~$0.001 |
| Batch (8 receipts) | ~0.0001 ETH | ~$0.001 |
| **Per Receipt (batch)** | ~0.0000125 ETH | ~$0.000125 |

### Comparison with Other Chains

| Chain | Single Anchor | Per Receipt (Batch) | Settlement |
|-------|---------------|---------------------|------------|
| **Starknet** | ~$0.001 | ~$0.000125 | L1 (Ethereum) |
| **Mina** | ~$0.08 | ~$0.01 | L1 (Mina) |
| **Ethereum L1** | ~$5-50 | ~$0.60-6 | L1 |

---

## Mainnet Deployment

### Deploy Your Own Contract

```bash
cd starknet-contract

# Build the contract
scarb build

# Declare the contract class
sncast --account myaccount declare \
  --contract-name NotaryOracle \
  --network mainnet

# Note the class hash from output
# CLASS_HASH=0x...

# Deploy an instance
sncast --account myaccount deploy \
  --class-hash 0x<CLASS_HASH> \
  --constructor-calldata 0x<YOUR_ACCOUNT_ADDRESS> \
  --network mainnet

# Note the contract address
# CONTRACT_ADDRESS=0x...

# Configure Anubis Notary to use your contract
anubis-notary anchor starknet config --contract 0x<CONTRACT_ADDRESS>
```

### Verify Contract on Voyager

```bash
cd starknet-contract

# Verify source code on Voyager
sncast verify \
  --contract-address 0x<CONTRACT_ADDRESS> \
  --contract-name NotaryOracle \
  --verifier voyager \
  --network mainnet
```

### Production Security Checklist

- [ ] Use a dedicated account for anchoring operations
- [ ] Store private keys securely (hardware wallet recommended for mainnet)
- [ ] Set up account monitoring for unexpected transactions
- [ ] Consider using a multisig for contract ownership
- [ ] Test thoroughly on Sepolia before mainnet deployment
- [ ] Budget for gas costs (recommend maintaining 0.01 ETH minimum)

---

## Technical Details

### SHA3-256 to Poseidon Conversion

Starknet's native field element (felt252) can only hold values up to 2^251 - 1, but SHA3-256 produces 256-bit hashes. The conversion process:

```
SHA3-256 Hash (32 bytes)
    │
    ├── High 16 bytes → felt252
    │
    └── Low 16 bytes → felt252
           │
           ▼
    poseidon_hash_many([high, low])
           │
           ▼
    Poseidon Root (felt252) → On-chain
```

This maintains cryptographic binding: the Poseidon root uniquely identifies the original SHA3-256 hash.

### NotaryOracle Contract Interface

```cairo
#[starknet::interface]
trait INotaryOracle<TContractState> {
    // Anchor a new Merkle root
    fn anchor_root(ref self: TContractState, root: felt252);

    // Verify if a root exists
    fn verify_root(self: @TContractState, root: felt252) -> bool;

    // Get total number of anchored roots
    fn get_anchor_count(self: @TContractState) -> u64;
}
```

### RPC Endpoints

The client uses [dRPC](https://drpc.org/) public endpoints by default:

| Network | RPC URL |
|---------|---------|
| Mainnet | `https://starknet-mainnet.drpc.org` |
| Sepolia | `https://starknet-sepolia.drpc.org` |
| Devnet | `http://localhost:5050` |

You can override with `--rpc-url <URL>` if needed.

---

## Troubleshooting

### "sncast not found"

Install Starknet Foundry:
```bash
curl -L https://raw.githubusercontent.com/foundry-rs/starknet-foundry/master/scripts/install.sh | sh
# Restart terminal
```

### "Account not found"

Create and deploy an account:
```bash
sncast account create --name myaccount --network sepolia
# Fund the account address shown
sncast account deploy --name myaccount --network sepolia
```

### "Insufficient funds"

Check balance and fund your account:
```bash
# Check balance
anubis-notary anchor starknet balance

# Fund via faucet (Sepolia) or bridge (mainnet)
```

### "Contract address required"

Configure the contract address:
```bash
anubis-notary anchor starknet config \
  --contract 0x04aa72f8dc65247389378621b6ff3e61852d56ddf571b522d03f02dc7f827606
```

### "Transaction reverted"

Check that:
1. Contract is deployed and accessible
2. You have sufficient ETH for gas
3. The root hasn't already been anchored (duplicates are rejected)

### "Timeout waiting for confirmation"

Starknet blocks take ~3-15 seconds. If still pending:
```bash
# Check transaction status manually
sncast tx-status --transaction-hash 0x<TX_HASH> --network sepolia
```

---

## Environment Variables Reference

| Variable | Description | Default |
|----------|-------------|---------|
| `STARKNET_ACCOUNT_NAME` | sncast account name | `anubis-deployer` |
| `STARKNET_NETWORK` | Network: `mainnet`, `sepolia`, `devnet` | `mainnet` |
| `STARKNET_RPC_URL` | Custom RPC endpoint | (network default) |
| `STARKNET_CONTRACT` | NotaryOracle contract address | (from config) |

---

## CLI Reference

```bash
# Show network info and configuration
anubis-notary anchor starknet info

# Generate a new Starknet keypair
anubis-notary anchor starknet keygen

# Configure contract address
anubis-notary anchor starknet config --contract <ADDRESS>

# Anchor a single receipt
anubis-notary anchor starknet anchor <RECEIPT>

# Verify a receipt is anchored
anubis-notary anchor starknet verify <RECEIPT>

# Queue receipt for batch anchoring
anubis-notary anchor starknet queue <RECEIPT>

# Show batch queue status
anubis-notary anchor starknet queue-status

# Submit batch to blockchain
anubis-notary anchor starknet flush [--force]

# Check account balance
anubis-notary anchor starknet balance
```

---

## See Also

- [Mina Protocol Anchoring](./MINA.md) - Alternative anchoring via Mina
- [Architecture Guide](./ARCHITECTURE.md) - System design overview
- [Troubleshooting Guide](./TROUBLESHOOTING.md) - General troubleshooting
