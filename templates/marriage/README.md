# Anubis Marriage Templates

Pre-built templates for blockchain-anchored marriage contracts on Starknet.

## Available Templates

| Template | Parties | Use Case |
|----------|---------|----------|
| `monogamy` | 2 | Standard two-party marriage |
| `polygamy` | 2-10 | Multi-party marriages |
| `simple` | 2 | Quick, minimal marriage |
| `prenup` | 2 | With prenuptial agreement |
| `comprehensive` | 2-10 | Full legal provisions |

## Quick Start

```bash
# Create a simple marriage document
anubis-notary marriage init \
  --template monogamy \
  --parties "Alice,Bob" \
  --jurisdiction US-CA \
  -o marriage.json

# Each party signs
ANUBIS_PASSWORD=xxx anubis-notary marriage sign marriage.json --party 0
ANUBIS_PASSWORD=xxx anubis-notary marriage sign marriage.json --party 1

# Verify all signatures
anubis-notary marriage verify marriage.json

# Create on-chain (Sepolia testnet)
anubis-notary marriage create marriage.json --network sepolia
```

## Template Details

### monogamy.json
Standard two-party marriage with:
- Equal 50/50 asset split
- Mutual consent required for divorce
- NFT rings for each spouse

### polygamy.json
Multi-party marriage (2-10 parties) with:
- Proportional asset distribution
- Majority threshold for divorce (n/2 + 1)
- All parties must sign to validate

### simple.json
Minimal template for quick ceremonies:
- Default equal asset split
- Mutual consent divorce
- No custom clauses

### prenup.json
Marriage with prenuptial agreement:
- Custom asset split
- 90-day cooling period before divorce
- Separate property provisions
- Encrypted financial terms recommended

### comprehensive.json
Full legal marriage contract with:
- All provision types supported
- 6-month cooling period
- Mandatory mediation for divorce
- Witness requirements (2-4)
- Legal counsel attestation
- Encrypted private terms
- Amendment support

## Contract Addresses

### Sepolia Testnet
- **Marriage Oracle**: `0x0457be1c094b09a3f27690388b8a4d70c908fec9b7de45bfb5d152488acd2181`
- **Marriage Ring NFT**: `0x07f579e725cbd8dbac8974245d05824f1024bc0c041d98e0a6133dbd5cdc7090`

### Mainnet
Not yet deployed.

## Privacy Options

For sensitive financial terms, use the private batch system:

```bash
# Encrypt terms for threshold decryption
anubis-notary private-batch create marriage.json \
  --recipient spouse1.mlkem.pub \
  --recipient spouse2.mlkem.pub \
  --recipient lawyer.mlkem.pub \
  --threshold 2 \
  -o private-marriage.batch

# Anchor the encrypted batch (only Merkle root on-chain)
anubis-notary anchor starknet anchor private-marriage.batch
```

## Costs

| Operation | Estimated Cost |
|-----------|----------------|
| Create Marriage | ~$0.001 |
| Mint NFT Rings (2) | ~$0.002 |
| Execute Divorce | ~$0.001 |
| Add Amendment | ~$0.001 |

Total ceremony: ~$0.005 on Starknet mainnet.

## Security

- **Post-Quantum Signatures**: All signatures use ML-DSA-87 (FIPS 204)
- **Encryption**: Terms encrypted with ML-KEM-1024 (FIPS 203)
- **Immutable**: Marriage hash permanently anchored on Starknet
- **Multi-sig**: All parties must consent before creation
