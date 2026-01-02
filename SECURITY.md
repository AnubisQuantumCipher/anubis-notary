# Security Policy

## Supported Versions

| Version | Supported          |
| ------- | ------------------ |
| 0.3.x   | :white_check_mark: |
| 0.2.x   | :x:                |
| 0.1.x   | :x:                |

## Reporting a Vulnerability

**Do NOT open public issues for security vulnerabilities.**

Please report security issues privately to: **sic.tau@pm.me**

### What to Include

- Description of the vulnerability
- Steps to reproduce
- Potential impact assessment
- Suggested fix (if any)
- Your contact information

### Response Timeline

| Phase | Timeframe |
|-------|-----------|
| Initial acknowledgment | 48 hours |
| Preliminary assessment | 7 days |
| Fix development | 14-30 days (severity dependent) |
| Public disclosure | After fix is released |

### Severity Classification

| Level | Description | Example |
|-------|-------------|---------|
| **Critical** | Remote code execution, key compromise | Memory corruption in crypto primitives |
| **High** | Signature forgery, encryption bypass | Timing attack on comparison |
| **Medium** | Information disclosure, DoS | Metadata leakage |
| **Low** | Minor issues, edge cases | Error message verbosity |

## Security Model

### Cryptographic Algorithms

| Algorithm | Standard | Security Level |
|-----------|----------|----------------|
| ML-DSA-87 | FIPS 204 | NIST Level 5 (256-bit post-quantum) |
| ML-KEM-1024 | FIPS 203 | NIST Level 5 (256-bit post-quantum) |
| SHA3-256 | FIPS 202 | 256-bit pre-image resistance |
| SHAKE256 | FIPS 202 | Arbitrary output length |
| ChaCha20Poly1305 | RFC 8439 | 256-bit symmetric |
| Argon2id | RFC 9106 | Memory-hard (1-4 GiB) |

### Implementation Security

- **Constant-time operations**: All secret-dependent computations use constant-time algorithms
- **Zeroization**: Sensitive data is securely cleared from memory using `zeroize` crate
- **Memory-hard KDF**: Argon2id with configurable memory (1-4 GiB) prevents brute-force attacks
- **Atomic file operations**: fsync + rename pattern prevents partial writes
- **No `unsafe` code** in cryptographic paths without explicit SAFETY documentation

### Formal Verification

Critical properties are formally verified using Rocq/Coq:

- Nonce injectivity (different inputs produce different nonces)
- CBOR totality (all valid inputs parse correctly)
- Merkle tree correctness (proof verification is sound)
- AEAD correctness (Decrypt(Encrypt(m)) = m)
- Signature properties (Verify(Sign(m)) = true)

### Known Limitations

| Limitation | Mitigation |
|------------|------------|
| Hardware side-channels (cache, power) | Use dedicated HSM for high-value keys |
| Memory corruption attacks | Stack canaries, ASLR enabled |
| Quantum attacks on ChaCha20 | Planned migration to quantum-safe AEAD |

## Secure Usage Guidelines

### Password Selection

```bash
# Strong password: 16+ chars, mixed case, numbers, symbols
export ANUBIS_PASSWORD="YourStr0ng!P@ssw0rd"

# Or use a password file with restricted permissions
echo "password" > ~/.anubis-password
chmod 600 ~/.anubis-password
export ANUBIS_PASSWORD_FILE=~/.anubis-password
```

### Key Storage

```bash
# Default keystore location
~/.anubis/keystore.bin

# Permissions should be restrictive
chmod 700 ~/.anubis
chmod 600 ~/.anubis/keystore.bin
```

### Environment Variables

| Variable | Security Note |
|----------|---------------|
| `ANUBIS_PASSWORD` | Visible in process list; prefer `ANUBIS_PASSWORD_FILE` |
| `ANUBIS_PASSWORD_FILE` | Ensure file has 600 permissions |
| `MINA_PRIVATE_KEY` | Required for blockchain anchoring; keep secure |

### Network Security

- All Mina GraphQL queries use HTTPS
- No plaintext secrets transmitted over network
- Consider VPN/Tor for sensitive operations

## Audit History

| Date | Auditor | Scope | Result |
|------|---------|-------|--------|
| 2024-12 | Internal | Full codebase | Initial security review |
| 2025-01 | CodeRabbit | Automated | CI/CD security scanning |

## Acknowledgments

We thank the following for responsible disclosure:

- *No public disclosures yet*

---

For general questions, open a [GitHub Discussion](https://github.com/AnubisQuantumCipher/anubis-notary/discussions).
