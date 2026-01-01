# Troubleshooting Guide

## Common Issues

### Keystore Issues

#### "Wrong password or corrupted data"

**Symptom:** Error when running any command that requires the keystore.

```
Error: decryption failed: wrong password or corrupted data
```

**Causes:**
1. Incorrect password
2. Corrupted `key.sealed` file
3. Wrong `ANUBIS_HOME` directory

**Solutions:**

```bash
# Check which keystore you're using
echo $ANUBIS_HOME
ls -la ${ANUBIS_HOME:-~/.anubis}/

# Verify the keystore exists
ls -la ${ANUBIS_HOME:-~/.anubis}/key.sealed

# Try with explicit password
ANUBIS_PASSWORD="your-password" anubis-notary key show

# If corrupted, restore from backup or reinitialize
anubis-notary key init
```

#### "Keystore not found"

**Symptom:** Command fails with keystore not found.

```
Error: Keystore not found. Run 'key init' first.
```

**Solution:**

```bash
# Initialize a new keystore
anubis-notary key init

# Or specify custom location
export ANUBIS_HOME=/path/to/keystore
anubis-notary key init
```

#### "Memory allocation failed" during key init

**Symptom:** Key initialization fails with memory error.

```
Error: memory allocation of 4294967296 bytes failed
```

**Cause:** System doesn't have 4 GiB free memory for Argon2id.

**Solution:**

```bash
# Use low-memory mode (1 GiB instead of 4 GiB)
anubis-notary key init --low-memory
```

---

### Mina Blockchain Issues

#### "Mina bridge not installed"

**Symptom:** Mina commands fail with bridge not found.

```
Mina Anchor:
  Status: Bridge not installed

Run 'anchor mina setup' to install the Mina bridge.
```

**Solution:**

```bash
# Install the Mina bridge
anubis-notary anchor mina setup

# Verify installation
ls -la ~/.anubis/mina-bridge/

# If using custom ANUBIS_HOME, copy bridge there
cp -r ~/.anubis/mina-bridge $ANUBIS_HOME/
```

#### "Wallet not configured - set MINA_PRIVATE_KEY"

**Symptom:** Anchor command fails requesting private key.

```
Anchor failed: Wallet not configured - set MINA_PRIVATE_KEY
```

**Solution:**

```bash
# Generate a new Mina keypair
anubis-notary anchor mina keygen

# Set the private key
export MINA_PRIVATE_KEY="EK..."

# Fund the wallet with ~0.1 MINA from an exchange
# Then retry
anubis-notary anchor mina anchor receipt.anb
```

#### "Insufficient balance"

**Symptom:** Anchor fails due to low balance.

```
Anchor failed: Insufficient balance for transaction
```

**Solution:**

```bash
# Check your balance
anubis-notary anchor mina balance

# Fund with at least 0.2 MINA (0.1 for tx + reserve)
# Send MINA to your address shown in balance output
```

#### "zkApp not configured"

**Symptom:** Anchor fails with zkApp error.

```
Anchor failed: zkApp not configured - set MINA_ZKAPP_ADDRESS
```

**Solution:**

The official zkApp is pre-configured. If you see this error:

```bash
# Reset to default configuration
anubis-notary anchor mina config --show

# Or use the official zkApp explicitly
export MINA_ZKAPP_ADDRESS="B62qmEptuweVvBJbv6dLBXC7QoVJqyUuQ8dkB4PZdjUyrxFUWhSnXBg"
```

#### "Transaction stuck pending"

**Symptom:** Anchor submitted but never confirms.

**Causes:**
1. Network congestion
2. Fee too low
3. Mina node issues

**Solutions:**

```bash
# Check transaction status on explorer
# https://minascan.io/mainnet/tx/<your-tx-hash>

# Retry with higher fee
export MINA_FEE="200000000"  # 0.2 MINA
anubis-notary anchor mina anchor receipt.anb

# Wait for network - transactions typically confirm in 3-15 minutes
```

#### "Anchor timed out after 120 seconds"

**Symptom:** Anchor fails with timeout.

**Cause:** zkApp proof generation takes longer than expected.

**Solutions:**

```bash
# Ensure Node.js has enough memory
export NODE_OPTIONS="--max-old-space-size=4096"

# Try again - first run compiles circuit, subsequent runs are faster
anubis-notary anchor mina anchor receipt.anb

# Check if bridge is working
anubis-notary anchor mina time
```

---

### Private Batch Issues

#### "Invalid ML-KEM public key"

**Symptom:** Private batch creation fails with key error.

```
Error: Invalid ML-KEM public key format
```

**Solution:**

```bash
# Regenerate recipient keypair
anubis-notary private-batch keygen -o recipient

# Verify key files exist
ls -la recipient.mlkem.pub recipient.mlkem.sec
```

#### "Not enough shares to decrypt"

**Symptom:** Combine fails with threshold error.

```
Error: Need 2 shares but only provided 1
```

**Solution:**

```bash
# Check batch threshold
anubis-notary private-batch info batch.private

# Collect required number of shares
anubis-notary private-batch combine batch.private \
    -s alice.share -s bob.share \
    -o decrypted/
```

#### "Share decryption failed"

**Symptom:** decrypt-share fails.

```
Error: ML-KEM decapsulation failed
```

**Causes:**
1. Wrong secret key for this batch
2. Corrupted batch or key file

**Solution:**

```bash
# Verify key matches recipient in batch
anubis-notary private-batch info batch.private

# Check fingerprint matches your key
sha3sum recipient.mlkem.pub
```

---

### Signature Issues

#### "Signature verification failed"

**Symptom:** Verify command returns false.

```
Signature verification: FAILED
```

**Causes:**
1. Document was modified after signing
2. Wrong signature file
3. Wrong public key

**Solutions:**

```bash
# Check document hash
anubis-notary stream hash document.pdf

# Compare with signature's expected hash
anubis-notary verify --sig document.sig document.pdf --verbose

# Ensure using correct public key
anubis-notary key show
```

#### "Invalid signature format"

**Symptom:** Signature file can't be parsed.

```
Error: Invalid signature: Cbor(...)
```

**Cause:** Corrupted or truncated signature file.

**Solution:**

```bash
# Check file size (should be ~4.6 KB for ML-DSA-87)
ls -la document.sig

# Re-sign if necessary
anubis-notary sign document.pdf -o document.sig
```

---

### Receipt Issues

#### "Invalid receipt: Cbor(TypeMismatch)"

**Symptom:** Receipt commands fail with parse error.

```
Error: Invalid receipt: Cbor(TypeMismatch { ... })
```

**Causes:**
1. Not a valid receipt file
2. File is a private batch, not a receipt
3. Corrupted file

**Solution:**

```bash
# Check file type
file receipt.anb

# For private batches, use private-batch commands
anubis-notary private-batch info batch.private
```

#### "Receipt check failed"

**Symptom:** Check command fails.

```
Receipt verification: FAILED
Document hash does not match receipt
```

**Cause:** Document was modified after attestation.

**Solution:**

```bash
# Compare hashes
anubis-notary stream hash document.pdf
anubis-notary check receipt.anb document.pdf --verbose
```

---

### Build Issues

#### "cargo build fails with libcrux"

**Symptom:** Build fails in libcrux dependency.

```
error[E0599]: no function or associated item named `...` found
```

**Solution:**

```bash
# Update Rust toolchain
rustup update stable

# Clean and rebuild
cargo clean
cargo build --release
```

#### "Cross-compilation fails for Linux"

**Symptom:** Building Linux binary on macOS fails.

```
error: linker `x86_64-linux-musl-gcc` not found
```

**Solution:**

```bash
# Install musl cross-compiler
brew install filosottile/musl-cross/musl-cross

# Add target
rustup target add x86_64-unknown-linux-musl

# Build with correct linker
TARGET_CC=/opt/homebrew/opt/musl-cross/bin/x86_64-linux-musl-gcc \
TARGET_AR=/opt/homebrew/opt/musl-cross/bin/x86_64-linux-musl-ar \
CARGO_TARGET_X86_64_UNKNOWN_LINUX_MUSL_LINKER=/opt/homebrew/opt/musl-cross/bin/x86_64-linux-musl-gcc \
cargo build --release --target x86_64-unknown-linux-musl
```

---

### Environment Issues

#### Commands not found after download

**Symptom:** Binary won't execute.

```
-bash: ./anubis-notary: Permission denied
```

**Solution:**

```bash
# Make executable
chmod +x anubis-notary-*

# On macOS, remove quarantine
xattr -d com.apple.quarantine anubis-notary-darwin-aarch64
```

#### "Node.js not found" for Mina

**Symptom:** Mina commands fail with Node.js error.

```
Error: Failed to spawn bridge: No such file or directory (os error 2)
```

**Solution:**

```bash
# Install Node.js 18+
# macOS
brew install node

# Ubuntu/Debian
curl -fsSL https://deb.nodesource.com/setup_20.x | sudo -E bash -
sudo apt-get install -y nodejs

# Verify
node --version  # Should be 18+
```

---

## Debug Mode

Enable debug output for troubleshooting:

```bash
# Rust debug logging
RUST_LOG=debug anubis-notary sign document.pdf -o doc.sig

# Mina bridge debug
MINA_DEBUG=1 anubis-notary anchor mina anchor receipt.anb

# JSON output for parsing
anubis-notary --json key show
```

## Getting Help

1. **Check version:** `anubis-notary --version`
2. **View help:** `anubis-notary --help` or `anubis-notary <command> --help`
3. **File issues:** https://github.com/AnubisQuantumCipher/anubis-notary/issues

When reporting issues, include:
- Anubis Notary version
- Operating system and version
- Full error message
- Steps to reproduce
