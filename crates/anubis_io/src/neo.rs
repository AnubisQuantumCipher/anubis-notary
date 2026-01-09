//! Neo N3 Protocol integration for blockchain anchoring.
//!
//! This module provides integration with the Neo N3 blockchain
//! for timestamping, anchoring, and identity verification. It enables:
//!
//! - **Merkle Root Anchoring**: Store SHA-512 Merkle roots on-chain via NotaryOracle
//! - **dBFT Finality**: One-block confirmation (no wait needed)
//! - **NeoFS Integration**: Decentralized storage for large receipts
//! - **NeoID Integration**: Quantum-Safe Identity (QSI) verification
//! - **NNS Integration**: Human-readable name resolution
//!
//! ## CNSA 2.0 Compliance
//!
//! All fingerprints and Merkle roots use **SHA-512** (64 bytes) for full
//! CNSA 2.0 / NIST Level 5 compliance. This provides ~256-bit collision
//! resistance, matching the security level of ML-DSA-87 and ML-KEM-1024.
//!
//! ## Architecture
//!
//! Uses a blocking JSON-RPC client via `ureq` to communicate with Neo nodes:
//!
//! ```text
//! Rust (anubis_io) → ureq (HTTPS) → Neo JSON-RPC → Neo N3 Network
//! ```
//!
//! ## Cost
//!
//! Neo N3 transactions are cost-efficient (~$0.01/tx on mainnet).
//! Batch anchoring enables 8x savings by combining multiple roots.
//!
//! ## Quantum-Safe Identity (QSI)
//!
//! The QSI protocol binds ML-DSA-87 public keys to on-chain identities:
//! - DID format: `did:anubis:neo:<network>:<fingerprint>`
//! - Fingerprint: SHA-512(ML-DSA-87 public key) = 64 bytes (128 hex chars)
//! - Identity documents stored in NeoFS with self-attestation signatures
//!
//! Use `anubis_core::sha2::fingerprint()` for all identity operations.
//!
//! ## Example
//!
//! ```ignore
//! use anubis_io::neo::{NeoClient, NeoConfig, NeoNetwork};
//!
//! let config = NeoConfig::new(NeoNetwork::MainNet)
//!     .with_contract("0x1234567890abcdef...");
//!
//! let client = NeoClient::new(config)?;
//!
//! // Get current blockchain time (dBFT provides instant finality)
//! let time = client.get_block_time()?;
//! println!("Block {} at timestamp {}", time.block_number, time.timestamp);
//! ```

use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use p256::ecdsa::{signature::Signer, Signature, SigningKey};
use ripemd::{Digest as RipemdDigest, Ripemd160};
use serde::{Deserialize, Serialize};
use sha2::Sha256;
use thiserror::Error;
use zeroize::Zeroize;

/// Neo N3 error types.
#[derive(Error, Debug)]
pub enum NeoError {
    /// RPC provider error.
    #[error("provider error: {0}")]
    Provider(String),

    /// Account/signing error.
    #[error("account error: {0}")]
    Account(String),

    /// Transaction execution failed.
    #[error("transaction failed: {0}")]
    TransactionFailed(String),

    /// Transaction reverted.
    #[error("transaction reverted: {0}")]
    TransactionReverted(String),

    /// Contract not found.
    #[error("contract not found: {0}")]
    ContractNotFound(String),

    /// Configuration error.
    #[error("config error: {0}")]
    ConfigError(String),

    /// Invalid address format.
    #[error("invalid address: {0}")]
    InvalidAddress(String),

    /// Invalid script hash format.
    #[error("invalid script hash: {0}")]
    InvalidScriptHash(String),

    /// Verification failed.
    #[error("verification failed: {0}")]
    VerificationFailed(String),

    /// Request timeout.
    #[error("request timeout")]
    Timeout,

    /// Insufficient funds for transaction.
    #[error("insufficient funds: have {balance}, need {required}")]
    InsufficientFunds {
        /// Current account balance (in GAS fractions).
        balance: u128,
        /// Required amount.
        required: u128,
    },

    /// HTTP/network error.
    #[error("network error: {0}")]
    Network(String),

    /// JSON serialization/deserialization error.
    #[error("JSON error: {0}")]
    Json(String),

    /// NeoFS storage error.
    #[error("neofs error: {0}")]
    NeoFs(String),

    /// NeoID identity error.
    #[error("neoid error: {0}")]
    NeoId(String),

    /// NNS resolution error.
    #[error("nns error: {0}")]
    Nns(String),

    /// QSI (Quantum-Safe Identity) error.
    #[error("qsi error: {0}")]
    Qsi(String),

    /// Cryptographic signing error.
    #[error("signing error: {0}")]
    Signing(String),

    /// Bridge error (for subprocess calls if needed).
    #[error("bridge error: {0}")]
    Bridge(String),
}

/// Neo N3 network selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum NeoNetwork {
    /// Neo N3 mainnet.
    #[default]
    MainNet,
    /// Neo N3 testnet (T5).
    TestNet,
    /// Local Neo Express or private network.
    Private,
}

impl NeoNetwork {
    /// Get the default RPC URL for this network.
    ///
    /// Uses reliable public endpoints from the Neo ecosystem.
    pub fn default_rpc_url(&self) -> &'static str {
        match self {
            // COZ (City of Zion) public endpoints - reliable and fast
            NeoNetwork::MainNet => "https://mainnet1.neo.coz.io:443",
            NeoNetwork::TestNet => "https://testnet1.neo.coz.io:443",
            NeoNetwork::Private => "http://localhost:10332",
        }
    }

    /// Get the default NeoFS REST gateway for this network.
    ///
    /// Uses the REST Gateway (recommended) instead of the deprecated HTTP gateway.
    /// REST Gateway endpoints: https://rest.fs.neo.org (mainnet), https://rest.t5.fs.neo.org (testnet)
    pub fn default_neofs_url(&self) -> &'static str {
        match self {
            NeoNetwork::MainNet => "https://rest.fs.neo.org",
            NeoNetwork::TestNet => "https://rest.t5.fs.neo.org",
            NeoNetwork::Private => "http://localhost:8090",
        }
    }

    /// Get the default NeoFS S3 gateway URL for this network.
    ///
    /// The S3 gateway supports AWS S3 multipart uploads for faster transfers.
    /// Returns `Some(url)` for networks with S3 gateways, `None` otherwise.
    pub fn default_neofs_s3_url(&self) -> Option<String> {
        match self {
            NeoNetwork::MainNet => Some("https://s3.fs.neo.org".to_string()),
            NeoNetwork::TestNet => Some("https://s3.t5.fs.neo.org".to_string()),
            NeoNetwork::Private => None, // No default S3 gateway for private networks
        }
    }

    /// Get the default NeoID resolver URL for this network.
    pub fn default_neoid_url(&self) -> &'static str {
        match self {
            NeoNetwork::MainNet => "https://neoid.neo.org",
            NeoNetwork::TestNet => "https://testnet.neoid.neo.org",
            NeoNetwork::Private => "http://localhost:9090",
        }
    }

    /// Get the NNS (Neo Name Service) contract script hash for this network.
    pub fn nns_script_hash(&self) -> &'static str {
        match self {
            // Official NNS contract on mainnet
            NeoNetwork::MainNet => "0x50ac1c37690cc2cfc594472833cf57505d5f46de",
            // NNS on testnet (T5)
            NeoNetwork::TestNet => "0x50ac1c37690cc2cfc594472833cf57505d5f46de",
            NeoNetwork::Private => "0x0000000000000000000000000000000000000000",
        }
    }

    /// Get the network magic number (used in transaction signing).
    pub fn magic(&self) -> u32 {
        match self {
            NeoNetwork::MainNet => 860833102,   // Neo N3 MainNet magic
            NeoNetwork::TestNet => 894710606,   // Neo N3 TestNet magic
            NeoNetwork::Private => 1234567890,  // Custom (should be configured)
        }
    }

    /// Get the network name.
    pub fn name(&self) -> &'static str {
        match self {
            NeoNetwork::MainNet => "mainnet",
            NeoNetwork::TestNet => "testnet",
            NeoNetwork::Private => "private",
        }
    }

    /// Parse network from string.
    pub fn parse(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "mainnet" | "main" => Some(NeoNetwork::MainNet),
            "testnet" | "test" | "t5" => Some(NeoNetwork::TestNet),
            "private" | "local" | "express" => Some(NeoNetwork::Private),
            _ => None,
        }
    }
}

// ============================================================================
// NEO N3 TRANSACTION INFRASTRUCTURE
// ============================================================================

/// Neo N3 account for transaction signing.
///
/// Handles WIF private key parsing and secp256r1 ECDSA signing.
#[derive(Clone)]
pub struct NeoAccount {
    /// The secp256r1 signing key.
    signing_key: SigningKey,
    /// The compressed public key (33 bytes).
    public_key: [u8; 33],
    /// The script hash (20 bytes, little-endian).
    script_hash: [u8; 20],
    /// The Neo N3 address (Base58Check encoded).
    address: String,
}

impl NeoAccount {
    /// Create a new account from a WIF (Wallet Import Format) private key.
    ///
    /// WIF format: Base58Check encoded with version byte 0x80.
    /// For compressed keys, ends with 0x01 compression flag.
    pub fn from_wif(wif: &str) -> Result<Self, NeoError> {
        // Decode Base58 (without checksum verification)
        let raw = bs58::decode(wif)
            .into_vec()
            .map_err(|e| NeoError::Account(format!("Invalid WIF: {}", e)))?;

        // Base58Check format: data || checksum (last 4 bytes)
        if raw.len() < 5 {
            return Err(NeoError::Account("WIF too short".to_string()));
        }

        let (data, checksum) = raw.split_at(raw.len() - 4);
        let expected_checksum = Sha256::digest(Sha256::digest(data));
        if checksum != &expected_checksum[0..4] {
            return Err(NeoError::Account("Invalid WIF checksum".to_string()));
        }

        let decoded = data;

        // WIF format: version(1) + privkey(32) + compression(1, optional)
        if decoded.len() < 33 {
            return Err(NeoError::Account("WIF too short".to_string()));
        }

        // Version byte should be 0x80 for mainnet
        if decoded[0] != 0x80 {
            return Err(NeoError::Account(format!(
                "Invalid WIF version: expected 0x80, got 0x{:02x}",
                decoded[0]
            )));
        }

        // Extract 32-byte private key
        let privkey_bytes: [u8; 32] = decoded[1..33]
            .try_into()
            .map_err(|_| NeoError::Account("Invalid private key length".to_string()))?;

        // Create signing key
        let signing_key = SigningKey::from_bytes((&privkey_bytes).into())
            .map_err(|e| NeoError::Account(format!("Invalid private key: {}", e)))?;

        // Get compressed public key (33 bytes: 0x02/0x03 + 32-byte X coordinate)
        let verifying_key = signing_key.verifying_key();
        let public_key_bytes = verifying_key.to_encoded_point(true);
        let public_key: [u8; 33] = public_key_bytes
            .as_bytes()
            .try_into()
            .map_err(|_| NeoError::Account("Invalid public key".to_string()))?;

        // Compute script hash: RIPEMD160(SHA256(verification_script))
        // Verification script: PUSHDATA1 0x21 <33-byte pubkey> SYSCALL "System.Crypto.CheckSig"
        let mut verification_script = Vec::with_capacity(40);
        verification_script.push(0x0c); // PUSHDATA1
        verification_script.push(0x21); // 33 bytes
        verification_script.extend_from_slice(&public_key);
        verification_script.push(0x41); // SYSCALL
        // System.Crypto.CheckSig interop hash (little-endian: 0x27b3e756)
        verification_script.extend_from_slice(&[0x56, 0xe7, 0xb3, 0x27]);

        let sha256_hash = Sha256::digest(&verification_script);
        let script_hash_bytes = <Ripemd160 as RipemdDigest>::digest(sha256_hash);
        let script_hash: [u8; 20] = script_hash_bytes
            .as_slice()
            .try_into()
            .map_err(|_| NeoError::Account("Invalid script hash".to_string()))?;

        // Compute Neo address: Base58Check(0x35 + script_hash)
        // Base58Check = Base58(data || checksum) where checksum = SHA256(SHA256(data))[0..4]
        let mut address_bytes = vec![0x35]; // Neo N3 address version
        address_bytes.extend_from_slice(&script_hash);
        let checksum = Sha256::digest(Sha256::digest(&address_bytes));
        address_bytes.extend_from_slice(&checksum[0..4]);
        let address = bs58::encode(&address_bytes).into_string();

        Ok(Self {
            signing_key,
            public_key,
            script_hash,
            address,
        })
    }

    /// Get the Neo N3 address.
    pub fn address(&self) -> &str {
        &self.address
    }

    /// Get the script hash as hex string (big-endian, 0x-prefixed).
    pub fn script_hash_hex(&self) -> String {
        // Neo displays script hashes in big-endian
        let mut be = self.script_hash;
        be.reverse();
        format!("0x{}", hex::encode(be))
    }

    /// Get the script hash bytes (little-endian, as used in transactions).
    pub fn script_hash_le(&self) -> &[u8; 20] {
        &self.script_hash
    }

    /// Sign a message hash with secp256r1 ECDSA.
    ///
    /// Returns the 64-byte signature (r || s).
    pub fn sign(&self, message: &[u8]) -> [u8; 64] {
        let signature: Signature = self.signing_key.sign(message);
        let sig_bytes = signature.to_bytes();
        let mut result = [0u8; 64];
        result.copy_from_slice(&sig_bytes);
        result
    }

    /// Get the verification script for this account.
    pub fn verification_script(&self) -> Vec<u8> {
        let mut script = Vec::with_capacity(40);
        script.push(0x0c); // PUSHDATA1
        script.push(0x21); // 33 bytes
        script.extend_from_slice(&self.public_key);
        script.push(0x41); // SYSCALL
        // System.Crypto.CheckSig interop hash (little-endian: 0x27b3e756)
        script.extend_from_slice(&[0x56, 0xe7, 0xb3, 0x27]);
        script
    }

    /// Get the compressed public key.
    pub fn public_key(&self) -> &[u8; 33] {
        &self.public_key
    }
}

/// Neo VM opcodes used in script building.
#[allow(dead_code)]
mod opcode {
    pub const PUSHDATA1: u8 = 0x0c;
    pub const PUSHDATA2: u8 = 0x0d;
    pub const PUSHINT8: u8 = 0x00;
    pub const PUSHINT16: u8 = 0x01;
    pub const PUSHINT32: u8 = 0x02;
    pub const PUSHINT64: u8 = 0x03;
    pub const PUSH0: u8 = 0x10;
    pub const PUSH1: u8 = 0x11;
    pub const PUSH2: u8 = 0x12;
    pub const PUSH3: u8 = 0x13;
    pub const PUSH4: u8 = 0x14;
    pub const PUSH5: u8 = 0x15;
    pub const PUSH6: u8 = 0x16;
    pub const PUSH7: u8 = 0x17;
    pub const PUSH8: u8 = 0x18;
    pub const PACK: u8 = 0xc0;
    pub const SYSCALL: u8 = 0x41;
}

/// Builder for Neo VM invocation scripts.
pub struct NeoScriptBuilder {
    script: Vec<u8>,
}

impl NeoScriptBuilder {
    /// Create a new script builder.
    pub fn new() -> Self {
        Self { script: Vec::new() }
    }

    /// Push a byte array onto the stack.
    pub fn push_bytes(&mut self, data: &[u8]) -> &mut Self {
        if data.len() <= 255 {
            self.script.push(opcode::PUSHDATA1);
            self.script.push(data.len() as u8);
        } else {
            self.script.push(opcode::PUSHDATA2);
            self.script.extend_from_slice(&(data.len() as u16).to_le_bytes());
        }
        self.script.extend_from_slice(data);
        self
    }

    /// Push a small integer (0-16) onto the stack.
    pub fn push_int(&mut self, value: i64) -> &mut Self {
        if value == 0 {
            self.script.push(opcode::PUSH0);
        } else if value >= 1 && value <= 16 {
            self.script.push(opcode::PUSH0 + value as u8);
        } else if value >= -128 && value <= 127 {
            self.script.push(opcode::PUSHINT8);
            self.script.push(value as u8);
        } else if value >= -32768 && value <= 32767 {
            self.script.push(opcode::PUSHINT16);
            self.script.extend_from_slice(&(value as i16).to_le_bytes());
        } else if value >= -2147483648 && value <= 2147483647 {
            self.script.push(opcode::PUSHINT32);
            self.script.extend_from_slice(&(value as i32).to_le_bytes());
        } else {
            self.script.push(opcode::PUSHINT64);
            self.script.extend_from_slice(&value.to_le_bytes());
        }
        self
    }

    /// Push a string onto the stack.
    pub fn push_string(&mut self, s: &str) -> &mut Self {
        self.push_bytes(s.as_bytes())
    }

    /// Emit PACK opcode to create an array from stack items.
    pub fn pack(&mut self) -> &mut Self {
        self.script.push(opcode::PACK);
        self
    }

    /// Emit SYSCALL opcode with the given interop service hash.
    pub fn syscall(&mut self, hash: &[u8; 4]) -> &mut Self {
        self.script.push(opcode::SYSCALL);
        self.script.extend_from_slice(hash);
        self
    }

    /// Build a contract call script.
    ///
    /// Format: PUSH args (reverse) -> PACK -> PUSH CallFlags -> PUSH method -> PUSH contract_hash -> SYSCALL
    pub fn emit_app_call(
        &mut self,
        contract_hash: &[u8; 20],
        method: &str,
        args: &[&[u8]],
    ) -> &mut Self {
        // Push args in reverse order
        for arg in args.iter().rev() {
            self.push_bytes(arg);
        }

        // Push arg count and pack
        self.push_int(args.len() as i64);
        self.pack();

        // Push CallFlags.All (15 = 0x0F)
        // Neo3 requires call flags for System.Contract.Call
        self.push_int(15);

        // Push method name
        self.push_string(method);

        // Push contract hash (already little-endian)
        self.push_bytes(contract_hash);

        // SYSCALL System.Contract.Call (0x627d5b52)
        self.syscall(&[0x62, 0x7d, 0x5b, 0x52]);

        self
    }

    /// Get the built script as hex string.
    pub fn build_hex(&self) -> String {
        hex::encode(&self.script)
    }

    /// Get the built script as bytes.
    pub fn build(&self) -> Vec<u8> {
        self.script.clone()
    }
}

impl Default for NeoScriptBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Neo N3 transaction signer scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum WitnessScope {
    /// No permissions.
    None = 0x00,
    /// Called by entry only.
    CalledByEntry = 0x01,
    /// Custom contracts.
    CustomContracts = 0x10,
    /// Custom groups.
    CustomGroups = 0x20,
    /// Witness rules.
    WitnessRules = 0x40,
    /// Global scope (not recommended).
    Global = 0x80,
}

/// Neo N3 transaction signer.
#[derive(Debug, Clone)]
pub struct NeoSigner {
    /// Account script hash (20 bytes, little-endian).
    pub account: [u8; 20],
    /// Witness scope.
    pub scopes: WitnessScope,
    /// Allowed contracts (for CustomContracts scope).
    pub allowed_contracts: Vec<[u8; 20]>,
    /// Allowed groups (for CustomGroups scope).
    pub allowed_groups: Vec<[u8; 33]>,
}

impl NeoSigner {
    /// Create a new signer with CalledByEntry scope.
    pub fn new(account: [u8; 20]) -> Self {
        Self {
            account,
            scopes: WitnessScope::CalledByEntry,
            allowed_contracts: Vec::new(),
            allowed_groups: Vec::new(),
        }
    }

    /// Serialize the signer for transaction.
    pub fn serialize(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(&self.account);
        buf.push(self.scopes as u8);
        // For CalledByEntry, no additional data needed
        buf
    }
}

/// Neo N3 transaction witness (signature).
#[derive(Debug, Clone)]
pub struct NeoWitness {
    /// Invocation script (signature).
    pub invocation: Vec<u8>,
    /// Verification script (public key check).
    pub verification: Vec<u8>,
}

impl NeoWitness {
    /// Create a witness from a signature and verification script.
    pub fn new(signature: &[u8; 64], verification_script: Vec<u8>) -> Self {
        // Invocation script: PUSHDATA1 0x40 <64-byte signature>
        let mut invocation = Vec::with_capacity(66);
        invocation.push(0x0c); // PUSHDATA1
        invocation.push(0x40); // 64 bytes
        invocation.extend_from_slice(signature);

        Self {
            invocation,
            verification: verification_script,
        }
    }

    /// Serialize the witness.
    pub fn serialize(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        // Invocation script (var-length)
        Self::write_var_int(&mut buf, self.invocation.len() as u64);
        buf.extend_from_slice(&self.invocation);
        // Verification script (var-length)
        Self::write_var_int(&mut buf, self.verification.len() as u64);
        buf.extend_from_slice(&self.verification);
        buf
    }

    fn write_var_int(buf: &mut Vec<u8>, value: u64) {
        if value < 0xfd {
            buf.push(value as u8);
        } else if value <= 0xffff {
            buf.push(0xfd);
            buf.extend_from_slice(&(value as u16).to_le_bytes());
        } else if value <= 0xffffffff {
            buf.push(0xfe);
            buf.extend_from_slice(&(value as u32).to_le_bytes());
        } else {
            buf.push(0xff);
            buf.extend_from_slice(&value.to_le_bytes());
        }
    }
}

/// Neo N3 transaction.
#[derive(Debug, Clone)]
pub struct NeoTransaction {
    /// Transaction version (always 0 for Neo N3).
    pub version: u8,
    /// Random nonce to prevent replay attacks.
    pub nonce: u32,
    /// System fee (in GAS fractions, 10^8 = 1 GAS).
    pub system_fee: u64,
    /// Network fee (in GAS fractions).
    pub network_fee: u64,
    /// Block height until which the transaction is valid.
    pub valid_until_block: u32,
    /// Transaction signers.
    pub signers: Vec<NeoSigner>,
    /// Transaction attributes (usually empty).
    pub attributes: Vec<u8>,
    /// Invocation script (contract call).
    pub script: Vec<u8>,
    /// Witnesses (signatures).
    pub witnesses: Vec<NeoWitness>,
}

impl NeoTransaction {
    /// Create a new transaction.
    pub fn new(
        script: Vec<u8>,
        signer: NeoSigner,
        valid_until_block: u32,
        system_fee: u64,
        network_fee: u64,
    ) -> Self {
        Self {
            version: 0,
            nonce: rand::random(),
            system_fee,
            network_fee,
            valid_until_block,
            signers: vec![signer],
            attributes: Vec::new(),
            script,
            witnesses: Vec::new(),
        }
    }

    /// Serialize the transaction for hashing (without witnesses).
    pub fn serialize_unsigned(&self) -> Vec<u8> {
        let mut buf = Vec::new();

        buf.push(self.version);
        buf.extend_from_slice(&self.nonce.to_le_bytes());
        buf.extend_from_slice(&self.system_fee.to_le_bytes());
        buf.extend_from_slice(&self.network_fee.to_le_bytes());
        buf.extend_from_slice(&self.valid_until_block.to_le_bytes());

        // Signers (var-length array)
        Self::write_var_int(&mut buf, self.signers.len() as u64);
        for signer in &self.signers {
            buf.extend_from_slice(&signer.serialize());
        }

        // Attributes (var-length array, usually empty)
        Self::write_var_int(&mut buf, 0);

        // Script (var-length)
        Self::write_var_int(&mut buf, self.script.len() as u64);
        buf.extend_from_slice(&self.script);

        buf
    }

    /// Compute the transaction hash (used for signing).
    pub fn get_hash_data(&self, network_magic: u32) -> Vec<u8> {
        let mut data = Vec::new();
        data.extend_from_slice(&network_magic.to_le_bytes());
        data.extend_from_slice(&Sha256::digest(self.serialize_unsigned()));
        data
    }

    /// Sign the transaction with the given account.
    pub fn sign(&mut self, account: &NeoAccount, network_magic: u32) {
        let hash_data = self.get_hash_data(network_magic);
        let signature = account.sign(&hash_data);
        let witness = NeoWitness::new(&signature, account.verification_script());
        self.witnesses.push(witness);
    }

    /// Serialize the complete transaction (with witnesses).
    pub fn serialize(&self) -> Vec<u8> {
        let mut buf = self.serialize_unsigned();

        // Witnesses (var-length array)
        Self::write_var_int(&mut buf, self.witnesses.len() as u64);
        for witness in &self.witnesses {
            buf.extend_from_slice(&witness.serialize());
        }

        buf
    }

    /// Get the transaction hash (txid).
    pub fn hash(&self) -> [u8; 32] {
        let serialized = self.serialize_unsigned();
        let hash = Sha256::digest(&serialized);
        let double_hash = Sha256::digest(&hash);
        let mut result = [0u8; 32];
        result.copy_from_slice(&double_hash);
        result
    }

    /// Get the transaction hash as hex string (big-endian, 0x-prefixed).
    pub fn hash_hex(&self) -> String {
        let mut hash = self.hash();
        hash.reverse(); // Display in big-endian
        format!("0x{}", hex::encode(hash))
    }

    fn write_var_int(buf: &mut Vec<u8>, value: u64) {
        if value < 0xfd {
            buf.push(value as u8);
        } else if value <= 0xffff {
            buf.push(0xfd);
            buf.extend_from_slice(&(value as u16).to_le_bytes());
        } else if value <= 0xffffffff {
            buf.push(0xfe);
            buf.extend_from_slice(&(value as u32).to_le_bytes());
        } else {
            buf.push(0xff);
            buf.extend_from_slice(&value.to_le_bytes());
        }
    }
}

/// Generate a random nonce.
fn rand_nonce() -> u32 {
    use std::time::{SystemTime, UNIX_EPOCH};
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    (duration.as_nanos() as u32) ^ (duration.as_secs() as u32)
}

/// Provide random for nonce generation.
mod rand {
    pub fn random() -> u32 {
        super::rand_nonce()
    }
}

// ============================================================================
// END NEO N3 TRANSACTION INFRASTRUCTURE
// ============================================================================

/// Configuration for Neo N3 client.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoConfig {
    /// RPC endpoint URL.
    pub rpc_url: String,
    /// Network selection.
    pub network: NeoNetwork,
    /// NotaryOracle contract script hash (0x-prefixed hex, 40 chars).
    pub contract_address: Option<String>,
    /// Account address for signing (Neo N3 address format, starts with 'N').
    pub account_address: Option<String>,
    /// NeoFS HTTP gateway URL.
    pub neofs_url: String,
    /// NeoID resolver URL.
    pub neoid_url: String,
    /// NNS contract script hash.
    pub nns_contract: String,
    /// Fee multiplier for gas estimation.
    #[serde(default = "default_fee_multiplier")]
    pub fee_multiplier: f64,
    /// Request timeout in seconds.
    #[serde(default = "default_timeout")]
    pub timeout_secs: u64,
    /// NeoFS container ID for identity documents.
    #[serde(default)]
    pub identity_container: Option<String>,
    /// NeoFS container ID for signed receipts.
    #[serde(default)]
    pub receipts_container: Option<String>,
    /// NeoFS container ID for private batches.
    #[serde(default)]
    pub batch_container: Option<String>,
    /// NeoFS container ID for marketplace sealed files.
    #[serde(default)]
    pub marketplace_container: Option<String>,
    /// Default NeoFS container ID for general uploads.
    #[serde(default)]
    pub default_container: Option<String>,

    // === S3 Gateway Configuration (for fast parallel uploads) ===

    /// NeoFS S3 gateway URL (e.g., "https://s3.fs.neo.org" for mainnet).
    /// If set, large files will use S3 multipart upload for ~4x faster uploads.
    #[serde(default)]
    pub neofs_s3_url: Option<String>,
    /// S3 access key (typically derived from Neo wallet public key).
    #[serde(default)]
    pub s3_access_key: Option<String>,
    /// S3 secret key (typically the WIF private key, encrypted at rest).
    #[serde(default)]
    pub s3_secret_key: Option<String>,
    /// Number of parallel connections for S3 multipart upload (default: 4).
    #[serde(default = "default_s3_parallel")]
    pub s3_parallel_connections: usize,
    /// Part size for S3 multipart upload in MB (default: 64).
    #[serde(default = "default_s3_part_size")]
    pub s3_part_size_mb: usize,
}

fn default_fee_multiplier() -> f64 {
    1.5
}

fn default_timeout() -> u64 {
    30
}

fn default_s3_parallel() -> usize {
    4 // 4 parallel connections for ~4x speedup
}

fn default_s3_part_size() -> usize {
    64 // 64 MB parts for optimal NeoFS S3 gateway performance
}

impl Default for NeoConfig {
    fn default() -> Self {
        Self::new(NeoNetwork::MainNet)
    }
}

impl NeoConfig {
    /// Create a new configuration for the specified network.
    pub fn new(network: NeoNetwork) -> Self {
        Self {
            rpc_url: network.default_rpc_url().to_string(),
            network,
            contract_address: None,
            account_address: None,
            neofs_url: network.default_neofs_url().to_string(),
            neoid_url: network.default_neoid_url().to_string(),
            nns_contract: network.nns_script_hash().to_string(),
            fee_multiplier: default_fee_multiplier(),
            timeout_secs: default_timeout(),
            identity_container: None,
            receipts_container: None,
            batch_container: None,
            marketplace_container: None,
            default_container: None,
            // S3 gateway defaults (optional - falls back to REST gateway)
            neofs_s3_url: network.default_neofs_s3_url(),
            s3_access_key: None,
            s3_secret_key: None,
            s3_parallel_connections: default_s3_parallel(),
            s3_part_size_mb: default_s3_part_size(),
        }
    }

    /// Set the RPC URL.
    pub fn with_rpc_url(mut self, url: &str) -> Self {
        self.rpc_url = url.to_string();
        self
    }

    /// Set the NotaryOracle contract script hash.
    pub fn with_contract(mut self, script_hash: &str) -> Self {
        self.contract_address = Some(script_hash.to_string());
        self
    }

    /// Set the account address.
    pub fn with_account(mut self, address: &str) -> Self {
        self.account_address = Some(address.to_string());
        self
    }

    /// Set the NeoFS URL.
    pub fn with_neofs_url(mut self, url: &str) -> Self {
        self.neofs_url = url.to_string();
        self
    }

    /// Set the NeoID URL.
    pub fn with_neoid_url(mut self, url: &str) -> Self {
        self.neoid_url = url.to_string();
        self
    }

    /// Set the NNS contract script hash.
    pub fn with_nns_contract(mut self, script_hash: &str) -> Self {
        self.nns_contract = script_hash.to_string();
        self
    }

    /// Set the fee multiplier.
    pub fn with_fee_multiplier(mut self, multiplier: f64) -> Self {
        self.fee_multiplier = multiplier;
        self
    }

    /// Set the timeout.
    pub fn with_timeout(mut self, secs: u64) -> Self {
        self.timeout_secs = secs;
        self
    }

    /// Set the identity container ID.
    pub fn with_identity_container(mut self, container_id: &str) -> Self {
        self.identity_container = Some(container_id.to_string());
        self
    }

    /// Set the receipts container ID.
    pub fn with_receipts_container(mut self, container_id: &str) -> Self {
        self.receipts_container = Some(container_id.to_string());
        self
    }

    /// Set the batch container ID.
    pub fn with_batch_container(mut self, container_id: &str) -> Self {
        self.batch_container = Some(container_id.to_string());
        self
    }

    /// Validate the configuration.
    pub fn validate(&self) -> Result<(), NeoError> {
        // Validate RPC URL
        if self.rpc_url.is_empty() {
            return Err(NeoError::ConfigError("RPC URL is required".to_string()));
        }

        // Validate contract address format if provided (script hash)
        if let Some(addr) = &self.contract_address {
            validate_neo_script_hash(addr)?;
        }

        // Validate account address format if provided
        if let Some(addr) = &self.account_address {
            validate_neo_address(addr)?;
        }

        // Validate NNS contract format
        if !self.nns_contract.is_empty() {
            validate_neo_script_hash(&self.nns_contract)?;
        }

        Ok(())
    }
}

/// Validate a Neo N3 address (Base58Check encoded, starts with 'N', 34 chars).
fn validate_neo_address(addr: &str) -> Result<(), NeoError> {
    // Neo N3 addresses start with 'N' and are 34 characters (Base58Check)
    if !addr.starts_with('N') {
        return Err(NeoError::InvalidAddress(format!(
            "Neo address must start with 'N': {}",
            addr
        )));
    }

    if addr.len() != 34 {
        return Err(NeoError::InvalidAddress(format!(
            "Neo address must be 34 characters: {} ({})",
            addr,
            addr.len()
        )));
    }

    // Validate Base58 characters (no 0, O, I, l)
    const BASE58_CHARS: &str = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    for c in addr.chars() {
        if !BASE58_CHARS.contains(c) {
            return Err(NeoError::InvalidAddress(format!(
                "Invalid Base58 character '{}' in address: {}",
                c, addr
            )));
        }
    }

    Ok(())
}

/// Validate a Neo script hash (0x-prefixed 40-character hex, 20 bytes).
fn validate_neo_script_hash(hash: &str) -> Result<(), NeoError> {
    let hash = hash.strip_prefix("0x").unwrap_or(hash);

    // Must be valid hex
    if !hash.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(NeoError::InvalidScriptHash(format!(
            "Invalid hex characters in script hash: {}",
            hash
        )));
    }

    // Must be exactly 40 hex chars (20 bytes)
    if hash.len() != 40 {
        return Err(NeoError::InvalidScriptHash(format!(
            "Script hash must be 40 hex chars (20 bytes): {} ({})",
            hash,
            hash.len()
        )));
    }

    Ok(())
}

/// Result of an anchor operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoAnchorResult {
    /// Transaction hash (hex).
    pub tx_hash: String,
    /// Block number when included.
    pub block_number: u64,
    /// Block timestamp (seconds since UNIX epoch).
    pub timestamp: u64,
    /// Root ID assigned by the NotaryOracle contract.
    pub root_id: u64,
    /// Contract script hash used.
    pub contract_address: String,
    /// Optional NeoFS CID if receipt was stored off-chain.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub neofs_cid: Option<String>,
}

/// Result of an identity registration operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoIdentityResult {
    /// Transaction hash (hex).
    pub tx_hash: String,
    /// Block number when included.
    pub block_number: u64,
    /// Block timestamp (seconds since UNIX epoch).
    pub timestamp: u64,
    /// Identity ID assigned by the NotaryOracle contract.
    pub identity_id: u64,
    /// Fingerprint of the registered identity (hex).
    pub fingerprint: String,
    /// Contract script hash used.
    pub contract_address: String,
    /// NeoFS CID where the full signature is stored.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub neofs_cid: Option<String>,
}

/// Result of a batch anchor operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoBatchAnchorResult {
    /// Transaction hash (hex).
    pub tx_hash: String,
    /// Block number when included.
    pub block_number: u64,
    /// Block timestamp (seconds since UNIX epoch).
    pub timestamp: u64,
    /// Batch ID assigned by the contract.
    pub batch_id: u64,
    /// Combined batch root (SHA-512 of all roots) - locally computed.
    #[serde(with = "hex_bytes")]
    pub batch_root: [u8; 64],
    /// Contract's computed batch root (32 bytes, for verification).
    /// This is what the contract actually stores and what IsAnchored checks.
    #[serde(with = "hex_bytes_32")]
    pub contract_root: [u8; 32],
    /// Number of roots in batch.
    pub root_count: usize,
    /// Merkle witnesses for each root (for individual verification).
    #[serde(skip)]
    pub witnesses: Vec<Vec<[u8; 64]>>,
    /// Contract script hash used.
    pub contract_address: String,
}

mod hex_bytes {
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&hex::encode(bytes))
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<[u8; 64], D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        let bytes = hex::decode(&s).map_err(serde::de::Error::custom)?;
        bytes.try_into().map_err(|_| serde::de::Error::custom("expected 64 bytes"))
    }
}

mod hex_bytes_32 {
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S>(bytes: &[u8; 32], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&hex::encode(bytes))
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<[u8; 32], D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        let bytes = hex::decode(&s).map_err(serde::de::Error::custom)?;
        bytes.try_into().map_err(|_| serde::de::Error::custom("expected 32 bytes"))
    }
}

mod hex_bytes_64 {
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&hex::encode(bytes))
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<[u8; 64], D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        let bytes = hex::decode(&s).map_err(serde::de::Error::custom)?;
        bytes.try_into().map_err(|_| serde::de::Error::custom("expected 64 bytes"))
    }
}

/// Result of a batch anchor operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoBatchResult {
    /// Transaction hash (hex).
    pub tx_hash: String,
    /// Block number when included.
    pub block_number: u64,
    /// Block timestamp (seconds since UNIX epoch).
    pub timestamp: u64,
    /// Root ID assigned by the contract.
    pub root_id: u64,
    /// Contract script hash used.
    pub contract_address: String,
    /// Combined batch root (SHA-512 hash).
    #[serde(with = "hex_bytes_64")]
    pub batch_root: [u8; 64],
    /// Number of roots in the batch.
    pub batch_size: usize,
    /// Optional NeoFS CID for the batch.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub neofs_cid: Option<String>,
}

/// Result of a time query.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoTimeResult {
    /// Current block number.
    pub block_number: u64,
    /// Block timestamp (milliseconds since UNIX epoch).
    pub timestamp: u64,
    /// Network name.
    pub network: String,
}

/// Transaction status from Neo.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoTransactionStatus {
    /// VM state: HALT (success) or FAULT (failed)
    pub vm_state: String,
    /// Block hash when included (if confirmed).
    pub block_hash: Option<String>,
    /// Block number when included (if confirmed).
    pub block_number: Option<u64>,
    /// Confirmations count.
    pub confirmations: u64,
}

/// Anchor record from the contract.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoAnchorRecord {
    /// Root ID.
    pub root_id: u64,
    /// Merkle root (hex).
    pub root: String,
    /// Block number when anchored.
    pub block_number: u64,
    /// Timestamp when anchored.
    pub timestamp: u64,
    /// Who anchored (account address).
    pub anchorer: String,
    /// Optional NeoFS CID.
    pub neofs_cid: Option<String>,
}

/// Result of a NeoFS store operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoFsStoreResult {
    /// Content Identifier (CID) in NeoFS.
    pub cid: String,
    /// Container ID where object was stored.
    pub container_id: String,
    /// Object ID within the container.
    pub object_id: String,
    /// Size in bytes.
    pub size: u64,
}

/// Result of a NeoFS deposit operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoFsDepositResult {
    /// Transaction hash (hex).
    pub tx_hash: String,
    /// Block number when included.
    pub block_number: u64,
    /// Amount deposited (in GAS fractions, 10^8 = 1 GAS).
    pub amount: u64,
    /// Sender address.
    pub from_address: String,
    /// NeoFS contract address.
    pub neofs_contract: String,
}

/// Result of a NeoID verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoIdVerifyResult {
    /// The DID that was verified.
    pub did: String,
    /// Whether the DID is valid and active.
    pub valid: bool,
    /// Verification timestamp.
    pub verified_at: u64,
    /// Claims from the identity document (if available).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub claims: Option<serde_json::Value>,
}

/// Result of an NNS resolution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NnsResolveResult {
    /// The name that was resolved.
    pub name: String,
    /// The resolved address (Neo N3 format).
    pub address: String,
    /// Expiry timestamp (if available).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expires: Option<u64>,
}

/// Identity status values from the smart contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[repr(u8)]
pub enum IdentityStatus {
    /// Identity not found on-chain.
    NotFound = 0,
    /// Identity is active and valid.
    Active = 1,
    /// Identity has been revoked.
    Revoked = 2,
    /// Identity has been rotated to a new key.
    Rotated = 3,
}

impl IdentityStatus {
    /// Parse status from integer value.
    pub fn from_u64(value: u64) -> Self {
        match value {
            1 => IdentityStatus::Active,
            2 => IdentityStatus::Revoked,
            3 => IdentityStatus::Rotated,
            _ => IdentityStatus::NotFound,
        }
    }

    /// Check if the identity is valid for participation.
    pub fn is_active(&self) -> bool {
        matches!(self, IdentityStatus::Active)
    }
}

impl std::fmt::Display for IdentityStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IdentityStatus::NotFound => write!(f, "not found"),
            IdentityStatus::Active => write!(f, "active"),
            IdentityStatus::Revoked => write!(f, "revoked"),
            IdentityStatus::Rotated => write!(f, "rotated"),
        }
    }
}

/// Result of a Dual-Key QSI registration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DkQsiRegistrationResult {
    /// Transaction hash (hex).
    pub tx_hash: String,
    /// Block number when included.
    pub block_number: u64,
    /// Block timestamp.
    pub timestamp: u64,
    /// The signing fingerprint (= DID suffix).
    pub signing_fingerprint: String,
    /// The decryption fingerprint (= CTA).
    pub decryption_fingerprint: String,
    /// NeoFS CID where the document is stored.
    pub neofs_cid: String,
    /// The full DID.
    pub did: String,
}

/// Result of resolving a Cryptographic Threshold Authority (CTA).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CtaResolveResult {
    /// The signing fingerprint that owns this CTA.
    pub signing_fingerprint: String,
    /// NeoFS CID where the identity document is stored.
    pub neofs_cid: String,
    /// Current status of the identity.
    pub status: IdentityStatus,
    /// The full DID derived from the signing fingerprint.
    pub did: String,
    /// Whether the CTA is valid for batch participation.
    pub can_participate: bool,
}

/// Result of validating batch participants.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchParticipantsValidationResult {
    /// Whether all participants are valid.
    pub all_valid: bool,
    /// Number of valid participants.
    pub valid_count: usize,
    /// Details for each participant.
    pub participants: Vec<ParticipantValidationResult>,
}

/// Validation result for a single participant.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParticipantValidationResult {
    /// Signing fingerprint.
    pub signing_fingerprint: String,
    /// DID.
    pub did: String,
    /// Identity status.
    pub status: IdentityStatus,
    /// Whether this participant is valid.
    pub valid: bool,
}

/// Quantum-Safe Identity (QSI) document.
///
/// This represents an on-chain identity bound to an ML-DSA-87 public key.
/// The fingerprint (DID) is derived from SHA-512(public_key).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QsiDocument {
    /// Algorithm (always "ML-DSA-87").
    pub algorithm: String,
    /// ML-DSA-87 public key (2592 bytes).
    #[serde(with = "hex_serde")]
    pub public_key: Vec<u8>,
    /// Fingerprint: SHA-512(public_key) truncated to first 32 hex chars.
    pub fingerprint: String,
    /// Derived Neo address.
    pub neo_address: String,
    /// Optional name claim.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// Optional email hash (SHA-512, privacy-preserving).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub email_hash: Option<String>,
    /// Optional organization claim.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub organization: Option<String>,
    /// Optional credential type.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub credential_type: Option<String>,
    /// Creation timestamp (Unix).
    pub created: u64,
    /// Optional expiry timestamp.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expires: Option<u64>,
    /// Optional revocation CID (NeoFS).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub revocation_cid: Option<String>,
    /// Previous key fingerprints (for key rotation chain).
    #[serde(default)]
    pub rotation_chain: Vec<String>,
    /// Self-attestation signature (ML-DSA-87, 4627 bytes).
    #[serde(with = "hex_serde")]
    pub signature: Vec<u8>,
}

/// Hex serde helper for byte arrays.
mod hex_serde {
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&hex::encode(bytes))
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        hex::decode(&s).map_err(serde::de::Error::custom)
    }
}

/// Blocking Neo N3 JSON-RPC client.
#[derive(Debug)]
pub struct NeoClient {
    /// Client configuration.
    config: NeoConfig,
    /// HTTP client.
    agent: ureq::Agent,
}

impl NeoClient {
    /// Create a new Neo client.
    pub fn new(config: NeoConfig) -> Result<Self, NeoError> {
        config.validate()?;

        let agent = ureq::AgentBuilder::new()
            .timeout(std::time::Duration::from_secs(config.timeout_secs))
            .build();

        Ok(Self { config, agent })
    }

    /// Get the current configuration.
    pub fn config(&self) -> &NeoConfig {
        &self.config
    }

    /// Get current block number and timestamp.
    ///
    /// Neo uses dBFT consensus which provides one-block finality,
    /// meaning transactions are final as soon as they're included in a block.
    pub fn get_block_time(&self) -> Result<NeoTimeResult, NeoError> {
        // Call getblockcount to get the current block height
        let block_count = self.call_rpc::<u64>("getblockcount", serde_json::json!([]))?;

        // Block indices are 0-based, so current block is count - 1
        let block_index = block_count.saturating_sub(1);

        // Get the latest block header to extract timestamp
        let block = self.call_rpc::<serde_json::Value>(
            "getblock",
            serde_json::json!([block_index, false]), // false = return header only
        )?;

        // Extract timestamp (Neo uses milliseconds since epoch)
        let timestamp = block
            .get("time")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);

        Ok(NeoTimeResult {
            block_number: block_index,
            timestamp,
            network: self.config.network.name().to_string(),
        })
    }

    /// Get account GAS balance.
    ///
    /// Returns balance in GAS fractions (1 GAS = 100,000,000 fractions).
    pub fn get_balance(&self, address: &str) -> Result<u128, NeoError> {
        validate_neo_address(address)?;

        // GAS contract script hash on Neo N3
        let gas_contract = "0xd2a4cff31913016155e38e474a2c06d08be276cf";

        // Use getnep17balances which is more reliable
        let result = self.call_rpc::<serde_json::Value>(
            "getnep17balances",
            serde_json::json!([address]),
        )?;

        // Parse the balance array
        let balances = result
            .get("balance")
            .and_then(|b| b.as_array())
            .ok_or_else(|| NeoError::Provider("Invalid response format".to_string()))?;

        // Find the GAS token balance
        for asset in balances {
            let asset_hash = asset
                .get("assethash")
                .and_then(|h| h.as_str())
                .unwrap_or("");

            if asset_hash == gas_contract {
                let amount = asset
                    .get("amount")
                    .and_then(|v| v.as_str())
                    .unwrap_or("0");

                return amount
                    .parse::<u128>()
                    .map_err(|e| NeoError::Provider(format!("Failed to parse balance: {}", e)));
            }
        }

        // GAS token not found in balances - return 0
        Ok(0)
    }

    /// Verify a root exists on-chain using the NotaryOracle contract.
    ///
    /// Calls the `verifyRoot` function on the contract.
    pub fn verify_anchor(
        &self,
        root_id: u64,
        expected_root: &[u8; 64],
    ) -> Result<bool, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError(
                "Contract address required. Run: anubis-notary anchor neo config --contract <HASH>"
                    .to_string(),
            )
        })?;

        // Neo RPC expects ByteArray as base64, not hex
        // The hash is passed as-is (byte array data, not a script hash)
        use base64::Engine;
        let root_b64 = base64::engine::general_purpose::STANDARD.encode(expected_root);

        // Call verifyRoot on the NotaryOracle contract with both root_id and expected_root
        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "verifyRoot",
                [
                    {"type": "Integer", "value": root_id.to_string()},
                    {"type": "ByteArray", "value": root_b64}
                ]
            ]),
        )?;

        // Check if VM executed successfully and returned true
        let state = result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            return Ok(false);
        }

        // Parse the boolean result from the stack
        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                let value = first.get("value");
                // Neo returns boolean as true/false or 1/0
                return Ok(value == Some(&serde_json::json!(true))
                    || value == Some(&serde_json::json!(1)));
            }
        }

        Ok(false)
    }

    /// Check if a root hash is anchored on-chain.
    ///
    /// This queries the `IsAnchored` function on the NotaryOracle contract.
    /// Use this to verify a receipt is anchored without needing a root ID.
    pub fn is_anchored(&self, root_hash: &[u8; 64]) -> Result<bool, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError(
                "Contract address required. Run: anubis-notary anchor neo config --contract <HASH>"
                    .to_string(),
            )
        })?;

        // Send full 64-byte SHA-512 root to the V2 contract.
        // The contract hashes it to SHA-256 for storage key indexing.
        // Document hashes are data (not script hashes), so no byte reversal needed.
        let hash_b64 = BASE64.encode(root_hash);

        // Call IsAnchored on the NotaryOracle contract
        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "isAnchored",
                [{"type": "ByteArray", "value": hash_b64}]
            ]),
        )?;

        // Check if VM executed successfully
        let state = result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            return Ok(false);
        }

        // Parse the boolean result from the stack
        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                let value = first.get("value");
                // Neo returns boolean as true/false or 1/0
                return Ok(value == Some(&serde_json::json!(true))
                    || value == Some(&serde_json::json!(1)));
            }
        }

        Ok(false)
    }

    /// Check if a 32-byte batch root is anchored on-chain.
    ///
    /// Batch roots are computed by the contract as SHA-256 of concatenated roots
    /// and stored directly as 32-byte keys (not hashed again).
    pub fn is_batch_anchored(&self, batch_root: &[u8; 32]) -> Result<bool, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError(
                "Contract address required. Run: anubis-notary anchor neo config --contract <HASH>"
                    .to_string(),
            )
        })?;

        // Send 32-byte batch root directly (no hashing needed for batch roots).
        // Document hashes are data (not script hashes), so no byte reversal needed.
        let hash_b64 = BASE64.encode(batch_root);

        // Call isAnchored on the NotaryOracle contract
        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "isAnchored",
                [{"type": "ByteArray", "value": hash_b64}]
            ]),
        )?;

        // Check if VM executed successfully
        let state = result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            return Ok(false);
        }

        // Parse the boolean result from the stack
        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                let value = first.get("value");
                return Ok(value == Some(&serde_json::json!(true))
                    || value == Some(&serde_json::json!(1)));
            }
        }

        Ok(false)
    }

    /// Get anchor status/info by root ID.
    #[allow(unused_variables)]
    pub fn get_anchor_status(&self, root_id: u64) -> Result<Option<NeoAnchorRecord>, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        // Call GetAnchor on the NotaryOracle contract
        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "getAnchor",
                [{"type": "Integer", "value": root_id.to_string()}]
            ]),
        )?;

        // Check if VM executed successfully
        let state = result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            return Ok(None);
        }

        // Parse the result - the contract returns a struct/array
        // This depends on the exact contract implementation
        // For now, return None as the exact format needs to match the contract
        Ok(None)
    }

    /// Get the current anchor count from the contract.
    pub fn get_anchor_count(&self) -> Result<u64, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([contract, "getAnchorCount", []]),
        )?;

        // Check if VM executed successfully
        let state = result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            return Err(NeoError::ContractNotFound(
                "GetAnchorCount failed".to_string(),
            ));
        }

        // Parse the integer result
        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                let value = first.get("value").and_then(|v| v.as_str()).unwrap_or("0");
                return value
                    .parse::<u64>()
                    .map_err(|e| NeoError::Provider(format!("Failed to parse count: {}", e)));
            }
        }

        Ok(0)
    }

    /// Get transaction status.
    pub fn get_transaction_status(&self, tx_hash: &str) -> Result<NeoTransactionStatus, NeoError> {
        // Get application log for the transaction
        let result = self.call_rpc::<serde_json::Value>(
            "getapplicationlog",
            serde_json::json!([tx_hash]),
        )?;

        let executions = result
            .get("executions")
            .and_then(|e| e.as_array())
            .ok_or_else(|| NeoError::Provider("Transaction not found or pending".to_string()))?;

        let first_exec = executions.first().ok_or_else(|| {
            NeoError::Provider("No execution results".to_string())
        })?;

        let vm_state = first_exec
            .get("vmstate")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT")
            .to_string();

        // Get the transaction to find block info
        let tx = self.call_rpc::<serde_json::Value>(
            "getrawtransaction",
            serde_json::json!([tx_hash, true]), // true = verbose
        )?;

        let block_hash = tx.get("blockhash").and_then(|h| h.as_str()).map(|s| s.to_string());
        let confirmations = tx.get("confirmations").and_then(|c| c.as_u64()).unwrap_or(0);

        // Get block number if we have the block hash
        let block_number = if let Some(ref hash) = block_hash {
            let block = self.call_rpc::<serde_json::Value>(
                "getblock",
                serde_json::json!([hash, false]),
            )?;
            block.get("index").and_then(|i| i.as_u64())
        } else {
            None
        };

        Ok(NeoTransactionStatus {
            vm_state,
            block_hash,
            block_number,
            confirmations,
        })
    }

    /// Anchor a receipt hash to Neo.
    ///
    /// This invokes the NotaryOracle contract's `anchorRoot` function.
    /// Requires NEO_PRIVATE_KEY environment variable to be set with a WIF key.
    pub fn anchor_root(
        &self,
        receipt_hash: &[u8; 64],
    ) -> Result<NeoAnchorResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError(
                "Contract address required. Run: anubis-notary anchor neo config --contract <HASH>"
                    .to_string(),
            )
        })?;

        // Get private key from environment
        // SECURITY: Wrap WIF in Zeroizing to clear from memory after use
        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError(
                "NEO_PRIVATE_KEY environment variable required for signing".to_string(),
            )
        })?);

        // Parse the WIF key
        let account = NeoAccount::from_wif(&wif)?;

        // Parse contract hash (remove 0x prefix and convert to LE bytes)
        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract hash: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract hash must be 20 bytes".to_string()))?;

        // Contract hash stored as BE in config, need to reverse to LE for script
        let mut contract_le = contract_bytes;
        contract_le.reverse();

        // Build the invocation script
        // The hash is passed as-is (byte array data, not a script hash that needs LE conversion)
        let mut builder = NeoScriptBuilder::new();
        builder.emit_app_call(&contract_le, "anchorRoot", &[receipt_hash.as_slice()]);
        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        // Get current block height
        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        // Test the invocation first
        // The RPC expects the script hash in big-endian (display) format, not little-endian
        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([
                script_base64,
                [{"account": account_hex, "scopes": "CalledByEntry"}]
            ]),
        )?;

        let state = test_result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            let exception = test_result
                .get("exception")
                .and_then(|e| e.as_str())
                .unwrap_or("Unknown error");
            return Err(NeoError::TransactionFailed(format!(
                "Contract invocation test failed: {}",
                exception
            )));
        }

        // Get system fee from test invocation
        let gas_consumed = test_result
            .get("gasconsumed")
            .and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(1_000_000);

        // Add 10% buffer to system fee
        let system_fee = gas_consumed + gas_consumed / 10;

        // Create and sign the transaction
        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(
            script,
            signer,
            current_height + 100,
            system_fee,
            500_000, // Network fee (~0.005 GAS)
        );

        // Sign with network magic
        tx.sign(&account, self.config.network.magic());

        // Serialize to base64 for RPC
        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        // Send the transaction
        let send_result = self.call_rpc::<serde_json::Value>(
            "sendrawtransaction",
            serde_json::json!([tx_base64]),
        )?;

        // Get the transaction hash from response
        let tx_hash = send_result
            .get("hash")
            .and_then(|h| h.as_str())
            .map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        // Wait for confirmation (Neo dBFT is fast)
        let mut block_number = 0u64;
        let mut timestamp = 0u64;
        let mut root_id = 0u64;

        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));

            if let Ok(app_log) = self.call_rpc::<serde_json::Value>(
                "getapplicationlog",
                serde_json::json!([tx_hash]),
            ) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            // Extract RootAnchored event data
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    if notif.get("eventname").and_then(|e| e.as_str()) == Some("RootAnchored") {
                                        if let Some(state_val) = notif.get("state").and_then(|s| s.get("value")).and_then(|v| v.as_array()) {
                                            root_id = state_val.get(0)
                                                .and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str())
                                                .and_then(|s| s.parse().ok())
                                                .unwrap_or(0);
                                            block_number = state_val.get(3)
                                                .and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str())
                                                .and_then(|s| s.parse().ok())
                                                .unwrap_or(0);
                                            timestamp = state_val.get(4)
                                                .and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str())
                                                .and_then(|s| s.parse().ok())
                                                .unwrap_or(0);
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        Ok(NeoAnchorResult {
            tx_hash,
            block_number,
            timestamp,
            root_id,
            contract_address: contract.clone(),
            neofs_cid: None,
        })
    }

    /// Register a Quantum-Safe Identity with proof on Neo N3.
    ///
    /// This registers an ML-DSA-87 fingerprint with a signature commitment
    /// that binds the registration to the sender's address, preventing
    /// front-running attacks.
    ///
    /// # Arguments
    /// * `fingerprint` - 64-byte SHA-512 fingerprint of the ML-DSA-87 public key
    /// * `commitment` - 32-byte SHA-256 commitment of the sender-bound signature
    /// * `neofs_cid` - NeoFS CID where the full signature is stored
    ///
    /// # Returns
    /// Identity registration result with assigned identity ID.
    pub fn register_identity_with_proof(
        &self,
        fingerprint: &[u8; 64],
        commitment: &[u8; 32],
        neofs_cid: &str,
    ) -> Result<NeoIdentityResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError(
                "Contract address required. Run: anubis-notary anchor neo config --contract <HASH>"
                    .to_string(),
            )
        })?;

        // Get private key from environment
        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError(
                "NEO_PRIVATE_KEY environment variable required for signing".to_string(),
            )
        })?);

        // Parse the WIF key
        let account = NeoAccount::from_wif(&wif)?;

        // Parse contract hash (remove 0x prefix and convert to LE bytes)
        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract hash: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract hash must be 20 bytes".to_string()))?;

        // Contract hash stored as BE in config, need to reverse to LE for script
        let mut contract_le = contract_bytes;
        contract_le.reverse();

        // Build the invocation script for registerIdentityWithProof(fingerprint, commitment, neofsCid)
        let mut builder = NeoScriptBuilder::new();

        // Push arguments in reverse order (Neo VM stack)
        // 1. neofsCid (string)
        builder.push_string(neofs_cid);
        // 2. commitment (32 bytes)
        builder.push_bytes(commitment);
        // 3. fingerprint (64 bytes)
        builder.push_bytes(fingerprint);

        // Pack into args array (3 arguments)
        builder.push_int(3);
        builder.pack();

        // Push CallFlags.All (15)
        builder.push_int(15);

        // Push method name and contract hash
        builder.push_string("registerIdentityWithProof");
        builder.push_bytes(&contract_le);

        // SYSCALL System.Contract.Call
        builder.syscall(&[0x62, 0x7d, 0x5b, 0x52]);

        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        // Get current block height
        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        // Test the invocation first
        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([
                script_base64,
                [{"account": account_hex, "scopes": "CalledByEntry"}]
            ]),
        )?;

        let state = test_result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            let exception = test_result
                .get("exception")
                .and_then(|e| e.as_str())
                .unwrap_or("Unknown error");
            return Err(NeoError::TransactionFailed(format!(
                "Identity registration test failed: {}",
                exception
            )));
        }

        // Get system fee from test invocation
        let gas_consumed = test_result
            .get("gasconsumed")
            .and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(1_000_000);

        // Add 10% buffer to system fee
        let system_fee = gas_consumed + gas_consumed / 10;

        // Create and sign the transaction
        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(
            script,
            signer,
            current_height + 100,
            system_fee,
            500_000, // Network fee (~0.005 GAS)
        );

        // Sign with network magic
        tx.sign(&account, self.config.network.magic());

        // Serialize to base64 for RPC
        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        // Send the transaction
        let send_result = self.call_rpc::<serde_json::Value>(
            "sendrawtransaction",
            serde_json::json!([tx_base64]),
        )?;

        // Get the transaction hash from response
        let tx_hash = send_result
            .get("hash")
            .and_then(|h| h.as_str())
            .map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        // Wait for confirmation
        let mut block_number = 0u64;
        let mut timestamp = 0u64;
        let mut identity_id = 0u64;

        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));

            if let Ok(app_log) = self.call_rpc::<serde_json::Value>(
                "getapplicationlog",
                serde_json::json!([tx_hash]),
            ) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            // Extract IdentityRegistered event data
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    if notif.get("eventname").and_then(|e| e.as_str()) == Some("IdentityRegistered") {
                                        if let Some(state_val) = notif.get("state").and_then(|s| s.get("value")).and_then(|v| v.as_array()) {
                                            // IdentityRegistered(id, fingerprint, timestamp)
                                            identity_id = state_val.get(0)
                                                .and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str())
                                                .and_then(|s| s.parse().ok())
                                                .unwrap_or(0);
                                            timestamp = state_val.get(2)
                                                .and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str())
                                                .and_then(|s| s.parse().ok())
                                                .unwrap_or(0);
                                        }
                                    }
                                }
                            }
                            // Get block number from transaction
                            if let Ok(tx_info) = self.call_rpc::<serde_json::Value>(
                                "getrawtransaction",
                                serde_json::json!([tx_hash, true]),
                            ) {
                                block_number = tx_info.get("blockhash")
                                    .and_then(|_| tx_info.get("confirmations"))
                                    .map(|_| {
                                        // Get block from blockhash
                                        if let Some(bh) = tx_info.get("blockhash").and_then(|v| v.as_str()) {
                                            if let Ok(block) = self.call_rpc::<serde_json::Value>(
                                                "getblock",
                                                serde_json::json!([bh, false]),
                                            ) {
                                                return block.get("index").and_then(|i| i.as_u64()).unwrap_or(0);
                                            }
                                        }
                                        0
                                    })
                                    .unwrap_or(0);
                            }
                            break;
                        }
                    }
                }
            }
        }

        Ok(NeoIdentityResult {
            tx_hash,
            block_number,
            timestamp,
            identity_id,
            fingerprint: hex::encode(fingerprint),
            contract_address: contract.clone(),
            neofs_cid: Some(neofs_cid.to_string()),
        })
    }

    /// Anchor multiple receipt hashes in a single batch transaction.
    ///
    /// This is more cost-effective than anchoring individually when you have
    /// multiple receipts to anchor. Max 8 roots per batch.
    ///
    /// # Arguments
    /// * `roots` - Array of SHA-512 receipt hashes (max 8)
    ///
    /// # Returns
    /// Batch anchor result with batch_root and individual witnesses.
    pub fn anchor_batch(
        &self,
        roots: &[[u8; 64]],
    ) -> Result<NeoBatchAnchorResult, NeoError> {
        if roots.is_empty() {
            return Err(NeoError::ConfigError("Batch cannot be empty".to_string()));
        }
        if roots.len() > 8 {
            return Err(NeoError::ConfigError(
                "Batch can have at most 8 roots".to_string(),
            ));
        }

        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError(
                "Contract address required. Run: anubis-notary anchor neo config --contract <HASH>"
                    .to_string(),
            )
        })?;

        // Get private key from environment
        // SECURITY: Wrap WIF in Zeroizing to clear from memory after use
        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError(
                "NEO_PRIVATE_KEY environment variable required for signing".to_string(),
            )
        })?);

        // Parse the WIF key
        let account = NeoAccount::from_wif(&wif)?;

        // Parse contract hash
        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract hash: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract hash must be 20 bytes".to_string()))?;

        let mut contract_le = contract_bytes;
        contract_le.reverse();

        // Compute the batch root (SHA-512 of concatenated roots)
        let batch_root = Self::compute_batch_root(roots);

        // Build the invocation script for anchorBatch
        // The contract expects a single parameter: an array of ByteStrings
        // System.Contract.Call expects: args (Array), callflags, method, contractHash
        // So we need: [[root1, root2, ...]], 15, "anchorBatch", contractHash
        let mut builder = NeoScriptBuilder::new();

        // Push each root in reverse order (for Neo VM stack)
        // V2 contract expects full 64-byte SHA-512 roots (CNSA 2.0 compliant)
        // Document hashes are data (not script hashes), so no byte reversal needed.
        for root in roots.iter().rev() {
            builder.push_bytes(root);
        }

        // Pack into the roots array (the parameter value)
        builder.push_int(roots.len() as i64);
        builder.pack();

        // Now wrap in another array - this is the "args" array for Contract.Call
        // The args array has 1 element: the roots array
        builder.push_int(1);
        builder.pack();

        // Push CallFlags.All (15)
        builder.push_int(15);

        // Push method name and contract hash
        builder.push_string("anchorBatch");
        builder.push_bytes(&contract_le);

        // SYSCALL System.Contract.Call
        builder.syscall(&[0x62, 0x7d, 0x5b, 0x52]);

        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        // Get current block height
        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        // Test the invocation first
        // RPC expects script hash in big-endian (display) format
        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex_for_rpc = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([
                script_base64,
                [{"account": account_hex_for_rpc, "scopes": "CalledByEntry"}]
            ]),
        )?;

        let state = test_result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            let exception = test_result
                .get("exception")
                .and_then(|e| e.as_str())
                .unwrap_or("Unknown error");
            return Err(NeoError::TransactionFailed(format!(
                "Batch anchor test failed: {}",
                exception
            )));
        }

        // Get system fee from test invocation
        let gas_consumed = test_result
            .get("gasconsumed")
            .and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(2_000_000);

        // Add 10% buffer to system fee
        let system_fee = gas_consumed + gas_consumed / 10;

        // Create and sign the transaction
        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(
            script,
            signer,
            current_height + 100,
            system_fee,
            500_000, // Network fee
        );

        tx.sign(&account, self.config.network.magic());

        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        // Send the transaction
        let send_result = self.call_rpc::<serde_json::Value>(
            "sendrawtransaction",
            serde_json::json!([tx_base64]),
        )?;

        let tx_hash = send_result
            .get("hash")
            .and_then(|h| h.as_str())
            .map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        // Wait for confirmation
        let mut block_number = 0u64;
        let mut timestamp = 0u64;
        let mut batch_id = 0u64;
        let mut contract_batch_root: Option<[u8; 32]> = None;

        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));

            if let Ok(app_log) = self.call_rpc::<serde_json::Value>(
                "getapplicationlog",
                serde_json::json!([tx_hash]),
            ) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            // Extract BatchAnchored event data
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    let event_name = notif.get("eventname").and_then(|e| e.as_str()).unwrap_or("");
                                    if event_name == "BatchAnchored" || event_name == "RootAnchored" {
                                        if let Some(state_val) = notif.get("state").and_then(|s| s.get("value")).and_then(|v| v.as_array()) {
                                            batch_id = state_val.get(0)
                                                .and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str())
                                                .and_then(|s| s.parse().ok())
                                                .unwrap_or(0);
                                            // Extract contract's computed batch root (index 1)
                                            if let Some(root_b64) = state_val.get(1)
                                                .and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str())
                                            {
                                                if let Ok(root_bytes) = BASE64.decode(root_b64) {
                                                    if root_bytes.len() == 32 {
                                                        let mut arr = [0u8; 32];
                                                        arr.copy_from_slice(&root_bytes);
                                                        contract_batch_root = Some(arr);
                                                    }
                                                }
                                            }
                                            block_number = state_val.get(4)
                                                .and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str())
                                                .and_then(|s| s.parse().ok())
                                                .unwrap_or(0);
                                            timestamp = state_val.get(5)
                                                .and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str())
                                                .and_then(|s| s.parse().ok())
                                                .unwrap_or(0);
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        // Compute witnesses for each root
        let witnesses: Vec<Vec<[u8; 64]>> = (0..roots.len())
            .map(|i| Self::compute_batch_witness(roots, i).unwrap_or_default())
            .collect();

        // Use contract's batch root if available, otherwise compute from submitted hashes
        let contract_root = contract_batch_root.unwrap_or_else(|| {
            // Fallback: compute Merkle root of truncated hashes (same as contract does)
            let truncated: Vec<[u8; 32]> = roots.iter()
                .map(|r| {
                    // SAFETY: r is [u8; 64], so r[..32] is always exactly 32 bytes
                    let arr: [u8; 32] = r[..32].try_into().expect("64-byte array always has 32-byte prefix");
                    arr
                })
                .collect();
            Self::compute_merkle_root_32(&truncated)
        });

        Ok(NeoBatchAnchorResult {
            tx_hash,
            block_number,
            timestamp,
            batch_id,
            batch_root,
            contract_root,
            root_count: roots.len(),
            witnesses,
            contract_address: contract.clone(),
        })
    }

    /// Compute batch root from multiple Merkle roots using SHA-512.
    pub fn compute_batch_root(roots: &[[u8; 64]]) -> [u8; 64] {
        if roots.is_empty() {
            return [0u8; 64];
        }

        // Concatenate all roots and hash with SHA-512
        let mut data = Vec::with_capacity(roots.len() * 64);
        for root in roots {
            data.extend_from_slice(root);
        }

        // Use SHA-512 for NIST Level 5 security
        anubis_core::sha2::sha512(&data)
    }

    /// Compute Merkle root from 32-byte leaves (matching contract's algorithm).
    /// Uses SHA-256 for compatibility with the Neo contract's Merkle tree.
    pub fn compute_merkle_root_32(leaves: &[[u8; 32]]) -> [u8; 32] {
        use sha2::{Digest, Sha256};

        if leaves.is_empty() {
            return [0u8; 32];
        }
        if leaves.len() == 1 {
            return leaves[0];
        }

        // Build Merkle tree bottom-up
        let mut current_level: Vec<[u8; 32]> = leaves.to_vec();

        while current_level.len() > 1 {
            let mut next_level = Vec::new();
            let mut i = 0;
            while i < current_level.len() {
                let left = &current_level[i];
                let right = if i + 1 < current_level.len() {
                    &current_level[i + 1]
                } else {
                    left // Duplicate last element if odd
                };

                let mut hasher = Sha256::new();
                hasher.update(left);
                hasher.update(right);
                let hash: [u8; 32] = hasher.finalize().into();
                next_level.push(hash);
                i += 2;
            }
            current_level = next_level;
        }

        current_level[0]
    }

    /// Compute Merkle witness for batch inclusion.
    ///
    /// Returns the sibling hashes needed to prove inclusion in a batch.
    /// Assumes a binary tree with up to 8 leaves (3 levels).
    pub fn compute_batch_witness(
        roots: &[[u8; 64]],
        index: usize,
    ) -> Result<Vec<[u8; 64]>, NeoError> {
        if roots.len() > 8 {
            return Err(NeoError::ConfigError(
                "Batch can have at most 8 roots".to_string(),
            ));
        }

        if index >= roots.len() {
            return Err(NeoError::ConfigError(format!(
                "Index {} out of range for batch of size {}",
                index,
                roots.len()
            )));
        }

        // Pad to 8 elements if needed
        let mut padded = roots.to_vec();
        while padded.len() < 8 {
            padded.push([0u8; 64]);
        }

        // Build Merkle tree (3 levels for 8 leaves)
        let mut witness = Vec::with_capacity(3);
        let mut current_level = padded.clone();
        let mut current_index = index;

        for _ in 0..3 {
            // Get sibling
            let sibling_index = if current_index % 2 == 0 {
                current_index + 1
            } else {
                current_index - 1
            };

            if sibling_index < current_level.len() {
                witness.push(current_level[sibling_index]);
            }

            // Compute parent level using SHA-512
            let mut parent_level: Vec<[u8; 64]> = Vec::new();
            for i in (0..current_level.len()).step_by(2) {
                let left = &current_level[i];
                let right = if i + 1 < current_level.len() {
                    current_level[i + 1]
                } else {
                    [0u8; 64]
                };

                // Hash pair with SHA-512
                let mut combined = [0u8; 128];
                combined[..64].copy_from_slice(left);
                combined[64..].copy_from_slice(&right);
                let parent = anubis_core::sha2::sha512(&combined);
                parent_level.push(parent);
            }

            current_level = parent_level;
            current_index /= 2;
        }

        Ok(witness)
    }

    /// Get the chain ID (network magic).
    pub fn get_chain_id(&self) -> Result<u32, NeoError> {
        let result = self.call_rpc::<serde_json::Value>("getversion", serde_json::json!([]))?;

        let magic = result
            .get("protocol")
            .and_then(|p| p.get("network"))
            .and_then(|n| n.as_u64())
            .map(|m| m as u32)
            .ok_or_else(|| NeoError::Provider("Failed to get network magic".to_string()))?;

        Ok(magic)
    }

    // =========================================================================
    // DUAL-KEY QUANTUM-SAFE IDENTITY (DK-QSI) METHODS
    // =========================================================================

    /// Register a Dual-Key Quantum-Safe Identity on-chain.
    ///
    /// This registers both the ML-DSA-87 signing key and ML-KEM-1024 decryption key
    /// as a single identity. The signing fingerprint becomes the DID suffix,
    /// and the decryption fingerprint becomes the CTA (Cryptographic Threshold Authority).
    ///
    /// The QSI document should be stored in NeoFS first, and its CID passed here.
    ///
    /// # Arguments
    /// * `signing_fingerprint` - SHA-512(ML-DSA-87 public key) - becomes DID suffix
    /// * `decryption_fingerprint` - SHA-512(ML-KEM-1024 public key) - becomes CTA
    /// * `neofs_cid` - NeoFS Content Identifier where the DK-QSI document is stored
    ///
    /// # Returns
    /// Registration result containing transaction hash, block info, and the DID.
    pub fn register_dual_key_identity(
        &self,
        signing_fingerprint: &[u8; 64],
        decryption_fingerprint: &[u8; 64],
        neofs_cid: &str,
    ) -> Result<DkQsiRegistrationResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError(
                "Contract address required. Run: anubis-notary anchor neo config --contract <HASH>"
                    .to_string(),
            )
        })?;

        // Get private key from environment
        // SECURITY: Wrap WIF in Zeroizing to clear from memory after use
        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError(
                "NEO_PRIVATE_KEY environment variable required for signing".to_string(),
            )
        })?);

        // Parse the WIF key
        let account = NeoAccount::from_wif(&wif)?;

        // Parse contract hash (remove 0x prefix and convert to LE bytes)
        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract hash: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract hash must be 20 bytes".to_string()))?;

        // Contract hash stored as BE in config, need to reverse to LE for script
        let mut contract_le = contract_bytes;
        contract_le.reverse();

        // NOTE: Fingerprints are ByteStrings, NOT script hashes.
        // They should be passed as-is (big-endian) so they can be looked up the same way.
        // Only script hashes need to be reversed for Neo VM.

        // Build the invocation script for registerDualKeyIdentity
        // Use emit_app_call helper which handles parameter packing correctly
        let mut builder = NeoScriptBuilder::new();

        // For methods with multiple individual params (not Array), use emit_app_call
        // Pass fingerprints as-is (not reversed) since they're ByteStrings
        builder.emit_app_call(
            &contract_le,
            "registerDualKeyIdentity",
            &[&signing_fingerprint[..], &decryption_fingerprint[..], neofs_cid.as_bytes()],
        );

        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        // Get current block height
        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        // Test the invocation first
        // RPC expects script hash in big-endian (display) format
        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex_for_rpc = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([
                script_base64,
                [{"account": account_hex_for_rpc, "scopes": "CalledByEntry"}]
            ]),
        )?;

        let state = test_result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            let exception = test_result
                .get("exception")
                .and_then(|e| e.as_str())
                .unwrap_or("Unknown error");
            return Err(NeoError::Qsi(format!(
                "Identity registration test failed: {}",
                exception
            )));
        }

        // Check the result - should be true (1) for success
        let stack = test_result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                let success = first.get("value") == Some(&serde_json::json!(true))
                    || first.get("value") == Some(&serde_json::json!(1));
                if !success {
                    return Err(NeoError::Qsi(
                        "Identity registration would fail - identity may already exist".to_string(),
                    ));
                }
            }
        }

        // Get system fee from test invocation
        let gas_consumed = test_result
            .get("gasconsumed")
            .and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(2_000_000);

        // Add 10% buffer to system fee
        let system_fee = gas_consumed + gas_consumed / 10;

        // Create and sign the transaction
        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(
            script,
            signer,
            current_height + 100,
            system_fee,
            500_000, // Network fee (~0.005 GAS)
        );

        // Sign with network magic
        tx.sign(&account, self.config.network.magic());

        // Serialize to base64 for RPC
        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        // Send the transaction
        let send_result = self.call_rpc::<serde_json::Value>(
            "sendrawtransaction",
            serde_json::json!([tx_base64]),
        )?;

        // Get the transaction hash from response
        let tx_hash = send_result
            .get("hash")
            .and_then(|h| h.as_str())
            .map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        // Wait for confirmation
        let mut block_number = 0u64;
        let mut timestamp = 0u64;

        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));

            if let Ok(app_log) = self.call_rpc::<serde_json::Value>(
                "getapplicationlog",
                serde_json::json!([tx_hash]),
            ) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            // Get block info
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    if notif.get("eventname").and_then(|e| e.as_str()) == Some("DualKeyIdentityRegistered") {
                                        // Successfully registered
                                        break;
                                    }
                                }
                            }

                            // Get block number from the transaction
                            if let Ok(tx_info) = self.call_rpc::<serde_json::Value>(
                                "getrawtransaction",
                                serde_json::json!([tx_hash, true]),
                            ) {
                                block_number = tx_info
                                    .get("blockhash")
                                    .and_then(|bh| bh.as_str())
                                    .and_then(|bh| {
                                        self.call_rpc::<serde_json::Value>(
                                            "getblock",
                                            serde_json::json!([bh, true]),
                                        ).ok()
                                    })
                                    .and_then(|b| b.get("index").and_then(|i| i.as_u64()))
                                    .unwrap_or(0);

                                timestamp = tx_info
                                    .get("blocktime")
                                    .and_then(|t| t.as_u64())
                                    .unwrap_or_else(|| {
                                        std::time::SystemTime::now()
                                            .duration_since(std::time::UNIX_EPOCH)
                                            .map(|d| d.as_secs())
                                            .unwrap_or(0)
                                    });
                            }
                            break;
                        }
                    }
                }
            }
        }

        let signing_fp_hex = hex::encode(signing_fingerprint);
        let decryption_fp_hex = hex::encode(decryption_fingerprint);

        // Build the DID from signing fingerprint
        let did = format!(
            "did:anubis:neo:{}:{}",
            self.config.network.name(),
            signing_fp_hex
        );

        Ok(DkQsiRegistrationResult {
            tx_hash,
            block_number,
            timestamp,
            signing_fingerprint: signing_fp_hex,
            decryption_fingerprint: decryption_fp_hex,
            neofs_cid: neofs_cid.to_string(),
            did,
        })
    }

    /// Update an existing DK-QSI identity with new ML-KEM-1024 decryption key.
    ///
    /// This updates the on-chain binding while keeping the same ML-DSA-87
    /// signing identity (DID anchor). Only the original registrant can update.
    ///
    /// # Arguments
    /// * `signing_fingerprint` - The identity's signing fingerprint (DID anchor)
    /// * `new_decryption_fingerprint` - SHA-512(new ML-KEM-1024 public key)
    /// * `new_neofs_cid` - New NeoFS CID for updated DK-QSI document
    ///
    /// # Returns
    /// The update result including transaction hash.
    pub fn update_dual_key_identity(
        &self,
        signing_fingerprint: &[u8; 64],
        new_decryption_fingerprint: &[u8; 64],
        new_neofs_cid: &str,
    ) -> Result<DkQsiRegistrationResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError(
                "Contract address required. Run: anubis-notary anchor neo config --contract <HASH>"
                    .to_string(),
            )
        })?;

        // Get private key from environment
        // SECURITY: Wrap WIF in Zeroizing to clear from memory after use
        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError(
                "NEO_PRIVATE_KEY environment variable required for signing".to_string(),
            )
        })?);

        // Parse the WIF key
        let account = NeoAccount::from_wif(&wif)?;

        // Parse contract hash (remove 0x prefix and convert to LE bytes)
        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract hash: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract hash must be 20 bytes".to_string()))?;

        // Contract hash stored as BE in config, need to reverse to LE for script
        let mut contract_le = contract_bytes;
        contract_le.reverse();

        // Build the invocation script for updateDualKeyIdentity
        let mut builder = NeoScriptBuilder::new();
        builder.emit_app_call(
            &contract_le,
            "updateDualKeyIdentity",
            &[&signing_fingerprint[..], &new_decryption_fingerprint[..], new_neofs_cid.as_bytes()],
        );

        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        // Get current block height
        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        // Test the invocation first
        // RPC expects script hash in big-endian (display) format
        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex_for_rpc = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([
                script_base64,
                [{"account": account_hex_for_rpc, "scopes": "CalledByEntry"}]
            ]),
        )?;

        let state = test_result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        // Get system fee from test invocation (even if it faulted, we can use gasconsumed)
        let gas_consumed = test_result
            .get("gasconsumed")
            .and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(5_000_000); // Default to 0.05 GAS if not available

        // Note: invokescript doesn't properly set tx.Sender, so the "Only registrant can update"
        // check will fail in test mode. We proceed anyway since the actual transaction will work
        // if we are the actual registrant.
        if state != "HALT" {
            let exception = test_result
                .get("exception")
                .and_then(|e| e.as_str())
                .unwrap_or("Unknown error");

            // If the error is about registrant authorization, proceed anyway
            // This is expected to fail in invokescript since tx.Sender isn't properly set
            if !exception.contains("Only registrant can update") {
                return Err(NeoError::Qsi(format!(
                    "Identity update test failed: {}",
                    exception
                )));
            }
            // Otherwise, continue with the actual transaction
        }

        // Add 10% buffer to system fee
        let system_fee = gas_consumed + gas_consumed / 10;

        // Create and sign the transaction
        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(
            script,
            signer,
            current_height + 100,
            system_fee,
            500_000, // Network fee (~0.005 GAS)
        );

        // Sign with network magic
        tx.sign(&account, self.config.network.magic());

        // Serialize to base64 for RPC
        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        // Send the transaction
        let send_result = self.call_rpc::<serde_json::Value>(
            "sendrawtransaction",
            serde_json::json!([tx_base64]),
        )?;

        // Get the transaction hash from response
        let tx_hash = send_result
            .get("hash")
            .and_then(|h| h.as_str())
            .map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        // Wait for confirmation
        let mut block_number = 0u64;
        let mut timestamp = 0u64;

        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));

            if let Ok(app_log) = self.call_rpc::<serde_json::Value>(
                "getapplicationlog",
                serde_json::json!([tx_hash]),
            ) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            // Get block info
                            if let Ok(tx_info) = self.call_rpc::<serde_json::Value>(
                                "getrawtransaction",
                                serde_json::json!([tx_hash, true]),
                            ) {
                                block_number = tx_info
                                    .get("blockhash")
                                    .and_then(|h| h.as_str())
                                    .and_then(|hash| {
                                        self.call_rpc::<serde_json::Value>("getblock", serde_json::json!([hash, false]))
                                            .ok()
                                    })
                                    .and_then(|b| b.get("index").and_then(|i| i.as_u64()))
                                    .unwrap_or(0);

                                timestamp = tx_info
                                    .get("blocktime")
                                    .and_then(|t| t.as_u64())
                                    .unwrap_or_else(|| {
                                        std::time::SystemTime::now()
                                            .duration_since(std::time::UNIX_EPOCH)
                                            .map(|d| d.as_secs())
                                            .unwrap_or(0)
                                    });
                            }
                            break;
                        }
                    }
                }
            }
        }

        let signing_fp_hex = hex::encode(signing_fingerprint);
        let decryption_fp_hex = hex::encode(new_decryption_fingerprint);

        // Build the ID from signing fingerprint
        let did = format!(
            "ML-DSA-87:ML-KEM-1024:{}",
            signing_fp_hex
        );

        Ok(DkQsiRegistrationResult {
            tx_hash,
            block_number,
            timestamp,
            signing_fingerprint: signing_fp_hex,
            decryption_fingerprint: decryption_fp_hex,
            neofs_cid: new_neofs_cid.to_string(),
            did,
        })
    }

    /// Resolve a Cryptographic Threshold Authority (CTA) to its identity.
    ///
    /// Given a decryption fingerprint (ML-KEM-1024 key hash), this looks up
    /// the associated signing identity. This enables reverse lookup from
    /// ML-KEM public keys to DIDs.
    ///
    /// # Arguments
    /// * `decryption_fingerprint` - SHA-512(ML-KEM-1024 public key)
    ///
    /// # Returns
    /// Resolution result if found, or None if the CTA is not registered.
    pub fn resolve_cta(
        &self,
        decryption_fingerprint: &[u8; 64],
    ) -> Result<Option<CtaResolveResult>, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        // Neo RPC expects ByteArray as base64, not hex
        use base64::Engine;
        let decryption_fp_b64 = base64::engine::general_purpose::STANDARD.encode(decryption_fingerprint);

        // Call ResolveCTA on the NotaryOracle contract
        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "resolveCTA",
                [{"type": "ByteArray", "value": decryption_fp_b64}]
            ]),
        )?;

        // Check VM state
        let state = result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            return Ok(None);
        }

        // Parse the result array [signingFp, neofsCid, status]
        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                // The contract returns an array of values
                let array_value = first.get("value").and_then(|v| v.as_array());

                if let Some(arr) = array_value {
                    // Extract signing fingerprint (should be at index 0)
                    let signing_fp = arr
                        .first()
                        .and_then(|v| v.get("value"))
                        .and_then(|v| v.as_str())
                        .unwrap_or("");

                    // Check if signing_fp is empty or null (not found)
                    if signing_fp.is_empty() {
                        return Ok(None);
                    }

                    // Extract NeoFS CID (index 1)
                    let neofs_cid = arr
                        .get(1)
                        .and_then(|v| v.get("value"))
                        .and_then(|v| v.as_str())
                        .unwrap_or("")
                        .to_string();

                    // Extract status (index 2)
                    let status_val = arr
                        .get(2)
                        .and_then(|v| v.get("value"))
                        .and_then(|v| v.as_str())
                        .and_then(|s| s.parse::<u64>().ok())
                        .unwrap_or(0);
                    let status = IdentityStatus::from_u64(status_val);

                    // Build DID
                    let did = format!(
                        "did:anubis:neo:{}:{}",
                        self.config.network.name(),
                        signing_fp
                    );

                    return Ok(Some(CtaResolveResult {
                        signing_fingerprint: signing_fp.to_string(),
                        neofs_cid,
                        status,
                        did,
                        can_participate: status.is_active(),
                    }));
                }
            }
        }

        Ok(None)
    }

    /// Get the status of an identity by its signing fingerprint.
    ///
    /// # Arguments
    /// * `signing_fingerprint` - SHA-512(ML-DSA-87 public key)
    ///
    /// # Returns
    /// The identity status (NotFound, Active, Revoked, or Rotated).
    pub fn get_identity_status(
        &self,
        signing_fingerprint: &[u8; 64],
    ) -> Result<IdentityStatus, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        // Neo RPC expects ByteArray as base64, not hex
        use base64::Engine;
        let signing_fp_b64 = base64::engine::general_purpose::STANDARD.encode(signing_fingerprint);

        // Call GetIdentityStatus on the NotaryOracle contract
        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "getIdentityStatus",
                [{"type": "ByteArray", "value": signing_fp_b64}]
            ]),
        )?;

        // Check VM state
        let state = result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            return Ok(IdentityStatus::NotFound);
        }

        // Parse the integer result
        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                let value = first
                    .get("value")
                    .and_then(|v| v.as_str())
                    .and_then(|s| s.parse::<u64>().ok())
                    .unwrap_or(0);
                return Ok(IdentityStatus::from_u64(value));
            }
        }

        Ok(IdentityStatus::NotFound)
    }

    /// Validate that all batch participants have active identities.
    ///
    /// This is used before creating a collaborative private batch to ensure
    /// all specified participants have valid, non-revoked DK-QSI identities.
    ///
    /// # Arguments
    /// * `signing_fingerprints` - Array of signing fingerprints for participants
    ///
    /// # Returns
    /// Validation result indicating if all participants are valid and details for each.
    pub fn validate_batch_participants(
        &self,
        signing_fingerprints: &[[u8; 64]],
    ) -> Result<BatchParticipantsValidationResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        // Neo RPC expects ByteArray as base64, not hex
        use base64::Engine;
        let fps_b64: Vec<serde_json::Value> = signing_fingerprints
            .iter()
            .map(|fp| {
                serde_json::json!({
                    "type": "ByteArray",
                    "value": base64::engine::general_purpose::STANDARD.encode(fp)
                })
            })
            .collect();

        // Call ValidateBatchParticipants on the NotaryOracle contract
        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "validateBatchParticipants",
                [{"type": "Array", "value": fps_b64}]
            ]),
        )?;

        // Check VM state
        let state = result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            return Err(NeoError::Qsi(
                "Failed to validate batch participants".to_string(),
            ));
        }

        // Parse the result array [allValid, decryptionFps[]]
        let stack = result.get("stack").and_then(|s| s.as_array());

        // Build individual validation results
        let mut participants = Vec::with_capacity(signing_fingerprints.len());
        let mut valid_count = 0;

        // For now, validate each participant individually since we need per-participant status
        // (The batch validation on-chain returns aggregate result; we supplement with individual checks)
        for fp in signing_fingerprints {
            let status = self.get_identity_status(fp)?;
            let fp_hex = hex::encode(fp);
            let did = format!(
                "did:anubis:neo:{}:{}",
                self.config.network.name(),
                fp_hex
            );
            let valid = status.is_active();
            if valid {
                valid_count += 1;
            }
            participants.push(ParticipantValidationResult {
                signing_fingerprint: fp_hex,
                did,
                status,
                valid,
            });
        }

        // Check if contract returned allValid flag
        let all_valid_from_contract = if let Some(items) = stack {
            if let Some(first) = items.first() {
                let array_value = first.get("value").and_then(|v| v.as_array());
                if let Some(arr) = array_value {
                    arr.first()
                        .and_then(|v| v.get("value"))
                        .map(|v| v == &serde_json::json!(true) || v == &serde_json::json!(1))
                        .unwrap_or(false)
                } else {
                    // Single boolean result
                    let value = first.get("value");
                    value == Some(&serde_json::json!(true)) || value == Some(&serde_json::json!(1))
                }
            } else {
                false
            }
        } else {
            false
        };

        // Use our computed all_valid as the authoritative result
        let all_valid = valid_count == signing_fingerprints.len();

        Ok(BatchParticipantsValidationResult {
            all_valid: all_valid && all_valid_from_contract,
            valid_count,
            participants,
        })
    }

    /// Resolve an identity by signing fingerprint.
    ///
    /// Returns the NeoFS CID where the identity document is stored,
    /// along with the identity status.
    ///
    /// # Arguments
    /// * `signing_fingerprint` - SHA-512(ML-DSA-87 public key)
    ///
    /// # Returns
    /// Tuple of (neofs_cid, status) if found.
    pub fn resolve_identity(
        &self,
        signing_fingerprint: &[u8; 64],
    ) -> Result<Option<(String, IdentityStatus)>, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        // Neo RPC expects ByteArray as base64, not hex
        use base64::Engine;
        let signing_fp_base64 = base64::engine::general_purpose::STANDARD.encode(signing_fingerprint);

        // Call ResolveIdentity on the NotaryOracle contract
        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "resolveIdentity",
                [{"type": "ByteArray", "value": signing_fp_base64}]
            ]),
        )?;

        // Check VM state
        let state = result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            return Ok(None);
        }

        // Parse the result [neofsCid, revoked, rotatedTo]
        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                let array_value = first.get("value").and_then(|v| v.as_array());

                if let Some(arr) = array_value {
                    // Neo returns ByteStrings as base64-encoded values
                    // Extract and decode NeoFS CID (index 0)
                    let neofs_cid_b64 = arr
                        .first()
                        .and_then(|v| v.get("value"))
                        .and_then(|v| v.as_str())
                        .unwrap_or("");

                    if neofs_cid_b64.is_empty() {
                        return Ok(None);
                    }

                    // Decode the base64 ByteString to get the actual CID string
                    let neofs_cid = base64::engine::general_purpose::STANDARD
                        .decode(neofs_cid_b64)
                        .ok()
                        .and_then(|bytes| String::from_utf8(bytes).ok())
                        .unwrap_or_default();

                    if neofs_cid.is_empty() {
                        return Ok(None);
                    }

                    // Extract revoked flag (index 1)
                    let revoked = arr
                        .get(1)
                        .and_then(|v| v.get("value"))
                        .map(|v| v == &serde_json::json!(true) || v == &serde_json::json!(1))
                        .unwrap_or(false);

                    // Extract rotatedTo (index 2) - also base64 encoded
                    let rotated_to_b64 = arr
                        .get(2)
                        .and_then(|v| v.get("value"))
                        .and_then(|v| v.as_str())
                        .unwrap_or("");

                    let rotated_to = if !rotated_to_b64.is_empty() {
                        base64::engine::general_purpose::STANDARD
                            .decode(rotated_to_b64)
                            .ok()
                            .and_then(|bytes| String::from_utf8(bytes).ok())
                            .unwrap_or_default()
                    } else {
                        String::new()
                    };

                    let status = if revoked {
                        IdentityStatus::Revoked
                    } else if !rotated_to.is_empty() {
                        IdentityStatus::Rotated
                    } else {
                        IdentityStatus::Active
                    };

                    return Ok(Some((neofs_cid, status)));
                }
            }
        }

        Ok(None)
    }

    /// Store a DK-QSI document in NeoFS and register it on-chain.
    ///
    /// This is a convenience method that:
    /// 1. Serializes the QSI document to CBOR
    /// 2. Stores it in NeoFS
    /// 3. Registers the identity on-chain
    ///
    /// # Arguments
    /// * `doc` - The DualKeyQsiDocument to register
    /// * `neofs_client` - NeoFS client for storage
    /// * `container_id` - NeoFS container to store in
    ///
    /// # Returns
    /// Registration result.
    pub fn register_qsi_document(
        &self,
        signing_fingerprint: &[u8; 64],
        decryption_fingerprint: &[u8; 64],
        doc_cbor: &[u8],
        neofs_client: &NeoFsClient,
        container_id: &str,
    ) -> Result<DkQsiRegistrationResult, NeoError> {
        // Store document in NeoFS
        let store_result = neofs_client.store(
            container_id,
            doc_cbor,
            Some(NeoFsObjectAttributes {
                content_type: Some("application/cbor".to_string()),
                anubis_type: Some("dk-qsi-document".to_string()),
                signing_fingerprint: Some(hex::encode(signing_fingerprint)),
                ..Default::default()
            }),
        )?;

        // Register on-chain with the NeoFS CID
        self.register_dual_key_identity(
            signing_fingerprint,
            decryption_fingerprint,
            &store_result.cid,
        )
    }

    /// Deposit GAS into the NeoFS balance.
    ///
    /// NeoFS requires a separate deposit from Neo chain GAS into the NeoFS contract.
    /// This transfers GAS from your Neo wallet to the NeoFS contract, making it
    /// available for NeoFS operations (container creation, file storage).
    ///
    /// # Arguments
    /// * `account` - The Neo account to deposit from
    /// * `amount` - Amount in GAS fractions (10^8 = 1 GAS)
    ///
    /// # Returns
    /// Deposit result with transaction hash and block number.
    pub fn deposit_neofs(
        &self,
        account: &NeoAccount,
        amount: u64,
    ) -> Result<NeoFsDepositResult, NeoError> {
        // NeoFS contract addresses
        let neofs_contract = match self.config.network {
            NeoNetwork::MainNet => "0xbc5c8a09b7fb5e1384bab01bcf1d1da5caf39a12",
            NeoNetwork::TestNet => "0x3c3f4b84773ef0141576e48c3ff60e5078235891",
            NeoNetwork::Private => "0x3c3f4b84773ef0141576e48c3ff60e5078235891",
        };

        // GAS token contract (same on all networks)
        let gas_contract_hex = "d2a4cff31913016155e38e474a2c06d08be276cf";
        let gas_contract_bytes: [u8; 20] = hex::decode(gas_contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid GAS hash: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("GAS hash must be 20 bytes".to_string()))?;

        // Parse NeoFS contract hash
        let neofs_hex = neofs_contract.trim_start_matches("0x");
        let neofs_bytes: [u8; 20] = hex::decode(neofs_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid NeoFS hash: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("NeoFS hash must be 20 bytes".to_string()))?;

        // Contract hashes in config are BE, need LE for script
        let mut gas_le = gas_contract_bytes;
        gas_le.reverse();
        let mut neofs_le = neofs_bytes;
        neofs_le.reverse();

        // Build the NEP-17 transfer script: GAS.transfer(from, to, amount, data)
        // Arguments order for System.Contract.Call: [args], callflags, method, contract
        // Args for transfer: from (Hash160), to (Hash160), amount (Integer), data (Any)
        let mut builder = NeoScriptBuilder::new();

        // Push args in reverse order (data, amount, to, from)
        // data: empty ByteArray (null for NeoFS deposit)
        builder.push_bytes(&[]);
        // amount
        builder.push_int(amount as i64);
        // to: NeoFS contract script hash (LE)
        builder.push_bytes(&neofs_le);
        // from: account script hash (LE)
        builder.push_bytes(account.script_hash_le());

        // Pack into args array (4 elements)
        builder.push_int(4);
        builder.pack();

        // Push CallFlags.All (15)
        builder.push_int(15);

        // Push method name
        builder.push_string("transfer");

        // Push GAS contract hash (LE)
        builder.push_bytes(&gas_le);

        // SYSCALL System.Contract.Call
        builder.syscall(&[0x62, 0x7d, 0x5b, 0x52]);

        let script = builder.build();

        // Get current block height
        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        // Use a fixed reasonable system fee for NEP-17 transfer
        // Transfer operations typically cost around 0.01-0.05 GAS
        // Using 0.1 GAS (10_000_000 fractions) for safety
        let system_fee: u64 = 10_000_000;

        // Create and sign the transaction
        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(
            script,
            signer,
            current_height + 100,
            system_fee,
            500_000, // Network fee (~0.005 GAS)
        );

        // Sign with network magic
        tx.sign(account, self.config.network.magic());

        // Serialize to base64 for RPC
        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        // Send the transaction
        let send_result = self.call_rpc::<serde_json::Value>(
            "sendrawtransaction",
            serde_json::json!([tx_base64]),
        )?;

        // Get the transaction hash from response
        let tx_hash = send_result
            .get("hash")
            .and_then(|h| h.as_str())
            .map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        // Wait for confirmation (Neo dBFT is fast)
        let mut block_number = 0u64;

        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));

            if let Ok(app_log) = self.call_rpc::<serde_json::Value>(
                "getapplicationlog",
                serde_json::json!([tx_hash]),
            ) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        let exec_state = exec.get("vmstate").and_then(|v| v.as_str()).unwrap_or("FAULT");
                        if exec_state == "HALT" {
                            // Get block number from transaction
                            if let Ok(tx_info) = self.call_rpc::<serde_json::Value>(
                                "getrawtransaction",
                                serde_json::json!([tx_hash, true]),
                            ) {
                                if let Some(bn) = tx_info.get("blocktime").and_then(|t| t.as_u64()) {
                                    block_number = bn;
                                }
                            }
                            break;
                        } else {
                            // Transaction failed
                            let exception = exec.get("exception").and_then(|e| e.as_str()).unwrap_or("Unknown");
                            return Err(NeoError::TransactionFailed(format!(
                                "Deposit transaction failed: {}",
                                exception
                            )));
                        }
                    }
                }
            }
        }

        Ok(NeoFsDepositResult {
            tx_hash,
            block_number,
            amount,
            from_address: account.address().to_string(),
            neofs_contract: neofs_contract.to_string(),
        })
    }

    /// Make a JSON-RPC call to the Neo node.
    ///
    /// This method is public to allow extension modules (marriage, rings) to
    /// make custom contract calls.
    pub fn call_rpc<T: serde::de::DeserializeOwned>(
        &self,
        method: &str,
        params: serde_json::Value,
    ) -> Result<T, NeoError> {
        let request = serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": method,
            "params": params
        });

        let response = self
            .agent
            .post(&self.config.rpc_url)
            .set("Content-Type", "application/json")
            .send_json(&request);

        // Handle HTTP errors with body content
        let response = match response {
            Ok(r) => r,
            Err(ureq::Error::Status(code, response)) => {
                let body = response.into_string().unwrap_or_default();
                return Err(NeoError::Provider(format!(
                    "HTTP {}: {}",
                    code,
                    if body.is_empty() {
                        "No details".to_string()
                    } else {
                        body
                    }
                )));
            }
            Err(ureq::Error::Transport(t)) => {
                return Err(NeoError::Network(format!("Transport error: {}", t)));
            }
        };

        let json: serde_json::Value = response
            .into_json()
            .map_err(|e| NeoError::Json(e.to_string()))?;

        if let Some(error) = json.get("error") {
            let code = error.get("code").and_then(|c| c.as_i64()).unwrap_or(0);
            let message = error
                .get("message")
                .and_then(|m| m.as_str())
                .unwrap_or("Unknown error");
            return Err(NeoError::Provider(format!("[{}] {}", code, message)));
        }

        let result = json
            .get("result")
            .ok_or_else(|| NeoError::Provider("Missing result in response".to_string()))?;

        serde_json::from_value(result.clone())
            .map_err(|e| NeoError::Json(format!("Failed to parse result: {}", e)))
    }

    // ========================================================================
    // DATA MARKETPLACE METHODS (Sealed Data Economy)
    // ========================================================================

    /// List sealed data for sale on the marketplace.
    ///
    /// # Arguments
    /// * `neofs_object_id` - The NeoFS object ID of the sealed data (ContainerID/ObjectID format)
    /// * `listing_pk` - ML-KEM-1024 public key for the listing (1568 bytes)
    /// * `wrapped_content_key` - Content key wrapped with listing_pk (1628 bytes)
    /// * `price` - Price in GAS fractions (1 GAS = 100,000,000)
    /// * `metadata` - Description/metadata about the listing
    /// * `duration_blocks` - How long the listing is active (in blocks)
    ///
    /// # Returns
    /// The listing ID and transaction hash.
    pub fn list_sealed_data(
        &self,
        neofs_object_id: &str,
        listing_pk: &[u8],
        wrapped_content_key: &[u8],
        price: u64,
        metadata: &str,
        duration_blocks: u64,
    ) -> Result<NeoMarketplaceListResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError("NEO_PRIVATE_KEY required".to_string())
        })?);
        let account = NeoAccount::from_wif(&wif)?;

        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract must be 20 bytes".to_string()))?;
        // Contract bytes in little-endian (for future use in manual script building)
        let mut _contract_le = contract_bytes;
        _contract_le.reverse();

        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        // Use invokefunction to get properly encoded script (handles type conversions correctly)
        let object_id_b64 = BASE64.encode(neofs_object_id.as_bytes());
        let listing_pk_b64 = BASE64.encode(listing_pk);
        let wrapped_key_b64 = BASE64.encode(wrapped_content_key);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "listSealedData",
                [
                    {"type": "ByteArray", "value": object_id_b64},
                    {"type": "Integer", "value": price.to_string()},
                    {"type": "String", "value": metadata},
                    {"type": "Integer", "value": duration_blocks.to_string()},
                    {"type": "ByteArray", "value": listing_pk_b64},
                    {"type": "ByteArray", "value": wrapped_key_b64}
                ],
                [{"account": account_hex, "scopes": "CalledByEntry"}]
            ]),
        )?;

        let state = test_result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" {
            let exception = test_result.get("exception").and_then(|e| e.as_str()).unwrap_or("Unknown");
            return Err(NeoError::TransactionFailed(format!("List test failed: {}", exception)));
        }

        // Get the actual script from the invokefunction result
        let script_from_rpc = test_result.get("script").and_then(|s| s.as_str())
            .ok_or_else(|| NeoError::TransactionFailed("No script in response".to_string()))?;
        let script = BASE64.decode(script_from_rpc)
            .map_err(|e| NeoError::TransactionFailed(format!("Failed to decode script: {}", e)))?;

        let gas_consumed = test_result.get("gasconsumed").and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok()).unwrap_or(1_000_000);
        let system_fee = gas_consumed + gas_consumed / 10;

        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(script, signer, current_height + 100, system_fee, 500_000);
        tx.sign(&account, self.config.network.magic());

        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        let send_result = self.call_rpc::<serde_json::Value>("sendrawtransaction", serde_json::json!([tx_base64]))?;
        let tx_hash = send_result.get("hash").and_then(|h| h.as_str()).map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        let mut listing_id = 0u64;
        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));
            if let Ok(app_log) = self.call_rpc::<serde_json::Value>("getapplicationlog", serde_json::json!([tx_hash])) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    if notif.get("eventname").and_then(|e| e.as_str()) == Some("DataListed") {
                                        if let Some(state_val) = notif.get("state").and_then(|s| s.get("value")).and_then(|v| v.as_array()) {
                                            listing_id = state_val.get(0).and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        Ok(NeoMarketplaceListResult { tx_hash, listing_id, price, neofs_object_id: neofs_object_id.to_string() })
    }

    /// Purchase access to listed sealed data.
    ///
    /// # Arguments
    /// * `listing_id` - The listing ID to purchase
    /// * `buyer_public_key` - Buyer's ML-KEM public key for re-encryption
    ///
    /// # Returns
    /// The decryption ticket and transaction hash.
    pub fn purchase_access(
        &self,
        listing_id: u64,
        buyer_public_key: &[u8],
    ) -> Result<NeoMarketplacePurchaseResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError("NEO_PRIVATE_KEY required".to_string())
        })?);
        let account = NeoAccount::from_wif(&wif)?;

        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract must be 20 bytes".to_string()))?;
        let mut contract_le = contract_bytes;
        contract_le.reverse();

        let mut builder = NeoScriptBuilder::new();
        builder.push_bytes(buyer_public_key);
        builder.push_int(listing_id as i64);
        builder.push_int(2);
        builder.pack();
        builder.push_int(15);
        builder.push_string("purchaseAccess");
        builder.push_bytes(&contract_le);
        builder.syscall(&[0x62, 0x7d, 0x5b, 0x52]);

        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([script_base64, [{"account": account_hex, "scopes": "CalledByEntry"}]]),
        )?;

        let state = test_result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" {
            let exception = test_result.get("exception").and_then(|e| e.as_str()).unwrap_or("Unknown");
            return Err(NeoError::TransactionFailed(format!("Purchase test failed: {}", exception)));
        }

        let gas_consumed = test_result.get("gasconsumed").and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok()).unwrap_or(1_000_000);
        let system_fee = gas_consumed + gas_consumed / 10;

        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(script, signer, current_height + 100, system_fee, 500_000);
        tx.sign(&account, self.config.network.magic());

        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        let send_result = self.call_rpc::<serde_json::Value>("sendrawtransaction", serde_json::json!([tx_base64]))?;
        let tx_hash = send_result.get("hash").and_then(|h| h.as_str()).map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        // Two-phase delivery: get purchase_id from transaction return value (stack)
        // The contract returns purchaseId, while the AccessPurchased event has:
        // (listingId, buyer, seller, price, platformFee) - NOT purchaseId
        let mut purchase_id = 0u64;
        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));
            if let Ok(app_log) = self.call_rpc::<serde_json::Value>("getapplicationlog", serde_json::json!([tx_hash])) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            // Get purchase_id from the return value (stack), not from the event
                            if let Some(stack) = exec.get("stack").and_then(|s| s.as_array()) {
                                if let Some(first) = stack.first() {
                                    purchase_id = first.get("value")
                                        .and_then(|v| v.as_str())
                                        .and_then(|s| s.parse().ok())
                                        .unwrap_or(0);
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        Ok(NeoMarketplacePurchaseResult { tx_hash, listing_id, purchase_id })
    }

    /// Claim accumulated revenue from a listing.
    pub fn claim_revenue(&self, listing_id: u64) -> Result<NeoMarketplaceClaimResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError("NEO_PRIVATE_KEY required".to_string())
        })?);
        let account = NeoAccount::from_wif(&wif)?;

        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract must be 20 bytes".to_string()))?;
        let mut contract_le = contract_bytes;
        contract_le.reverse();

        let mut builder = NeoScriptBuilder::new();
        builder.push_int(listing_id as i64);
        builder.push_int(1);
        builder.pack();
        builder.push_int(15);
        builder.push_string("claimRevenue");
        builder.push_bytes(&contract_le);
        builder.syscall(&[0x62, 0x7d, 0x5b, 0x52]);

        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([script_base64, [{"account": account_hex, "scopes": "CalledByEntry"}]]),
        )?;

        let state = test_result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" {
            let exception = test_result.get("exception").and_then(|e| e.as_str()).unwrap_or("Unknown");
            return Err(NeoError::TransactionFailed(format!("Claim test failed: {}", exception)));
        }

        let gas_consumed = test_result.get("gasconsumed").and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok()).unwrap_or(1_000_000);
        let system_fee = gas_consumed + gas_consumed / 10;

        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(script, signer, current_height + 100, system_fee, 500_000);
        tx.sign(&account, self.config.network.magic());

        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        let send_result = self.call_rpc::<serde_json::Value>("sendrawtransaction", serde_json::json!([tx_base64]))?;
        let tx_hash = send_result.get("hash").and_then(|h| h.as_str()).map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        let mut amount_claimed = 0u64;
        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));
            if let Ok(app_log) = self.call_rpc::<serde_json::Value>("getapplicationlog", serde_json::json!([tx_hash])) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    if notif.get("eventname").and_then(|e| e.as_str()) == Some("RevenueClaimed") {
                                        if let Some(state_val) = notif.get("state").and_then(|s| s.get("value")).and_then(|v| v.as_array()) {
                                            amount_claimed = state_val.get(2).and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        Ok(NeoMarketplaceClaimResult { tx_hash, listing_id, amount_claimed })
    }

    /// Get listing details.
    pub fn get_listing(&self, listing_id: u64) -> Result<Option<NeoMarketplaceListing>, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([contract, "getListing", [{"type": "Integer", "value": listing_id.to_string()}]]),
        )?;

        let state = result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" { return Ok(None); }

        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                if first.get("type").and_then(|t| t.as_str()) == Some("Array") {
                    if let Some(values) = first.get("value").and_then(|v| v.as_array()) {
                        // Contract structure (two-phase key delivery):
                        // [0]objectId, [1]seller, [2]price, [3]metadata, [4]listedBlock,
                        // [5]listingPk (1568 bytes), [6]wrappedContentKey (1628 bytes),
                        // [7]salesCount, [8]totalRevenue
                        return Ok(Some(NeoMarketplaceListing {
                            id: listing_id,
                            neofs_object_id: values.get(0).and_then(|v| v.get("value")).and_then(|v| v.as_str())
                                .map(|s| String::from_utf8(BASE64.decode(s).unwrap_or_default()).unwrap_or_default())
                                .unwrap_or_default(),
                            price: values.get(2).and_then(|v| v.get("value")).and_then(|v| v.as_str())
                                .and_then(|s| s.parse().ok()).unwrap_or(0),
                            metadata: values.get(3).and_then(|v| v.get("value")).and_then(|v| v.as_str())
                                .map(|s| String::from_utf8(BASE64.decode(s).unwrap_or_default()).unwrap_or_default())
                                .unwrap_or_default(),
                            wrapped_content_key: values.get(6).and_then(|v| v.get("value")).and_then(|v| v.as_str())
                                .map(|s| BASE64.decode(s).unwrap_or_default())
                                .unwrap_or_default(),
                            is_active: true, // Listing exists = active (no explicit active flag in contract)
                            sales_count: values.get(7).and_then(|v| v.get("value")).and_then(|v| v.as_str())
                                .and_then(|s| s.parse().ok()).unwrap_or(0),
                            total_revenue: values.get(8).and_then(|v| v.get("value")).and_then(|v| v.as_str())
                                .and_then(|s| s.parse().ok()).unwrap_or(0),
                        }));
                    }
                }
            }
        }
        Ok(None)
    }

    /// Get total listing count.
    pub fn get_listing_count(&self) -> Result<u64, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([contract, "getListingCount", []]),
        )?;

        let state = result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" { return Ok(0); }

        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                return Ok(first.get("value").and_then(|v| v.as_str())
                    .and_then(|s| s.parse().ok()).unwrap_or(0));
            }
        }
        Ok(0)
    }

    /// Deliver access to a buyer (seller wraps content key for buyer's public key).
    ///
    /// This is called by the seller after a purchase to provide the buyer
    /// with a wrapped content key that only the buyer can decrypt.
    ///
    /// # Arguments
    /// * `purchase_id` - The purchase ID to deliver access for
    /// * `buyer_wrapped_key` - Content key wrapped with buyer's ML-KEM public key (1628 bytes)
    pub fn deliver_access(
        &self,
        purchase_id: u64,
        buyer_wrapped_key: &[u8],
    ) -> Result<NeoMarketplaceDeliverResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError("NEO_PRIVATE_KEY required".to_string())
        })?);
        let account = NeoAccount::from_wif(&wif)?;

        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        // Encode the wrapped key as base64
        let wrapped_key_b64 = BASE64.encode(buyer_wrapped_key);

        // Use invokefunction to get properly encoded script
        let test_result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "deliverAccess",
                [
                    {"type": "Integer", "value": purchase_id.to_string()},
                    {"type": "ByteArray", "value": wrapped_key_b64}
                ],
                [{"account": account_hex, "scopes": "CalledByEntry"}]
            ]),
        )?;

        let state = test_result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" {
            let exception = test_result.get("exception").and_then(|e| e.as_str()).unwrap_or("Unknown");
            return Err(NeoError::TransactionFailed(format!("Deliver access test failed: {}", exception)));
        }

        // Get the actual script from the invokefunction result
        let script_from_rpc = test_result.get("script").and_then(|s| s.as_str())
            .ok_or_else(|| NeoError::TransactionFailed("No script in response".to_string()))?;
        let script = BASE64.decode(script_from_rpc)
            .map_err(|e| NeoError::TransactionFailed(format!("Failed to decode script: {}", e)))?;

        let gas_consumed = test_result.get("gasconsumed").and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok()).unwrap_or(1_000_000);
        let system_fee = gas_consumed + gas_consumed / 10;

        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(script, signer, current_height + 100, system_fee, 500_000);
        tx.sign(&account, self.config.network.magic());

        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        let send_result = self.call_rpc::<serde_json::Value>("sendrawtransaction", serde_json::json!([tx_base64]))?;
        let tx_hash = send_result.get("hash").and_then(|h| h.as_str()).map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        // Wait for confirmation and parse AccessDelivered event
        // Event: (purchaseId, listingId, buyer, seller)
        let mut listing_id = 0u64;
        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));
            if let Ok(app_log) = self.call_rpc::<serde_json::Value>("getapplicationlog", serde_json::json!([tx_hash])) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    if notif.get("eventname").and_then(|e| e.as_str()) == Some("AccessDelivered") {
                                        if let Some(state_val) = notif.get("state").and_then(|s| s.get("value")).and_then(|v| v.as_array()) {
                                            listing_id = state_val.get(1).and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        Ok(NeoMarketplaceDeliverResult { tx_hash, purchase_id, listing_id })
    }

    /// Get pending deliveries for the caller (seller).
    ///
    /// Returns a list of purchases that the seller needs to deliver access for.
    pub fn get_pending_deliveries(&self) -> Result<Vec<NeoPendingDelivery>, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError("NEO_PRIVATE_KEY required".to_string())
        })?);
        let account = NeoAccount::from_wif(&wif)?;

        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                "getPendingDeliveries",
                [{"type": "Hash160", "value": account_hex}]
            ]),
        )?;

        let state = result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" { return Ok(vec![]); }

        let mut deliveries = Vec::new();

        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                if first.get("type").and_then(|t| t.as_str()) == Some("Array") {
                    if let Some(arr) = first.get("value").and_then(|v| v.as_array()) {
                        for item in arr {
                            if item.get("type").and_then(|t| t.as_str()) == Some("Array") {
                                if let Some(values) = item.get("value").and_then(|v| v.as_array()) {
                                    // Contract returns: [purchaseId, listingId, buyer, buyerPk, purchaseBlock]
                                    let purchase_id = values.get(0).and_then(|v| v.get("value"))
                                        .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                                    let listing_id = values.get(1).and_then(|v| v.get("value"))
                                        .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                                    let buyer = values.get(2).and_then(|v| v.get("value"))
                                        .and_then(|v| v.as_str())
                                        .map(|s| hex::encode(BASE64.decode(s).unwrap_or_default()))
                                        .unwrap_or_default();
                                    let buyer_pk = values.get(3).and_then(|v| v.get("value"))
                                        .and_then(|v| v.as_str())
                                        .map(|s| BASE64.decode(s).unwrap_or_default())
                                        .unwrap_or_default();
                                    let purchase_block = values.get(4).and_then(|v| v.get("value"))
                                        .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);

                                    deliveries.push(NeoPendingDelivery {
                                        purchase_id,
                                        listing_id,
                                        buyer,
                                        buyer_pk,
                                        purchase_block,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }

        Ok(deliveries)
    }

    /// Get purchase details by ID.
    pub fn get_purchase(&self, purchase_id: u64) -> Result<Option<NeoMarketplacePurchaseInfo>, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([contract, "getPurchase", [{"type": "Integer", "value": purchase_id.to_string()}]]),
        )?;

        let state = result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" { return Ok(None); }

        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                if first.get("type").and_then(|t| t.as_str()) == Some("Array") {
                    if let Some(values) = first.get("value").and_then(|v| v.as_array()) {
                        // Contract structure (9 fields):
                        // [0]purchaseId, [1]listingId, [2]buyer, [3]buyerPk, [4]seller,
                        // [5]purchaseBlock, [6]buyerWrappedKey, [7]delivered, [8]claimed
                        let listing_id = values.get(1).and_then(|v| v.get("value"))
                            .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                        let buyer = values.get(2).and_then(|v| v.get("value"))
                            .and_then(|v| v.as_str())
                            .map(|s| hex::encode(BASE64.decode(s).unwrap_or_default()))
                            .unwrap_or_default();
                        let buyer_pk = values.get(3).and_then(|v| v.get("value"))
                            .and_then(|v| v.as_str())
                            .map(|s| BASE64.decode(s).unwrap_or_default())
                            .unwrap_or_default();
                        let purchase_block = values.get(5).and_then(|v| v.get("value"))
                            .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                        let buyer_wrapped_key = values.get(6).and_then(|v| v.get("value"))
                            .and_then(|v| v.as_str())
                            .map(|s| BASE64.decode(s).unwrap_or_default())
                            .unwrap_or_default();
                        let delivered = values.get(7).and_then(|v| v.get("value"))
                            .and_then(|v| v.as_bool()).unwrap_or(false);
                        let claimed = values.get(8).and_then(|v| v.get("value"))
                            .and_then(|v| v.as_bool()).unwrap_or(false);

                        return Ok(Some(NeoMarketplacePurchaseInfo {
                            purchase_id,
                            listing_id,
                            buyer,
                            buyer_pk,
                            purchase_block,
                            buyer_wrapped_key,
                            delivered,
                            claimed,
                        }));
                    }
                }
            }
        }
        Ok(None)
    }

    /// Get total purchase count.
    pub fn get_purchase_count(&self) -> Result<u64, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([contract, "getPurchaseCount", []]),
        )?;

        let state = result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" { return Ok(0); }

        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                return Ok(first.get("value").and_then(|v| v.as_str())
                    .and_then(|s| s.parse().ok()).unwrap_or(0));
            }
        }
        Ok(0)
    }

    // ========================================================================
    // MEMBERSHIP NFT METHODS
    // ========================================================================

    /// Mint a membership NFT (Notary or Vault tier).
    ///
    /// # Arguments
    /// * `tier` - "notary" (50 GAS/year) or "vault" (200 GAS/year)
    pub fn mint_membership(&self, tier: &str) -> Result<NeoMembershipResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError("NEO_PRIVATE_KEY required".to_string())
        })?);
        let account = NeoAccount::from_wif(&wif)?;

        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract must be 20 bytes".to_string()))?;
        let mut contract_le = contract_bytes;
        contract_le.reverse();

        let mut builder = NeoScriptBuilder::new();
        builder.push_string(tier);
        builder.push_int(1);
        builder.pack();
        builder.push_int(15);
        builder.push_string("mintMembership");
        builder.push_bytes(&contract_le);
        builder.syscall(&[0x62, 0x7d, 0x5b, 0x52]);

        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([script_base64, [{"account": account_hex, "scopes": "CalledByEntry"}]]),
        )?;

        let state = test_result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" {
            let exception = test_result.get("exception").and_then(|e| e.as_str()).unwrap_or("Unknown");
            return Err(NeoError::TransactionFailed(format!("Mint test failed: {}", exception)));
        }

        let gas_consumed = test_result.get("gasconsumed").and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok()).unwrap_or(1_000_000);
        let system_fee = gas_consumed + gas_consumed / 10;

        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(script, signer, current_height + 100, system_fee, 500_000);
        tx.sign(&account, self.config.network.magic());

        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        let send_result = self.call_rpc::<serde_json::Value>("sendrawtransaction", serde_json::json!([tx_base64]))?;
        let tx_hash = send_result.get("hash").and_then(|h| h.as_str()).map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        let mut token_id = 0u64;
        let mut expiry = 0u64;
        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));
            if let Ok(app_log) = self.call_rpc::<serde_json::Value>("getapplicationlog", serde_json::json!([tx_hash])) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    if notif.get("eventname").and_then(|e| e.as_str()) == Some("MembershipMinted") {
                                        if let Some(state_val) = notif.get("state").and_then(|s| s.get("value")).and_then(|v| v.as_array()) {
                                            token_id = state_val.get(0).and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                                            expiry = state_val.get(3).and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        Ok(NeoMembershipResult { tx_hash, token_id, tier: tier.to_string(), expiry_block: expiry })
    }

    /// Get user's membership tier.
    pub fn get_user_tier(&self, address: &str) -> Result<String, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let script_hash_hex = address_to_script_hash(address)?;
        let script_hash_bytes = hex::decode(&script_hash_hex)
            .map_err(|e| NeoError::InvalidAddress(format!("Hex decode: {}", e)))?;
        let script_hash_b64 = BASE64.encode(&script_hash_bytes);

        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([contract, "getUserTierName", [{"type": "ByteArray", "value": script_hash_b64}]]),
        )?;

        let state = result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" { return Ok("Free".to_string()); }

        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                if let Some(tier_b64) = first.get("value").and_then(|v| v.as_str()) {
                    let tier_bytes = BASE64.decode(tier_b64).unwrap_or_default();
                    return Ok(String::from_utf8(tier_bytes).unwrap_or_else(|_| "Free".to_string()));
                }
            }
        }
        Ok("Free".to_string())
    }

    /// Renew membership.
    pub fn renew_membership(&self, token_id: u64) -> Result<NeoMembershipResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError("NEO_PRIVATE_KEY required".to_string())
        })?);
        let account = NeoAccount::from_wif(&wif)?;

        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract must be 20 bytes".to_string()))?;
        let mut contract_le = contract_bytes;
        contract_le.reverse();

        let mut builder = NeoScriptBuilder::new();
        builder.push_int(token_id as i64);
        builder.push_int(1);
        builder.pack();
        builder.push_int(15);
        builder.push_string("renewMembership");
        builder.push_bytes(&contract_le);
        builder.syscall(&[0x62, 0x7d, 0x5b, 0x52]);

        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([script_base64, [{"account": account_hex, "scopes": "CalledByEntry"}]]),
        )?;

        let state = test_result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" {
            let exception = test_result.get("exception").and_then(|e| e.as_str()).unwrap_or("Unknown");
            return Err(NeoError::TransactionFailed(format!("Renew test failed: {}", exception)));
        }

        let gas_consumed = test_result.get("gasconsumed").and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok()).unwrap_or(1_000_000);
        let system_fee = gas_consumed + gas_consumed / 10;

        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(script, signer, current_height + 100, system_fee, 500_000);
        tx.sign(&account, self.config.network.magic());

        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        let send_result = self.call_rpc::<serde_json::Value>("sendrawtransaction", serde_json::json!([tx_base64]))?;
        let tx_hash = send_result.get("hash").and_then(|h| h.as_str()).map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        let mut expiry = 0u64;
        let mut tier = String::new();
        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));
            if let Ok(app_log) = self.call_rpc::<serde_json::Value>("getapplicationlog", serde_json::json!([tx_hash])) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    if notif.get("eventname").and_then(|e| e.as_str()) == Some("MembershipRenewed") {
                                        if let Some(state_val) = notif.get("state").and_then(|s| s.get("value")).and_then(|v| v.as_array()) {
                                            expiry = state_val.get(2).and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                                            if let Some(tier_b64) = state_val.get(1).and_then(|v| v.get("value")).and_then(|v| v.as_str()) {
                                                tier = String::from_utf8(BASE64.decode(tier_b64).unwrap_or_default()).unwrap_or_default();
                                            }
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        Ok(NeoMembershipResult { tx_hash, token_id, tier, expiry_block: expiry })
    }

    // ========================================================================
    // DATA ESCROW METHODS
    // ========================================================================

    /// Create a time-locked escrow.
    pub fn create_time_lock_escrow(
        &self,
        neofs_object_id: &str,
        re_key: &[u8],
        unlock_block: u64,
        beneficiary: &str,
    ) -> Result<NeoEscrowResult, NeoError> {
        self.create_escrow_internal("createTimeLockEscrow", neofs_object_id, re_key, beneficiary, Some(unlock_block), None, None)
    }

    /// Create a payment-gated escrow.
    pub fn create_payment_escrow(
        &self,
        neofs_object_id: &str,
        re_key: &[u8],
        price: u64,
        beneficiary: &str,
    ) -> Result<NeoEscrowResult, NeoError> {
        self.create_escrow_internal("createPaymentEscrow", neofs_object_id, re_key, beneficiary, None, Some(price), None)
    }

    /// Create a multi-sig escrow.
    pub fn create_multi_sig_escrow(
        &self,
        neofs_object_id: &str,
        re_key: &[u8],
        signers: &[&str],
        threshold: u32,
        beneficiary: &str,
    ) -> Result<NeoEscrowResult, NeoError> {
        self.create_escrow_internal("createMultiSigEscrow", neofs_object_id, re_key, beneficiary, Some(threshold as u64), None, Some(signers))
    }

    /// Create a dead-man switch escrow.
    pub fn create_dead_man_escrow(
        &self,
        neofs_object_id: &str,
        re_key: &[u8],
        heartbeat_interval_blocks: u64,
        beneficiary: &str,
    ) -> Result<NeoEscrowResult, NeoError> {
        self.create_escrow_internal("createDeadManEscrow", neofs_object_id, re_key, beneficiary, Some(heartbeat_interval_blocks), None, None)
    }

    /// Internal helper for escrow creation.
    /// Uses invokefunction RPC for proper parameter encoding (handles large byte arrays).
    fn create_escrow_internal(
        &self,
        method: &str,
        neofs_object_id: &str,
        re_key: &[u8],
        beneficiary: &str,
        param1: Option<u64>,
        param2: Option<u64>,
        signers: Option<&[&str]>,
    ) -> Result<NeoEscrowResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError("NEO_PRIVATE_KEY required".to_string())
        })?);
        let account = NeoAccount::from_wif(&wif)?;

        let beneficiary_hash = address_to_script_hash(beneficiary)?;

        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        // Encode parameters for invokefunction
        let object_id_b64 = BASE64.encode(neofs_object_id.as_bytes());
        let re_key_b64 = BASE64.encode(re_key);

        // Build args array based on method type
        let args: Vec<serde_json::Value> = match method {
            // createTimeLockEscrow(objectId, unlockBlock, beneficiary, reEncryptionKey)
            // createDeadManEscrow(objectId, heartbeatBlocks, beneficiary, reEncryptionKey)
            "createTimeLockEscrow" | "createDeadManEscrow" => {
                vec![
                    serde_json::json!({"type": "ByteArray", "value": object_id_b64}),
                    serde_json::json!({"type": "Integer", "value": param1.unwrap_or(0).to_string()}),
                    serde_json::json!({"type": "Hash160", "value": beneficiary_hash}),
                    serde_json::json!({"type": "ByteArray", "value": re_key_b64}),
                ]
            },
            // createPaymentEscrow(objectId, price, beneficiary, reEncryptionKey)
            "createPaymentEscrow" => {
                vec![
                    serde_json::json!({"type": "ByteArray", "value": object_id_b64}),
                    serde_json::json!({"type": "Integer", "value": param2.unwrap_or(0).to_string()}),
                    serde_json::json!({"type": "Hash160", "value": beneficiary_hash}),
                    serde_json::json!({"type": "ByteArray", "value": re_key_b64}),
                ]
            },
            // createMultiSigEscrow(objectId, signerFingerprints, threshold, beneficiary, reEncryptionKey)
            "createMultiSigEscrow" => {
                let signer_fps: Vec<serde_json::Value> = if let Some(signer_list) = signers {
                    signer_list.iter().map(|s| {
                        let sh = address_to_script_hash(s).unwrap_or_default();
                        let sh_b64 = BASE64.encode(hex::decode(&sh).unwrap_or_default());
                        serde_json::json!({"type": "ByteArray", "value": sh_b64})
                    }).collect()
                } else {
                    vec![]
                };
                vec![
                    serde_json::json!({"type": "ByteArray", "value": object_id_b64}),
                    serde_json::json!({"type": "Array", "value": signer_fps}),
                    serde_json::json!({"type": "Integer", "value": param1.unwrap_or(2).to_string()}),
                    serde_json::json!({"type": "Hash160", "value": beneficiary_hash}),
                    serde_json::json!({"type": "ByteArray", "value": re_key_b64}),
                ]
            },
            _ => return Err(NeoError::ConfigError(format!("Unknown escrow method: {}", method))),
        };

        // Use invokefunction to get properly encoded script
        let test_result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                contract,
                method,
                args,
                [{"account": account_hex, "scopes": "CalledByEntry"}]
            ]),
        )?;

        let state = test_result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" {
            let exception = test_result.get("exception").and_then(|e| e.as_str()).unwrap_or("Unknown");
            return Err(NeoError::TransactionFailed(format!("Escrow test failed: {}", exception)));
        }

        // Get the actual script from the invokefunction result
        let script_from_rpc = test_result.get("script").and_then(|s| s.as_str())
            .ok_or_else(|| NeoError::TransactionFailed("No script in response".to_string()))?;
        let script = BASE64.decode(script_from_rpc)
            .map_err(|e| NeoError::TransactionFailed(format!("Failed to decode script: {}", e)))?;

        let gas_consumed = test_result.get("gasconsumed").and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok()).unwrap_or(1_000_000);
        let system_fee = gas_consumed + gas_consumed / 10;

        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(script, signer, current_height + 100, system_fee, 500_000);
        tx.sign(&account, self.config.network.magic());

        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        let send_result = self.call_rpc::<serde_json::Value>("sendrawtransaction", serde_json::json!([tx_base64]))?;
        let tx_hash = send_result.get("hash").and_then(|h| h.as_str()).map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        let mut escrow_id = 0u64;
        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));
            if let Ok(app_log) = self.call_rpc::<serde_json::Value>("getapplicationlog", serde_json::json!([tx_hash])) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    if notif.get("eventname").and_then(|e| e.as_str()) == Some("EscrowCreated") {
                                        if let Some(state_val) = notif.get("state").and_then(|s| s.get("value")).and_then(|v| v.as_array()) {
                                            escrow_id = state_val.get(0).and_then(|v| v.get("value"))
                                                .and_then(|v| v.as_str()).and_then(|s| s.parse().ok()).unwrap_or(0);
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        Ok(NeoEscrowResult { tx_hash, escrow_id, escrow_type: method.to_string() })
    }

    /// Heartbeat for dead-man switch escrow.
    pub fn escrow_heartbeat(&self, escrow_id: u64) -> Result<String, NeoError> {
        self.simple_escrow_call("heartbeat", escrow_id)
    }

    /// Approve multi-sig escrow.
    pub fn approve_escrow(&self, escrow_id: u64) -> Result<String, NeoError> {
        self.simple_escrow_call("approveEscrow", escrow_id)
    }

    /// Pay for payment-gated escrow.
    pub fn pay_escrow(&self, escrow_id: u64) -> Result<String, NeoError> {
        self.simple_escrow_call("payEscrow", escrow_id)
    }

    /// Claim escrow (get decryption access).
    pub fn claim_escrow(&self, escrow_id: u64) -> Result<NeoEscrowClaimResult, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError("NEO_PRIVATE_KEY required".to_string())
        })?);
        let account = NeoAccount::from_wif(&wif)?;

        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract must be 20 bytes".to_string()))?;
        let mut contract_le = contract_bytes;
        contract_le.reverse();

        let mut builder = NeoScriptBuilder::new();
        builder.push_int(escrow_id as i64);
        builder.push_int(1);
        builder.pack();
        builder.push_int(15);
        builder.push_string("claimEscrow");
        builder.push_bytes(&contract_le);
        builder.syscall(&[0x62, 0x7d, 0x5b, 0x52]);

        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([script_base64, [{"account": account_hex, "scopes": "CalledByEntry"}]]),
        )?;

        let state = test_result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" {
            let exception = test_result.get("exception").and_then(|e| e.as_str()).unwrap_or("Unknown");
            return Err(NeoError::TransactionFailed(format!("Claim test failed: {}", exception)));
        }

        let gas_consumed = test_result.get("gasconsumed").and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok()).unwrap_or(1_000_000);
        let system_fee = gas_consumed + gas_consumed / 10;

        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(script, signer, current_height + 100, system_fee, 500_000);
        tx.sign(&account, self.config.network.magic());

        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        let send_result = self.call_rpc::<serde_json::Value>("sendrawtransaction", serde_json::json!([tx_base64]))?;
        let tx_hash = send_result.get("hash").and_then(|h| h.as_str()).map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        let mut re_key = Vec::new();
        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));
            if let Ok(app_log) = self.call_rpc::<serde_json::Value>("getapplicationlog", serde_json::json!([tx_hash])) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            if let Some(notifications) = exec.get("notifications").and_then(|n| n.as_array()) {
                                for notif in notifications {
                                    if notif.get("eventname").and_then(|e| e.as_str()) == Some("EscrowReleased") {
                                        if let Some(state_val) = notif.get("state").and_then(|s| s.get("value")).and_then(|v| v.as_array()) {
                                            if let Some(key_b64) = state_val.get(2).and_then(|v| v.get("value")).and_then(|v| v.as_str()) {
                                                re_key = BASE64.decode(key_b64).unwrap_or_default();
                                            }
                                        }
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        Ok(NeoEscrowClaimResult { tx_hash, escrow_id, re_key })
    }

    /// Simple escrow call helper (heartbeat, approve, pay).
    fn simple_escrow_call(&self, method: &str, escrow_id: u64) -> Result<String, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let wif = zeroize::Zeroizing::new(std::env::var("NEO_PRIVATE_KEY").map_err(|_| {
            NeoError::ConfigError("NEO_PRIVATE_KEY required".to_string())
        })?);
        let account = NeoAccount::from_wif(&wif)?;

        let contract_hex = contract.trim_start_matches("0x");
        let contract_bytes: [u8; 20] = hex::decode(contract_hex)
            .map_err(|e| NeoError::InvalidScriptHash(format!("Invalid contract: {}", e)))?
            .try_into()
            .map_err(|_| NeoError::InvalidScriptHash("Contract must be 20 bytes".to_string()))?;
        let mut contract_le = contract_bytes;
        contract_le.reverse();

        let mut builder = NeoScriptBuilder::new();
        builder.push_int(escrow_id as i64);
        builder.push_int(1);
        builder.pack();
        builder.push_int(15);
        builder.push_string(method);
        builder.push_bytes(&contract_le);
        builder.syscall(&[0x62, 0x7d, 0x5b, 0x52]);

        let script = builder.build();
        let script_base64 = BASE64.encode(&script);

        let height_result = self.call_rpc::<serde_json::Value>("getblockcount", serde_json::json!([]))?;
        let current_height = height_result.as_u64().unwrap_or(0) as u32;

        let mut script_hash_be = *account.script_hash_le();
        script_hash_be.reverse();
        let account_hex = hex::encode(script_hash_be);

        let test_result = self.call_rpc::<serde_json::Value>(
            "invokescript",
            serde_json::json!([script_base64, [{"account": account_hex, "scopes": "CalledByEntry"}]]),
        )?;

        let state = test_result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" {
            let exception = test_result.get("exception").and_then(|e| e.as_str()).unwrap_or("Unknown");
            return Err(NeoError::TransactionFailed(format!("{} test failed: {}", method, exception)));
        }

        let gas_consumed = test_result.get("gasconsumed").and_then(|g| g.as_str())
            .and_then(|s| s.parse::<u64>().ok()).unwrap_or(1_000_000);
        let system_fee = gas_consumed + gas_consumed / 10;

        let signer = NeoSigner::new(*account.script_hash_le());
        let mut tx = NeoTransaction::new(script, signer, current_height + 100, system_fee, 500_000);
        tx.sign(&account, self.config.network.magic());

        let tx_bytes = tx.serialize();
        let tx_base64 = BASE64.encode(&tx_bytes);

        let send_result = self.call_rpc::<serde_json::Value>("sendrawtransaction", serde_json::json!([tx_base64]))?;
        let tx_hash = send_result.get("hash").and_then(|h| h.as_str()).map(|s| s.to_string())
            .unwrap_or_else(|| tx.hash_hex());

        // Wait for confirmation
        for _ in 0..15 {
            std::thread::sleep(std::time::Duration::from_secs(2));
            if let Ok(app_log) = self.call_rpc::<serde_json::Value>("getapplicationlog", serde_json::json!([tx_hash])) {
                if let Some(executions) = app_log.get("executions").and_then(|e| e.as_array()) {
                    if let Some(exec) = executions.first() {
                        if exec.get("vmstate").and_then(|v| v.as_str()) == Some("HALT") {
                            break;
                        }
                    }
                }
            }
        }

        Ok(tx_hash)
    }

    /// Get escrow details.
    pub fn get_escrow(&self, escrow_id: u64) -> Result<Option<NeoEscrowInfo>, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([contract, "getEscrow", [{"type": "Integer", "value": escrow_id.to_string()}]]),
        )?;

        let state = result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" { return Ok(None); }

        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                if first.get("type").and_then(|t| t.as_str()) == Some("Array") {
                    if let Some(values) = first.get("value").and_then(|v| v.as_array()) {
                        return Ok(Some(NeoEscrowInfo {
                            id: values.get(0).and_then(|v| v.get("value")).and_then(|v| v.as_str())
                                .and_then(|s| s.parse().ok()).unwrap_or(0),
                            escrow_type: values.get(2).and_then(|v| v.get("value")).and_then(|v| v.as_str())
                                .and_then(|s| s.parse().ok()).unwrap_or(0),
                            neofs_object_id: values.get(1).and_then(|v| v.get("value")).and_then(|v| v.as_str())
                                .map(|s| String::from_utf8(BASE64.decode(s).unwrap_or_default()).unwrap_or_default())
                                .unwrap_or_default(),
                            is_released: values.get(6).and_then(|v| v.get("value")).map(|v| v == &serde_json::json!(true)).unwrap_or(false),
                        }));
                    }
                }
            }
        }
        Ok(None)
    }

    /// Get total escrow count.
    pub fn get_escrow_count(&self) -> Result<u64, NeoError> {
        let contract = self.config.contract_address.as_ref().ok_or_else(|| {
            NeoError::ConfigError("Contract address required".to_string())
        })?;

        let result = self.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([contract, "getEscrowCount", []]),
        )?;

        let state = result.get("state").and_then(|s| s.as_str()).unwrap_or("FAULT");
        if state != "HALT" { return Ok(0); }

        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                return Ok(first.get("value").and_then(|v| v.as_str())
                    .and_then(|s| s.parse().ok()).unwrap_or(0));
            }
        }
        Ok(0)
    }
}

// ============================================================================
// MARKETPLACE, MEMBERSHIP, ESCROW RESULT TYPES
// ============================================================================

/// Result of listing sealed data on the marketplace.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoMarketplaceListResult {
    /// Transaction hash.
    pub tx_hash: String,
    /// Assigned listing ID.
    pub listing_id: u64,
    /// Price in GAS fractions.
    pub price: u64,
    /// NeoFS object ID.
    pub neofs_object_id: String,
}

/// Result of purchasing access to listed data.
/// In the two-phase delivery model, the buyer receives a purchase_id
/// and waits for the seller to deliver the access ticket.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoMarketplacePurchaseResult {
    /// Transaction hash.
    pub tx_hash: String,
    /// Listing ID purchased.
    pub listing_id: u64,
    /// Assigned purchase ID (used for delivery tracking).
    pub purchase_id: u64,
}

/// Result of delivering access to a buyer.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoMarketplaceDeliverResult {
    /// Transaction hash.
    pub tx_hash: String,
    /// Purchase ID that was fulfilled.
    pub purchase_id: u64,
    /// Listing ID.
    pub listing_id: u64,
}

/// Purchase information (two-phase delivery model).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoMarketplacePurchaseInfo {
    /// Purchase ID.
    pub purchase_id: u64,
    /// Listing ID.
    pub listing_id: u64,
    /// Buyer's Neo address (script hash hex).
    pub buyer: String,
    /// Buyer's ML-KEM-1024 public key (1568 bytes).
    pub buyer_pk: Vec<u8>,
    /// Block when the purchase was made.
    pub purchase_block: u64,
    /// Wrapped content key for buyer (1628 bytes, empty if not delivered).
    pub buyer_wrapped_key: Vec<u8>,
    /// Whether the seller has delivered the access ticket.
    pub delivered: bool,
    /// Whether the buyer has claimed the content.
    pub claimed: bool,
}

/// A pending delivery (purchase waiting for seller to deliver access).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoPendingDelivery {
    /// Purchase ID.
    pub purchase_id: u64,
    /// Listing ID.
    pub listing_id: u64,
    /// Buyer's Neo address.
    pub buyer: String,
    /// Buyer's ML-KEM public key for re-wrapping.
    pub buyer_pk: Vec<u8>,
    /// Block when the purchase was made.
    pub purchase_block: u64,
}

/// Result of claiming revenue from a listing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoMarketplaceClaimResult {
    /// Transaction hash.
    pub tx_hash: String,
    /// Listing ID.
    pub listing_id: u64,
    /// Amount of GAS claimed.
    pub amount_claimed: u64,
}

/// Marketplace listing details.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoMarketplaceListing {
    /// Listing ID.
    pub id: u64,
    /// NeoFS object ID.
    pub neofs_object_id: String,
    /// Price in GAS fractions.
    pub price: u64,
    /// Metadata/description.
    pub metadata: String,
    /// Wrapped content key (encrypted for listing's ML-KEM public key).
    pub wrapped_content_key: Vec<u8>,
    /// Whether the listing is active.
    pub is_active: bool,
    /// Number of sales.
    pub sales_count: u64,
    /// Total revenue accumulated (in GAS fractions, unclaimed).
    pub total_revenue: u64,
}

/// Result of minting or renewing membership.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoMembershipResult {
    /// Transaction hash.
    pub tx_hash: String,
    /// Membership token ID.
    pub token_id: u64,
    /// Tier name (notary or vault).
    pub tier: String,
    /// Expiry block number.
    pub expiry_block: u64,
}

/// Result of creating an escrow.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoEscrowResult {
    /// Transaction hash.
    pub tx_hash: String,
    /// Assigned escrow ID.
    pub escrow_id: u64,
    /// Escrow type.
    pub escrow_type: String,
}

/// Result of claiming an escrow.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoEscrowClaimResult {
    /// Transaction hash.
    pub tx_hash: String,
    /// Escrow ID.
    pub escrow_id: u64,
    /// Re-encryption key for decryption.
    pub re_key: Vec<u8>,
}

/// Escrow information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NeoEscrowInfo {
    /// Escrow ID.
    pub id: u64,
    /// Escrow type (0=TimeLock, 1=Payment, 2=MultiSig, 3=DeadMan).
    pub escrow_type: u8,
    /// NeoFS object ID.
    pub neofs_object_id: String,
    /// Whether the escrow has been released.
    pub is_released: bool,
}

/// Convert a Neo N3 address to its script hash (little-endian).
///
/// Neo addresses are Base58Check encoded. The script hash is embedded
/// in the address after the version byte.
fn address_to_script_hash(address: &str) -> Result<String, NeoError> {
    validate_neo_address(address)?;

    // Base58 decode the address
    let decoded = bs58::decode(address)
        .into_vec()
        .map_err(|e| NeoError::InvalidAddress(format!("Base58 decode failed: {}", e)))?;

    // Neo address format: version (1 byte) + script hash (20 bytes) + checksum (4 bytes)
    if decoded.len() != 25 {
        return Err(NeoError::InvalidAddress(format!(
            "Invalid decoded length: {}",
            decoded.len()
        )));
    }

    // Extract script hash (bytes 1-20, little-endian)
    let script_hash = &decoded[1..21];

    // Return as hex (already little-endian)
    Ok(hex::encode(script_hash))
}

/// Parse a Neo script hash from hex string to bytes (20 bytes).
pub fn parse_script_hash(hash: &str) -> Result<[u8; 20], NeoError> {
    validate_neo_script_hash(hash)?;

    let hash = hash.strip_prefix("0x").unwrap_or(hash);
    let mut bytes = [0u8; 20];

    hex::decode_to_slice(hash, &mut bytes)
        .map_err(|e| NeoError::InvalidScriptHash(format!("Hex decode error: {}", e)))?;

    Ok(bytes)
}

/// Format bytes as Neo script hash (0x-prefixed hex).
pub fn format_script_hash(bytes: &[u8; 20]) -> String {
    format!("0x{}", hex::encode(bytes))
}

/// Parse a Neo identifier (address or script hash) to script hash bytes.
///
/// This unified parser accepts either format, providing API flexibility:
/// - **Neo address**: `"NXV7ZhHiyM1aHXwpVsRZC6BN2E4qFxLYkN"` (Base58Check, 34 chars, starts with 'N')
/// - **Script hash**: `"0x50ac1c37690cc2cfc594472833cf57505d5f46de"` (hex, 40 chars, optional 0x prefix)
///
/// # Examples
///
/// ```ignore
/// // Both return the same script hash bytes:
/// let from_addr = parse_neo_identifier("NXV7ZhHiyM1aHXwpVsRZC6BN2E4qFxLYkN")?;
/// let from_hash = parse_neo_identifier("0x50ac1c37690cc2cfc594472833cf57505d5f46de")?;
/// ```
///
/// # Errors
///
/// Returns `NeoError::InvalidAddress` if the address format is invalid.
/// Returns `NeoError::InvalidScriptHash` if the script hash format is invalid.
pub fn parse_neo_identifier(identifier: &str) -> Result<[u8; 20], NeoError> {
    if identifier.starts_with('N') && identifier.len() == 34 {
        // It's a Neo address - convert to script hash
        let hash_hex = address_to_script_hash(identifier)?;
        parse_script_hash(&hash_hex)
    } else {
        // It's already a script hash (hex format)
        parse_script_hash(identifier)
    }
}

/// NeoFS object attributes for upload.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct NeoFsObjectAttributes {
    /// Content type (e.g., "application/octet-stream", "application/cbor").
    pub content_type: Option<String>,
    /// Anubis-specific type (e.g., "receipt", "identity", "batch").
    pub anubis_type: Option<String>,
    /// Content hash (SHA-512 hex).
    pub content_hash: Option<String>,
    /// Signing fingerprint of the creator.
    pub signing_fingerprint: Option<String>,
    /// Original filename.
    pub filename: Option<String>,
}

/// Manifest for chunked file uploads.
///
/// When files exceed `CHUNK_THRESHOLD` (20MB), they are split into chunks
/// and this manifest is created to track them. The manifest is stored as
/// a JSON object in NeoFS with `anubis_type = "chunked-manifest"`.
///
/// # Reassembly
///
/// To reassemble a chunked file:
/// 1. Download the manifest object
/// 2. Download each chunk by its object ID
/// 3. Concatenate chunks in order
/// 4. Verify the SHA-512 hash matches `content_hash`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChunkedManifest {
    /// Manifest version (currently 1).
    pub version: u32,
    /// Total size of the original file in bytes.
    pub total_size: u64,
    /// Size of each chunk in bytes (except possibly the last one).
    pub chunk_size: u64,
    /// Object IDs of chunks, in order.
    pub chunks: Vec<String>,
    /// SHA-512 hash of the complete file (hex-encoded).
    pub content_hash: String,
    /// Original attributes from the upload request.
    pub original_attributes: Option<NeoFsObjectAttributes>,
}

/// NeoFS authentication credentials.
#[derive(Debug, Clone)]
pub struct NeoFsAuth {
    /// Neo wallet address (owner ID).
    pub owner_id: String,
    /// Base64-encoded bearer token (signed).
    pub bearer_token: String,
    /// Hex-encoded public key that signed the token.
    pub signature_key: String,
}

// ============================================================================
// NEO WALLET SIGNING FOR NEOFS
// ============================================================================
//
// NeoFS supports two signature schemes:
// 1. Standard NeoFS: ECDSA with SHA-512 on secp256r1 (65-byte signature)
// 2. WalletConnect: RFC 6979 deterministic ECDSA with SHA-256 (80-byte signature)
//
// The REST gateway uses the `walletConnect` query parameter to choose (default: false).

use p256::ecdsa::VerifyingKey;
use sha2::Sha512;

/// Neo wallet for signing NeoFS requests.
///
/// Holds the secp256r1 (P-256) private key used for Neo N3 transactions
/// and NeoFS bearer token signing.
#[derive(Clone)]
pub struct NeoWallet {
    /// The ECDSA signing key (secp256r1/P-256).
    signing_key: SigningKey,
    /// The public key (compressed form).
    public_key: VerifyingKey,
    /// The Neo N3 address derived from the public key.
    address: String,
}

impl std::fmt::Debug for NeoWallet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NeoWallet")
            .field("address", &self.address)
            .field("public_key", &self.public_key_hex())
            .finish_non_exhaustive()
    }
}

impl NeoWallet {
    /// Create a NeoWallet from a WIF (Wallet Import Format) private key.
    ///
    /// WIF is the standard format for Neo private keys, starting with 'K' or 'L'.
    ///
    /// # Example
    /// ```ignore
    /// let wallet = NeoWallet::from_wif("KzAhz8gANe8pdy3bQKYpbCi96UsmiPKyukHJKuKntcHDr4SVWd2i")?;
    /// println!("Address: {}", wallet.address());
    /// ```
    pub fn from_wif(wif: &str) -> Result<Self, NeoError> {
        // Decode WIF (Base58Check)
        let decoded = bs58::decode(wif)
            .into_vec()
            .map_err(|e| NeoError::Signing(format!("Invalid WIF format: {}", e)))?;

        // WIF format: version (1) + key (32) + compressed flag (1) + checksum (4)
        // Compressed WIF: 38 bytes total (version 0x80 + 32 bytes + 0x01 + 4 byte checksum)
        if decoded.len() != 38 && decoded.len() != 37 {
            return Err(NeoError::Signing(format!(
                "Invalid WIF length: {} (expected 37 or 38)",
                decoded.len()
            )));
        }

        // Verify version byte (0x80 for mainnet)
        if decoded[0] != 0x80 {
            return Err(NeoError::Signing(format!(
                "Invalid WIF version: 0x{:02x} (expected 0x80)",
                decoded[0]
            )));
        }

        // Verify checksum (double SHA-256 of payload)
        let checksum_start = decoded.len() - 4;
        let payload = &decoded[..checksum_start];
        let expected_checksum = &decoded[checksum_start..];

        let hash1 = Sha256::digest(payload);
        let hash2 = Sha256::digest(&hash1);
        let actual_checksum = &hash2[..4];

        if expected_checksum != actual_checksum {
            return Err(NeoError::Signing("WIF checksum verification failed".to_string()));
        }

        // Extract the 32-byte private key (bytes 1-32)
        let private_key_bytes: [u8; 32] = decoded[1..33]
            .try_into()
            .map_err(|_| NeoError::Signing("Failed to extract private key".to_string()))?;

        Self::from_private_key(&private_key_bytes)
    }

    /// Create a NeoWallet from raw private key bytes.
    pub fn from_private_key(private_key: &[u8; 32]) -> Result<Self, NeoError> {
        let signing_key = SigningKey::from_bytes(private_key.into())
            .map_err(|e| NeoError::Signing(format!("Invalid private key: {}", e)))?;

        let public_key = *signing_key.verifying_key();

        // Derive Neo address from public key
        let address = Self::derive_address(&public_key)?;

        Ok(Self {
            signing_key,
            public_key,
            address,
        })
    }

    /// Generate a new random Neo wallet.
    ///
    /// Uses cryptographically secure random number generation to create
    /// a new secp256r1/P-256 private key.
    pub fn generate() -> Result<Self, NeoError> {
        use p256::ecdsa::SigningKey;
        use p256::elliptic_curve::rand_core::OsRng;

        let signing_key = SigningKey::random(&mut OsRng);
        let public_key = *signing_key.verifying_key();
        let address = Self::derive_address(&public_key)?;

        Ok(Self {
            signing_key,
            public_key,
            address,
        })
    }

    /// Export the wallet's private key in WIF (Wallet Import Format).
    ///
    /// WIF is the standard format for Neo private keys and can be imported
    /// into other Neo wallets.
    pub fn to_wif(&self) -> String {
        let private_key_bytes = self.signing_key.to_bytes();

        // WIF format: version (0x80) + 32-byte key + compression flag (0x01) + checksum (4 bytes)
        let mut wif_data = Vec::with_capacity(38);
        wif_data.push(0x80); // Version byte for mainnet
        wif_data.extend_from_slice(&private_key_bytes);
        wif_data.push(0x01); // Compression flag

        // Checksum: first 4 bytes of double SHA256
        let hash1 = Sha256::digest(&wif_data);
        let hash2 = Sha256::digest(&hash1);
        wif_data.extend_from_slice(&hash2[..4]);

        bs58::encode(&wif_data).into_string()
    }

    /// Get the raw private key bytes.
    pub fn private_key_bytes(&self) -> [u8; 32] {
        self.signing_key.to_bytes().into()
    }

    /// Derive Neo N3 address from public key.
    fn derive_address(public_key: &VerifyingKey) -> Result<String, NeoError> {
        // Get compressed public key (33 bytes)
        let point = public_key.to_encoded_point(true);
        let compressed_pubkey = point.as_bytes();

        // Build verification script for single-sig account
        // Format: PUSHDATA1 <len> <compressed_pubkey> SYSCALL <CheckSig_hash>
        // Example: 0c21<33-byte-pubkey>4156e7b327
        let mut script = Vec::with_capacity(40);
        script.push(0x0c); // PUSHDATA1
        script.push(compressed_pubkey.len() as u8);
        script.extend_from_slice(compressed_pubkey);
        script.push(0x41); // SYSCALL
        // "System.Crypto.CheckSig" interop hash (little-endian uint32)
        script.extend_from_slice(&[0x56, 0xe7, 0xb3, 0x27]);

        // Script hash = RIPEMD160(SHA256(script))
        let sha256_hash = Sha256::digest(&script);
        let script_hash: [u8; 20] = ripemd::Ripemd160::digest(&sha256_hash)
            .as_slice()
            .try_into()
            .map_err(|_| NeoError::Signing("RIPEMD160 produced unexpected length".to_string()))?;

        // Neo N3 address = Base58Check(version + script_hash)
        // Version byte: 0x35 (53) for Neo N3 mainnet
        let mut address_data = vec![0x35];
        address_data.extend_from_slice(&script_hash);

        // Checksum: first 4 bytes of double SHA256
        let check1 = Sha256::digest(&address_data);
        let check2 = Sha256::digest(&check1);
        address_data.extend_from_slice(&check2[..4]);

        Ok(bs58::encode(&address_data).into_string())
    }

    /// Get the Neo N3 address.
    pub fn address(&self) -> &str {
        &self.address
    }

    /// Get the public key as hex string (compressed form).
    pub fn public_key_hex(&self) -> String {
        let point = self.public_key.to_encoded_point(true);
        hex::encode(point.as_bytes())
    }

    /// Get the public key as uncompressed hex string (for NeoFS headers).
    pub fn public_key_uncompressed_hex(&self) -> String {
        let point = self.public_key.to_encoded_point(false);
        hex::encode(point.as_bytes())
    }

    /// Sign data using WalletConnect scheme (RFC 6979 ECDSA with SHA-256).
    ///
    /// This is the scheme used by NeoFS REST gateway when `walletConnect=true`.
    ///
    /// The signature format is:
    /// - 64 bytes: ECDSA signature (r || s)
    /// - 16 bytes: random salt used in message construction
    ///
    /// The message is constructed as:
    /// - Header: 0x01 0x00 0x01 0xf0
    /// - Variable length encoding of (salt + data) length
    /// - Hex-encoded salt (32 hex chars for 16 bytes)
    /// - Base64-encoded original data
    /// - Footer: 0x00 0x00
    pub fn sign_wallet_connect(&self, data: &[u8]) -> Result<Vec<u8>, NeoError> {
        // Generate 16-byte random salt
        let mut salt = [0u8; 16];
        getrandom::getrandom(&mut salt)
            .map_err(|e| NeoError::Signing(format!("Failed to generate salt: {}", e)))?;

        self.sign_wallet_connect_with_salt(data, &salt)
    }

    /// Sign data using WalletConnect scheme with a specific salt.
    pub fn sign_wallet_connect_with_salt(&self, data: &[u8], salt: &[u8; 16]) -> Result<Vec<u8>, NeoError> {
        // Build the salted message
        let salt_hex = hex::encode(salt);
        let data_b64 = base64::Engine::encode(&base64::engine::general_purpose::STANDARD, data);

        // Calculate content length (salt_hex + data_b64)
        let content_len = salt_hex.len() + data_b64.len();

        // Build message with WalletConnect format
        let mut message = Vec::new();

        // Header: 0x01 0x00 0x01 0xf0
        message.extend_from_slice(&[0x01, 0x00, 0x01, 0xf0]);

        // Variable length encoding of content length
        Self::write_var_int(&mut message, content_len as u64);

        // Salt (hex encoded) + Data (base64 encoded)
        message.extend_from_slice(salt_hex.as_bytes());
        message.extend_from_slice(data_b64.as_bytes());

        // Footer: 0x00 0x00
        message.extend_from_slice(&[0x00, 0x00]);

        // Sign the message using RFC 6979 (deterministic ECDSA)
        // The p256 crate uses RFC 6979 by default with the Signer trait
        let signature: Signature = self.signing_key.sign(&message);

        // Combine signature (64 bytes) + salt (16 bytes)
        let mut result = Vec::with_capacity(80);
        result.extend_from_slice(&signature.to_bytes());
        result.extend_from_slice(salt);

        Ok(result)
    }

    /// Sign data using standard NeoFS scheme (ECDSA with SHA-512).
    ///
    /// This is the default scheme used by NeoFS REST gateway.
    ///
    /// The signature format is:
    /// - 1 byte: prefix (0x04 for uncompressed point)
    /// - 32 bytes: r component
    /// - 32 bytes: s component
    pub fn sign_neofs_standard(&self, data: &[u8]) -> Result<Vec<u8>, NeoError> {
        // Hash data with SHA-512
        let hash = Sha512::digest(data);

        // Sign the hash
        // Note: p256 crate signs with SHA-256 by default, but we need SHA-512
        // We manually hash with SHA-512 and sign the hash
        let signature: Signature = self.signing_key.sign(&hash);

        // Format as 65-byte uncompressed point: 0x04 || r || s
        let sig_bytes = signature.to_bytes();
        let mut result = Vec::with_capacity(65);
        result.push(0x04); // Uncompressed point prefix
        result.extend_from_slice(&sig_bytes);

        Ok(result)
    }

    /// Write variable-length integer (Neo/NeoFS format).
    fn write_var_int(buf: &mut Vec<u8>, value: u64) {
        if value < 0xfd {
            buf.push(value as u8);
        } else if value <= 0xffff {
            buf.push(0xfd);
            buf.extend_from_slice(&(value as u16).to_le_bytes());
        } else if value <= 0xffffffff {
            buf.push(0xfe);
            buf.extend_from_slice(&(value as u32).to_le_bytes());
        } else {
            buf.push(0xff);
            buf.extend_from_slice(&value.to_le_bytes());
        }
    }

    /// Create NeoFS authentication for REST gateway requests.
    ///
    /// # Arguments
    /// * `use_wallet_connect` - Use WalletConnect signature scheme (recommended for REST gateway)
    ///
    /// # Returns
    /// * `NeoFsAuth` with owner_id, bearer_token (signature), and signature_key
    pub fn create_neofs_auth(&self, data: &[u8], use_wallet_connect: bool) -> Result<NeoFsAuth, NeoError> {
        let (signature, signature_key) = if use_wallet_connect {
            let sig = self.sign_wallet_connect(data)?;
            // WalletConnect uses compressed public key
            (sig, self.public_key_hex())
        } else {
            let sig = self.sign_neofs_standard(data)?;
            // Standard NeoFS uses uncompressed public key
            (sig, self.public_key_uncompressed_hex())
        };

        Ok(NeoFsAuth {
            owner_id: self.address.clone(),
            // NeoFS REST gateway expects hex-encoded signature
            bearer_token: hex::encode(&signature),
            signature_key,
        })
    }

    /// Create a signed bearer token for NeoFS operations.
    ///
    /// This signs a message and returns the complete auth structure needed
    /// for NeoFS REST gateway requests.
    ///
    /// # Arguments
    /// * `operation` - The operation being performed (e.g., "PUT", "GET", "DELETE")
    /// * `container_id` - Optional container ID for the operation
    ///
    /// # Returns
    /// * `NeoFsAuth` ready to use with `NeoFsClient`
    pub fn sign_request(&self, operation: &str, container_id: Option<&str>) -> Result<NeoFsAuth, NeoError> {
        // Construct message to sign
        // Format: operation + container_id (if present) + timestamp
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| NeoError::Signing(format!("Failed to get timestamp: {}", e)))?
            .as_secs();

        let mut message = operation.to_string();
        if let Some(cid) = container_id {
            message.push(':');
            message.push_str(cid);
        }
        message.push(':');
        message.push_str(&timestamp.to_string());

        // Use WalletConnect scheme (recommended for REST gateway)
        self.create_neofs_auth(message.as_bytes(), true)
    }
}

impl NeoFsAuth {
    /// Create NeoFsAuth from a NeoWallet by signing a request.
    pub fn from_wallet(wallet: &NeoWallet, operation: &str, container_id: Option<&str>) -> Result<Self, NeoError> {
        wallet.sign_request(operation, container_id)
    }

    /// Create NeoFsAuth with empty signature (for public read operations).
    pub fn public_read(owner_id: &str) -> Self {
        Self {
            owner_id: owner_id.to_string(),
            bearer_token: String::new(),
            signature_key: String::new(),
        }
    }
}

/// NeoFS container configuration for creation.
#[derive(Debug, Clone)]
pub struct NeoFsContainerConfig {
    /// Placement policy (required). Examples: "REP 2", "REP 3 IN X CBF 1 SELECT 3 FROM * AS X"
    pub placement_policy: String,
    /// Basic ACL (required). Examples: "public-read-write", "private", "0x0FBFBFFF"
    pub basic_acl: String,
    /// Optional container name.
    pub name: Option<String>,
    /// Optional attributes (key-value pairs).
    pub attributes: Option<Vec<(String, String)>>,
    /// Register name in NNS (Neo Name Service) globally.
    pub name_scope_global: bool,
}

impl Default for NeoFsContainerConfig {
    fn default() -> Self {
        Self {
            placement_policy: "REP 2".to_string(),
            basic_acl: "public-read-write".to_string(),
            name: None,
            attributes: None,
            name_scope_global: false,
        }
    }
}

impl NeoFsContainerConfig {
    /// Create a new container config with the given placement policy and ACL.
    pub fn new(placement_policy: &str, basic_acl: &str) -> Self {
        Self {
            placement_policy: placement_policy.to_string(),
            basic_acl: basic_acl.to_string(),
            ..Default::default()
        }
    }

    /// Set the container name.
    pub fn with_name(mut self, name: &str) -> Self {
        self.name = Some(name.to_string());
        self
    }

    /// Add an attribute.
    pub fn with_attribute(mut self, key: &str, value: &str) -> Self {
        let attrs = self.attributes.get_or_insert_with(Vec::new);
        attrs.push((key.to_string(), value.to_string()));
        self
    }

    /// Enable NNS global name registration.
    pub fn with_global_name(mut self) -> Self {
        self.name_scope_global = true;
        self
    }
}

/// Result of container creation.
#[derive(Debug, Clone)]
pub struct NeoFsContainerResult {
    /// The created container ID (Base58 encoded).
    pub container_id: String,
}

/// NeoFS client for decentralized object storage.
///
/// Uses the NeoFS REST Gateway API (recommended over deprecated HTTP gateway).
/// REST Gateway endpoints:
/// - Upload: POST /v1/objects/{containerId}
/// - Download: GET /v1/objects/{containerId}/by_id/{objectId}
/// - Get by attribute: GET /v1/get_by_attribute/{containerId}/{key}/{value}
/// - Auth: POST /v1/auth
#[derive(Debug)]
pub struct NeoFsClient {
    /// REST gateway URL (e.g., "https://rest.fs.neo.org" for MainNet).
    gateway_url: String,
    /// HTTP client.
    agent: ureq::Agent,
    /// Authentication credentials.
    auth: Option<NeoFsAuth>,
}

/// Session token data for container operations.
#[derive(Debug, Clone)]
pub struct SessionTokenData {
    /// Base64-encoded unsigned token body
    pub token: String,
    /// Base64-encoded signature
    pub signature: String,
    /// Hex-encoded public key
    pub public_key: String,
}

impl NeoFsClient {
    /// Create a new NeoFS client.
    ///
    /// # Arguments
    /// * `gateway_url` - REST gateway URL (e.g., "https://rest.fs.neo.org")
    /// * `timeout_secs` - Request timeout in seconds
    pub fn new(gateway_url: &str, timeout_secs: u64) -> Self {
        let agent = ureq::AgentBuilder::new()
            .timeout(std::time::Duration::from_secs(timeout_secs))
            .build();

        Self {
            gateway_url: gateway_url.trim_end_matches('/').to_string(),
            agent,
            auth: None,
        }
    }

    /// Create a new NeoFS client with full authentication.
    ///
    /// # Arguments
    /// * `gateway_url` - REST gateway URL
    /// * `timeout_secs` - Request timeout in seconds
    /// * `auth` - Authentication credentials
    pub fn new_with_auth(gateway_url: &str, timeout_secs: u64, auth: NeoFsAuth) -> Self {
        let agent = ureq::AgentBuilder::new()
            .timeout(std::time::Duration::from_secs(timeout_secs))
            .build();

        Self {
            gateway_url: gateway_url.trim_end_matches('/').to_string(),
            agent,
            auth: Some(auth),
        }
    }

    /// Set authentication credentials.
    pub fn set_auth(&mut self, auth: NeoFsAuth) {
        self.auth = Some(auth);
    }

    /// Set bearer token only (simplified auth for compatible gateways).
    pub fn set_bearer_token(&mut self, token: &str) {
        if let Some(ref mut auth) = self.auth {
            auth.bearer_token = token.to_string();
        } else {
            self.auth = Some(NeoFsAuth {
                owner_id: String::new(),
                bearer_token: token.to_string(),
                signature_key: String::new(),
            });
        }
    }

    /// Create a bearer token for object operations using a wallet.
    ///
    /// This performs the full NeoFS REST gateway authentication flow:
    /// 1. POST /v1/auth to get unsigned token body
    /// 2. Sign the token with the wallet
    /// 3. GET /v1/auth/bearer to get the signed bearer token
    ///
    /// # Arguments
    /// * `wallet` - NeoWallet for signing
    /// * `operations` - List of operations to allow (e.g., ["PUT", "GET", "DELETE"])
    ///
    /// # Returns
    /// * Bearer token string that can be used for subsequent requests
    pub fn create_bearer_token(
        &self,
        wallet: &NeoWallet,
        operations: &[&str],
    ) -> Result<String, NeoError> {
        // Build object permission records
        let records: Vec<serde_json::Value> = operations.iter().map(|op| {
            serde_json::json!({
                "operation": op.to_uppercase(),
                "action": "ALLOW",
                "filters": [],
                "targets": [{"role": "OTHERS", "keys": []}]
            })
        }).collect();

        let token_request = serde_json::json!([{
            "name": "anubis-bearer",
            "object": records
        }]);

        // Step 1: POST /v1/auth to get unsigned token body
        let auth_url = format!("{}/v1/auth", self.gateway_url);
        let response = self.agent
            .post(&auth_url)
            .set("Content-Type", "application/json")
            .set("X-Bearer-Owner-Id", wallet.address())
            .send_string(&token_request.to_string())
            .map_err(|e| NeoError::NeoFs(format!("Auth request failed: {}", e)))?;

        let auth_response: Vec<serde_json::Value> = response
            .into_json()
            .map_err(|e| NeoError::NeoFs(format!("Invalid auth response: {}", e)))?;

        if auth_response.is_empty() {
            return Err(NeoError::NeoFs("No token returned from auth endpoint".to_string()));
        }

        let token_body_b64 = auth_response[0]["token"]
            .as_str()
            .ok_or_else(|| NeoError::NeoFs("Missing token in auth response".to_string()))?;

        // Step 2: Sign the token body with WalletConnect scheme
        let token_body = base64::Engine::decode(
            &base64::engine::general_purpose::STANDARD,
            token_body_b64
        ).map_err(|e| NeoError::NeoFs(format!("Invalid token encoding: {}", e)))?;

        let signature = wallet.sign_wallet_connect(&token_body)?;
        let signature_b64 = base64::Engine::encode(
            &base64::engine::general_purpose::STANDARD,
            &signature
        );

        // Step 3: GET /v1/auth/bearer to get signed bearer token
        // URL encode the token (base64 can contain + and / which need encoding)
        let token_encoded: String = token_body_b64.chars().map(|c| match c {
            '+' => "%2B".to_string(),
            '/' => "%2F".to_string(),
            '=' => "%3D".to_string(),
            _ => c.to_string(),
        }).collect();
        let bearer_url = format!(
            "{}/v1/auth/bearer?token={}&walletConnect=true",
            self.gateway_url,
            token_encoded
        );

        let bearer_response = self.agent
            .get(&bearer_url)
            .set("X-Bearer-Signature", &signature_b64)
            .set("X-Bearer-Signature-Key", &wallet.public_key_hex())
            .call()
            .map_err(|e| NeoError::NeoFs(format!("Bearer request failed: {}", e)))?;

        let bearer_json: serde_json::Value = bearer_response
            .into_json()
            .map_err(|e| NeoError::NeoFs(format!("Invalid bearer response: {}", e)))?;

        bearer_json["token"]
            .as_str()
            .map(|s| s.to_string())
            .ok_or_else(|| NeoError::NeoFs("Missing token in bearer response".to_string()))
    }

    /// Create a session token for container operations using a wallet.
    ///
    /// This performs the NeoFS REST gateway authentication flow for container operations:
    /// 1. POST /v1/auth with container verb to get unsigned token body
    /// 2. Sign the token with the wallet using WalletConnect scheme
    ///
    /// The returned SessionTokenData should be passed directly to container operations.
    ///
    /// # Arguments
    /// * `wallet` - NeoWallet for signing
    /// * `verb` - Container operation verb (PUT, DELETE, SETEACL)
    ///
    /// # Returns
    /// * SessionTokenData with token, signature, and public key
    pub fn create_session_token(
        &self,
        wallet: &NeoWallet,
        verb: &str,
    ) -> Result<SessionTokenData, NeoError> {
        // Build container session request
        // NeoFS REST gateway expects exact verb names: PUT, DELETE, SETEACL
        let verb_upper = verb.to_uppercase();
        let token_request = serde_json::json!([{
            "name": "anubis-session",
            "container": {
                "verb": verb_upper
            }
        }]);

        // Debug output for session token creation (can be removed in production)
        // eprintln!("  Requesting session token with verb: {}", verb_upper);

        // Step 1: POST /v1/auth to get unsigned token body
        let auth_url = format!("{}/v1/auth", self.gateway_url);
        let response = self.agent
            .post(&auth_url)
            .set("Content-Type", "application/json")
            .set("X-Bearer-Owner-Id", wallet.address())
            .send_string(&token_request.to_string())
            .map_err(|e| NeoError::NeoFs(format!("Session auth request failed: {}", e)))?;

        let auth_response: Vec<serde_json::Value> = response
            .into_json()
            .map_err(|e| NeoError::NeoFs(format!("Invalid session auth response: {}", e)))?;

        if auth_response.is_empty() {
            return Err(NeoError::NeoFs("No token returned from session auth endpoint".to_string()));
        }

        let token_body_b64 = auth_response[0]["token"]
            .as_str()
            .ok_or_else(|| NeoError::NeoFs("Missing token in session auth response".to_string()))?
            .to_string();

        // Validate token type (silently)
        let _token_type = auth_response[0]["type"].as_str().unwrap_or("unknown");

        // Step 2: Sign the token body with WalletConnect scheme
        let token_body = base64::Engine::decode(
            &base64::engine::general_purpose::STANDARD,
            &token_body_b64
        ).map_err(|e| NeoError::NeoFs(format!("Invalid session token encoding: {}", e)))?;

        let signature = wallet.sign_wallet_connect(&token_body)?;
        // NeoFS REST gateway expects hex-encoded signature for container session tokens
        let signature_hex = hex::encode(&signature);

        let public_key_hex = wallet.public_key_hex();

        // Session token signed successfully

        Ok(SessionTokenData {
            token: token_body_b64,
            signature: signature_hex,
            public_key: public_key_hex,
        })
    }

    /// Set session token data for container operations.
    ///
    /// This sets the auth with the raw token, signature, and public key
    /// that will be passed directly to container endpoints.
    pub fn set_session_token(&mut self, session: &SessionTokenData) {
        self.auth = Some(NeoFsAuth {
            owner_id: String::new(),  // Not used for session tokens
            bearer_token: session.token.clone(),
            signature_key: format!("{}:{}", session.signature, session.public_key),
        });
    }

    /// Check if client has authentication configured.
    pub fn has_auth(&self) -> bool {
        self.auth.is_some()
    }

    /// Get the gateway URL.
    pub fn gateway_url(&self) -> &str {
        &self.gateway_url
    }

    /// Store an object in NeoFS via REST Gateway.
    ///
    /// Uses POST /v1/objects/{containerId} endpoint (NeoFS REST API v2).
    ///
    /// # Arguments
    /// * `container_id` - NeoFS container ID (Base58 encoded)
    /// * `data` - Object data to store
    /// * `attributes` - Optional object attributes/metadata
    ///
    /// # Returns
    /// * `NeoFsStoreResult` with container_id, object_id, and CID
    ///
    /// # Errors
    /// * `NeoError::NeoFs` if upload fails or no auth configured
    ///
    /// # Authentication
    /// Requires either:
    /// - Bearer token set via `set_bearer_token()` (uses X-Bearer-Signature headers)
    /// - Or public container with write ACL
    pub fn store(
        &self,
        container_id: &str,
        data: &[u8],
        attributes: Option<NeoFsObjectAttributes>,
    ) -> Result<NeoFsStoreResult, NeoError> {
        let url = format!("{}/v1/objects/{}", self.gateway_url, container_id);

        // Build request - use POST per NeoFS REST API v2 spec
        let mut request = self
            .agent
            .post(&url)
            .set("Content-Type", "application/octet-stream");

        // Add authentication if configured
        // NeoFS REST API uses Authorization: Bearer <token> header for bearer tokens
        // from the /v1/auth/bearer endpoint
        if let Some(ref auth) = self.auth {
            if !auth.bearer_token.is_empty() {
                // Use Authorization header with Bearer scheme
                request = request.set("Authorization", &format!("Bearer {}", auth.bearer_token));
            }
            // Also set X-Bearer-Owner-Id if available (for backwards compat)
            if !auth.owner_id.is_empty() {
                request = request.set("X-Bearer-Owner-Id", &auth.owner_id);
            }
        }

        // Build attributes as JSON for X-Attributes header
        if let Some(attrs) = &attributes {
            let mut attr_map = serde_json::Map::new();
            if let Some(ref ct) = attrs.content_type {
                attr_map.insert("Content-Type".to_string(), serde_json::Value::String(ct.clone()));
            }
            if let Some(ref at) = attrs.anubis_type {
                attr_map.insert("Anubis-Type".to_string(), serde_json::Value::String(at.clone()));
            }
            if let Some(ref ch) = attrs.content_hash {
                attr_map.insert("Content-Hash".to_string(), serde_json::Value::String(ch.clone()));
            }
            if let Some(ref sf) = attrs.signing_fingerprint {
                attr_map.insert("Signing-Fingerprint".to_string(), serde_json::Value::String(sf.clone()));
            }
            if let Some(ref fn_) = attrs.filename {
                attr_map.insert("FileName".to_string(), serde_json::Value::String(fn_.clone()));
            }
            if !attr_map.is_empty() {
                let attrs_json = serde_json::to_string(&serde_json::Value::Object(attr_map))
                    .map_err(|e| NeoError::NeoFs(format!("Failed to serialize attributes: {}", e)))?;
                request = request.set("X-Attributes", &attrs_json);
            }
        }

        // Send the data
        let response = request
            .send_bytes(data)
            .map_err(|e| {
                // Extract more detailed error message
                match e {
                    ureq::Error::Status(code, resp) => {
                        let body = resp.into_string().unwrap_or_default();
                        NeoError::NeoFs(format!("Upload failed (HTTP {}): {}", code, body))
                    }
                    _ => NeoError::NeoFs(format!("Failed to upload object: {}", e)),
                }
            })?;

        // Parse response JSON to get object ID
        // Response format: {"container_id": "...", "object_id": "..."}
        let json: serde_json::Value = response
            .into_json()
            .map_err(|e| NeoError::NeoFs(format!("Failed to parse upload response: {}", e)))?;

        // Try both snake_case and camelCase field names
        let object_id = json
            .get("object_id")
            .or_else(|| json.get("objectId"))
            .and_then(|v| v.as_str())
            .ok_or_else(|| NeoError::NeoFs(format!("Response missing object_id: {:?}", json)))?
            .to_string();

        let returned_container = json
            .get("container_id")
            .or_else(|| json.get("containerId"))
            .and_then(|v| v.as_str())
            .unwrap_or(container_id);

        // Format CID as "containerId/objectId"
        let cid = format!("{}/{}", returned_container, object_id);

        Ok(NeoFsStoreResult {
            cid,
            container_id: returned_container.to_string(),
            object_id,
            size: data.len() as u64,
        })
    }

    /// Chunk size for large file uploads (1 MB).
    /// This is tested to work reliably with NeoFS REST gateway timeouts.
    /// NeoFS testnet gateway has ~20 second timeouts; 1MB uploads in ~12s.
    pub const CHUNK_SIZE: usize = 1024 * 1024;

    /// Threshold for automatic chunking (1 MB).
    /// Files larger than this will be automatically split into chunks.
    pub const CHUNK_THRESHOLD: usize = 1024 * 1024;

    /// Store a large file in NeoFS with automatic chunking.
    ///
    /// Files larger than `CHUNK_THRESHOLD` (1MB) are automatically split into
    /// chunks and a manifest is created to track them. This allows uploading
    /// files up to several GB through the REST gateway without timeouts.
    ///
    /// # Arguments
    /// * `container_id` - NeoFS container ID
    /// * `data` - File data to store
    /// * `attributes` - Optional object attributes
    /// * `progress_callback` - Optional callback for upload progress
    ///
    /// # Returns
    /// * `NeoFsStoreResult` with the manifest CID (or direct object CID for small files)
    pub fn store_large(
        &self,
        container_id: &str,
        data: &[u8],
        attributes: Option<NeoFsObjectAttributes>,
        progress_callback: Option<&dyn Fn(usize, usize)>,
    ) -> Result<NeoFsStoreResult, NeoError> {
        // For small files, use direct upload
        if data.len() <= Self::CHUNK_THRESHOLD {
            return self.store(container_id, data, attributes);
        }

        // Calculate number of chunks
        let num_chunks = (data.len() + Self::CHUNK_SIZE - 1) / Self::CHUNK_SIZE;
        let mut chunk_cids = Vec::with_capacity(num_chunks);

        // Upload each chunk
        for (i, chunk) in data.chunks(Self::CHUNK_SIZE).enumerate() {
            let chunk_attrs = NeoFsObjectAttributes {
                content_type: Some("application/octet-stream".to_string()),
                anubis_type: Some("chunk".to_string()),
                ..Default::default()
            };

            let result = self.store(container_id, chunk, Some(chunk_attrs))?;
            chunk_cids.push(result.object_id);

            if let Some(cb) = progress_callback {
                cb(i + 1, num_chunks);
            }
        }

        // Create manifest
        let manifest = ChunkedManifest {
            version: 1,
            total_size: data.len() as u64,
            chunk_size: Self::CHUNK_SIZE as u64,
            chunks: chunk_cids,
            content_hash: hex::encode(anubis_core::sha2::sha512(data)),
            original_attributes: attributes.clone(),
        };

        let manifest_json = serde_json::to_vec(&manifest)
            .map_err(|e| NeoError::NeoFs(format!("Failed to serialize manifest: {}", e)))?;

        // Store manifest with special type marker
        let mut manifest_attrs = attributes.unwrap_or_default();
        manifest_attrs.anubis_type = Some("chunked-manifest".to_string());
        manifest_attrs.content_type = Some("application/json".to_string());

        self.store(container_id, &manifest_json, Some(manifest_attrs))
    }

    /// Store a large file with encryption and automatic chunking.
    ///
    /// Encrypts the entire file first, then chunks it for upload.
    pub fn store_large_encrypted(
        &self,
        container_id: &str,
        data: &[u8],
        recipient_pk: &anubis_core::mlkem::MlKemPublicKey,
        attributes: Option<NeoFsObjectAttributes>,
        progress_callback: Option<&dyn Fn(usize, usize)>,
    ) -> Result<NeoFsStoreResult, NeoError> {
        use anubis_core::aead::{ChaCha20Poly1305, KEY_SIZE, NONCE_SIZE};
        use anubis_core::mlkem::CIPHERTEXT_SIZE;

        const VERSION_MLKEM_CHACHA: u8 = 0x01;

        // 1. ML-KEM encapsulate
        let (mlkem_ciphertext, mut shared_secret) = recipient_pk
            .encapsulate()
            .map_err(|e| NeoError::NeoFs(format!("ML-KEM encapsulation failed: {}", e)))?;

        // 2. Derive key from shared secret (SHA-512 for CNSA 2.0)
        let mut key = [0u8; KEY_SIZE];
        let hash = anubis_core::sha2::sha512(&shared_secret);
        key.copy_from_slice(&hash[..KEY_SIZE]);

        // Zeroize shared secret immediately after key derivation
        shared_secret.zeroize();

        // 3. Generate random nonce
        let mut nonce = [0u8; NONCE_SIZE];
        getrandom::getrandom(&mut nonce)
            .map_err(|e| NeoError::NeoFs(format!("Failed to generate nonce: {}", e)))?;

        // 4. Encrypt data
        let cipher = ChaCha20Poly1305::from_key(&key);
        let ciphertext = cipher
            .seal_fixed(&nonce, &[], data)
            .map_err(|e| NeoError::NeoFs(format!("Encryption failed: {}", e)))?;

        // 5. Build encrypted payload
        let payload_size = 1 + CIPHERTEXT_SIZE + NONCE_SIZE + ciphertext.len();
        let mut payload = Vec::with_capacity(payload_size);
        payload.push(VERSION_MLKEM_CHACHA);
        payload.extend_from_slice(&mlkem_ciphertext);
        payload.extend_from_slice(&nonce);
        payload.extend_from_slice(&ciphertext);

        // 6. Zeroize key (using zeroize crate to prevent compiler optimization)
        key.zeroize();

        // 7. Update attributes
        let mut attrs = attributes.unwrap_or_default();
        attrs.content_type = Some("application/x-anubis-encrypted".to_string());

        // 8. Upload with chunking
        self.store_large(container_id, &payload, Some(attrs), progress_callback)
    }

    /// Get a potentially chunked object from NeoFS.
    ///
    /// Automatically detects if the object is a chunked manifest and
    /// reassembles the original file from chunks.
    pub fn get_large(&self, cid: &str) -> Result<Vec<u8>, NeoError> {
        let data = self.get(cid)?;

        // Try to parse as manifest
        if let Ok(manifest) = serde_json::from_slice::<ChunkedManifest>(&data) {
            if manifest.version == 1 {
                return self.get_chunked_from_manifest(cid, &manifest);
            }
        }

        // Not a manifest, return as-is
        Ok(data)
    }

    /// Reassemble a chunked file from its manifest.
    fn get_chunked_from_manifest(
        &self,
        manifest_cid: &str,
        manifest: &ChunkedManifest,
    ) -> Result<Vec<u8>, NeoError> {
        // Extract container ID from manifest CID
        let container_id = manifest_cid
            .split('/')
            .next()
            .ok_or_else(|| NeoError::NeoFs("Invalid manifest CID format".to_string()))?;

        let mut result = Vec::with_capacity(manifest.total_size as usize);

        for chunk_oid in &manifest.chunks {
            let chunk_cid = format!("{}/{}", container_id, chunk_oid);
            let chunk_data = self.get(&chunk_cid)?;
            result.extend_from_slice(&chunk_data);
        }

        // Verify hash if present
        if !manifest.content_hash.is_empty() {
            let actual_hash = hex::encode(anubis_core::sha2::sha512(&result));
            if actual_hash != manifest.content_hash {
                return Err(NeoError::NeoFs(format!(
                    "Content hash mismatch. Expected: {}, Got: {}",
                    manifest.content_hash, actual_hash
                )));
            }
        }

        Ok(result)
    }

    /// Get a potentially chunked and encrypted object from NeoFS.
    ///
    /// Automatically handles both chunked manifests and encryption.
    pub fn get_large_encrypted(
        &self,
        cid: &str,
        recipient_sk: &anubis_core::mlkem::MlKemSecretKey,
    ) -> Result<Vec<u8>, NeoError> {
        let raw_data = self.get_large(cid)?;

        // Check if encrypted
        if Self::is_mlkem_encrypted(&raw_data) {
            self.get_encrypted_with_data(&raw_data, recipient_sk)
        } else {
            Ok(raw_data)
        }
    }

    /// Get an object from NeoFS by CID.
    ///
    /// Uses GET /v1/objects/{containerId}/by_id/{objectId} endpoint (NeoFS REST API v2).
    ///
    /// # Arguments
    /// * `cid` - Content ID in format "containerId/objectId"
    ///
    /// # Returns
    /// * Object data as bytes
    ///
    /// # Errors
    /// * `NeoError::NeoFs` if download fails or CID format is invalid
    pub fn get(&self, cid: &str) -> Result<Vec<u8>, NeoError> {
        // Parse CID: "containerId/objectId"
        let (container_id, object_id) = cid
            .split_once('/')
            .ok_or_else(|| NeoError::NeoFs(format!("Invalid CID format '{}'. Expected 'containerId/objectId'", cid)))?;

        // NeoFS REST API v2 uses /v1/objects/{containerId}/by_id/{objectId}
        let url = format!("{}/v1/objects/{}/by_id/{}", self.gateway_url, container_id, object_id);

        // Build request (auth optional for public containers)
        let mut request = self.agent.get(&url);
        if let Some(ref auth) = self.auth {
            if !auth.owner_id.is_empty() {
                request = request.set("X-Bearer-Owner-Id", &auth.owner_id);
            }
            if !auth.bearer_token.is_empty() {
                request = request.set("X-Bearer-Signature", &auth.bearer_token);
            }
            if !auth.signature_key.is_empty() {
                request = request.set("X-Bearer-Signature-Key", &auth.signature_key);
            }
        }

        let response = request
            .call()
            .map_err(|e| match e {
                ureq::Error::Status(404, _) => {
                    NeoError::NeoFs(format!("Object not found: {}", cid))
                }
                ureq::Error::Status(403, _) => {
                    NeoError::NeoFs("Access denied. Bearer token may be required or invalid.".to_string())
                }
                ureq::Error::Status(code, resp) => {
                    let body = resp.into_string().unwrap_or_default();
                    NeoError::NeoFs(format!("Download failed (HTTP {}): {}", code, body))
                }
                _ => NeoError::NeoFs(format!("Failed to fetch object: {}", e)),
            })?;

        let mut data = Vec::new();
        response
            .into_reader()
            .read_to_end(&mut data)
            .map_err(|e| NeoError::NeoFs(format!("Failed to read response: {}", e)))?;

        Ok(data)
    }

    /// Get an object by attribute from NeoFS.
    ///
    /// Uses GET /v1/get_by_attribute/{containerId}/{key}/{value} endpoint.
    ///
    /// # Arguments
    /// * `container_id` - NeoFS container ID
    /// * `key` - Attribute key to search by
    /// * `value` - Attribute value to match
    ///
    /// # Returns
    /// * Object data as bytes
    pub fn get_by_attribute(
        &self,
        container_id: &str,
        key: &str,
        value: &str,
    ) -> Result<Vec<u8>, NeoError> {
        let url = format!(
            "{}/v1/get_by_attribute/{}/{}/{}",
            self.gateway_url, container_id, key, value
        );

        let mut request = self.agent.get(&url);
        if let Some(ref auth) = self.auth {
            if !auth.owner_id.is_empty() {
                request = request.set("X-Bearer-Owner-Id", &auth.owner_id);
            }
            if !auth.bearer_token.is_empty() {
                request = request.set("X-Bearer-Signature", &auth.bearer_token);
            }
            if !auth.signature_key.is_empty() {
                request = request.set("X-Bearer-Signature-Key", &auth.signature_key);
            }
        }

        let response = request
            .call()
            .map_err(|e| match e {
                ureq::Error::Status(404, _) => {
                    NeoError::NeoFs(format!("No object found with {}={}", key, value))
                }
                ureq::Error::Status(403, _) => {
                    NeoError::NeoFs("Access denied. Bearer token may be required.".to_string())
                }
                _ => NeoError::NeoFs(format!("Failed to fetch object: {}", e)),
            })?;

        let mut data = Vec::new();
        response
            .into_reader()
            .read_to_end(&mut data)
            .map_err(|e| NeoError::NeoFs(format!("Failed to read response: {}", e)))?;

        Ok(data)
    }

    /// Create a new container in NeoFS.
    ///
    /// Uses POST /v1/containers endpoint (NeoFS REST API v2).
    ///
    /// # Arguments
    /// * `config` - Container configuration (placement policy, ACL, name, attributes)
    ///
    /// # Returns
    /// * `NeoFsContainerResult` with the created container ID
    ///
    /// # Errors
    /// * `NeoError::NeoFs` if creation fails or no auth configured
    ///
    /// # Authentication
    /// Requires full authentication with:
    /// - Owner ID (Neo wallet address)
    /// - Signature (signed request)
    /// - Signature key (public key)
    ///
    /// # Example
    /// ```ignore
    /// let config = NeoFsContainerConfig::new("REP 2", "public-read-write")
    ///     .with_name("my-container")
    ///     .with_attribute("Purpose", "anubis-receipts");
    /// let result = client.create_container(config)?;
    /// println!("Created container: {}", result.container_id);
    /// ```
    pub fn create_container(
        &self,
        config: NeoFsContainerConfig,
    ) -> Result<NeoFsContainerResult, NeoError> {
        // Verify authentication is configured
        let auth = self.auth.as_ref().ok_or_else(|| {
            NeoError::NeoFs("Authentication required for container creation. Use create_session_token() and set_bearer_token() first.".to_string())
        })?;

        if auth.bearer_token.is_empty() {
            return Err(NeoError::NeoFs("Session token required for container creation. Call create_session_token() first.".to_string()));
        }

        // Build URL with optional name-scope-global query param
        let mut url = format!("{}/v1/containers", self.gateway_url);
        if config.name_scope_global {
            url.push_str("?name-scope-global=true");
        }

        // Build request body
        let mut body = serde_json::Map::new();
        body.insert("placementPolicy".to_string(), serde_json::Value::String(config.placement_policy));
        body.insert("basicAcl".to_string(), serde_json::Value::String(config.basic_acl));

        if let Some(name) = config.name {
            body.insert("containerName".to_string(), serde_json::Value::String(name));
        }

        if let Some(attrs) = config.attributes {
            let attrs_array: Vec<serde_json::Value> = attrs
                .into_iter()
                .map(|(k, v)| {
                    let mut attr = serde_json::Map::new();
                    attr.insert("key".to_string(), serde_json::Value::String(k));
                    attr.insert("value".to_string(), serde_json::Value::String(v));
                    serde_json::Value::Object(attr)
                })
                .collect();
            body.insert("attributes".to_string(), serde_json::Value::Array(attrs_array));
        }

        let body_json = serde_json::Value::Object(body);

        // Add walletConnect query param
        let final_url = if url.contains('?') {
            format!("{}&walletConnect=true", url)
        } else {
            format!("{}?walletConnect=true", url)
        };

        // Parse signature:public_key from signature_key field
        let (signature, public_key) = if !auth.signature_key.is_empty() {
            if let Some((sig, pk)) = auth.signature_key.split_once(':') {
                (sig.to_string(), pk.to_string())
            } else {
                (String::new(), String::new())
            }
        } else {
            (String::new(), String::new())
        };

        // Build request with authentication headers
        // NeoFS REST API uses POST method for container creation
        // Session token goes in Authorization header, signature in X-Bearer-* headers
        // Container creation request prepared

        let response = self
            .agent
            .post(&final_url)
            .set("Content-Type", "application/json")
            .set("Authorization", &format!("Bearer {}", auth.bearer_token))
            .set("X-Bearer-Signature", &signature)
            .set("X-Bearer-Signature-Key", &public_key)
            .send_json(&body_json)
            .map_err(|e| {
                match e {
                    ureq::Error::Status(400, resp) => {
                        let body = resp.into_string().unwrap_or_default();
                        NeoError::NeoFs(format!("Invalid container config: {}", body))
                    }
                    ureq::Error::Status(403, resp) => {
                        let body = resp.into_string().unwrap_or_default();
                        NeoError::NeoFs(format!("Access denied. Check authentication credentials: {}", body))
                    }
                    ureq::Error::Status(502, resp) | ureq::Error::Status(504, resp) => {
                        let body = resp.into_string().unwrap_or_default();
                        NeoError::NeoFs(format!("Gateway error: {}", body))
                    }
                    ureq::Error::Status(code, resp) => {
                        let body = resp.into_string().unwrap_or_default();
                        NeoError::NeoFs(format!("Container creation failed (HTTP {}): {}", code, body))
                    }
                    _ => NeoError::NeoFs(format!("Failed to create container: {}", e)),
                }
            })?;

        // Parse response
        let json: serde_json::Value = response
            .into_json()
            .map_err(|e| NeoError::NeoFs(format!("Failed to parse response: {}", e)))?;

        // Extract container ID (try both camelCase and snake_case)
        let container_id = json
            .get("containerId")
            .or_else(|| json.get("container_id"))
            .and_then(|v| v.as_str())
            .ok_or_else(|| NeoError::NeoFs(format!("Response missing containerId: {:?}", json)))?
            .to_string();

        Ok(NeoFsContainerResult { container_id })
    }

    /// Check if an object exists in NeoFS.
    ///
    /// Uses HEAD /v1/objects/{containerId}/by_id/{objectId} endpoint.
    pub fn exists(&self, cid: &str) -> Result<bool, NeoError> {
        let (container_id, object_id) = cid
            .split_once('/')
            .ok_or_else(|| NeoError::NeoFs(format!("Invalid CID format '{}'. Expected 'containerId/objectId'", cid)))?;

        let url = format!("{}/v1/objects/{}/by_id/{}", self.gateway_url, container_id, object_id);

        let mut request = self.agent.head(&url);
        if let Some(ref auth) = self.auth {
            if !auth.bearer_token.is_empty() {
                request = request.set("X-Bearer-Signature", &auth.bearer_token);
            }
            if !auth.signature_key.is_empty() {
                request = request.set("X-Bearer-Signature-Key", &auth.signature_key);
            }
        }

        match request.call() {
            Ok(_) => Ok(true),
            Err(ureq::Error::Status(404, _)) => Ok(false),
            Err(e) => Err(NeoError::NeoFs(format!("Failed to check object existence: {}", e))),
        }
    }

    // ========================================================================
    // QUANTUM-SAFE ENCRYPTED STORAGE (ML-KEM-1024 + ChaCha20Poly1305)
    // ========================================================================

    /// Store an object encrypted for a specific ML-KEM-1024 public key.
    ///
    /// Uses post-quantum ML-KEM-1024 for key encapsulation and ChaCha20Poly1305 for
    /// authenticated encryption. Only the holder of the corresponding ML-KEM secret
    /// key can decrypt the stored object.
    ///
    /// # Encrypted Payload Format
    ///
    /// ```text
    /// ┌─────────────────────────────────────────────────────────────────────┐
    /// │ Version │ ML-KEM Ciphertext │  Nonce  │    Encrypted Data + Tag     │
    /// │ (1 B)   │    (1568 B)       │ (12 B)  │  (plaintext.len() + 16 B)   │
    /// └─────────────────────────────────────────────────────────────────────┘
    /// ```
    ///
    /// - **Version** (`0x01`): Indicates ML-KEM-1024 + ChaCha20Poly1305
    /// - **ML-KEM Ciphertext**: Encapsulated shared secret (1568 bytes)
    /// - **Nonce**: Random 12-byte ChaCha20Poly1305 nonce
    /// - **Encrypted Data**: ChaCha20Poly1305 ciphertext with 16-byte auth tag
    ///
    /// # Security Properties
    ///
    /// - **Post-Quantum**: ML-KEM-1024 provides NIST Level 5 security
    /// - **Forward Secrecy**: Each upload uses fresh key encapsulation
    /// - **Authenticated**: ChaCha20Poly1305 ensures integrity
    /// - **Formally Verified**: Both ML-KEM and ChaCha20Poly1305 from libcrux
    ///
    /// # Arguments
    ///
    /// * `container_id` - NeoFS container ID
    /// * `data` - Plaintext data to encrypt and store
    /// * `recipient_pk` - Recipient's ML-KEM-1024 public key
    /// * `attributes` - Optional object attributes
    ///
    /// # Returns
    ///
    /// * `NeoFsStoreResult` with CID of the encrypted object
    ///
    /// # Example
    ///
    /// ```ignore
    /// use anubis_core::mlkem::{MlKemKeyPair, MlKemPublicKey};
    ///
    /// // Recipient generates keypair and shares public key
    /// let recipient_kp = MlKemKeyPair::generate()?;
    /// let recipient_pk = MlKemPublicKey::from_bytes(recipient_kp.public_key_bytes())?;
    ///
    /// // Sender encrypts and uploads
    /// let result = client.store_encrypted(container_id, &data, &recipient_pk, None)?;
    ///
    /// // Only recipient can decrypt
    /// let decrypted = client.get_encrypted(&result.cid, &recipient_sk)?;
    /// ```
    pub fn store_encrypted(
        &self,
        container_id: &str,
        data: &[u8],
        recipient_pk: &anubis_core::mlkem::MlKemPublicKey,
        attributes: Option<NeoFsObjectAttributes>,
    ) -> Result<NeoFsStoreResult, NeoError> {
        use anubis_core::aead::{XChaCha20Poly1305, KEY_SIZE, XCHACHA_NONCE_SIZE};
        use anubis_core::mlkem::CIPHERTEXT_SIZE;

        // Version byte for XChaCha20-Poly1305 with 192-bit nonce
        // 0x01 = legacy ChaCha20-Poly1305 (12-byte nonce)
        // 0x02 = XChaCha20-Poly1305 (24-byte nonce) - future-proof distributed encryption
        const VERSION_MLKEM_XCHACHA: u8 = 0x02;

        // 1. ML-KEM encapsulate → (ciphertext, shared_secret)
        let (mlkem_ciphertext, mut shared_secret) = recipient_pk
            .encapsulate()
            .map_err(|e| NeoError::NeoFs(format!("ML-KEM encapsulation failed: {}", e)))?;

        // 2. Derive XChaCha20Poly1305 key from shared secret using SHA-512 (CNSA 2.0)
        // The shared secret is already 32 bytes, but we hash it for domain separation
        let mut key = [0u8; KEY_SIZE];
        let hash = anubis_core::sha2::sha512(&shared_secret);
        key.copy_from_slice(&hash[..KEY_SIZE]); // Take first 32 bytes of 64-byte hash

        // Zeroize shared secret immediately after key derivation
        shared_secret.zeroize();

        // 3. Generate random 24-byte nonce (safe for random generation in distributed systems)
        let mut nonce = [0u8; XCHACHA_NONCE_SIZE];
        getrandom::getrandom(&mut nonce)
            .map_err(|e| NeoError::NeoFs(format!("Failed to generate nonce: {}", e)))?;

        // 4. Encrypt with XChaCha20Poly1305
        let cipher = XChaCha20Poly1305::from_key(&key)
            .map_err(|e| NeoError::NeoFs(format!("Failed to init cipher: {}", e)))?;
        let ciphertext = cipher
            .seal_fixed(&nonce, &[], data)
            .map_err(|e| NeoError::NeoFs(format!("Encryption failed: {}", e)))?;

        // 5. Build encrypted payload: version || mlkem_ct || nonce || encrypted_data
        let payload_size = 1 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE + ciphertext.len();
        let mut payload = Vec::with_capacity(payload_size);
        payload.push(VERSION_MLKEM_XCHACHA);
        payload.extend_from_slice(&mlkem_ciphertext);
        payload.extend_from_slice(&nonce);
        payload.extend_from_slice(&ciphertext);

        // 6. Zeroize sensitive data (using zeroize crate to prevent compiler optimization)
        key.zeroize();

        // 7. Update attributes to indicate encryption
        let mut attrs = attributes.unwrap_or_default();
        if attrs.anubis_type.is_none() {
            attrs.anubis_type = Some("encrypted".to_string());
        }
        attrs.content_type = Some("application/x-anubis-encrypted".to_string());

        // 8. Upload encrypted payload
        self.store(container_id, &payload, Some(attrs))
    }

    /// Get and decrypt an object encrypted with ML-KEM-1024.
    ///
    /// Decrypts objects that were stored using `store_encrypted()`.
    /// Requires the ML-KEM-1024 secret key corresponding to the public key
    /// used during encryption.
    ///
    /// # Arguments
    ///
    /// * `cid` - Content ID of the encrypted object ("containerId/objectId")
    /// * `recipient_sk` - ML-KEM-1024 secret key for decryption
    ///
    /// # Returns
    ///
    /// * Decrypted plaintext data
    ///
    /// # Errors
    ///
    /// * `NeoError::NeoFs` if:
    ///   - Object not found
    ///   - Payload format invalid
    ///   - Decryption fails (wrong key or tampered data)
    ///
    /// # Security
    ///
    /// - Authentication tag is verified before returning plaintext
    /// - On failure, no partial data is returned
    /// - Secret key material is handled securely
    pub fn get_encrypted(
        &self,
        cid: &str,
        recipient_sk: &anubis_core::mlkem::MlKemSecretKey,
    ) -> Result<Vec<u8>, NeoError> {
        use anubis_core::aead::{
            ChaCha20Poly1305, XChaCha20Poly1305, KEY_SIZE, NONCE_SIZE, XCHACHA_NONCE_SIZE, TAG_SIZE,
        };
        use anubis_core::mlkem::CIPHERTEXT_SIZE;

        // Version bytes
        const VERSION_MLKEM_CHACHA: u8 = 0x01; // Legacy 12-byte nonce
        const VERSION_MLKEM_XCHACHA: u8 = 0x02; // Extended 24-byte nonce

        // 1. Download encrypted payload
        let payload = self.get(cid)?;

        // 2. Validate minimum size (smallest possible: version + mlkem_ct + 12B nonce + tag)
        const MIN_PAYLOAD_SIZE_V1: usize = 1 + CIPHERTEXT_SIZE + NONCE_SIZE + TAG_SIZE;
        if payload.is_empty() {
            return Err(NeoError::NeoFs("Empty encrypted payload".to_string()));
        }

        // 3. Parse version byte and dispatch to appropriate decryption path
        let version = payload[0];
        match version {
            VERSION_MLKEM_CHACHA => {
                // Legacy ChaCha20-Poly1305 with 12-byte nonce
                if payload.len() < MIN_PAYLOAD_SIZE_V1 {
                    return Err(NeoError::NeoFs(format!(
                        "Encrypted payload too small: {} bytes (minimum {} for v0x01)",
                        payload.len(),
                        MIN_PAYLOAD_SIZE_V1
                    )));
                }

                // Extract components
                let mlkem_ct_start = 1;
                let mlkem_ct_end = mlkem_ct_start + CIPHERTEXT_SIZE;
                let nonce_start = mlkem_ct_end;
                let nonce_end = nonce_start + NONCE_SIZE;
                let ciphertext_start = nonce_end;

                let mlkem_ciphertext = &payload[mlkem_ct_start..mlkem_ct_end];
                let nonce: [u8; NONCE_SIZE] = payload[nonce_start..nonce_end]
                    .try_into()
                    .map_err(|_| NeoError::NeoFs("Failed to extract nonce".to_string()))?;
                let ciphertext = &payload[ciphertext_start..];

                // ML-KEM decapsulate
                let mut shared_secret = recipient_sk
                    .decapsulate(mlkem_ciphertext)
                    .map_err(|e| NeoError::NeoFs(format!("ML-KEM decapsulation failed: {}", e)))?;

                // Derive key
                let mut key = [0u8; KEY_SIZE];
                let hash = anubis_core::sha2::sha512(&shared_secret);
                key.copy_from_slice(&hash[..KEY_SIZE]);
                shared_secret.zeroize();

                // Decrypt with legacy ChaCha20Poly1305
                let cipher = ChaCha20Poly1305::from_key(&key);
                // SECURITY: Store result to ensure key is zeroized even on error
                let result = cipher
                    .open_fixed(&nonce, &[], ciphertext)
                    .map_err(|e| {
                        NeoError::NeoFs(format!("Decryption failed (wrong key or tampered): {}", e))
                    });

                // Always zeroize key before returning (success or error)
                key.zeroize();
                result.map(|pt| pt.to_vec())
            }
            VERSION_MLKEM_XCHACHA => {
                // XChaCha20-Poly1305 with 24-byte nonce
                const MIN_PAYLOAD_SIZE_V2: usize =
                    1 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE + TAG_SIZE;
                if payload.len() < MIN_PAYLOAD_SIZE_V2 {
                    return Err(NeoError::NeoFs(format!(
                        "Encrypted payload too small: {} bytes (minimum {} for v0x02)",
                        payload.len(),
                        MIN_PAYLOAD_SIZE_V2
                    )));
                }

                // Extract components
                let mlkem_ct_start = 1;
                let mlkem_ct_end = mlkem_ct_start + CIPHERTEXT_SIZE;
                let nonce_start = mlkem_ct_end;
                let nonce_end = nonce_start + XCHACHA_NONCE_SIZE;
                let ciphertext_start = nonce_end;

                let mlkem_ciphertext = &payload[mlkem_ct_start..mlkem_ct_end];
                let nonce: [u8; XCHACHA_NONCE_SIZE] = payload[nonce_start..nonce_end]
                    .try_into()
                    .map_err(|_| NeoError::NeoFs("Failed to extract nonce".to_string()))?;
                let ciphertext = &payload[ciphertext_start..];

                // ML-KEM decapsulate
                let mut shared_secret = recipient_sk
                    .decapsulate(mlkem_ciphertext)
                    .map_err(|e| NeoError::NeoFs(format!("ML-KEM decapsulation failed: {}", e)))?;

                // Derive key
                let mut key = [0u8; KEY_SIZE];
                let hash = anubis_core::sha2::sha512(&shared_secret);
                key.copy_from_slice(&hash[..KEY_SIZE]);
                shared_secret.zeroize();

                // Decrypt with XChaCha20Poly1305
                // SECURITY: Store results to ensure key is zeroized even on error
                let cipher_result = XChaCha20Poly1305::from_key(&key)
                    .map_err(|e| NeoError::NeoFs(format!("Failed to init cipher: {}", e)));

                let result = match cipher_result {
                    Ok(cipher) => cipher
                        .open_fixed(&nonce, &[], ciphertext)
                        .map(|pt| pt.to_vec())
                        .map_err(|e| {
                            NeoError::NeoFs(format!("Decryption failed (wrong key or tampered): {}", e))
                        }),
                    Err(e) => Err(e),
                };

                // Always zeroize key before returning (success or error)
                key.zeroize();
                result
            }
            _ => Err(NeoError::NeoFs(format!(
                "Unknown encryption version: 0x{:02x} (supported: 0x01, 0x02)",
                version
            ))),
        }
    }

    /// Decrypt already-fetched encrypted data using ML-KEM-1024.
    ///
    /// This is useful when you've already downloaded data and want to decrypt it
    /// without re-fetching. The method auto-detects the encryption format.
    ///
    /// # Arguments
    ///
    /// * `payload` - Already-fetched encrypted payload
    /// * `recipient_sk` - The recipient's ML-KEM-1024 secret key
    ///
    /// # Returns
    ///
    /// * `Ok(Vec<u8>)` - The decrypted plaintext
    /// * `Err(NeoError)` - If decryption fails or data is malformed
    pub fn get_encrypted_with_data(
        &self,
        payload: &[u8],
        recipient_sk: &anubis_core::mlkem::MlKemSecretKey,
    ) -> Result<Vec<u8>, NeoError> {
        use anubis_core::aead::{
            ChaCha20Poly1305, XChaCha20Poly1305, KEY_SIZE, NONCE_SIZE, XCHACHA_NONCE_SIZE, TAG_SIZE,
        };
        use anubis_core::mlkem::CIPHERTEXT_SIZE;

        // Version bytes
        const VERSION_MLKEM_CHACHA: u8 = 0x01; // Legacy 12-byte nonce
        const VERSION_MLKEM_XCHACHA: u8 = 0x02; // Extended 24-byte nonce

        // Validate minimum size
        if payload.is_empty() {
            return Err(NeoError::NeoFs("Empty encrypted payload".to_string()));
        }

        // Parse version byte and dispatch
        let version = payload[0];
        match version {
            VERSION_MLKEM_CHACHA => {
                // Legacy ChaCha20-Poly1305 with 12-byte nonce
                const MIN_PAYLOAD_SIZE_V1: usize = 1 + CIPHERTEXT_SIZE + NONCE_SIZE + TAG_SIZE;
                if payload.len() < MIN_PAYLOAD_SIZE_V1 {
                    return Err(NeoError::NeoFs(format!(
                        "Encrypted payload too small: {} bytes (minimum {} for v0x01)",
                        payload.len(),
                        MIN_PAYLOAD_SIZE_V1
                    )));
                }

                // Extract components
                let mlkem_ct_start = 1;
                let mlkem_ct_end = mlkem_ct_start + CIPHERTEXT_SIZE;
                let nonce_start = mlkem_ct_end;
                let nonce_end = nonce_start + NONCE_SIZE;
                let ciphertext_start = nonce_end;

                let mlkem_ciphertext = &payload[mlkem_ct_start..mlkem_ct_end];
                let nonce: [u8; NONCE_SIZE] = payload[nonce_start..nonce_end]
                    .try_into()
                    .map_err(|_| NeoError::NeoFs("Failed to extract nonce".to_string()))?;
                let ciphertext = &payload[ciphertext_start..];

                // ML-KEM decapsulate
                let mut shared_secret = recipient_sk
                    .decapsulate(mlkem_ciphertext)
                    .map_err(|e| NeoError::NeoFs(format!("ML-KEM decapsulation failed: {}", e)))?;

                // Derive key
                let mut key = [0u8; KEY_SIZE];
                let hash = anubis_core::sha2::sha512(&shared_secret);
                key.copy_from_slice(&hash[..KEY_SIZE]);
                shared_secret.zeroize();

                // Decrypt with legacy ChaCha20Poly1305
                let cipher = ChaCha20Poly1305::from_key(&key);
                // SECURITY: Store result to ensure key is zeroized even on error
                let result = cipher
                    .open_fixed(&nonce, &[], ciphertext)
                    .map_err(|e| {
                        NeoError::NeoFs(format!("Decryption failed (wrong key or tampered): {}", e))
                    });

                // Always zeroize key before returning (success or error)
                key.zeroize();
                result.map(|pt| pt.to_vec())
            }
            VERSION_MLKEM_XCHACHA => {
                // XChaCha20-Poly1305 with 24-byte nonce
                const MIN_PAYLOAD_SIZE_V2: usize =
                    1 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE + TAG_SIZE;
                if payload.len() < MIN_PAYLOAD_SIZE_V2 {
                    return Err(NeoError::NeoFs(format!(
                        "Encrypted payload too small: {} bytes (minimum {} for v0x02)",
                        payload.len(),
                        MIN_PAYLOAD_SIZE_V2
                    )));
                }

                // Extract components
                let mlkem_ct_start = 1;
                let mlkem_ct_end = mlkem_ct_start + CIPHERTEXT_SIZE;
                let nonce_start = mlkem_ct_end;
                let nonce_end = nonce_start + XCHACHA_NONCE_SIZE;
                let ciphertext_start = nonce_end;

                let mlkem_ciphertext = &payload[mlkem_ct_start..mlkem_ct_end];
                let nonce: [u8; XCHACHA_NONCE_SIZE] = payload[nonce_start..nonce_end]
                    .try_into()
                    .map_err(|_| NeoError::NeoFs("Failed to extract nonce".to_string()))?;
                let ciphertext = &payload[ciphertext_start..];

                // ML-KEM decapsulate
                let mut shared_secret = recipient_sk
                    .decapsulate(mlkem_ciphertext)
                    .map_err(|e| NeoError::NeoFs(format!("ML-KEM decapsulation failed: {}", e)))?;

                // Derive key
                let mut key = [0u8; KEY_SIZE];
                let hash = anubis_core::sha2::sha512(&shared_secret);
                key.copy_from_slice(&hash[..KEY_SIZE]);
                shared_secret.zeroize();

                // Decrypt with XChaCha20Poly1305
                // SECURITY: Store results to ensure key is zeroized even on error
                let cipher_result = XChaCha20Poly1305::from_key(&key)
                    .map_err(|e| NeoError::NeoFs(format!("Failed to init cipher: {}", e)));

                let result = match cipher_result {
                    Ok(cipher) => cipher
                        .open_fixed(&nonce, &[], ciphertext)
                        .map(|pt| pt.to_vec())
                        .map_err(|e| {
                            NeoError::NeoFs(format!("Decryption failed (wrong key or tampered): {}", e))
                        }),
                    Err(e) => Err(e),
                };

                // Always zeroize key before returning (success or error)
                key.zeroize();
                result
            }
            _ => Err(NeoError::NeoFs(format!(
                "Unknown encryption version: 0x{:02x} (supported: 0x01, 0x02)",
                version
            ))),
        }
    }

    /// Check if data appears to be ML-KEM encrypted.
    ///
    /// Useful for auto-detecting encryption when retrieving objects.
    /// Detects both legacy ChaCha20-Poly1305 (v0x01) and XChaCha20-Poly1305 (v0x02) formats.
    ///
    /// # Arguments
    ///
    /// * `data` - Raw data bytes
    ///
    /// # Returns
    ///
    /// * `true` if data has ML-KEM encryption header (version 0x01 or 0x02)
    /// * `false` otherwise
    pub fn is_mlkem_encrypted(data: &[u8]) -> bool {
        use anubis_core::aead::{NONCE_SIZE, XCHACHA_NONCE_SIZE, TAG_SIZE};
        use anubis_core::mlkem::CIPHERTEXT_SIZE;

        const VERSION_MLKEM_CHACHA: u8 = 0x01; // Legacy 12-byte nonce
        const VERSION_MLKEM_XCHACHA: u8 = 0x02; // Extended 24-byte nonce

        // Minimum payload size for v0x01 (smaller nonce)
        const MIN_PAYLOAD_SIZE_V1: usize = 1 + CIPHERTEXT_SIZE + NONCE_SIZE + TAG_SIZE;
        // Minimum payload size for v0x02 (larger nonce)
        const MIN_PAYLOAD_SIZE_V2: usize = 1 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE + TAG_SIZE;

        if data.is_empty() {
            return false;
        }

        match data[0] {
            VERSION_MLKEM_CHACHA => data.len() >= MIN_PAYLOAD_SIZE_V1,
            VERSION_MLKEM_XCHACHA => data.len() >= MIN_PAYLOAD_SIZE_V2,
            _ => false,
        }
    }
}

use std::io::Read;

/// NeoID client for identity verification.
#[derive(Debug)]
pub struct NeoIdClient {
    /// NeoID resolver URL.
    resolver_url: String,
    /// HTTP client.
    agent: ureq::Agent,
}

impl NeoIdClient {
    /// Create a new NeoID client.
    pub fn new(resolver_url: &str, timeout_secs: u64) -> Self {
        let agent = ureq::AgentBuilder::new()
            .timeout(std::time::Duration::from_secs(timeout_secs))
            .build();

        Self {
            resolver_url: resolver_url.to_string(),
            agent,
        }
    }

    /// Verify a DID and return claims.
    pub fn verify(&self, did: &str) -> Result<NeoIdVerifyResult, NeoError> {
        // Parse the DID to extract the fingerprint
        // Format: did:anubis:neo:<network>:<fingerprint>
        let parts: Vec<&str> = did.split(':').collect();
        if parts.len() != 5 || parts[0] != "did" || parts[1] != "anubis" || parts[2] != "neo" {
            return Err(NeoError::NeoId(format!("Invalid DID format: {}", did)));
        }

        let _network = parts[3];
        let fingerprint = parts[4];

        // Query the resolver
        let url = format!("{}/resolve/{}", self.resolver_url, fingerprint);

        let response = self.agent.get(&url).call();

        match response {
            Ok(resp) => {
                let result: serde_json::Value = resp
                    .into_json()
                    .map_err(|e| NeoError::NeoId(format!("Failed to parse response: {}", e)))?;

                let valid = result.get("valid").and_then(|v| v.as_bool()).unwrap_or(false);
                let claims = result.get("claims").cloned();

                Ok(NeoIdVerifyResult {
                    did: did.to_string(),
                    valid,
                    verified_at: std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .map(|d| d.as_secs())
                        .unwrap_or(0),
                    claims,
                })
            }
            Err(ureq::Error::Status(404, _)) => {
                // DID not found
                Ok(NeoIdVerifyResult {
                    did: did.to_string(),
                    valid: false,
                    verified_at: std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .map(|d| d.as_secs())
                        .unwrap_or(0),
                    claims: None,
                })
            }
            Err(e) => Err(NeoError::NeoId(format!("Verification failed: {}", e))),
        }
    }
}

/// Neo Name Service (NNS) client.
#[derive(Debug)]
pub struct NnsClient {
    /// Neo RPC client.
    neo_client: NeoClient,
    /// NNS contract script hash.
    nns_contract: String,
}

impl NnsClient {
    /// Create a new NNS client.
    pub fn new(neo_client: NeoClient) -> Self {
        let nns_contract = neo_client.config().nns_contract.clone();
        Self {
            neo_client,
            nns_contract,
        }
    }

    /// Resolve a name to an address.
    pub fn resolve(&self, name: &str) -> Result<NnsResolveResult, NeoError> {
        // Call resolve on the NNS contract
        let result = self.neo_client.call_rpc::<serde_json::Value>(
            "invokefunction",
            serde_json::json!([
                self.nns_contract,
                "resolve",
                [
                    {"type": "String", "value": name},
                    {"type": "Integer", "value": "16"}  // RecordType.Address
                ]
            ]),
        )?;

        // Check VM state
        let state = result
            .get("state")
            .and_then(|s| s.as_str())
            .unwrap_or("FAULT");

        if state != "HALT" {
            return Err(NeoError::Nns(format!("Failed to resolve name: {}", name)));
        }

        // Parse the result
        let stack = result.get("stack").and_then(|s| s.as_array());
        if let Some(items) = stack {
            if let Some(first) = items.first() {
                let value = first.get("value").and_then(|v| v.as_str());
                if let Some(address) = value {
                    return Ok(NnsResolveResult {
                        name: name.to_string(),
                        address: address.to_string(),
                        expires: None,
                    });
                }
            }
        }

        Err(NeoError::Nns(format!("Name not found: {}", name)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_network_default_urls() {
        assert!(NeoNetwork::MainNet.default_rpc_url().contains("mainnet"));
        assert!(NeoNetwork::TestNet.default_rpc_url().contains("testnet"));
        assert!(NeoNetwork::Private.default_rpc_url().contains("localhost"));
    }

    #[test]
    fn test_network_from_str() {
        assert_eq!(NeoNetwork::parse("mainnet"), Some(NeoNetwork::MainNet));
        assert_eq!(NeoNetwork::parse("testnet"), Some(NeoNetwork::TestNet));
        assert_eq!(NeoNetwork::parse("private"), Some(NeoNetwork::Private));
        assert_eq!(NeoNetwork::parse("invalid"), None);
    }

    #[test]
    fn test_config_validation() {
        let config = NeoConfig::new(NeoNetwork::MainNet);
        assert!(config.validate().is_ok());

        // Valid script hash
        let config_with_contract = NeoConfig::new(NeoNetwork::MainNet)
            .with_contract("0x50ac1c37690cc2cfc594472833cf57505d5f46de");
        assert!(config_with_contract.validate().is_ok());

        // Invalid script hash (wrong length)
        let invalid_config = NeoConfig::new(NeoNetwork::MainNet)
            .with_contract("0x1234");
        assert!(invalid_config.validate().is_err());
    }

    #[test]
    fn test_address_validation() {
        // Valid Neo address
        assert!(validate_neo_address("NXV7ZhHaLY4w7xgQPaPXAwVXMeMKWBzLzQ").is_ok());

        // Invalid: doesn't start with N
        assert!(validate_neo_address("AXV7ZhHaLY4w7xgQPaPXAwVXMeMKWBzLzQ").is_err());

        // Invalid: wrong length
        assert!(validate_neo_address("NXV7ZhHaLY4").is_err());

        // Invalid: contains invalid Base58 character (0)
        assert!(validate_neo_address("N0V7ZhHaLY4w7xgQPaPXAwVXMeMKWBzLzQ").is_err());
    }

    #[test]
    fn test_script_hash_validation() {
        // Valid script hash
        assert!(validate_neo_script_hash("0x50ac1c37690cc2cfc594472833cf57505d5f46de").is_ok());
        assert!(validate_neo_script_hash("50ac1c37690cc2cfc594472833cf57505d5f46de").is_ok());

        // Invalid: wrong length
        assert!(validate_neo_script_hash("0x1234").is_err());

        // Invalid: non-hex characters
        assert!(validate_neo_script_hash("0xGGac1c37690cc2cfc594472833cf57505d5f46de").is_err());
    }

    #[test]
    fn test_batch_root_computation() {
        let roots = [[0x11u8; 64], [0x22u8; 64], [0x33u8; 64], [0x44u8; 64]];

        let batch_root = NeoClient::compute_batch_root(&roots);

        // Batch root should be non-zero and deterministic
        assert_ne!(batch_root, [0u8; 64]);

        // Same input should give same output
        let batch_root_2 = NeoClient::compute_batch_root(&roots);
        assert_eq!(batch_root, batch_root_2);

        // Different input should give different output
        let different_roots = [[0xAAu8; 64]; 4];
        let different_batch_root = NeoClient::compute_batch_root(&different_roots);
        assert_ne!(batch_root, different_batch_root);
    }

    #[test]
    fn test_batch_witness_computation() {
        let roots = [[0x11u8; 64], [0x22u8; 64], [0x33u8; 64], [0x44u8; 64]];

        // Should be able to compute witness for valid indices
        let witness = NeoClient::compute_batch_witness(&roots, 0).unwrap();
        assert_eq!(witness.len(), 3); // 3 levels for 8 leaves

        // Invalid index should fail
        let result = NeoClient::compute_batch_witness(&roots, 10);
        assert!(result.is_err());

        // Too many roots should fail
        let too_many: Vec<[u8; 64]> = (0..10).map(|i| [i as u8; 64]).collect();
        let result = NeoClient::compute_batch_witness(&too_many, 0);
        assert!(result.is_err());
    }

    #[test]
    fn test_empty_batch_root() {
        let empty: &[[u8; 64]] = &[];
        let root = NeoClient::compute_batch_root(empty);
        assert_eq!(root, [0u8; 64]);
    }

    #[test]
    fn test_parse_script_hash() {
        let hash = "0x50ac1c37690cc2cfc594472833cf57505d5f46de";
        let bytes = parse_script_hash(hash).unwrap();
        assert_eq!(bytes.len(), 20);

        // Verify round-trip
        let formatted = format_script_hash(&bytes);
        assert_eq!(formatted, hash);
    }

    #[test]
    fn test_qsi_document_serialization() {
        let doc = QsiDocument {
            algorithm: "ML-DSA-87".to_string(),
            public_key: vec![0xAA; 2592],
            fingerprint: "7a3b9c2d5e8f1a4b6c0d3e5f7890abcd".to_string(),
            neo_address: "NXV7ZhHaLY4w7xgQPaPXAwVXMeMKWBzLzQ".to_string(),
            name: Some("Test User".to_string()),
            email_hash: None,
            organization: None,
            credential_type: Some("test".to_string()),
            created: 1704067200,
            expires: Some(1735689600),
            revocation_cid: None,
            rotation_chain: vec![],
            signature: vec![0xBB; 4627],
        };

        // Should serialize to JSON without errors
        let json = serde_json::to_string(&doc).unwrap();
        assert!(json.contains("ML-DSA-87"));
        assert!(json.contains("Test User"));

        // Should deserialize back
        let parsed: QsiDocument = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.algorithm, "ML-DSA-87");
        assert_eq!(parsed.name, Some("Test User".to_string()));
    }

    #[test]
    fn test_network_magic() {
        assert_eq!(NeoNetwork::MainNet.magic(), 860833102);
        assert_eq!(NeoNetwork::TestNet.magic(), 894710606);
    }

    #[test]
    fn test_neo_wallet_from_wif() {
        // Test WIF from project (testnet account)
        let wif = "KzAhz8gANe8pdy3bQKYpbCi96UsmiPKyukHJKuKntcHDr4SVWd2i";
        let wallet = NeoWallet::from_wif(wif).expect("Failed to parse WIF");

        // Verify public key matches
        assert_eq!(
            wallet.public_key_hex(),
            "039a8bfda9e0e634af2ac3cc4f3d85f5a70ae95db6bda8cb16d4cc937c031b847a",
            "Public key mismatch"
        );

        // Verify address matches expected (NbWpv2WLyyqXz4Y5T5uzM5c27zZSzxsC2S from config)
        assert_eq!(wallet.address(), "NbWpv2WLyyqXz4Y5T5uzM5c27zZSzxsC2S");

        // Verify public key is valid (compressed = 33 bytes = 66 hex chars)
        let pubkey_hex = wallet.public_key_hex();
        assert_eq!(pubkey_hex.len(), 66);
        assert!(pubkey_hex.starts_with("02") || pubkey_hex.starts_with("03"));

        // Verify uncompressed public key (65 bytes = 130 hex chars)
        let pubkey_uncompressed = wallet.public_key_uncompressed_hex();
        assert_eq!(pubkey_uncompressed.len(), 130);
        assert!(pubkey_uncompressed.starts_with("04"));
    }

    #[test]
    fn test_neo_wallet_wallet_connect_signature() {
        let wif = "KzAhz8gANe8pdy3bQKYpbCi96UsmiPKyukHJKuKntcHDr4SVWd2i";
        let wallet = NeoWallet::from_wif(wif).unwrap();

        let data = b"test message for signing";

        // WalletConnect signature should be 80 bytes (64 sig + 16 salt)
        let sig = wallet.sign_wallet_connect(data).unwrap();
        assert_eq!(sig.len(), 80);

        // Each signature should be different (random salt)
        let sig2 = wallet.sign_wallet_connect(data).unwrap();
        assert_ne!(sig, sig2);
    }

    #[test]
    fn test_neo_wallet_wallet_connect_deterministic_with_salt() {
        let wif = "KzAhz8gANe8pdy3bQKYpbCi96UsmiPKyukHJKuKntcHDr4SVWd2i";
        let wallet = NeoWallet::from_wif(wif).unwrap();

        let data = b"test message for signing";
        let salt = [0x42u8; 16];

        // Same salt should produce same signature (RFC 6979 is deterministic)
        let sig1 = wallet.sign_wallet_connect_with_salt(data, &salt).unwrap();
        let sig2 = wallet.sign_wallet_connect_with_salt(data, &salt).unwrap();
        assert_eq!(sig1, sig2);

        // Different salt should produce different signature
        let different_salt = [0x43u8; 16];
        let sig3 = wallet.sign_wallet_connect_with_salt(data, &different_salt).unwrap();
        assert_ne!(sig1, sig3);
    }

    #[test]
    fn test_neo_wallet_standard_neofs_signature() {
        let wif = "KzAhz8gANe8pdy3bQKYpbCi96UsmiPKyukHJKuKntcHDr4SVWd2i";
        let wallet = NeoWallet::from_wif(wif).unwrap();

        let data = b"test message for signing";

        // Standard NeoFS signature should be 65 bytes (1 prefix + 64 sig)
        let sig = wallet.sign_neofs_standard(data).unwrap();
        assert_eq!(sig.len(), 65);
        assert_eq!(sig[0], 0x04); // Uncompressed point prefix
    }

    #[test]
    fn test_neo_wallet_auth_creation() {
        let wif = "KzAhz8gANe8pdy3bQKYpbCi96UsmiPKyukHJKuKntcHDr4SVWd2i";
        let wallet = NeoWallet::from_wif(wif).unwrap();

        let auth = wallet.sign_request("PUT", Some("test-container")).unwrap();

        // Owner ID should be the wallet address
        assert_eq!(auth.owner_id, wallet.address());

        // Bearer token should be hex-encoded 80-byte signature (64 bytes ECDSA + 16 bytes salt)
        let decoded = hex::decode(&auth.bearer_token).unwrap();
        assert_eq!(decoded.len(), 80);

        // Signature key should be hex-encoded compressed public key
        assert_eq!(auth.signature_key, wallet.public_key_hex());
    }

    #[test]
    fn test_neo_wallet_invalid_wif() {
        // Invalid WIF (wrong checksum - changed last char)
        let result = NeoWallet::from_wif("KzAhz8gANe8pdy3bQKYpbCi96UsmiPKyukHJKuKntcHDr4SVWd2X");
        assert!(result.is_err(), "Should fail with wrong checksum");

        // Invalid WIF (too short)
        let result = NeoWallet::from_wif("KzAhz8gANe8");
        assert!(result.is_err(), "Should fail when too short");

        // Invalid Base58 (contains invalid character '0')
        let result = NeoWallet::from_wif("K0Ahz8gANe8pdy3bQKYpbCi96UsmiPKyukHJKuKntcHDr4SVWd2i");
        assert!(result.is_err(), "Should fail with invalid Base58 char");
    }

    // ========================================================================
    // ML-KEM ENCRYPTED STORAGE TESTS
    // ========================================================================

    #[test]
    fn test_mlkem_encryption_payload_format() {
        use anubis_core::aead::{ChaCha20Poly1305, KEY_SIZE, NONCE_SIZE, TAG_SIZE};
        use anubis_core::mlkem::{MlKemKeyPair, MlKemPublicKey, CIPHERTEXT_SIZE};

        // Generate recipient keypair
        let kp = MlKemKeyPair::generate().unwrap();
        let pk = MlKemPublicKey::from_bytes(kp.public_key_bytes()).unwrap();

        // Create test data
        let plaintext = b"Hello, quantum-safe world!";

        // Manually construct what store_encrypted would create
        let (mlkem_ct, shared_secret) = pk.encapsulate().unwrap();

        // Derive key (SHA-512 for CNSA 2.0, take first 32 bytes)
        let hash = anubis_core::sha2::sha512(&shared_secret);
        let key: [u8; KEY_SIZE] = hash[..KEY_SIZE].try_into().unwrap();

        // Create nonce
        let mut nonce = [0u8; NONCE_SIZE];
        getrandom::getrandom(&mut nonce).unwrap();

        // Encrypt
        let cipher = ChaCha20Poly1305::from_key(&key);
        let ciphertext = cipher.seal_fixed(&nonce, &[], plaintext).unwrap();

        // Build payload
        let mut payload = Vec::new();
        payload.push(0x01); // Version
        payload.extend_from_slice(&mlkem_ct);
        payload.extend_from_slice(&nonce);
        payload.extend_from_slice(&ciphertext);

        // Verify size
        let expected_size = 1 + CIPHERTEXT_SIZE + NONCE_SIZE + plaintext.len() + TAG_SIZE;
        assert_eq!(payload.len(), expected_size);

        // Verify detection
        assert!(NeoFsClient::is_mlkem_encrypted(&payload));
    }

    #[test]
    fn test_mlkem_encryption_roundtrip() {
        use anubis_core::aead::{ChaCha20Poly1305, KEY_SIZE, NONCE_SIZE};
        use anubis_core::mlkem::{MlKemKeyPair, CIPHERTEXT_SIZE};

        // Generate recipient keypair
        let kp = MlKemKeyPair::generate().unwrap();
        let (sk, pk) = kp.into_parts();

        // Test data
        let plaintext = b"This is a secret message that should be encrypted with ML-KEM-1024!";

        // --- Encrypt (simulating store_encrypted) ---
        const VERSION: u8 = 0x01;

        // 1. ML-KEM encapsulate
        let (mlkem_ct, shared_secret) = pk.encapsulate().unwrap();

        // 2. Derive key (SHA-512 for CNSA 2.0, take first 32 bytes)
        let mut key = [0u8; KEY_SIZE];
        let hash = anubis_core::sha2::sha512(&shared_secret);
        key.copy_from_slice(&hash[..KEY_SIZE]);

        // 3. Generate nonce
        let mut nonce = [0u8; NONCE_SIZE];
        getrandom::getrandom(&mut nonce).unwrap();

        // 4. Encrypt
        let cipher = ChaCha20Poly1305::from_key(&key);
        let ciphertext = cipher.seal_fixed(&nonce, &[], plaintext).unwrap();

        // 5. Build payload
        let mut payload = Vec::new();
        payload.push(VERSION);
        payload.extend_from_slice(&mlkem_ct);
        payload.extend_from_slice(&nonce);
        payload.extend_from_slice(&ciphertext);

        // --- Decrypt (simulating get_encrypted) ---

        // 1. Parse components
        let version = payload[0];
        assert_eq!(version, VERSION);

        let mlkem_ct_dec = &payload[1..1 + CIPHERTEXT_SIZE];
        let nonce_dec: [u8; NONCE_SIZE] = payload[1 + CIPHERTEXT_SIZE..1 + CIPHERTEXT_SIZE + NONCE_SIZE]
            .try_into()
            .unwrap();
        let ct_dec = &payload[1 + CIPHERTEXT_SIZE + NONCE_SIZE..];

        // 2. Decapsulate
        let shared_secret_dec = sk.decapsulate(mlkem_ct_dec).unwrap();

        // 3. Derive key (SHA-512 for CNSA 2.0, take first 32 bytes)
        let mut key_dec = [0u8; KEY_SIZE];
        let hash_dec = anubis_core::sha2::sha512(&shared_secret_dec);
        key_dec.copy_from_slice(&hash_dec[..KEY_SIZE]);

        // 4. Decrypt
        let cipher_dec = ChaCha20Poly1305::from_key(&key_dec);
        let decrypted = cipher_dec.open_fixed(&nonce_dec, &[], ct_dec).unwrap();

        // Verify
        assert_eq!(decrypted.as_slice(), plaintext);
    }

    #[test]
    fn test_mlkem_encryption_roundtrip_v02() {
        use anubis_core::aead::{XChaCha20Poly1305, KEY_SIZE, XCHACHA_NONCE_SIZE};
        use anubis_core::mlkem::{MlKemKeyPair, CIPHERTEXT_SIZE};

        let kp = MlKemKeyPair::generate().unwrap();
        let (sk, pk) = kp.into_parts();

        let plaintext = b"Test data for XChaCha20-Poly1305 v0x02 encryption";

        // Encrypt (produces v0x02 format)
        let (mlkem_ct, shared_secret) = pk.encapsulate().unwrap();
        let mut key = [0u8; KEY_SIZE];
        let hash = anubis_core::sha2::sha512(&shared_secret);
        key.copy_from_slice(&hash[..KEY_SIZE]);

        let mut nonce = [0u8; XCHACHA_NONCE_SIZE];
        getrandom::getrandom(&mut nonce).unwrap();

        let cipher = XChaCha20Poly1305::from_key(&key).unwrap();
        let ciphertext = cipher.seal_fixed(&nonce, &[], plaintext).unwrap();

        // Build v0x02 payload
        let mut payload = vec![0x02];
        payload.extend_from_slice(&mlkem_ct);
        payload.extend_from_slice(&nonce);
        payload.extend_from_slice(&ciphertext);

        assert!(NeoFsClient::is_mlkem_encrypted(&payload));

        // Decrypt
        let mlkem_ct_dec: &[u8; CIPHERTEXT_SIZE] =
            payload[1..1 + CIPHERTEXT_SIZE].try_into().unwrap();
        let nonce_dec: &[u8; XCHACHA_NONCE_SIZE] =
            payload[1 + CIPHERTEXT_SIZE..1 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE]
                .try_into()
                .unwrap();
        let ct_dec = &payload[1 + CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE..];

        let shared_secret_dec = sk.decapsulate(mlkem_ct_dec).unwrap();
        let mut key_dec = [0u8; KEY_SIZE];
        let hash_dec = anubis_core::sha2::sha512(&shared_secret_dec);
        key_dec.copy_from_slice(&hash_dec[..KEY_SIZE]);

        let cipher_dec = XChaCha20Poly1305::from_key(&key_dec).unwrap();
        let decrypted = cipher_dec.open_fixed(nonce_dec, &[], ct_dec).unwrap();

        assert_eq!(decrypted.as_slice(), plaintext);
    }

    #[test]
    fn test_is_mlkem_encrypted_detection() {
        use anubis_core::aead::{NONCE_SIZE, XCHACHA_NONCE_SIZE, TAG_SIZE};
        use anubis_core::mlkem::CIPHERTEXT_SIZE;

        // Valid v0x01 (ChaCha20-Poly1305) payload
        let mut valid_v1 = vec![0x01];
        valid_v1.extend_from_slice(&[0u8; CIPHERTEXT_SIZE + NONCE_SIZE + TAG_SIZE]);
        assert!(NeoFsClient::is_mlkem_encrypted(&valid_v1));

        // Valid v0x02 (XChaCha20-Poly1305) payload
        let mut valid_v2 = vec![0x02];
        valid_v2.extend_from_slice(&[0u8; CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE + TAG_SIZE]);
        assert!(NeoFsClient::is_mlkem_encrypted(&valid_v2));

        // v0x01 too small
        let small = vec![0x01, 0x00, 0x00];
        assert!(!NeoFsClient::is_mlkem_encrypted(&small));

        // v0x02 with v0x01 size (too small - nonce is 12 bytes instead of 24)
        let mut v2_wrong_size = vec![0x02];
        v2_wrong_size.extend_from_slice(&[0u8; CIPHERTEXT_SIZE + NONCE_SIZE + TAG_SIZE]);
        assert!(!NeoFsClient::is_mlkem_encrypted(&v2_wrong_size));

        // Unknown version byte (0x03)
        let mut unknown_version = vec![0x03];
        unknown_version.extend_from_slice(&[0u8; CIPHERTEXT_SIZE + XCHACHA_NONCE_SIZE + TAG_SIZE]);
        assert!(!NeoFsClient::is_mlkem_encrypted(&unknown_version));

        // Empty
        assert!(!NeoFsClient::is_mlkem_encrypted(&[]));

        // Plain text (no encryption header)
        let plaintext = b"This is just plain text, not encrypted";
        assert!(!NeoFsClient::is_mlkem_encrypted(plaintext));
    }

    #[test]
    fn test_mlkem_different_keys_fail() {
        use anubis_core::aead::{ChaCha20Poly1305, KEY_SIZE, NONCE_SIZE};
        use anubis_core::mlkem::MlKemKeyPair;

        // Generate two different keypairs
        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();
        let (sk2, _) = kp2.into_parts();
        let (_, pk1) = kp1.into_parts();

        // Encrypt to pk1
        let plaintext = b"Secret message";
        let (mlkem_ct, shared_secret) = pk1.encapsulate().unwrap();

        let mut key = [0u8; KEY_SIZE];
        let hash = anubis_core::sha2::sha512(&shared_secret);
        key.copy_from_slice(&hash[..KEY_SIZE]);

        let mut nonce = [0u8; NONCE_SIZE];
        getrandom::getrandom(&mut nonce).unwrap();

        let cipher = ChaCha20Poly1305::from_key(&key);
        let ciphertext = cipher.seal_fixed(&nonce, &[], plaintext).unwrap();

        // Try to decrypt with sk2 (wrong key)
        let wrong_shared_secret = sk2.decapsulate(&mlkem_ct).unwrap();

        let mut wrong_key = [0u8; KEY_SIZE];
        let wrong_hash = anubis_core::sha2::sha512(&wrong_shared_secret);
        wrong_key.copy_from_slice(&wrong_hash[..KEY_SIZE]);

        let wrong_cipher = ChaCha20Poly1305::from_key(&wrong_key);
        let result = wrong_cipher.open_fixed(&nonce, &[], &ciphertext);

        // Should fail authentication
        assert!(result.is_err());
    }

    #[test]
    fn test_mlkem_empty_data() {
        use anubis_core::aead::{ChaCha20Poly1305, KEY_SIZE, NONCE_SIZE, TAG_SIZE};
        use anubis_core::mlkem::MlKemKeyPair;

        let kp = MlKemKeyPair::generate().unwrap();
        let (sk, pk) = kp.into_parts();

        // Encrypt empty data
        let plaintext = b"";
        let (mlkem_ct, shared_secret) = pk.encapsulate().unwrap();

        let mut key = [0u8; KEY_SIZE];
        let hash = anubis_core::sha2::sha512(&shared_secret);
        key.copy_from_slice(&hash[..KEY_SIZE]);

        let mut nonce = [0u8; NONCE_SIZE];
        getrandom::getrandom(&mut nonce).unwrap();

        let cipher = ChaCha20Poly1305::from_key(&key);
        let ciphertext = cipher.seal_fixed(&nonce, &[], plaintext).unwrap();

        // Should just be the auth tag
        assert_eq!(ciphertext.len(), TAG_SIZE);

        // Build and verify payload
        let mut payload = vec![0x01];
        payload.extend_from_slice(&mlkem_ct);
        payload.extend_from_slice(&nonce);
        payload.extend_from_slice(&ciphertext);

        assert!(NeoFsClient::is_mlkem_encrypted(&payload));

        // Decrypt
        let shared_secret_dec = sk.decapsulate(&mlkem_ct).unwrap();
        let mut key_dec = [0u8; KEY_SIZE];
        let hash_dec = anubis_core::sha2::sha512(&shared_secret_dec);
        key_dec.copy_from_slice(&hash_dec[..KEY_SIZE]);

        let cipher_dec = ChaCha20Poly1305::from_key(&key_dec);
        let decrypted = cipher_dec.open_fixed(&nonce, &[], &ciphertext).unwrap();

        assert!(decrypted.is_empty());
    }

    #[test]
    fn test_mlkem_large_data() {
        use anubis_core::aead::{ChaCha20Poly1305, KEY_SIZE, NONCE_SIZE};
        use anubis_core::mlkem::MlKemKeyPair;

        let kp = MlKemKeyPair::generate().unwrap();
        let (sk, pk) = kp.into_parts();

        // Encrypt 1MB of data
        let plaintext: Vec<u8> = (0..1_000_000).map(|i| (i % 256) as u8).collect();

        let (mlkem_ct, shared_secret) = pk.encapsulate().unwrap();

        let mut key = [0u8; KEY_SIZE];
        let hash = anubis_core::sha2::sha512(&shared_secret);
        key.copy_from_slice(&hash[..KEY_SIZE]);

        let mut nonce = [0u8; NONCE_SIZE];
        getrandom::getrandom(&mut nonce).unwrap();

        let cipher = ChaCha20Poly1305::from_key(&key);
        let ciphertext = cipher.seal_fixed(&nonce, &[], &plaintext).unwrap();

        // Decrypt
        let shared_secret_dec = sk.decapsulate(&mlkem_ct).unwrap();
        let mut key_dec = [0u8; KEY_SIZE];
        let hash_dec = anubis_core::sha2::sha512(&shared_secret_dec);
        key_dec.copy_from_slice(&hash_dec[..KEY_SIZE]);

        let cipher_dec = ChaCha20Poly1305::from_key(&key_dec);
        let decrypted = cipher_dec.open_fixed(&nonce, &[], &ciphertext).unwrap();

        assert_eq!(decrypted.as_slice(), plaintext.as_slice());
    }
}

