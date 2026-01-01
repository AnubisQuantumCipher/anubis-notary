//! Mina Protocol integration for Anubis Notary.
//!
//! This module provides anchoring and timestamping capabilities using
//! the Mina Protocol blockchain. Since there is no official Mina Rust SDK,
//! this implementation uses a Node.js subprocess bridge that interfaces
//! with the o1js library.
//!
//! # Architecture
//!
//! ```text
//! Rust (anubis_io) → stdin/stdout → Node.js (mina-bridge.js) → o1js → Mina Network
//! ```
//!
//! # Quick Start (Public Users)
//!
//! The AnubisAnchor zkApp is already deployed on Mina mainnet. Users only need:
//! 1. A Mina wallet with ~0.1 MINA for transaction fees
//! 2. Run `anubis-notary anchor mina setup` to initialize
//! 3. Set `MINA_PRIVATE_KEY` environment variable
//! 4. Anchor documents with `anubis-notary anchor mina anchor <receipt>`
//!
//! # Requirements
//!
//! - Node.js v18+ with npm
//! - The `mina-bridge` script (auto-installed by `anchor mina setup`)
//! - A Mina wallet with sufficient funds for transactions (~0.1 MINA per anchor)
//!
//! # Features
//!
//! - **Anchoring**: Submit Merkle roots to the official zkApp smart contract
//! - **Timestamping**: Retrieve blockchain timestamps for receipts
//! - **Verification**: Verify anchor existence on-chain
//! - **ZK Proofs**: Generate and verify zero-knowledge proofs for offline verification

/// Official AnubisAnchor zkApp address on Mina mainnet.
/// This contract is deployed and maintained by the Anubis Notary project.
/// Users can anchor documents to this contract by paying transaction fees.
pub const MAINNET_ZKAPP_ADDRESS: &str = "B62qnHLXkWxxJ4NwKgT8zwJ2JKZ8nymgrUyK7R7k5fm7ELPRgeEH8E3";

/// Deployment transaction hash for the official zkApp.
pub const MAINNET_DEPLOY_TX: &str = "5JvH2AvfsQDwXu41yAWJHosgadAtzEcqrRCeRYraSu43nriKoKe7";

/// Fee payer address that deployed the zkApp.
pub const MAINNET_DEPLOYER: &str = "B62qpxzahqwoTULNHKegn4ExZ95XpprhjRMQGDPDhknkovTr45Migte";

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use thiserror::Error;

use anubis_core::receipt::{
    AnchorType, TimeSource as ReceiptTimeSource, MAX_MINA_ADDRESS_SIZE, MAX_MINA_PROOF_SIZE,
    MAX_MINA_TX_HASH_SIZE,
};

/// Mina-specific errors.
#[derive(Error, Debug)]
pub enum MinaError {
    /// Bridge not found at expected path.
    #[error("mina bridge not found at {0}")]
    BridgeNotFound(PathBuf),

    /// Failed to spawn bridge process.
    #[error("failed to spawn bridge: {0}")]
    SpawnFailed(#[from] std::io::Error),

    /// Bridge process exited unexpectedly.
    #[error("bridge process exited: {0}")]
    BridgeExited(String),

    /// Communication error with bridge.
    #[error("bridge communication error: {0}")]
    Communication(String),

    /// Invalid response from bridge.
    #[error("invalid bridge response: {0}")]
    InvalidResponse(String),

    /// Transaction failed on Mina network.
    #[error("mina transaction failed: {0}")]
    TransactionFailed(String),

    /// Wallet error (no funds, locked, etc.).
    #[error("wallet error: {0}")]
    WalletError(String),

    /// Network error (connection, timeout, etc.).
    #[error("network error: {0}")]
    NetworkError(String),

    /// ZK proof generation failed.
    #[error("proof generation failed: {0}")]
    ProofFailed(String),

    /// zkApp not deployed at address.
    #[error("zkApp not found at {0}")]
    ZkAppNotFound(String),

    /// Verification failed.
    #[error("verification failed: {0}")]
    VerificationFailed(String),

    /// Configuration error.
    #[error("configuration error: {0}")]
    ConfigError(String),

    /// Invalid address format.
    #[error("invalid mina address: {0}")]
    InvalidAddress(String),

    /// Address too large.
    #[error("mina address too large: {0} bytes (max {MAX_MINA_ADDRESS_SIZE})")]
    AddressTooLarge(usize),

    /// Transaction hash too large.
    #[error("transaction hash too large: {0} bytes (max {MAX_MINA_TX_HASH_SIZE})")]
    TxHashTooLarge(usize),

    /// Proof too large.
    #[error("proof too large: {0} bytes (max {MAX_MINA_PROOF_SIZE})")]
    ProofTooLarge(usize),
}

/// Result type for Mina operations.
pub type Result<T> = std::result::Result<T, MinaError>;

/// Mina network type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MinaNetwork {
    /// Mainnet (production).
    Mainnet,
    /// Devnet (testing).
    Devnet,
    /// Local testnet (development).
    LocalTestnet,
}

impl MinaNetwork {
    /// Get the GraphQL endpoint URL for this network.
    pub fn graphql_url(&self) -> &'static str {
        match self {
            MinaNetwork::Mainnet => "https://graphql.minaexplorer.com",
            MinaNetwork::Devnet => "https://devnet.minaexplorer.com/graphql",
            MinaNetwork::LocalTestnet => "http://localhost:8080/graphql",
        }
    }

    /// Get the archive node URL for this network.
    pub fn archive_url(&self) -> &'static str {
        match self {
            MinaNetwork::Mainnet => "https://archive.minaexplorer.com",
            MinaNetwork::Devnet => "https://devnet-archive.minaexplorer.com",
            MinaNetwork::LocalTestnet => "http://localhost:8081",
        }
    }

    /// Get the network name string.
    pub fn name(&self) -> &'static str {
        match self {
            MinaNetwork::Mainnet => "mainnet",
            MinaNetwork::Devnet => "devnet",
            MinaNetwork::LocalTestnet => "local",
        }
    }
}

impl std::str::FromStr for MinaNetwork {
    type Err = MinaError;

    fn from_str(s: &str) -> Result<Self> {
        match s.to_lowercase().as_str() {
            "mainnet" | "main" => Ok(MinaNetwork::Mainnet),
            "devnet" | "dev" => Ok(MinaNetwork::Devnet),
            "local" | "localhost" | "testnet" => Ok(MinaNetwork::LocalTestnet),
            _ => Err(MinaError::ConfigError(format!("unknown network: {}", s))),
        }
    }
}

/// Configuration for the Mina client.
#[derive(Debug, Clone)]
pub struct MinaConfig {
    /// Path to the Node.js bridge script directory.
    pub bridge_path: PathBuf,
    /// Mina network to use.
    pub network: MinaNetwork,
    /// zkApp contract address (Base58 public key).
    pub zkapp_address: String,
    /// Wallet private key (for signing transactions).
    /// This should be loaded from secure storage, not hardcoded.
    pub wallet_private_key: Option<String>,
    /// Transaction fee in nanomina (1 MINA = 1e9 nanomina).
    pub fee_nanomina: u64,
    /// Timeout for bridge operations in seconds.
    pub timeout_secs: u64,
    /// Maximum retries for network operations.
    pub max_retries: u32,
}

impl Default for MinaConfig {
    fn default() -> Self {
        Self {
            bridge_path: dirs::home_dir()
                .unwrap_or_else(|| PathBuf::from("."))
                .join(".anubis")
                .join("mina-bridge"),
            // Default to mainnet with official zkApp for public use
            network: MinaNetwork::Mainnet,
            zkapp_address: MAINNET_ZKAPP_ADDRESS.to_string(),
            wallet_private_key: None,
            fee_nanomina: 100_000_000, // 0.1 MINA
            timeout_secs: 120,
            max_retries: 3,
        }
    }
}

impl MinaConfig {
    /// Create a new configuration for mainnet.
    pub fn mainnet(zkapp_address: impl Into<String>) -> Self {
        Self {
            network: MinaNetwork::Mainnet,
            zkapp_address: zkapp_address.into(),
            ..Default::default()
        }
    }

    /// Create a new configuration for devnet.
    pub fn devnet(zkapp_address: impl Into<String>) -> Self {
        Self {
            network: MinaNetwork::Devnet,
            zkapp_address: zkapp_address.into(),
            ..Default::default()
        }
    }

    /// Set the bridge path.
    pub fn with_bridge_path(mut self, path: impl Into<PathBuf>) -> Self {
        self.bridge_path = path.into();
        self
    }

    /// Set the wallet private key.
    pub fn with_wallet(mut self, private_key: impl Into<String>) -> Self {
        self.wallet_private_key = Some(private_key.into());
        self
    }

    /// Set the transaction fee.
    pub fn with_fee(mut self, fee_nanomina: u64) -> Self {
        self.fee_nanomina = fee_nanomina;
        self
    }

    /// Set the timeout.
    pub fn with_timeout(mut self, timeout_secs: u64) -> Self {
        self.timeout_secs = timeout_secs;
        self
    }
}

/// Result of anchoring a Merkle root to Mina.
#[derive(Debug, Clone)]
pub struct MinaAnchorResult {
    /// zkApp contract address.
    pub zkapp_address: String,
    /// Transaction hash.
    pub tx_hash: String,
    /// Block height when anchored.
    pub block_height: u64,
    /// Mina timestamp in milliseconds since UNIX epoch.
    pub timestamp_ms: u64,
    /// ZK proof for offline verification (base64-encoded).
    pub proof: Option<String>,
}

impl MinaAnchorResult {
    /// Convert to `AnchorType::Mina`.
    pub fn to_anchor_type(&self) -> Result<AnchorType> {
        let addr_bytes = self.zkapp_address.as_bytes();
        if addr_bytes.len() > MAX_MINA_ADDRESS_SIZE {
            return Err(MinaError::AddressTooLarge(addr_bytes.len()));
        }
        let mut zkapp_address = [0u8; MAX_MINA_ADDRESS_SIZE];
        let zkapp_address_len = addr_bytes.len();
        zkapp_address[..zkapp_address_len].copy_from_slice(addr_bytes);

        let tx_bytes = self.tx_hash.as_bytes();
        if tx_bytes.len() > MAX_MINA_TX_HASH_SIZE {
            return Err(MinaError::TxHashTooLarge(tx_bytes.len()));
        }
        let mut tx_hash = [0u8; MAX_MINA_TX_HASH_SIZE];
        let tx_hash_len = tx_bytes.len();
        tx_hash[..tx_hash_len].copy_from_slice(tx_bytes);

        let (proof, proof_len) = if let Some(ref proof_str) = self.proof {
            let proof_bytes = proof_str.as_bytes();
            if proof_bytes.len() > MAX_MINA_PROOF_SIZE {
                return Err(MinaError::ProofTooLarge(proof_bytes.len()));
            }
            let mut proof_arr = [0u8; MAX_MINA_PROOF_SIZE];
            let len = proof_bytes.len();
            proof_arr[..len].copy_from_slice(proof_bytes);
            (proof_arr, len)
        } else {
            ([0u8; MAX_MINA_PROOF_SIZE], 0)
        };

        Ok(AnchorType::Mina {
            zkapp_address,
            zkapp_address_len,
            tx_hash,
            tx_hash_len,
            block_height: self.block_height,
            timestamp_ms: self.timestamp_ms,
            proof,
            proof_len,
        })
    }
}

/// Result of getting a timestamp from Mina.
#[derive(Debug, Clone)]
pub struct MinaTimeResult {
    /// Block height.
    pub block_height: u64,
    /// Mina timestamp in milliseconds since UNIX epoch.
    pub timestamp_ms: u64,
    /// Transaction hash (if from a specific transaction).
    pub tx_hash: Option<String>,
}

impl MinaTimeResult {
    /// Convert to `TimeSource::Mina`.
    pub fn to_time_source(&self) -> Result<ReceiptTimeSource> {
        let (tx_hash, tx_hash_len) = if let Some(ref hash) = self.tx_hash {
            let bytes = hash.as_bytes();
            if bytes.len() > MAX_MINA_TX_HASH_SIZE {
                return Err(MinaError::TxHashTooLarge(bytes.len()));
            }
            let mut arr = [0u8; MAX_MINA_TX_HASH_SIZE];
            arr[..bytes.len()].copy_from_slice(bytes);
            (arr, bytes.len())
        } else {
            ([0u8; MAX_MINA_TX_HASH_SIZE], 0)
        };

        Ok(ReceiptTimeSource::Mina {
            block_height: self.block_height,
            timestamp_ms: self.timestamp_ms,
            tx_hash,
            tx_hash_len,
        })
    }
}

/// Bridge message types.
#[derive(Debug)]
enum BridgeCommand {
    Anchor { merkle_root: [u8; 32] },
    Verify { merkle_root: [u8; 32] },
    GetTime,
    GetBalance,
    Shutdown,
}

impl BridgeCommand {
    fn to_json(&self) -> String {
        match self {
            BridgeCommand::Anchor { merkle_root } => {
                format!(r#"{{"cmd":"anchor","root":"{}"}}"#, hex::encode(merkle_root))
            }
            BridgeCommand::Verify { merkle_root } => {
                format!(r#"{{"cmd":"verify","root":"{}"}}"#, hex::encode(merkle_root))
            }
            BridgeCommand::GetTime => r#"{"cmd":"time"}"#.to_string(),
            BridgeCommand::GetBalance => r#"{"cmd":"balance"}"#.to_string(),
            BridgeCommand::Shutdown => r#"{"cmd":"shutdown"}"#.to_string(),
        }
    }
}

/// Mina Protocol client.
///
/// This client communicates with a Node.js bridge process to interact
/// with the Mina blockchain using the o1js library.
pub struct MinaClient {
    config: MinaConfig,
    bridge_process: Option<Child>,
    is_connected: Arc<AtomicBool>,
}

impl MinaClient {
    /// Create a new Mina client with the given configuration.
    pub fn new(config: MinaConfig) -> Result<Self> {
        // Validate configuration
        if config.zkapp_address.is_empty() {
            return Err(MinaError::ConfigError(
                "zkApp address is required".to_string(),
            ));
        }

        // Validate address format (Mina addresses are Base58-encoded, ~55 chars)
        if config.zkapp_address.len() < 50 || config.zkapp_address.len() > 60 {
            return Err(MinaError::InvalidAddress(config.zkapp_address.clone()));
        }

        // Check if bridge exists
        let bridge_script = config.bridge_path.join("mina-bridge.js");
        if !bridge_script.exists() {
            return Err(MinaError::BridgeNotFound(bridge_script));
        }

        Ok(Self {
            config,
            bridge_process: None,
            is_connected: Arc::new(AtomicBool::new(false)),
        })
    }

    /// Start the bridge process.
    pub fn connect(&mut self) -> Result<()> {
        if self.is_connected.load(Ordering::Acquire) {
            return Ok(());
        }

        let bridge_script = self.config.bridge_path.join("mina-bridge.js");

        // Build environment variables
        let mut cmd = Command::new("node");
        cmd.arg(&bridge_script)
            .env("MINA_NETWORK", self.config.network.name())
            .env("MINA_GRAPHQL_URL", self.config.network.graphql_url())
            .env("MINA_ZKAPP_ADDRESS", &self.config.zkapp_address)
            .env("MINA_FEE", self.config.fee_nanomina.to_string())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        // Add wallet key if provided
        if let Some(ref key) = self.config.wallet_private_key {
            cmd.env("MINA_PRIVATE_KEY", key);
        }

        let child = cmd.spawn()?;
        self.bridge_process = Some(child);
        self.is_connected.store(true, Ordering::Release);

        Ok(())
    }

    /// Disconnect from the bridge process.
    pub fn disconnect(&mut self) -> Result<()> {
        if !self.is_connected.load(Ordering::Acquire) {
            return Ok(());
        }

        // Send shutdown command
        if let Some(ref mut process) = self.bridge_process {
            if let Some(ref mut stdin) = process.stdin {
                let _ = writeln!(stdin, "{}", BridgeCommand::Shutdown.to_json());
            }
            let _ = process.wait();
        }

        self.bridge_process = None;
        self.is_connected.store(false, Ordering::Release);

        Ok(())
    }

    /// Check if connected to the bridge.
    pub fn is_connected(&self) -> bool {
        self.is_connected.load(Ordering::Acquire)
    }

    /// Send a command to the bridge and get the response.
    fn send_command(&mut self, cmd: BridgeCommand) -> Result<String> {
        if !self.is_connected() {
            self.connect()?;
        }

        let process = self
            .bridge_process
            .as_mut()
            .ok_or_else(|| MinaError::Communication("bridge not running".to_string()))?;

        // Send command
        let stdin = process
            .stdin
            .as_mut()
            .ok_or_else(|| MinaError::Communication("stdin not available".to_string()))?;
        writeln!(stdin, "{}", cmd.to_json())?;
        stdin.flush()?;

        // Read response
        let stdout = process
            .stdout
            .as_mut()
            .ok_or_else(|| MinaError::Communication("stdout not available".to_string()))?;
        let mut reader = BufReader::new(stdout);
        let mut response = String::new();
        reader.read_line(&mut response)?;

        if response.is_empty() {
            return Err(MinaError::BridgeExited("no response".to_string()));
        }

        Ok(response.trim().to_string())
    }

    /// Anchor a Merkle root to the Mina blockchain.
    ///
    /// This submits a transaction to the zkApp contract that stores
    /// the Merkle root on-chain along with the current timestamp.
    pub fn anchor(&mut self, merkle_root: &[u8; 32]) -> Result<MinaAnchorResult> {
        let response = self.send_command(BridgeCommand::Anchor {
            merkle_root: *merkle_root,
        })?;

        // Parse JSON response
        self.parse_anchor_response(&response)
    }

    /// Verify that a Merkle root exists on-chain.
    pub fn verify(&mut self, merkle_root: &[u8; 32]) -> Result<bool> {
        let response = self.send_command(BridgeCommand::Verify {
            merkle_root: *merkle_root,
        })?;

        // Parse JSON response
        self.parse_verify_response(&response)
    }

    /// Get the current Mina blockchain time.
    pub fn get_time(&mut self) -> Result<MinaTimeResult> {
        let response = self.send_command(BridgeCommand::GetTime)?;
        self.parse_time_response(&response)
    }

    /// Get the wallet balance.
    pub fn get_balance(&mut self) -> Result<u64> {
        let response = self.send_command(BridgeCommand::GetBalance)?;
        self.parse_balance_response(&response)
    }

    /// Parse anchor response JSON.
    fn parse_anchor_response(&self, response: &str) -> Result<MinaAnchorResult> {
        // Simple JSON parsing without dependencies
        // Expected format: {"ok":true,"address":"B62...","tx":"Ckp...","height":123,"timestamp":1234567890000,"proof":"..."}
        if response.contains(r#""ok":false"#) || response.contains(r#""error""#) {
            let err = extract_json_string(response, "error").unwrap_or_else(|| "unknown".to_string());
            return Err(MinaError::TransactionFailed(err));
        }

        let zkapp_address = extract_json_string(response, "address")
            .ok_or_else(|| MinaError::InvalidResponse("missing address".to_string()))?;
        let tx_hash = extract_json_string(response, "tx")
            .ok_or_else(|| MinaError::InvalidResponse("missing tx".to_string()))?;
        let block_height = extract_json_number(response, "height")
            .ok_or_else(|| MinaError::InvalidResponse("missing height".to_string()))?;
        let timestamp_ms = extract_json_number(response, "timestamp")
            .ok_or_else(|| MinaError::InvalidResponse("missing timestamp".to_string()))?;
        let proof = extract_json_string(response, "proof");

        Ok(MinaAnchorResult {
            zkapp_address,
            tx_hash,
            block_height,
            timestamp_ms,
            proof,
        })
    }

    /// Parse verify response JSON.
    fn parse_verify_response(&self, response: &str) -> Result<bool> {
        if response.contains(r#""error""#) {
            let err = extract_json_string(response, "error").unwrap_or_else(|| "unknown".to_string());
            return Err(MinaError::VerificationFailed(err));
        }

        Ok(response.contains(r#""verified":true"#))
    }

    /// Parse time response JSON.
    fn parse_time_response(&self, response: &str) -> Result<MinaTimeResult> {
        if response.contains(r#""error""#) {
            let err = extract_json_string(response, "error").unwrap_or_else(|| "unknown".to_string());
            return Err(MinaError::NetworkError(err));
        }

        let block_height = extract_json_number(response, "height")
            .ok_or_else(|| MinaError::InvalidResponse("missing height".to_string()))?;
        let timestamp_ms = extract_json_number(response, "timestamp")
            .ok_or_else(|| MinaError::InvalidResponse("missing timestamp".to_string()))?;

        Ok(MinaTimeResult {
            block_height,
            timestamp_ms,
            tx_hash: None,
        })
    }

    /// Parse balance response JSON.
    fn parse_balance_response(&self, response: &str) -> Result<u64> {
        if response.contains(r#""error""#) {
            let err = extract_json_string(response, "error").unwrap_or_else(|| "unknown".to_string());
            return Err(MinaError::WalletError(err));
        }

        extract_json_number(response, "balance")
            .ok_or_else(|| MinaError::InvalidResponse("missing balance".to_string()))
    }

    /// Get the configuration.
    pub fn config(&self) -> &MinaConfig {
        &self.config
    }
}

impl Drop for MinaClient {
    fn drop(&mut self) {
        let _ = self.disconnect();
    }
}

/// Extract a string value from a JSON object.
fn extract_json_string(json: &str, key: &str) -> Option<String> {
    let pattern = format!(r#""{}":"#, key);
    let start = json.find(&pattern)?;
    let value_start = start + pattern.len();

    if json.as_bytes().get(value_start)? != &b'"' {
        return None;
    }

    let value_content_start = value_start + 1;
    let mut end = value_content_start;
    let bytes = json.as_bytes();

    while end < bytes.len() {
        if bytes[end] == b'"' && (end == value_content_start || bytes[end - 1] != b'\\') {
            break;
        }
        end += 1;
    }

    Some(json[value_content_start..end].to_string())
}

/// Extract a number value from a JSON object.
fn extract_json_number(json: &str, key: &str) -> Option<u64> {
    let pattern = format!(r#""{}":"#, key);
    let start = json.find(&pattern)?;
    let value_start = start + pattern.len();

    let mut end = value_start;
    let bytes = json.as_bytes();

    while end < bytes.len() && (bytes[end].is_ascii_digit() || bytes[end] == b'.') {
        end += 1;
    }

    json[value_start..end].parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_network_urls() {
        assert!(MinaNetwork::Mainnet
            .graphql_url()
            .contains("minaexplorer.com"));
        assert!(MinaNetwork::Devnet.graphql_url().contains("devnet"));
        assert!(MinaNetwork::LocalTestnet.graphql_url().contains("localhost"));
    }

    #[test]
    fn test_network_parse() {
        assert_eq!(
            "mainnet".parse::<MinaNetwork>().unwrap(),
            MinaNetwork::Mainnet
        );
        assert_eq!(
            "devnet".parse::<MinaNetwork>().unwrap(),
            MinaNetwork::Devnet
        );
        assert_eq!(
            "local".parse::<MinaNetwork>().unwrap(),
            MinaNetwork::LocalTestnet
        );
    }

    #[test]
    fn test_config_default() {
        let config = MinaConfig::default();
        // Default to mainnet with official zkApp for public use
        assert_eq!(config.network, MinaNetwork::Mainnet);
        assert_eq!(config.zkapp_address, MAINNET_ZKAPP_ADDRESS);
        assert_eq!(config.fee_nanomina, 100_000_000);
        assert_eq!(config.timeout_secs, 120);
    }

    #[test]
    fn test_config_builder() {
        let config = MinaConfig::mainnet("B62qabcdef123")
            .with_fee(50_000_000)
            .with_timeout(60);
        assert_eq!(config.network, MinaNetwork::Mainnet);
        assert_eq!(config.zkapp_address, "B62qabcdef123");
        assert_eq!(config.fee_nanomina, 50_000_000);
        assert_eq!(config.timeout_secs, 60);
    }

    #[test]
    fn test_extract_json_string() {
        let json = r#"{"address":"B62qtest","tx":"Ckptest"}"#;
        assert_eq!(
            extract_json_string(json, "address"),
            Some("B62qtest".to_string())
        );
        assert_eq!(
            extract_json_string(json, "tx"),
            Some("Ckptest".to_string())
        );
        assert_eq!(extract_json_string(json, "missing"), None);
    }

    #[test]
    fn test_extract_json_number() {
        let json = r#"{"height":12345,"timestamp":1704067200000}"#;
        assert_eq!(extract_json_number(json, "height"), Some(12345));
        assert_eq!(extract_json_number(json, "timestamp"), Some(1704067200000));
        assert_eq!(extract_json_number(json, "missing"), None);
    }

    #[test]
    fn test_anchor_result_to_anchor_type() {
        let result = MinaAnchorResult {
            zkapp_address: "B62qtest123456789012345678901234567890123456789012".to_string(),
            tx_hash: "CkpYxyz123".to_string(),
            block_height: 12345,
            timestamp_ms: 1704067200000,
            proof: Some("proofdata".to_string()),
        };

        let anchor = result.to_anchor_type().unwrap();
        match anchor {
            AnchorType::Mina {
                block_height,
                timestamp_ms,
                zkapp_address_len,
                tx_hash_len,
                proof_len,
                ..
            } => {
                assert_eq!(block_height, 12345);
                assert_eq!(timestamp_ms, 1704067200000);
                assert!(zkapp_address_len > 0);
                assert!(tx_hash_len > 0);
                assert!(proof_len > 0);
            }
            _ => panic!("expected Mina anchor type"),
        }
    }

    #[test]
    fn test_time_result_to_time_source() {
        let result = MinaTimeResult {
            block_height: 12345,
            timestamp_ms: 1704067200000,
            tx_hash: Some("CkpTest123".to_string()),
        };

        let time_source = result.to_time_source().unwrap();
        match time_source {
            ReceiptTimeSource::Mina {
                block_height,
                timestamp_ms,
                tx_hash_len,
                ..
            } => {
                assert_eq!(block_height, 12345);
                assert_eq!(timestamp_ms, 1704067200000);
                assert!(tx_hash_len > 0);
            }
            _ => panic!("expected Mina time source"),
        }
    }
}
