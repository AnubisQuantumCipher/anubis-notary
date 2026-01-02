//! Starknet Protocol integration for blockchain anchoring.
//!
//! This module provides integration with the Starknet Protocol blockchain
//! for timestamping and anchoring. It enables:
//!
//! - **Merkle Root Anchoring**: Store SHA3-256/Poseidon Merkle roots on-chain
//! - **Blockchain Timestamps**: Leverage Starknet's block timestamps for proof-of-existence
//! - **ZK-STARK Verification**: Native STARK proofs for validity rollup
//!
//! ## Architecture
//!
//! Uses a blocking JSON-RPC client via `ureq` to communicate with Starknet nodes:
//!
//! ```text
//! Rust (anubis_io) → ureq (HTTPS) → Starknet JSON-RPC → Starknet Network
//! ```
//!
//! ## Cost
//!
//! Starknet transactions are extremely cost-efficient (~$0.001/tx on mainnet).
//! Batch anchoring enables 8x savings by combining multiple roots.
//!
//! ## Example
//!
//! ```ignore
//! use anubis_io::starknet::{StarknetClient, StarknetConfig, StarknetNetwork};
//!
//! let config = StarknetConfig::new(StarknetNetwork::Mainnet)
//!     .with_contract("0x049d36570d4e46f48e99674bd3fcc84644ddd6b96f7c741b1562b82f9e004dc7");
//!
//! let client = StarknetClient::new(config)?;
//!
//! // Get current blockchain time
//! let (block, timestamp) = client.get_block_time()?;
//! println!("Block {} at timestamp {}", block, timestamp);
//! ```

use serde::{Deserialize, Serialize};
use starknet_core::types::Felt;
use starknet_crypto::poseidon_hash_many;
use thiserror::Error;

/// Starknet error types.
#[derive(Error, Debug)]
pub enum StarknetError {
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

    /// Verification failed.
    #[error("verification failed: {0}")]
    VerificationFailed(String),

    /// Request timeout.
    #[error("request timeout")]
    Timeout,

    /// Insufficient funds for transaction.
    #[error("insufficient funds: have {balance}, need {required}")]
    InsufficientFunds {
        /// Current account balance.
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
}

/// Starknet network selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum StarknetNetwork {
    /// Starknet mainnet.
    #[default]
    Mainnet,
    /// Starknet Sepolia testnet.
    Sepolia,
    /// Local Starknet devnet.
    Devnet,
}

impl StarknetNetwork {
    /// Get the default RPC URL for this network.
    pub fn default_rpc_url(&self) -> &'static str {
        match self {
            StarknetNetwork::Mainnet => "https://starknet-mainnet.public.blastapi.io",
            StarknetNetwork::Sepolia => "https://starknet-sepolia.public.blastapi.io",
            StarknetNetwork::Devnet => "http://localhost:5050",
        }
    }

    /// Get the network name.
    pub fn name(&self) -> &'static str {
        match self {
            StarknetNetwork::Mainnet => "mainnet",
            StarknetNetwork::Sepolia => "sepolia",
            StarknetNetwork::Devnet => "devnet",
        }
    }

    /// Parse network from string.
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "mainnet" | "main" => Some(StarknetNetwork::Mainnet),
            "sepolia" | "testnet" | "test" => Some(StarknetNetwork::Sepolia),
            "devnet" | "local" => Some(StarknetNetwork::Devnet),
            _ => None,
        }
    }
}

/// Configuration for Starknet client.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StarknetConfig {
    /// RPC endpoint URL.
    pub rpc_url: String,
    /// Network selection.
    pub network: StarknetNetwork,
    /// NotaryOracle contract address (hex with 0x prefix).
    pub contract_address: Option<String>,
    /// Account address for signing (hex with 0x prefix).
    pub account_address: Option<String>,
    /// Fee multiplier for gas estimation.
    #[serde(default = "default_fee_multiplier")]
    pub fee_multiplier: f64,
    /// Request timeout in seconds.
    #[serde(default = "default_timeout")]
    pub timeout_secs: u64,
}

fn default_fee_multiplier() -> f64 {
    1.5
}

fn default_timeout() -> u64 {
    30
}

impl Default for StarknetConfig {
    fn default() -> Self {
        Self::new(StarknetNetwork::Mainnet)
    }
}

impl StarknetConfig {
    /// Create a new configuration for the specified network.
    pub fn new(network: StarknetNetwork) -> Self {
        Self {
            rpc_url: network.default_rpc_url().to_string(),
            network,
            contract_address: None,
            account_address: None,
            fee_multiplier: default_fee_multiplier(),
            timeout_secs: default_timeout(),
        }
    }

    /// Set the RPC URL.
    pub fn with_rpc_url(mut self, url: &str) -> Self {
        self.rpc_url = url.to_string();
        self
    }

    /// Set the contract address.
    pub fn with_contract(mut self, address: &str) -> Self {
        self.contract_address = Some(address.to_string());
        self
    }

    /// Set the account address.
    pub fn with_account(mut self, address: &str) -> Self {
        self.account_address = Some(address.to_string());
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

    /// Validate the configuration.
    pub fn validate(&self) -> Result<(), StarknetError> {
        // Validate RPC URL
        if self.rpc_url.is_empty() {
            return Err(StarknetError::ConfigError("RPC URL is required".to_string()));
        }

        // Validate contract address format if provided
        if let Some(addr) = &self.contract_address {
            validate_starknet_address(addr)?;
        }

        // Validate account address format if provided
        if let Some(addr) = &self.account_address {
            validate_starknet_address(addr)?;
        }

        Ok(())
    }
}

/// Validate a Starknet address (felt252 in hex format).
fn validate_starknet_address(addr: &str) -> Result<(), StarknetError> {
    let addr = addr.strip_prefix("0x").unwrap_or(addr);

    // Must be valid hex
    if !addr.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(StarknetError::InvalidAddress(format!(
            "Invalid hex characters in address: {}",
            addr
        )));
    }

    // Maximum 64 hex chars (32 bytes = felt252)
    if addr.len() > 64 {
        return Err(StarknetError::InvalidAddress(format!(
            "Address too long (max 64 hex chars): {}",
            addr.len()
        )));
    }

    Ok(())
}

/// Result of an anchor operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StarknetAnchorResult {
    /// Transaction hash (hex).
    pub tx_hash: String,
    /// Block number when included.
    pub block_number: u64,
    /// Block timestamp (seconds since UNIX epoch).
    pub timestamp: u64,
    /// Root ID assigned by the contract.
    pub root_id: u64,
    /// Contract address used.
    pub contract_address: String,
}

/// Result of a batch anchor operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StarknetBatchResult {
    /// Transaction hash (hex).
    pub tx_hash: String,
    /// Block number when included.
    pub block_number: u64,
    /// Block timestamp (seconds since UNIX epoch).
    pub timestamp: u64,
    /// Root ID assigned by the contract.
    pub root_id: u64,
    /// Contract address used.
    pub contract_address: String,
    /// Combined batch root (Poseidon hash).
    pub batch_root: [u8; 32],
    /// Number of roots in the batch.
    pub batch_size: usize,
}

/// Result of a time query.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StarknetTimeResult {
    /// Current block number.
    pub block_number: u64,
    /// Block timestamp (seconds since UNIX epoch).
    pub timestamp: u64,
    /// Network name.
    pub network: String,
}

/// Anchor record from the contract.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnchorRecord {
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
}

/// Blocking Starknet JSON-RPC client.
#[derive(Debug)]
pub struct StarknetClient {
    /// Client configuration.
    config: StarknetConfig,
    /// HTTP client.
    agent: ureq::Agent,
}

impl StarknetClient {
    /// Create a new Starknet client.
    pub fn new(config: StarknetConfig) -> Result<Self, StarknetError> {
        config.validate()?;

        let agent = ureq::AgentBuilder::new()
            .timeout(std::time::Duration::from_secs(config.timeout_secs))
            .build();

        Ok(Self { config, agent })
    }

    /// Get the current configuration.
    pub fn config(&self) -> &StarknetConfig {
        &self.config
    }

    /// Get current block number and timestamp.
    pub fn get_block_time(&self) -> Result<StarknetTimeResult, StarknetError> {
        // Call starknet_blockNumber
        let block_number = self.call_rpc::<u64>("starknet_blockNumber", serde_json::json!([]))?;

        // Get the block to extract timestamp
        let block = self.call_rpc::<serde_json::Value>(
            "starknet_getBlockWithTxHashes",
            serde_json::json!([{"block_number": block_number}]),
        )?;

        let timestamp = block
            .get("timestamp")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);

        Ok(StarknetTimeResult {
            block_number,
            timestamp,
            network: self.config.network.name().to_string(),
        })
    }

    /// Get account balance (in wei/fri).
    pub fn get_balance(&self, address: &str) -> Result<u128, StarknetError> {
        validate_starknet_address(address)?;

        // ETH contract on Starknet
        let eth_contract = "0x049d36570d4e46f48e99674bd3fcc84644ddd6b96f7c741b1562b82f9e004dc7";

        // Call balanceOf
        let result = self.call_rpc::<Vec<String>>(
            "starknet_call",
            serde_json::json!([
                {
                    "contract_address": eth_contract,
                    "entry_point_selector": "0x2e4263afad30923c891518314c3c95dbe830a16874e8abc5777a9a20b54c76e", // balanceOf
                    "calldata": [address]
                },
                "latest"
            ]),
        )?;

        // Parse the u256 result (low, high)
        if result.len() >= 2 {
            let low = u128::from_str_radix(result[0].trim_start_matches("0x"), 16).unwrap_or(0);
            let high = u128::from_str_radix(result[1].trim_start_matches("0x"), 16).unwrap_or(0);
            Ok(low.saturating_add(high.saturating_mul(1u128 << 64)))
        } else if !result.is_empty() {
            u128::from_str_radix(result[0].trim_start_matches("0x"), 16)
                .map_err(|e| StarknetError::Provider(format!("Failed to parse balance: {}", e)))
        } else {
            Ok(0)
        }
    }

    /// Verify an anchor exists on-chain.
    pub fn verify_anchor(&self, root_id: u64, expected_root: &[u8; 32]) -> Result<bool, StarknetError> {
        let contract = self
            .config
            .contract_address
            .as_ref()
            .ok_or_else(|| StarknetError::ConfigError("Contract address required".to_string()))?;

        // Call get_anchor on the contract
        let result = self.call_rpc::<Vec<String>>(
            "starknet_call",
            serde_json::json!([
                {
                    "contract_address": contract,
                    "entry_point_selector": "0x1a35984e05126dbecb7c3bb9929e7dd9106d460c59b1b6e4f2bb0a1b2e06e4e", // get_anchor (example selector)
                    "calldata": [format!("0x{:x}", root_id)]
                },
                "latest"
            ]),
        )?;

        // Parse root from result
        if result.is_empty() {
            return Ok(false);
        }

        // Compare roots
        let stored_root = result[0].trim_start_matches("0x");
        let expected_hex = hex::encode(expected_root);

        Ok(stored_root == expected_hex)
    }

    /// Get anchor status/info.
    pub fn get_anchor_status(&self, root_id: u64) -> Result<Option<AnchorRecord>, StarknetError> {
        let contract = self
            .config
            .contract_address
            .as_ref()
            .ok_or_else(|| StarknetError::ConfigError("Contract address required".to_string()))?;

        let result = self.call_rpc::<Vec<String>>(
            "starknet_call",
            serde_json::json!([
                {
                    "contract_address": contract,
                    "entry_point_selector": "0x1a35984e05126dbecb7c3bb9929e7dd9106d460c59b1b6e4f2bb0a1b2e06e4e", // get_anchor
                    "calldata": [format!("0x{:x}", root_id)]
                },
                "latest"
            ]),
        )?;

        if result.is_empty() {
            return Ok(None);
        }

        // Parse the anchor record (assuming contract returns: root, block_number, timestamp, anchorer)
        if result.len() >= 4 {
            Ok(Some(AnchorRecord {
                root_id,
                root: result[0].clone(),
                block_number: u64::from_str_radix(result[1].trim_start_matches("0x"), 16)
                    .unwrap_or(0),
                timestamp: u64::from_str_radix(result[2].trim_start_matches("0x"), 16)
                    .unwrap_or(0),
                anchorer: result[3].clone(),
            }))
        } else {
            Ok(None)
        }
    }

    /// Compute Poseidon hash for a batch of Merkle roots.
    ///
    /// This is used for creating batch anchors where multiple roots are
    /// combined into a single on-chain root.
    pub fn compute_batch_root(roots: &[[u8; 32]]) -> [u8; 32] {
        if roots.is_empty() {
            return [0u8; 32];
        }

        // Convert roots to Felts
        let felts: Vec<Felt> = roots
            .iter()
            .map(|r| Felt::from_bytes_be_slice(r))
            .collect();

        // Compute Poseidon hash
        let hash = poseidon_hash_many(&felts);

        // Convert back to bytes
        hash.to_bytes_be()
    }

    /// Compute Merkle witness for batch inclusion.
    ///
    /// Returns the sibling hashes needed to prove inclusion in a batch.
    /// Assumes a binary tree with 8 leaves (3 levels).
    pub fn compute_batch_witness(
        roots: &[[u8; 32]],
        index: usize,
    ) -> Result<Vec<[u8; 32]>, StarknetError> {
        if roots.len() > 8 {
            return Err(StarknetError::ConfigError(
                "Batch can have at most 8 roots".to_string(),
            ));
        }

        if index >= roots.len() {
            return Err(StarknetError::ConfigError(format!(
                "Index {} out of range for batch of size {}",
                index,
                roots.len()
            )));
        }

        // Pad to 8 elements if needed
        let mut padded = roots.to_vec();
        while padded.len() < 8 {
            padded.push([0u8; 32]);
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

            // Compute parent level
            let mut parent_level = Vec::new();
            for i in (0..current_level.len()).step_by(2) {
                let left = Felt::from_bytes_be_slice(&current_level[i]);
                let right = if i + 1 < current_level.len() {
                    Felt::from_bytes_be_slice(&current_level[i + 1])
                } else {
                    Felt::ZERO
                };
                let parent = poseidon_hash_many(&[left, right]);
                parent_level.push(parent.to_bytes_be());
            }

            current_level = parent_level;
            current_index /= 2;
        }

        Ok(witness)
    }

    /// Make a JSON-RPC call to the Starknet node.
    fn call_rpc<T: serde::de::DeserializeOwned>(
        &self,
        method: &str,
        params: serde_json::Value,
    ) -> Result<T, StarknetError> {
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
            .send_json(&request)
            .map_err(|e| StarknetError::Network(e.to_string()))?;

        let json: serde_json::Value = response
            .into_json()
            .map_err(|e| StarknetError::Json(e.to_string()))?;

        if let Some(error) = json.get("error") {
            let message = error
                .get("message")
                .and_then(|m| m.as_str())
                .unwrap_or("Unknown error");
            return Err(StarknetError::Provider(message.to_string()));
        }

        let result = json
            .get("result")
            .ok_or_else(|| StarknetError::Provider("Missing result in response".to_string()))?;

        serde_json::from_value(result.clone())
            .map_err(|e| StarknetError::Json(format!("Failed to parse result: {}", e)))
    }
}

/// Parse a Starknet address from hex string to bytes.
pub fn parse_address(addr: &str) -> Result<[u8; 32], StarknetError> {
    validate_starknet_address(addr)?;

    let addr = addr.strip_prefix("0x").unwrap_or(addr);
    let mut bytes = [0u8; 32];

    // Pad with leading zeros if necessary
    let hex_len = addr.len();
    let start = 32 - (hex_len + 1) / 2;

    hex::decode_to_slice(addr, &mut bytes[start..])
        .map_err(|e| StarknetError::InvalidAddress(format!("Hex decode error: {}", e)))?;

    Ok(bytes)
}

/// Format bytes as Starknet address (0x-prefixed hex).
pub fn format_address(bytes: &[u8]) -> String {
    format!("0x{}", hex::encode(bytes).trim_start_matches('0'))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_network_default_urls() {
        assert!(StarknetNetwork::Mainnet
            .default_rpc_url()
            .contains("mainnet"));
        assert!(StarknetNetwork::Sepolia
            .default_rpc_url()
            .contains("sepolia"));
        assert!(StarknetNetwork::Devnet.default_rpc_url().contains("localhost"));
    }

    #[test]
    fn test_network_from_str() {
        assert_eq!(
            StarknetNetwork::from_str("mainnet"),
            Some(StarknetNetwork::Mainnet)
        );
        assert_eq!(
            StarknetNetwork::from_str("sepolia"),
            Some(StarknetNetwork::Sepolia)
        );
        assert_eq!(
            StarknetNetwork::from_str("devnet"),
            Some(StarknetNetwork::Devnet)
        );
        assert_eq!(StarknetNetwork::from_str("invalid"), None);
    }

    #[test]
    fn test_config_validation() {
        let config = StarknetConfig::new(StarknetNetwork::Mainnet);
        assert!(config.validate().is_ok());

        let config_with_contract = config.with_contract("0x049d36570d4e46f48e99674bd3fcc8");
        assert!(config_with_contract.validate().is_ok());

        let invalid_config = StarknetConfig::new(StarknetNetwork::Mainnet)
            .with_contract("not_a_valid_hex");
        assert!(invalid_config.validate().is_err());
    }

    #[test]
    fn test_address_validation() {
        assert!(validate_starknet_address(
            "0x049d36570d4e46f48e99674bd3fcc84644ddd6b96f7c741b1562b82f9e004dc7"
        )
        .is_ok());
        assert!(validate_starknet_address("049d36570d4e46f48e99674bd3fcc8").is_ok());
        assert!(validate_starknet_address("invalid_hex!").is_err());
        assert!(validate_starknet_address(&"a".repeat(65)).is_err());
    }

    #[test]
    fn test_parse_address() {
        let addr = "0x049d36570d4e46f48e99674bd3fcc8";
        let bytes = parse_address(addr).unwrap();
        assert_eq!(&bytes[bytes.len() - 15..], &hex::decode("049d36570d4e46f48e99674bd3fcc8").unwrap()[..]);
    }

    #[test]
    fn test_batch_root_computation() {
        let roots = [
            [0x11u8; 32],
            [0x22u8; 32],
            [0x33u8; 32],
            [0x44u8; 32],
        ];

        let batch_root = StarknetClient::compute_batch_root(&roots);

        // Batch root should be non-zero and deterministic
        assert_ne!(batch_root, [0u8; 32]);

        // Same input should give same output
        let batch_root_2 = StarknetClient::compute_batch_root(&roots);
        assert_eq!(batch_root, batch_root_2);

        // Different input should give different output
        let different_roots = [[0xAAu8; 32]; 4];
        let different_batch_root = StarknetClient::compute_batch_root(&different_roots);
        assert_ne!(batch_root, different_batch_root);
    }

    #[test]
    fn test_batch_witness_computation() {
        let roots = [
            [0x11u8; 32],
            [0x22u8; 32],
            [0x33u8; 32],
            [0x44u8; 32],
        ];

        // Should be able to compute witness for valid indices
        let witness = StarknetClient::compute_batch_witness(&roots, 0).unwrap();
        assert_eq!(witness.len(), 3); // 3 levels for 8 leaves

        // Invalid index should fail
        let result = StarknetClient::compute_batch_witness(&roots, 10);
        assert!(result.is_err());

        // Too many roots should fail
        let too_many: Vec<[u8; 32]> = (0..10).map(|i| [i as u8; 32]).collect();
        let result = StarknetClient::compute_batch_witness(&too_many, 0);
        assert!(result.is_err());
    }

    #[test]
    fn test_empty_batch_root() {
        let empty: &[[u8; 32]] = &[];
        let root = StarknetClient::compute_batch_root(empty);
        assert_eq!(root, [0u8; 32]);
    }
}
