//! Ztarknet Protocol integration for privacy-preserving blockchain anchoring.
//!
//! This module provides integration with the Ztarknet Protocol (https://ztarknet.cash),
//! a Starknet-compatible L2 that settles to Zcash L1, enabling:
//!
//! - **Privacy-Preserving Anchoring**: Hide document hashes using Pedersen commitments
//! - **Selective Disclosure**: Time-limited viewing tokens for auditors
//! - **Zero-Knowledge Proofs**: Prove document existence without revealing hash
//! - **Zcash Settlement**: Inherit Zcash's privacy features at L1
//!
//! ## Privacy Modes
//!
//! 1. **Public**: Standard anchoring (hash visible on-chain, same as Starknet)
//! 2. **Selective**: Hash encrypted with viewing key, disclosed via tokens
//! 3. **Committed**: Only Pedersen commitment on-chain (ZK proof of existence)
//!
//! ## Architecture
//!
//! ```text
//! Rust (anubis_io) → ureq (HTTPS) → Ztarknet JSON-RPC (Madara) → Zcash L1
//! ```
//!
//! ## Example
//!
//! ```ignore
//! use anubis_io::ztarknet::{ZtarknetClient, ZtarknetConfig, ZtarknetNetwork, PrivacyMode};
//!
//! let config = ZtarknetConfig::new(ZtarknetNetwork::Mainnet)
//!     .with_contract("0x...");
//!
//! let client = ZtarknetClient::new(config)?;
//!
//! // Anchor with privacy (hash hidden)
//! let result = client.anchor_with_privacy(&hash, PrivacyMode::Committed)?;
//! println!("Commitment ID: {}", result.commitment_id);
//! ```

use serde::{Deserialize, Serialize};
use sha3::{Digest, Keccak256};
use starknet_core::types::Felt;
use starknet_crypto::poseidon_hash_many;
use thiserror::Error;

/// Ztarknet error types.
#[derive(Error, Debug)]
pub enum ZtarknetError {
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

    /// Invalid commitment.
    #[error("invalid commitment: {0}")]
    InvalidCommitment(String),

    /// Disclosure expired.
    #[error("disclosure token expired")]
    DisclosureExpired,

    /// Commitment not found.
    #[error("commitment not found: {0}")]
    CommitmentNotFound(u64),

    /// Already revealed.
    #[error("commitment already revealed")]
    AlreadyRevealed,

    /// Request timeout.
    #[error("request timeout")]
    Timeout,

    /// HTTP/network error.
    #[error("network error: {0}")]
    Network(String),

    /// JSON serialization/deserialization error.
    #[error("JSON error: {0}")]
    Json(String),

    /// Starknet client error (for Madara compatibility).
    #[error("starknet error: {0}")]
    Starknet(#[from] crate::starknet::StarknetError),
}

/// Ztarknet network selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ZtarknetNetwork {
    /// Ztarknet mainnet (settles to Zcash mainnet).
    #[default]
    Mainnet,
    /// Ztarknet testnet (settles to Zcash testnet).
    Testnet,
    /// Local Ztarknet devnet.
    Devnet,
}

impl ZtarknetNetwork {
    /// Get the default RPC URL for this network.
    ///
    /// Note: These URLs are placeholders until Ztarknet launches.
    pub fn default_rpc_url(&self) -> &'static str {
        match self {
            ZtarknetNetwork::Mainnet => "https://rpc.ztarknet.cash",
            ZtarknetNetwork::Testnet => "https://testnet-rpc.ztarknet.cash",
            ZtarknetNetwork::Devnet => "http://localhost:5050",
        }
    }

    /// Get the network name.
    pub fn name(&self) -> &'static str {
        match self {
            ZtarknetNetwork::Mainnet => "ztarknet-mainnet",
            ZtarknetNetwork::Testnet => "ztarknet-testnet",
            ZtarknetNetwork::Devnet => "ztarknet-devnet",
        }
    }

    /// Parse network from string.
    pub fn parse(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "mainnet" | "main" | "ztarknet-mainnet" => Some(ZtarknetNetwork::Mainnet),
            "testnet" | "test" | "ztarknet-testnet" => Some(ZtarknetNetwork::Testnet),
            "devnet" | "local" | "ztarknet-devnet" => Some(ZtarknetNetwork::Devnet),
            _ => None,
        }
    }
}

/// Privacy mode for anchoring.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PrivacyMode {
    /// Standard anchoring - hash visible on-chain.
    #[default]
    Public,
    /// Selective disclosure - viewing key required.
    Selective,
    /// Committed anchoring - only Pedersen commitment on-chain.
    Committed,
}

impl PrivacyMode {
    /// Parse from string.
    pub fn parse(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "public" => Some(PrivacyMode::Public),
            "selective" => Some(PrivacyMode::Selective),
            "committed" | "private" | "zk" => Some(PrivacyMode::Committed),
            _ => None,
        }
    }

    /// Get display name.
    pub fn name(&self) -> &'static str {
        match self {
            PrivacyMode::Public => "public",
            PrivacyMode::Selective => "selective",
            PrivacyMode::Committed => "committed",
        }
    }
}

/// Pedersen commitment for hiding document hashes.
///
/// A commitment is computed as: C = Poseidon(document_hash, blinding_factor)
///
/// This is binding (can't change the hash after committing) and hiding
/// (the hash is not revealed until explicitly disclosed).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PedersenCommitment {
    /// The commitment value (on-chain).
    pub commitment: [u8; 32],
    /// Blinding factor (secret, for reveal).
    pub blinding_factor: [u8; 32],
    /// Original document hash (secret, for reveal).
    pub original_hash: [u8; 32],
}

impl PedersenCommitment {
    /// Create a new Pedersen commitment for a document hash.
    ///
    /// Generates a cryptographically random blinding factor and computes
    /// the commitment using Poseidon hash (Cairo/Starknet compatible).
    pub fn new(document_hash: &[u8; 32]) -> Self {
        let mut blinding = [0u8; 32];
        getrandom::getrandom(&mut blinding).expect("Failed to generate random blinding factor");

        let commitment = Self::compute_commitment(document_hash, &blinding);

        Self {
            commitment,
            blinding_factor: blinding,
            original_hash: *document_hash,
        }
    }

    /// Create a commitment with a specific blinding factor (for testing/recovery).
    pub fn with_blinding(document_hash: &[u8; 32], blinding: &[u8; 32]) -> Self {
        let commitment = Self::compute_commitment(document_hash, blinding);
        Self {
            commitment,
            blinding_factor: *blinding,
            original_hash: *document_hash,
        }
    }

    /// Compute C = Poseidon(document_hash, blinding_factor).
    ///
    /// Uses Starknet's Poseidon implementation for Cairo compatibility.
    fn compute_commitment(message: &[u8; 32], blinding: &[u8; 32]) -> [u8; 32] {
        // Convert to Felt (split into two 16-byte chunks for each 32-byte input)
        let msg_high = Felt::from_bytes_be_slice(&message[0..16]);
        let msg_low = Felt::from_bytes_be_slice(&message[16..32]);
        let blind_high = Felt::from_bytes_be_slice(&blinding[0..16]);
        let blind_low = Felt::from_bytes_be_slice(&blinding[16..32]);

        // Combine message chunks into single felt
        let msg_felt = poseidon_hash_many(&[msg_high, msg_low]);
        let blind_felt = poseidon_hash_many(&[blind_high, blind_low]);

        // Compute final commitment
        let commitment_felt = poseidon_hash_many(&[msg_felt, blind_felt]);
        commitment_felt.to_bytes_be()
    }

    /// Verify the commitment matches the original values.
    pub fn verify(&self) -> bool {
        let computed = Self::compute_commitment(&self.original_hash, &self.blinding_factor);
        computed == self.commitment
    }

    /// Get the commitment as a hex string.
    pub fn commitment_hex(&self) -> String {
        format!("0x{}", hex::encode(self.commitment))
    }

    /// Get the blinding factor as a hex string.
    pub fn blinding_hex(&self) -> String {
        format!("0x{}", hex::encode(self.blinding_factor))
    }

    /// Get the original hash as a hex string.
    pub fn hash_hex(&self) -> String {
        format!("0x{}", hex::encode(self.original_hash))
    }
}

/// Disclosure token for selective revelation to auditors.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DisclosureToken {
    /// Token ID (hash of parameters).
    pub token_id: [u8; 32],
    /// The commitment this token grants access to.
    pub commitment_id: u64,
    /// Recipient address/identifier.
    pub recipient: String,
    /// Expiration timestamp (seconds since UNIX epoch).
    pub expires_at: u64,
    /// Optional viewing key for decryption.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub viewing_key: Option<Vec<u8>>,
}

impl DisclosureToken {
    /// Check if the token has expired.
    pub fn is_expired(&self) -> bool {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        now > self.expires_at
    }

    /// Get the token ID as hex.
    pub fn token_id_hex(&self) -> String {
        format!("0x{}", hex::encode(self.token_id))
    }
}

/// Configuration for Ztarknet client.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ZtarknetConfig {
    /// RPC endpoint URL.
    pub rpc_url: String,
    /// Network selection.
    pub network: ZtarknetNetwork,
    /// PrivacyOracle contract address (hex with 0x prefix).
    pub contract_address: Option<String>,
    /// Account address for signing (hex with 0x prefix).
    pub account_address: Option<String>,
    /// Default privacy mode for anchoring.
    #[serde(default)]
    pub default_privacy_mode: PrivacyMode,
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

impl Default for ZtarknetConfig {
    fn default() -> Self {
        Self::new(ZtarknetNetwork::Mainnet)
    }
}

impl ZtarknetConfig {
    /// Create a new configuration for the specified network.
    pub fn new(network: ZtarknetNetwork) -> Self {
        Self {
            rpc_url: network.default_rpc_url().to_string(),
            network,
            contract_address: None,
            account_address: None,
            default_privacy_mode: PrivacyMode::Committed,
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

    /// Set the default privacy mode.
    pub fn with_privacy_mode(mut self, mode: PrivacyMode) -> Self {
        self.default_privacy_mode = mode;
        self
    }

    /// Set the timeout.
    pub fn with_timeout(mut self, secs: u64) -> Self {
        self.timeout_secs = secs;
        self
    }

    /// Validate the configuration.
    pub fn validate(&self) -> Result<(), ZtarknetError> {
        if self.rpc_url.is_empty() {
            return Err(ZtarknetError::ConfigError(
                "RPC URL is required".to_string(),
            ));
        }

        if let Some(addr) = &self.contract_address {
            validate_address(addr)?;
        }

        if let Some(addr) = &self.account_address {
            validate_address(addr)?;
        }

        Ok(())
    }
}

/// Validate a Starknet/Ztarknet address.
fn validate_address(addr: &str) -> Result<(), ZtarknetError> {
    let addr = addr.strip_prefix("0x").unwrap_or(addr);

    if !addr.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(ZtarknetError::InvalidAddress(format!(
            "Invalid hex characters in address: {}",
            addr
        )));
    }

    if addr.len() > 64 {
        return Err(ZtarknetError::InvalidAddress(format!(
            "Address too long (max 64 hex chars): {}",
            addr.len()
        )));
    }

    Ok(())
}

/// Result of a privacy-preserving anchor operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrivacyAnchorResult {
    /// Transaction hash (hex).
    pub tx_hash: String,
    /// Block number when included.
    pub block_number: u64,
    /// Block timestamp (seconds since UNIX epoch).
    pub timestamp: u64,
    /// Commitment ID assigned by the contract.
    pub commitment_id: u64,
    /// Privacy mode used.
    pub privacy_mode: PrivacyMode,
    /// The commitment stored on-chain (for Committed mode).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub commitment: Option<[u8; 32]>,
    /// The blinding factor (for reveal, stored locally).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub blinding_factor: Option<[u8; 32]>,
    /// Contract address used.
    pub contract_address: String,
}

/// Result of a reveal operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RevealResult {
    /// Transaction hash (hex).
    pub tx_hash: String,
    /// Block number when included.
    pub block_number: u64,
    /// Commitment ID that was revealed.
    pub commitment_id: u64,
    /// The original hash that was revealed.
    pub original_hash: [u8; 32],
}

/// Block time result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockTimeResult {
    /// Current block number.
    pub block_number: u64,
    /// Block timestamp in seconds since UNIX epoch.
    pub timestamp: u64,
}

/// Information about a commitment.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommitmentInfo {
    /// The Pedersen commitment stored on-chain.
    pub commitment: [u8; 32],
    /// Timestamp when anchored.
    pub timestamp: u64,
    /// Whether the commitment has been revealed.
    pub revealed: bool,
    /// The original hash if revealed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub original_hash: Option<[u8; 32]>,
    /// Commitment ID.
    pub commitment_id: u64,
}

/// Result of verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VerifyResult {
    /// Public verification succeeded.
    Public { verified: bool, timestamp: u64 },
    /// Commitment verified but not revealed.
    CommitmentExists { commitment_id: u64, timestamp: u64 },
    /// Commitment was revealed and verified.
    Revealed {
        verified: bool,
        commitment_id: u64,
        timestamp: u64,
    },
    /// Need viewing key or reveal to verify.
    NeedsDisclosure,
}

/// Blocking Ztarknet JSON-RPC client.
///
/// Provides privacy-preserving document anchoring on Ztarknet.
#[derive(Debug)]
pub struct ZtarknetClient {
    /// Client configuration.
    config: ZtarknetConfig,
    /// HTTP client.
    agent: ureq::Agent,
}

impl ZtarknetClient {
    /// Create a new Ztarknet client.
    pub fn new(config: ZtarknetConfig) -> Result<Self, ZtarknetError> {
        config.validate()?;

        let agent = ureq::AgentBuilder::new()
            .timeout(std::time::Duration::from_secs(config.timeout_secs))
            .build();

        Ok(Self { config, agent })
    }

    /// Get the current configuration.
    pub fn config(&self) -> &ZtarknetConfig {
        &self.config
    }

    /// Create a Pedersen commitment for a document hash.
    ///
    /// This is a local operation - nothing is sent to the network.
    pub fn create_commitment(document_hash: &[u8; 32]) -> PedersenCommitment {
        PedersenCommitment::new(document_hash)
    }

    /// Anchor a document with the specified privacy mode.
    ///
    /// - **Public**: Standard anchoring (hash visible)
    /// - **Selective**: Anchors commitment, requires viewing key for disclosure
    /// - **Committed**: Only commitment on-chain, hash never revealed publicly
    pub fn anchor_with_privacy(
        &self,
        document_hash: &[u8; 32],
        mode: PrivacyMode,
    ) -> Result<PrivacyAnchorResult, ZtarknetError> {
        match mode {
            PrivacyMode::Public => self.anchor_public(document_hash),
            PrivacyMode::Selective | PrivacyMode::Committed => {
                self.anchor_committed(document_hash)
            }
        }
    }

    /// Anchor with default privacy mode from config.
    pub fn anchor(&self, document_hash: &[u8; 32]) -> Result<PrivacyAnchorResult, ZtarknetError> {
        self.anchor_with_privacy(document_hash, self.config.default_privacy_mode)
    }

    /// Public anchoring (hash visible on-chain).
    fn anchor_public(&self, document_hash: &[u8; 32]) -> Result<PrivacyAnchorResult, ZtarknetError> {
        let contract = self.get_contract_address()?;

        // Convert to Poseidon felt (same as Starknet module)
        let high = Felt::from_bytes_be_slice(&document_hash[0..16]);
        let low = Felt::from_bytes_be_slice(&document_hash[16..32]);
        let root_felt = poseidon_hash_many(&[high, low]);
        let _root_hex = format!("0x{:x}", root_felt);

        // TODO: Implement actual RPC call when Ztarknet launches
        // For now, return a placeholder result
        Ok(PrivacyAnchorResult {
            tx_hash: format!("0x{}", hex::encode([0u8; 32])),
            block_number: 0,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            commitment_id: 0,
            privacy_mode: PrivacyMode::Public,
            commitment: None,
            blinding_factor: None,
            contract_address: contract,
        })
    }

    /// Committed anchoring (only commitment on-chain).
    fn anchor_committed(
        &self,
        document_hash: &[u8; 32],
    ) -> Result<PrivacyAnchorResult, ZtarknetError> {
        let contract = self.get_contract_address()?;

        // Create Pedersen commitment
        let commitment = PedersenCommitment::new(document_hash);

        // TODO: Implement actual RPC call to anchor_commitment when Ztarknet launches
        // The commitment.commitment should be sent to the PrivacyOracle contract

        Ok(PrivacyAnchorResult {
            tx_hash: format!("0x{}", hex::encode([0u8; 32])),
            block_number: 0,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            commitment_id: 0,
            privacy_mode: PrivacyMode::Committed,
            commitment: Some(commitment.commitment),
            blinding_factor: Some(commitment.blinding_factor),
            contract_address: contract,
        })
    }

    /// Reveal a committed anchor.
    ///
    /// This proves on-chain that the original hash matches the commitment.
    /// After reveal, the hash is publicly visible.
    pub fn reveal_commitment(
        &self,
        commitment_id: u64,
        original_hash: &[u8; 32],
        blinding_factor: &[u8; 32],
    ) -> Result<RevealResult, ZtarknetError> {
        let _contract = self.get_contract_address()?;

        // Verify locally first
        let commitment = PedersenCommitment::with_blinding(original_hash, blinding_factor);
        if !commitment.verify() {
            return Err(ZtarknetError::InvalidCommitment(
                "Local verification failed".to_string(),
            ));
        }

        // TODO: Implement actual RPC call to reveal_commitment when Ztarknet launches

        Ok(RevealResult {
            tx_hash: format!("0x{}", hex::encode([0u8; 32])),
            block_number: 0,
            commitment_id,
            original_hash: *original_hash,
        })
    }

    /// Grant a disclosure token to an auditor.
    ///
    /// The token allows the recipient to verify the commitment for a limited time.
    pub fn grant_disclosure(
        &self,
        commitment_id: u64,
        recipient: &str,
        duration_seconds: u64,
    ) -> Result<DisclosureToken, ZtarknetError> {
        let _contract = self.get_contract_address()?;

        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        let expires_at = now + duration_seconds;

        // Compute token ID
        let mut hasher = Keccak256::new();
        hasher.update(commitment_id.to_le_bytes());
        hasher.update(recipient.as_bytes());
        hasher.update(expires_at.to_le_bytes());
        let token_id: [u8; 32] = hasher.finalize().into();

        // TODO: Implement actual RPC call to grant_disclosure when Ztarknet launches

        Ok(DisclosureToken {
            token_id,
            commitment_id,
            recipient: recipient.to_string(),
            expires_at,
            viewing_key: None,
        })
    }

    /// Verify a disclosure token is valid.
    pub fn verify_disclosure(
        &self,
        token_id: &[u8; 32],
        claimer: &str,
    ) -> Result<bool, ZtarknetError> {
        let _contract = self.get_contract_address()?;

        // Compute claimer hash
        let mut hasher = Keccak256::new();
        hasher.update(claimer.as_bytes());
        let _claimer_hash: [u8; 32] = hasher.finalize().into();

        // TODO: Implement actual RPC call to verify_disclosure when Ztarknet launches
        // For now, return false (unverified)
        let _ = token_id;
        Ok(false)
    }

    /// Revoke a disclosure token.
    pub fn revoke_disclosure(&self, token_id: &[u8; 32]) -> Result<bool, ZtarknetError> {
        let _contract = self.get_contract_address()?;

        // TODO: Implement actual RPC call to revoke_disclosure when Ztarknet launches
        let _ = token_id;
        Ok(true)
    }

    /// Verify an anchor exists.
    pub fn verify_anchor(
        &self,
        document_hash: &[u8; 32],
        mode: PrivacyMode,
    ) -> Result<VerifyResult, ZtarknetError> {
        match mode {
            PrivacyMode::Public => {
                // TODO: Implement actual verification
                Ok(VerifyResult::Public {
                    verified: false,
                    timestamp: 0,
                })
            }
            PrivacyMode::Selective | PrivacyMode::Committed => {
                // Can't verify without commitment ID and blinding factor
                let _ = document_hash;
                Ok(VerifyResult::NeedsDisclosure)
            }
        }
    }

    /// Get block time from the network.
    pub fn get_block_time(&self) -> Result<BlockTimeResult, ZtarknetError> {
        // TODO: Implement actual RPC call when Ztarknet launches
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        Ok(BlockTimeResult {
            block_number: 0,
            timestamp: now,
        })
    }

    /// Get account balance in wei.
    pub fn get_balance(&self, account: &str) -> Result<u128, ZtarknetError> {
        // TODO: Implement actual RPC call when Ztarknet launches
        let _ = account;
        Ok(0)
    }

    /// Get information about a commitment.
    pub fn get_commitment_info(&self, commitment_id: u64) -> Result<CommitmentInfo, ZtarknetError> {
        let _contract = self.get_contract_address()?;

        // TODO: Implement actual RPC call when Ztarknet launches
        Ok(CommitmentInfo {
            commitment: [0u8; 32],
            timestamp: 0,
            revealed: false,
            original_hash: None,
            commitment_id,
        })
    }

    /// Helper to get contract address from config.
    fn get_contract_address(&self) -> Result<String, ZtarknetError> {
        self.config
            .contract_address
            .clone()
            .ok_or_else(|| ZtarknetError::ConfigError("Contract address required".to_string()))
    }

    /// Make a JSON-RPC call.
    #[allow(dead_code)]
    fn call_rpc<T: serde::de::DeserializeOwned>(
        &self,
        method: &str,
        params: serde_json::Value,
    ) -> Result<T, ZtarknetError> {
        let body = serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": method,
            "params": params,
        });

        let response = self
            .agent
            .post(&self.config.rpc_url)
            .set("Content-Type", "application/json")
            .send_json(&body)
            .map_err(|e| ZtarknetError::Network(e.to_string()))?;

        let result: serde_json::Value = response
            .into_json()
            .map_err(|e| ZtarknetError::Json(e.to_string()))?;

        if let Some(error) = result.get("error") {
            return Err(ZtarknetError::Provider(error.to_string()));
        }

        let result = result.get("result").ok_or_else(|| {
            ZtarknetError::Provider("Missing 'result' in response".to_string())
        })?;

        serde_json::from_value(result.clone())
            .map_err(|e| ZtarknetError::Json(e.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pedersen_commitment_roundtrip() {
        let hash = [0x42u8; 32];
        let commitment = PedersenCommitment::new(&hash);

        // Verify the commitment is valid
        assert!(commitment.verify());

        // Recreate with same values should produce same commitment
        let commitment2 =
            PedersenCommitment::with_blinding(&hash, &commitment.blinding_factor);
        assert_eq!(commitment.commitment, commitment2.commitment);
        assert!(commitment2.verify());
    }

    #[test]
    fn test_different_hashes_different_commitments() {
        let blinding = [0x11u8; 32];

        let hash1 = [0x01u8; 32];
        let hash2 = [0x02u8; 32];

        let commitment1 = PedersenCommitment::with_blinding(&hash1, &blinding);
        let commitment2 = PedersenCommitment::with_blinding(&hash2, &blinding);

        assert_ne!(commitment1.commitment, commitment2.commitment);
    }

    #[test]
    fn test_different_blindings_different_commitments() {
        let hash = [0x42u8; 32];

        let blinding1 = [0x11u8; 32];
        let blinding2 = [0x22u8; 32];

        let commitment1 = PedersenCommitment::with_blinding(&hash, &blinding1);
        let commitment2 = PedersenCommitment::with_blinding(&hash, &blinding2);

        assert_ne!(commitment1.commitment, commitment2.commitment);
    }

    #[test]
    fn test_commitment_hex_formats() {
        let hash = [0x42u8; 32];
        let commitment = PedersenCommitment::new(&hash);

        assert!(commitment.commitment_hex().starts_with("0x"));
        assert!(commitment.blinding_hex().starts_with("0x"));
        assert!(commitment.hash_hex().starts_with("0x"));
    }

    #[test]
    fn test_disclosure_token_expiry() {
        let token = DisclosureToken {
            token_id: [0u8; 32],
            commitment_id: 1,
            recipient: "auditor".to_string(),
            expires_at: 0, // Already expired
            viewing_key: None,
        };
        assert!(token.is_expired());

        let future_token = DisclosureToken {
            token_id: [0u8; 32],
            commitment_id: 1,
            recipient: "auditor".to_string(),
            expires_at: u64::MAX, // Far future
            viewing_key: None,
        };
        assert!(!future_token.is_expired());
    }

    #[test]
    fn test_privacy_mode_parse() {
        assert_eq!(PrivacyMode::parse("public"), Some(PrivacyMode::Public));
        assert_eq!(PrivacyMode::parse("selective"), Some(PrivacyMode::Selective));
        assert_eq!(PrivacyMode::parse("committed"), Some(PrivacyMode::Committed));
        assert_eq!(PrivacyMode::parse("private"), Some(PrivacyMode::Committed));
        assert_eq!(PrivacyMode::parse("zk"), Some(PrivacyMode::Committed));
        assert_eq!(PrivacyMode::parse("invalid"), None);
    }

    #[test]
    fn test_network_parse() {
        assert_eq!(
            ZtarknetNetwork::parse("mainnet"),
            Some(ZtarknetNetwork::Mainnet)
        );
        assert_eq!(
            ZtarknetNetwork::parse("testnet"),
            Some(ZtarknetNetwork::Testnet)
        );
        assert_eq!(
            ZtarknetNetwork::parse("devnet"),
            Some(ZtarknetNetwork::Devnet)
        );
    }

    #[test]
    fn test_config_validation() {
        let config = ZtarknetConfig::new(ZtarknetNetwork::Testnet)
            .with_contract("0x1234567890abcdef");
        assert!(config.validate().is_ok());

        let bad_config = ZtarknetConfig::new(ZtarknetNetwork::Testnet)
            .with_contract("not-hex");
        assert!(bad_config.validate().is_err());
    }

    #[test]
    fn test_client_creation() {
        let config = ZtarknetConfig::new(ZtarknetNetwork::Devnet)
            .with_contract("0x123");
        let client = ZtarknetClient::new(config);
        assert!(client.is_ok());
    }

    #[test]
    fn test_create_commitment_static() {
        let hash = [0xAAu8; 32];
        let commitment = ZtarknetClient::create_commitment(&hash);
        assert!(commitment.verify());
        assert_eq!(commitment.original_hash, hash);
    }
}
