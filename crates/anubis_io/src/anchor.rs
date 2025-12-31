//! HTTP anchoring client for transparency log services.
//!
//! This module provides a client for submitting Merkle roots to HTTP-based
//! transparency logs and retrieving inclusion proofs.
//!
//! ## Protocol
//!
//! The anchoring protocol uses a simple JSON API:
//!
//! ### Submit endpoint: `POST /v1/anchor`
//! ```json
//! { "merkle_root": "<hex>", "timestamp": <unix_secs> }
//! ```
//!
//! ### Response:
//! ```json
//! { "anchor_id": "<uuid>", "status": "pending"|"confirmed", "entry_id": <n> }
//! ```
//!
//! ### Status endpoint: `GET /v1/anchor/<anchor_id>`
//! Returns:
//! ```json
//! { "anchor_id": "<uuid>", "status": "pending"|"confirmed", "entry_id": <n>, "proof": "<hex>" }
//! ```
//!
//! ## Security
//!
//! - All connections use TLS (HTTPS only)
//! - Timeout set to 30 seconds to prevent hanging
//! - Response size limited to 1 MiB

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Maximum response size (1 MiB).
const MAX_RESPONSE_SIZE: u64 = 1024 * 1024;

/// Default timeout in seconds.
const DEFAULT_TIMEOUT_SECS: u64 = 30;

/// Anchoring errors.
#[derive(Debug, Error)]
pub enum AnchorError {
    /// Network/connection error.
    #[error("network error: {0}")]
    Network(String),

    /// HTTP error with status code.
    #[error("HTTP {0}: {1}")]
    Http(u16, String),

    /// JSON parsing error.
    #[error("JSON error: {0}")]
    Json(String),

    /// Invalid URL.
    #[error("invalid URL: {0}")]
    InvalidUrl(String),

    /// Response too large.
    #[error("response exceeds size limit")]
    ResponseTooLarge,

    /// Anchor not found.
    #[error("anchor not found: {0}")]
    NotFound(String),

    /// Invalid anchor status.
    #[error("invalid anchor status: {0}")]
    InvalidStatus(String),
}

/// Anchor status.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum AnchorStatus {
    /// Anchor is pending inclusion in the log.
    Pending,
    /// Anchor has been confirmed and included.
    Confirmed,
    /// Anchor submission failed.
    Failed,
}

impl std::fmt::Display for AnchorStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AnchorStatus::Pending => write!(f, "pending"),
            AnchorStatus::Confirmed => write!(f, "confirmed"),
            AnchorStatus::Failed => write!(f, "failed"),
        }
    }
}

/// Request to submit an anchor.
#[derive(Debug, Serialize)]
struct SubmitRequest<'a> {
    /// Merkle root as hex string.
    merkle_root: &'a str,
    /// Unix timestamp.
    timestamp: i64,
}

/// Response from submit/status endpoints.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AnchorResponse {
    /// Unique anchor ID from the log.
    pub anchor_id: String,
    /// Current status.
    pub status: AnchorStatus,
    /// Log entry ID (if confirmed).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub entry_id: Option<u64>,
    /// Inclusion proof (if confirmed, hex-encoded).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof: Option<String>,
    /// Error message (if failed).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// HTTP anchoring client.
pub struct AnchorClient {
    /// Base URL for the anchoring service.
    base_url: String,
    /// HTTP agent with configured timeout.
    agent: ureq::Agent,
}

impl AnchorClient {
    /// Create a new anchor client for the given service URL.
    ///
    /// # Arguments
    ///
    /// * `base_url` - Base URL of the anchoring service (e.g., `https://anchor.example.com`)
    ///
    /// # Errors
    ///
    /// Returns an error if the URL is invalid.
    pub fn new(base_url: &str) -> Result<Self, AnchorError> {
        // Validate URL format
        if !base_url.starts_with("https://") {
            return Err(AnchorError::InvalidUrl(
                "URL must use HTTPS".to_string(),
            ));
        }

        let agent = ureq::AgentBuilder::new()
            .timeout(std::time::Duration::from_secs(DEFAULT_TIMEOUT_SECS))
            .build();

        Ok(Self {
            base_url: base_url.trim_end_matches('/').to_string(),
            agent,
        })
    }

    /// Submit a Merkle root to the anchoring service.
    ///
    /// # Arguments
    ///
    /// * `merkle_root` - The Merkle root to anchor (32 bytes)
    /// * `timestamp` - Unix timestamp of the batch
    ///
    /// # Returns
    ///
    /// Returns the anchor response with ID and initial status.
    pub fn submit(
        &self,
        merkle_root: &[u8; 32],
        timestamp: i64,
    ) -> Result<AnchorResponse, AnchorError> {
        let url = format!("{}/v1/anchor", self.base_url);
        let merkle_root_hex = hex::encode(merkle_root);

        let request = SubmitRequest {
            merkle_root: &merkle_root_hex,
            timestamp,
        };

        let response = self
            .agent
            .post(&url)
            .set("Content-Type", "application/json")
            .set("User-Agent", "anubis-notary/0.1")
            .send_json(&request)
            .map_err(|e| self.map_ureq_error(e))?;

        self.parse_response(response)
    }

    /// Check the status of an existing anchor.
    ///
    /// # Arguments
    ///
    /// * `anchor_id` - The anchor ID returned from `submit`
    ///
    /// # Returns
    ///
    /// Returns the current status and proof if confirmed.
    pub fn status(&self, anchor_id: &str) -> Result<AnchorResponse, AnchorError> {
        let url = format!("{}/v1/anchor/{}", self.base_url, anchor_id);

        let response = self
            .agent
            .get(&url)
            .set("User-Agent", "anubis-notary/0.1")
            .call()
            .map_err(|e| self.map_ureq_error(e))?;

        self.parse_response(response)
    }

    /// Submit and wait for confirmation with exponential backoff.
    ///
    /// This method submits an anchor and polls with exponential backoff until
    /// confirmed or timeout. The backoff starts at the base interval and doubles
    /// on each attempt, up to a maximum of 60 seconds.
    ///
    /// # Arguments
    ///
    /// * `merkle_root` - The Merkle root to anchor
    /// * `timestamp` - Unix timestamp
    /// * `max_wait_secs` - Maximum seconds to wait for confirmation
    /// * `base_interval_secs` - Initial poll interval (doubles with each attempt)
    ///
    /// # Returns
    ///
    /// Returns the final anchor response.
    ///
    /// # Backoff Strategy
    ///
    /// Uses exponential backoff with jitter to prevent thundering herd:
    /// - First poll: base_interval_secs
    /// - Second poll: base_interval_secs * 2
    /// - Third poll: base_interval_secs * 4
    /// - ... up to MAX_BACKOFF_SECS (60 seconds)
    ///
    /// Small random jitter (0-500ms) is added to prevent synchronized retries.
    pub fn submit_and_wait(
        &self,
        merkle_root: &[u8; 32],
        timestamp: i64,
        max_wait_secs: u64,
        base_interval_secs: u64,
    ) -> Result<AnchorResponse, AnchorError> {
        const MAX_BACKOFF_SECS: u64 = 60;

        let response = self.submit(merkle_root, timestamp)?;

        if response.status == AnchorStatus::Confirmed {
            return Ok(response);
        }

        if response.status == AnchorStatus::Failed {
            return Err(AnchorError::InvalidStatus(
                response.error.unwrap_or_else(|| "unknown error".to_string()),
            ));
        }

        let anchor_id = response.anchor_id;
        let start = std::time::Instant::now();
        let max_duration = std::time::Duration::from_secs(max_wait_secs);
        let mut current_interval_secs = base_interval_secs;

        loop {
            // Add small jitter (0-500ms) to prevent synchronized retries
            let jitter_ms = {
                let mut buf = [0u8; 2];
                if getrandom::getrandom(&mut buf).is_ok() {
                    u16::from_le_bytes(buf) as u64 % 500
                } else {
                    0
                }
            };
            let sleep_duration = std::time::Duration::from_secs(current_interval_secs)
                + std::time::Duration::from_millis(jitter_ms);

            std::thread::sleep(sleep_duration);

            if start.elapsed() > max_duration {
                // Return last known status rather than error
                return self.status(&anchor_id);
            }

            let status = self.status(&anchor_id)?;

            match status.status {
                AnchorStatus::Confirmed => return Ok(status),
                AnchorStatus::Failed => {
                    return Err(AnchorError::InvalidStatus(
                        status.error.unwrap_or_else(|| "unknown error".to_string()),
                    ));
                }
                AnchorStatus::Pending => {
                    // Exponential backoff: double interval, cap at MAX_BACKOFF_SECS
                    current_interval_secs = (current_interval_secs * 2).min(MAX_BACKOFF_SECS);
                }
            }
        }
    }

    fn map_ureq_error(&self, e: ureq::Error) -> AnchorError {
        match e {
            ureq::Error::Status(code, response) => {
                let body = response
                    .into_string()
                    .unwrap_or_else(|_| "unknown error".to_string());
                AnchorError::Http(code, body)
            }
            ureq::Error::Transport(t) => AnchorError::Network(t.to_string()),
        }
    }

    fn parse_response(&self, response: ureq::Response) -> Result<AnchorResponse, AnchorError> {
        // Check content length if present - reject if too large
        if let Some(len) = response.header("Content-Length") {
            if let Ok(len) = len.parse::<u64>() {
                if len > MAX_RESPONSE_SIZE {
                    return Err(AnchorError::ResponseTooLarge);
                }
            }
        }

        // SECURITY: Always limit body read regardless of Content-Length header.
        // A malicious server could omit the header and send unlimited data.
        // Use take() to enforce the limit at the read level.
        use std::io::Read;
        let mut limited_reader = response.into_reader().take(MAX_RESPONSE_SIZE + 1);
        let mut body = String::new();

        match limited_reader.read_to_string(&mut body) {
            Ok(n) if n > MAX_RESPONSE_SIZE as usize => {
                return Err(AnchorError::ResponseTooLarge);
            }
            Ok(_) => {}
            Err(e) => return Err(AnchorError::Network(e.to_string())),
        }

        serde_json::from_str(&body).map_err(|e| AnchorError::Json(e.to_string()))
    }
}

/// Verify an anchor proof against a Merkle root.
///
/// This function verifies that the inclusion proof is valid for the given
/// Merkle root by computing the path from the leaf to the expected tree root.
///
/// # Arguments
///
/// * `merkle_root` - The original Merkle root (leaf hash to verify)
/// * `proof` - The inclusion proof from the log (sequence of 33-byte entries: hash + direction)
/// * `entry_id` - The log entry ID (must be non-zero for confirmed anchors)
/// * `expected_tree_root` - The log's signed tree head root to verify against
///
/// # Returns
///
/// Returns `true` if the proof correctly shows that `merkle_root` is included
/// in the tree with root `expected_tree_root`.
///
/// # Proof Format
///
/// Each step in the proof is 33 bytes:
/// - Bytes 0..32: Sibling hash at this level
/// - Byte 32: Direction (0 = sibling is left, non-zero = sibling is right)
///
/// The proof is verified by starting with the `merkle_root` and repeatedly
/// combining with siblings until we reach the tree root.
pub fn verify_anchor_proof(
    merkle_root: &[u8; 32],
    proof: &[u8],
    entry_id: u64,
    expected_tree_root: &[u8; 32],
) -> bool {
    // Entry ID 0 is reserved (no confirmed anchor)
    if entry_id == 0 {
        return false;
    }

    // Empty proof is only valid if the tree has a single leaf
    // In that case, merkle_root should equal expected_tree_root
    if proof.is_empty() {
        return merkle_root == expected_tree_root;
    }

    // Minimum proof size: at least one step (32-byte hash + 1-byte direction)
    if proof.len() < 33 {
        return false;
    }

    // Proof must be a multiple of 33 bytes (hash + direction per step)
    if proof.len() % 33 != 0 {
        return false;
    }

    // Compute the tree root from the merkle_root and proof path
    let mut current = *merkle_root;
    let proof_steps = proof.len() / 33;

    for i in 0..proof_steps {
        let offset = i * 33;

        // Extract sibling hash (safe: we verified proof.len() % 33 == 0)
        let sibling: [u8; 32] = match proof[offset..offset + 32].try_into() {
            Ok(arr) => arr,
            Err(_) => return false, // Should never happen due to length check
        };

        let is_right = proof[offset + 32] != 0;

        // Combine hashes based on direction
        let combined = if is_right {
            // Current is left child, sibling is right child
            let mut data = [0u8; 64];
            data[..32].copy_from_slice(&current);
            data[32..].copy_from_slice(&sibling);
            anubis_core::keccak::sha3::sha3_256(&data)
        } else {
            // Sibling is left child, current is right child
            let mut data = [0u8; 64];
            data[..32].copy_from_slice(&sibling);
            data[32..].copy_from_slice(&current);
            anubis_core::keccak::sha3::sha3_256(&data)
        };

        current = combined;
    }

    // Verify computed root matches the expected tree root
    use anubis_core::ct::ct_eq;
    ct_eq(&current, expected_tree_root)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_anchor_status_display() {
        assert_eq!(AnchorStatus::Pending.to_string(), "pending");
        assert_eq!(AnchorStatus::Confirmed.to_string(), "confirmed");
        assert_eq!(AnchorStatus::Failed.to_string(), "failed");
    }

    #[test]
    fn test_client_requires_https() {
        let result = AnchorClient::new("http://insecure.example.com");
        assert!(matches!(result, Err(AnchorError::InvalidUrl(_))));

        let result = AnchorClient::new("https://secure.example.com");
        assert!(result.is_ok());
    }

    #[test]
    fn test_anchor_response_serialization() {
        let response = AnchorResponse {
            anchor_id: "abc123".to_string(),
            status: AnchorStatus::Confirmed,
            entry_id: Some(42),
            proof: Some("deadbeef".to_string()),
            error: None,
        };

        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("confirmed"));
        assert!(json.contains("42"));

        let parsed: AnchorResponse = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.anchor_id, "abc123");
        assert_eq!(parsed.status, AnchorStatus::Confirmed);
    }

    #[test]
    fn test_verify_anchor_proof_single_leaf() {
        // For a single-leaf tree, the root IS the leaf
        let root = [0x42u8; 32];
        let tree_root = [0x42u8; 32];
        // Empty proof means single leaf - root should equal tree root
        assert!(verify_anchor_proof(&root, &[], 1, &tree_root));
    }

    #[test]
    fn test_verify_anchor_proof_single_leaf_mismatch() {
        let root = [0x42u8; 32];
        let tree_root = [0x00u8; 32]; // Different
        // Single leaf but roots don't match
        assert!(!verify_anchor_proof(&root, &[], 1, &tree_root));
    }

    #[test]
    fn test_verify_anchor_proof_too_short() {
        let root = [0u8; 32];
        let tree_root = [0u8; 32];
        let short_proof = [0u8; 16]; // Not enough for one step
        assert!(!verify_anchor_proof(&root, &short_proof, 1, &tree_root));
    }

    #[test]
    fn test_verify_anchor_proof_bad_length() {
        let root = [0u8; 32];
        let tree_root = [0u8; 32];
        let bad_proof = [0u8; 50]; // Not multiple of 33
        assert!(!verify_anchor_proof(&root, &bad_proof, 1, &tree_root));
    }

    #[test]
    fn test_verify_anchor_proof_entry_id_zero() {
        let root = [0u8; 32];
        let tree_root = [0u8; 32];
        let proof = [0u8; 33];
        assert!(!verify_anchor_proof(&root, &proof, 0, &tree_root));
    }

    #[test]
    fn test_verify_anchor_proof_valid_path() {
        use anubis_core::keccak::sha3::sha3_256;

        // Create a simple 2-leaf tree:
        // leaf0 = sha3(b"leaf0"), leaf1 = sha3(b"leaf1")
        // root = sha3(leaf0 || leaf1)
        let leaf0 = sha3_256(b"leaf0");
        let leaf1 = sha3_256(b"leaf1");

        let mut combined = [0u8; 64];
        combined[..32].copy_from_slice(&leaf0);
        combined[32..].copy_from_slice(&leaf1);
        let tree_root = sha3_256(&combined);

        // Proof for leaf0: sibling is leaf1, direction = 1 (sibling is right)
        let mut proof = [0u8; 33];
        proof[..32].copy_from_slice(&leaf1);
        proof[32] = 1; // sibling is right

        assert!(verify_anchor_proof(&leaf0, &proof, 1, &tree_root));

        // Proof for leaf1: sibling is leaf0, direction = 0 (sibling is left)
        let mut proof = [0u8; 33];
        proof[..32].copy_from_slice(&leaf0);
        proof[32] = 0; // sibling is left

        assert!(verify_anchor_proof(&leaf1, &proof, 2, &tree_root));
    }

    #[test]
    fn test_verify_anchor_proof_wrong_tree_root() {
        use anubis_core::keccak::sha3::sha3_256;

        let leaf0 = sha3_256(b"leaf0");
        let leaf1 = sha3_256(b"leaf1");

        let mut combined = [0u8; 64];
        combined[..32].copy_from_slice(&leaf0);
        combined[32..].copy_from_slice(&leaf1);
        let _correct_root = sha3_256(&combined);
        let wrong_root = [0xFFu8; 32]; // Wrong tree root

        let mut proof = [0u8; 33];
        proof[..32].copy_from_slice(&leaf1);
        proof[32] = 1;

        // Should fail because tree root doesn't match
        assert!(!verify_anchor_proof(&leaf0, &proof, 1, &wrong_root));
    }
}
