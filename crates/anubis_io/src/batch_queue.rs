//! Batch queue for collecting receipts before anchoring.
//!
//! This module provides a local queue for batching multiple receipt
//! anchoring operations into a single blockchain transaction, reducing
//! costs by up to 8x.
//!
//! # Architecture
//!
//! ```text
//! Receipt 1 ─┐
//! Receipt 2 ─┼─> Batch Queue ─> When full (8 receipts) ─> Single TX to Batch Vault
//! Receipt 3 ─┘
//! ```
//!
//! # Cost Savings
//!
//! - Individual anchoring: 0.1 MINA per receipt
//! - Batch anchoring (8 receipts): 0.1 MINA total = 0.0125 MINA per receipt
//!
//! # Usage
//!
//! ```ignore
//! let mut queue = BatchQueue::open(&keystore_path)?;
//!
//! // Add receipts to queue
//! queue.enqueue(&receipt_digest, &receipt_path)?;
//!
//! // Check if ready to submit (8 receipts)
//! if queue.is_ready() {
//!     let batch = queue.prepare_batch()?;
//!     // Submit batch to blockchain...
//!     queue.mark_submitted(&tx_hash)?;
//! }
//! ```

use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::{read_file, write_file_atomic, IoError, Result};

/// Default number of receipts per batch.
pub const DEFAULT_BATCH_SIZE: usize = 8;

/// Queue file name.
const QUEUE_FILE: &str = "batch_queue.json";

/// Batch history file name.
const HISTORY_FILE: &str = "batch_history.json";

/// Entry in the batch queue.
#[derive(Debug, Clone)]
pub struct BatchQueueEntry {
    /// SHA3-256 digest of the receipt (hex).
    pub digest: String,
    /// Original file path of the receipt.
    pub receipt_path: String,
    /// Timestamp when added to queue (Unix ms).
    pub queued_at: u64,
}

/// Submitted batch record.
#[derive(Debug, Clone)]
pub struct BatchRecord {
    /// Batch ID (Merkle root of digests).
    pub batch_id: String,
    /// Digests included in this batch.
    pub digests: Vec<String>,
    /// Transaction hash on blockchain.
    pub tx_hash: String,
    /// Block height when anchored.
    pub block_height: u64,
    /// Timestamp when submitted (Unix ms).
    pub submitted_at: u64,
}

/// Batch queue for collecting receipts before anchoring.
#[derive(Debug)]
pub struct BatchQueue {
    /// Base path for queue storage.
    path: PathBuf,
    /// Maximum batch size.
    max_batch_size: usize,
}

impl BatchQueue {
    /// Open or create a batch queue at the given path.
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref().to_path_buf();

        // Create directory if needed
        if !path.exists() {
            fs::create_dir_all(&path)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let perms = std::fs::Permissions::from_mode(0o700);
                fs::set_permissions(&path, perms)?;
            }
        }

        Ok(Self {
            path,
            max_batch_size: DEFAULT_BATCH_SIZE,
        })
    }

    /// Set the maximum batch size.
    pub fn with_batch_size(mut self, size: usize) -> Self {
        self.max_batch_size = size.max(1);
        self
    }

    /// Get the queue file path.
    fn queue_path(&self) -> PathBuf {
        self.path.join(QUEUE_FILE)
    }

    /// Get the history file path.
    fn history_path(&self) -> PathBuf {
        self.path.join(HISTORY_FILE)
    }

    /// Add a receipt to the queue.
    ///
    /// Returns the queue entry.
    pub fn enqueue(&self, digest: &[u8; 32], receipt_path: &Path) -> Result<BatchQueueEntry> {
        let digest_hex = hex::encode(digest);
        let receipt_path_str = receipt_path.to_string_lossy().to_string();

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0);

        let entry = BatchQueueEntry {
            digest: digest_hex.clone(),
            receipt_path: receipt_path_str,
            queued_at: now,
        };

        // Read existing queue
        let mut entries = self.read_queue()?;

        // Check for duplicate
        if entries.iter().any(|e| e.digest == digest_hex) {
            return Err(IoError::Keystore(format!(
                "Receipt already queued: {}",
                &digest_hex[..16]
            )));
        }

        // Add new entry
        entries.push(entry.clone());

        // Write updated queue
        self.write_queue(&entries)?;

        Ok(entry)
    }

    /// Get all pending entries in the queue.
    pub fn pending(&self) -> Result<Vec<BatchQueueEntry>> {
        self.read_queue()
    }

    /// Get the number of pending entries.
    pub fn pending_count(&self) -> Result<usize> {
        Ok(self.read_queue()?.len())
    }

    /// Check if the queue has enough entries for a batch.
    pub fn is_ready(&self) -> Result<bool> {
        Ok(self.pending_count()? >= self.max_batch_size)
    }

    /// Prepare a batch from the queue.
    ///
    /// Returns the entries that will be included in the batch.
    /// Does not remove them from the queue - call `mark_submitted` after successful TX.
    pub fn prepare_batch(&self) -> Result<Vec<BatchQueueEntry>> {
        let entries = self.read_queue()?;

        if entries.is_empty() {
            return Err(IoError::Keystore("Queue is empty".to_string()));
        }

        // Take up to max_batch_size entries (oldest first)
        let batch_size = entries.len().min(self.max_batch_size);
        Ok(entries[..batch_size].to_vec())
    }

    /// Mark entries as submitted and move to history.
    ///
    /// Call this after successfully submitting the batch transaction.
    pub fn mark_submitted(
        &self,
        digests: &[String],
        tx_hash: &str,
        block_height: u64,
    ) -> Result<BatchRecord> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0);

        // Compute batch ID (Merkle root of digests)
        let batch_id = compute_batch_id(digests);

        let record = BatchRecord {
            batch_id: batch_id.clone(),
            digests: digests.to_vec(),
            tx_hash: tx_hash.to_string(),
            block_height,
            submitted_at: now,
        };

        // Add to history FIRST to prevent data loss if queue write fails
        let mut history = self.read_history()?;
        history.push(record.clone());
        self.write_history(&history)?;

        // Then remove submitted entries from queue
        let mut entries = self.read_queue()?;
        entries.retain(|e| !digests.contains(&e.digest));
        self.write_queue(&entries)?;

        Ok(record)
    }

    /// Remove a specific entry from the queue.
    pub fn remove(&self, digest: &str) -> Result<bool> {
        let mut entries = self.read_queue()?;
        let initial_len = entries.len();
        entries.retain(|e| e.digest != digest);

        if entries.len() < initial_len {
            self.write_queue(&entries)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Clear all pending entries from the queue.
    pub fn clear(&self) -> Result<usize> {
        let entries = self.read_queue()?;
        let count = entries.len();
        self.write_queue(&[])?;
        Ok(count)
    }

    /// Get batch history.
    pub fn history(&self) -> Result<Vec<BatchRecord>> {
        self.read_history()
    }

    /// Find which batch contains a given digest.
    pub fn find_batch(&self, digest: &str) -> Result<Option<BatchRecord>> {
        let history = self.read_history()?;
        Ok(history.into_iter().find(|b| b.digests.contains(&digest.to_string())))
    }

    /// Read queue entries from file.
    fn read_queue(&self) -> Result<Vec<BatchQueueEntry>> {
        let path = self.queue_path();
        if !path.exists() {
            return Ok(Vec::new());
        }

        let data = read_file(&path)?;
        let json = String::from_utf8_lossy(&data);
        parse_queue_entries(&json)
    }

    /// Write queue entries to file.
    fn write_queue(&self, entries: &[BatchQueueEntry]) -> Result<()> {
        let json = serialize_queue_entries(entries);
        write_file_atomic(self.queue_path(), json.as_bytes())
    }

    /// Read history from file.
    fn read_history(&self) -> Result<Vec<BatchRecord>> {
        let path = self.history_path();
        if !path.exists() {
            return Ok(Vec::new());
        }

        let data = read_file(&path)?;
        let json = String::from_utf8_lossy(&data);
        parse_batch_records(&json)
    }

    /// Write history to file.
    fn write_history(&self, records: &[BatchRecord]) -> Result<()> {
        let json = serialize_batch_records(records);
        write_file_atomic(self.history_path(), json.as_bytes())
    }
}

/// Compute batch ID from digests (Merkle root).
fn compute_batch_id(digests: &[String]) -> String {
    use anubis_core::keccak::sha3::sha3_256;

    if digests.is_empty() {
        return hex::encode([0u8; 32]);
    }

    // Convert hex strings to bytes
    let mut hashes: Vec<[u8; 32]> = digests
        .iter()
        .filter_map(|d| {
            let bytes = hex::decode(d).ok()?;
            if bytes.len() == 32 {
                let mut arr = [0u8; 32];
                arr.copy_from_slice(&bytes);
                Some(arr)
            } else {
                None
            }
        })
        .collect();

    // Build Merkle tree
    while hashes.len() > 1 {
        let mut next_level = Vec::new();
        for chunk in hashes.chunks(2) {
            if chunk.len() == 2 {
                // Hash pair
                let mut combined = [0u8; 65];
                combined[0] = 0x01; // Internal node prefix
                combined[1..33].copy_from_slice(&chunk[0]);
                combined[33..65].copy_from_slice(&chunk[1]);
                next_level.push(sha3_256(&combined));
            } else {
                // Odd node - promote
                next_level.push(chunk[0]);
            }
        }
        hashes = next_level;
    }

    hex::encode(hashes[0])
}

/// Serialize queue entries to JSON.
fn serialize_queue_entries(entries: &[BatchQueueEntry]) -> String {
    let mut json = String::from("[\n");
    for (i, entry) in entries.iter().enumerate() {
        if i > 0 {
            json.push_str(",\n");
        }
        json.push_str(&format!(
            r#"  {{"digest":"{}","receipt_path":"{}","queued_at":{}}}"#,
            entry.digest,
            entry.receipt_path.replace('\\', "\\\\").replace('"', "\\\""),
            entry.queued_at
        ));
    }
    json.push_str("\n]");
    json
}

/// Parse queue entries from JSON.
fn parse_queue_entries(json: &str) -> Result<Vec<BatchQueueEntry>> {
    let mut entries = Vec::new();
    let trimmed = json.trim();

    if !trimmed.starts_with('[') || !trimmed.ends_with(']') {
        return Ok(entries);
    }

    // Simple JSON array parsing
    let inner = &trimmed[1..trimmed.len() - 1];

    // Find each object
    let mut depth = 0;
    let mut start = 0;

    for (i, c) in inner.char_indices() {
        match c {
            '{' => {
                if depth == 0 {
                    start = i;
                }
                depth += 1;
            }
            '}' => {
                depth -= 1;
                if depth == 0 {
                    let obj = &inner[start..=i];
                    if let Some(entry) = parse_queue_entry(obj) {
                        entries.push(entry);
                    }
                }
            }
            _ => {}
        }
    }

    Ok(entries)
}

/// Parse a single queue entry from JSON object.
fn parse_queue_entry(json: &str) -> Option<BatchQueueEntry> {
    let digest = extract_string_field(json, "digest")?;
    let receipt_path = extract_string_field(json, "receipt_path")?;
    let queued_at = extract_number_field(json, "queued_at")?;

    Some(BatchQueueEntry {
        digest,
        receipt_path,
        queued_at,
    })
}

/// Serialize batch records to JSON.
fn serialize_batch_records(records: &[BatchRecord]) -> String {
    let mut json = String::from("[\n");
    for (i, record) in records.iter().enumerate() {
        if i > 0 {
            json.push_str(",\n");
        }
        let digests_json: Vec<String> = record.digests.iter().map(|d| format!(r#""{}""#, d)).collect();
        json.push_str(&format!(
            r#"  {{"batch_id":"{}","digests":[{}],"tx_hash":"{}","block_height":{},"submitted_at":{}}}"#,
            record.batch_id,
            digests_json.join(","),
            record.tx_hash,
            record.block_height,
            record.submitted_at
        ));
    }
    json.push_str("\n]");
    json
}

/// Parse batch records from JSON.
fn parse_batch_records(json: &str) -> Result<Vec<BatchRecord>> {
    let mut records = Vec::new();
    let trimmed = json.trim();

    if !trimmed.starts_with('[') || !trimmed.ends_with(']') {
        return Ok(records);
    }

    let inner = &trimmed[1..trimmed.len() - 1];
    let mut depth = 0;
    let mut start = 0;

    for (i, c) in inner.char_indices() {
        match c {
            '{' => {
                if depth == 0 {
                    start = i;
                }
                depth += 1;
            }
            '}' => {
                depth -= 1;
                if depth == 0 {
                    let obj = &inner[start..=i];
                    if let Some(record) = parse_batch_record(obj) {
                        records.push(record);
                    }
                }
            }
            '[' => depth += 1,
            ']' => depth -= 1,
            _ => {}
        }
    }

    Ok(records)
}

/// Parse a single batch record from JSON object.
fn parse_batch_record(json: &str) -> Option<BatchRecord> {
    let batch_id = extract_string_field(json, "batch_id")?;
    let tx_hash = extract_string_field(json, "tx_hash")?;
    let block_height = extract_number_field(json, "block_height")?;
    let submitted_at = extract_number_field(json, "submitted_at")?;

    // Parse digests array
    let digests_start = json.find(r#""digests":"#)?;
    let arr_start = json[digests_start..].find('[')?;
    let arr_end = json[digests_start + arr_start..].find(']')?;
    let arr = &json[digests_start + arr_start..digests_start + arr_start + arr_end + 1];

    let digests: Vec<String> = arr
        .trim_matches(|c| c == '[' || c == ']')
        .split(',')
        .filter_map(|s| {
            let trimmed = s.trim().trim_matches('"');
            if trimmed.is_empty() {
                None
            } else {
                Some(trimmed.to_string())
            }
        })
        .collect();

    Some(BatchRecord {
        batch_id,
        digests,
        tx_hash,
        block_height,
        submitted_at,
    })
}

/// Extract a string field from JSON.
fn extract_string_field(json: &str, key: &str) -> Option<String> {
    let pattern = format!(r#""{}":"#, key);
    let start = json.find(&pattern)?;
    let value_start = start + pattern.len();

    if json.as_bytes().get(value_start)? != &b'"' {
        return None;
    }

    let content_start = value_start + 1;
    let mut end = content_start;
    let bytes = json.as_bytes();

    while end < bytes.len() {
        if bytes[end] == b'"' && (end == content_start || bytes[end - 1] != b'\\') {
            break;
        }
        end += 1;
    }

    Some(json[content_start..end].to_string())
}

/// Extract a number field from JSON.
fn extract_number_field(json: &str, key: &str) -> Option<u64> {
    let pattern = format!(r#""{}":"#, key);
    let start = json.find(&pattern)?;
    let value_start = start + pattern.len();

    let mut end = value_start;
    let bytes = json.as_bytes();

    while end < bytes.len() && bytes[end].is_ascii_digit() {
        end += 1;
    }

    json[value_start..end].parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_queue_basic() {
        let dir = TempDir::new().unwrap();
        let queue = BatchQueue::open(dir.path()).unwrap();

        // Queue should be empty initially
        assert_eq!(queue.pending_count().unwrap(), 0);
        assert!(!queue.is_ready().unwrap());

        // Add an entry
        let digest = [1u8; 32];
        let path = PathBuf::from("/test/receipt.anb");
        let entry = queue.enqueue(&digest, &path).unwrap();

        assert_eq!(entry.digest, hex::encode([1u8; 32]));
        assert_eq!(queue.pending_count().unwrap(), 1);
        // TempDir auto-cleans on drop
    }

    #[test]
    fn test_queue_duplicate() {
        let dir = TempDir::new().unwrap();
        let queue = BatchQueue::open(dir.path()).unwrap();

        let digest = [2u8; 32];
        let path = PathBuf::from("/test/receipt.anb");

        // First add should succeed
        queue.enqueue(&digest, &path).unwrap();

        // Second add should fail (duplicate)
        assert!(queue.enqueue(&digest, &path).is_err());
        // TempDir auto-cleans on drop
    }

    #[test]
    fn test_batch_id_computation() {
        let digests = vec![
            hex::encode([1u8; 32]),
            hex::encode([2u8; 32]),
        ];

        let batch_id = compute_batch_id(&digests);
        assert_eq!(batch_id.len(), 64); // 32 bytes hex
    }

    #[test]
    fn test_serialize_parse_entries() {
        let entries = vec![
            BatchQueueEntry {
                digest: "abc123".to_string(),
                receipt_path: "/path/to/receipt".to_string(),
                queued_at: 1234567890000,
            },
        ];

        let json = serialize_queue_entries(&entries);
        let parsed = parse_queue_entries(&json).unwrap();

        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].digest, "abc123");
        assert_eq!(parsed[0].receipt_path, "/path/to/receipt");
        assert_eq!(parsed[0].queued_at, 1234567890000);
    }
}
