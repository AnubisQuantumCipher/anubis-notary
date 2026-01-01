//! Audit logging for security-critical operations.
//!
//! This module provides tamper-evident audit logging with cryptographic
//! integrity protection for all security-sensitive operations.
//!
//! ## Security Properties
//!
//! - All entries are cryptographically chained (hash chain)
//! - Entries include precise timestamps
//! - Log tampering is detectable
//! - Sensitive data (passwords, keys) is never logged
//!
//! ## Logged Operations
//!
//! - Key generation and derivation
//! - Signing operations
//! - Verification attempts (success/failure)
//! - Encryption/decryption
//! - License operations
//! - Authentication attempts
//! - Key recovery operations

use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::keccak::sha3::sha3_256;

/// Maximum log file size before rotation (10 MiB).
const MAX_LOG_SIZE: u64 = 10 * 1024 * 1024;

/// Number of rotated logs to keep.
const MAX_ROTATED_LOGS: usize = 5;

/// Split a string on a delimiter, respecting escape sequences.
/// For example, split_escaped("a|b\\|c|d", '|', '\\') returns ["a", "b|c", "d"].
fn split_escaped(s: &str, delimiter: char, escape: char) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == escape {
            if let Some(&next) = chars.peek() {
                if next == delimiter || next == escape {
                    current.push(chars.next().unwrap());
                } else {
                    current.push(c);
                }
            } else {
                current.push(c);
            }
        } else if c == delimiter {
            parts.push(std::mem::take(&mut current));
        } else {
            current.push(c);
        }
    }
    parts.push(current);
    parts
}

/// Audit event severity levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Severity {
    /// Informational events (key generation, successful operations).
    Info = 0,
    /// Warning events (rate limiting triggered, unusual patterns).
    Warning = 1,
    /// Error events (verification failures, decryption failures).
    Error = 2,
    /// Critical events (potential attacks, key compromise indicators).
    Critical = 3,
}

impl Severity {
    /// Convert to string representation.
    pub fn as_str(&self) -> &'static str {
        match self {
            Severity::Info => "INFO",
            Severity::Warning => "WARN",
            Severity::Error => "ERROR",
            Severity::Critical => "CRIT",
        }
    }

    /// Parse severity from string representation.
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "INFO" => Some(Severity::Info),
            "WARN" => Some(Severity::Warning),
            "ERROR" => Some(Severity::Error),
            "CRIT" => Some(Severity::Critical),
            _ => None,
        }
    }
}

/// Audit event categories.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventCategory {
    /// Key management operations.
    KeyManagement,
    /// Signing operations.
    Signing,
    /// Verification operations.
    Verification,
    /// Encryption/decryption operations.
    Encryption,
    /// Authentication attempts.
    Authentication,
    /// License operations.
    License,
    /// Receipt/attestation operations.
    Attestation,
    /// Anchor/timestamping operations.
    Anchoring,
    /// Key recovery operations.
    Recovery,
    /// HSM operations.
    Hsm,
    /// System events.
    System,
}

impl EventCategory {
    /// Convert to string representation.
    pub fn as_str(&self) -> &'static str {
        match self {
            EventCategory::KeyManagement => "KEY",
            EventCategory::Signing => "SIGN",
            EventCategory::Verification => "VERIFY",
            EventCategory::Encryption => "ENCRYPT",
            EventCategory::Authentication => "AUTH",
            EventCategory::License => "LICENSE",
            EventCategory::Attestation => "ATTEST",
            EventCategory::Anchoring => "ANCHOR",
            EventCategory::Recovery => "RECOVERY",
            EventCategory::Hsm => "HSM",
            EventCategory::System => "SYSTEM",
        }
    }
}

/// An audit log entry.
#[derive(Debug, Clone)]
pub struct AuditEntry {
    /// Unix timestamp in milliseconds.
    pub timestamp: i64,
    /// Event sequence number.
    pub sequence: u64,
    /// Severity level.
    pub severity: Severity,
    /// Event category.
    pub category: EventCategory,
    /// Event description.
    pub message: String,
    /// Additional context (key ID, file path, etc.).
    pub context: Option<String>,
    /// Hash of previous entry (chain integrity).
    pub prev_hash: [u8; 32],
    /// Hash of this entry.
    pub entry_hash: [u8; 32],
}

impl AuditEntry {
    /// Compute the hash of this entry's content.
    fn compute_hash(&self) -> [u8; 32] {
        let mut data = Vec::new();
        data.extend_from_slice(&self.timestamp.to_le_bytes());
        data.extend_from_slice(&self.sequence.to_le_bytes());
        data.push(self.severity as u8);
        data.extend_from_slice(self.category.as_str().as_bytes());
        data.extend_from_slice(self.message.as_bytes());
        if let Some(ref ctx) = self.context {
            data.extend_from_slice(ctx.as_bytes());
        }
        data.extend_from_slice(&self.prev_hash);
        sha3_256(&data)
    }

    /// Serialize entry to log line format.
    pub fn to_log_line(&self) -> String {
        let context_str = self.context.as_deref().unwrap_or("-");
        format!(
            "{}|{}|{}|{}|{}|{}|{}|{}\n",
            self.timestamp,
            self.sequence,
            self.severity.as_str(),
            self.category.as_str(),
            self.message.replace('|', "\\|"),
            context_str.replace('|', "\\|"),
            hex::encode(self.prev_hash),
            hex::encode(self.entry_hash),
        )
    }

    /// Parse entry from log line.
    pub fn from_log_line(line: &str) -> Option<Self> {
        // Use escape-aware splitting (backslash escapes |)
        let parts = split_escaped(line.trim(), '|', '\\');
        if parts.len() != 8 {
            return None;
        }

        let timestamp = parts[0].parse().ok()?;
        let sequence = parts[1].parse().ok()?;
        let severity = Severity::parse(&parts[2])?;
        let category_str = parts[3].as_str();
        let message = parts[4].clone();
        let context = if parts[5] == "-" {
            None
        } else {
            Some(parts[5].clone())
        };
        let prev_hash = hex::decode(&parts[6]).ok()?;
        let entry_hash = hex::decode(&parts[7]).ok()?;

        if prev_hash.len() != 32 || entry_hash.len() != 32 {
            return None;
        }

        let category = match category_str {
            "KEY" => EventCategory::KeyManagement,
            "SIGN" => EventCategory::Signing,
            "VERIFY" => EventCategory::Verification,
            "ENCRYPT" => EventCategory::Encryption,
            "AUTH" => EventCategory::Authentication,
            "LICENSE" => EventCategory::License,
            "ATTEST" => EventCategory::Attestation,
            "ANCHOR" => EventCategory::Anchoring,
            "RECOVERY" => EventCategory::Recovery,
            "HSM" => EventCategory::Hsm,
            "SYSTEM" => EventCategory::System,
            _ => return None,
        };

        let mut prev_hash_arr = [0u8; 32];
        let mut entry_hash_arr = [0u8; 32];
        prev_hash_arr.copy_from_slice(&prev_hash);
        entry_hash_arr.copy_from_slice(&entry_hash);

        Some(Self {
            timestamp,
            sequence,
            severity,
            category,
            message,
            context,
            prev_hash: prev_hash_arr,
            entry_hash: entry_hash_arr,
        })
    }

    /// Verify this entry's hash chain integrity.
    pub fn verify(&self) -> bool {
        self.entry_hash == self.compute_hash()
    }
}

/// Audit logger with hash chain integrity.
pub struct AuditLogger {
    log_path: PathBuf,
    sequence: Mutex<u64>,
    prev_hash: Mutex<[u8; 32]>,
}

impl AuditLogger {
    /// Create a new audit logger.
    pub fn new(log_dir: impl AsRef<Path>) -> std::io::Result<Self> {
        let log_dir = log_dir.as_ref();
        std::fs::create_dir_all(log_dir)?;

        let log_path = log_dir.join("audit.log");

        // Load state from existing log
        let (sequence, prev_hash) = if log_path.exists() {
            Self::load_last_state(&log_path)?
        } else {
            (0, [0u8; 32])
        };

        Ok(Self {
            log_path,
            sequence: Mutex::new(sequence),
            prev_hash: Mutex::new(prev_hash),
        })
    }

    /// Load the last sequence and hash from existing log.
    fn load_last_state(path: &Path) -> std::io::Result<(u64, [u8; 32])> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);

        let mut last_entry: Option<AuditEntry> = None;
        for line in reader.lines().map_while(Result::ok) {
            if let Some(entry) = AuditEntry::from_log_line(&line) {
                last_entry = Some(entry);
            }
        }

        match last_entry {
            Some(entry) => Ok((entry.sequence + 1, entry.entry_hash)),
            None => Ok((0, [0u8; 32])),
        }
    }

    /// Get current timestamp in milliseconds.
    fn now_millis() -> i64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as i64)
            .unwrap_or(0)
    }

    /// Log an audit event.
    pub fn log(
        &self,
        severity: Severity,
        category: EventCategory,
        message: impl Into<String>,
        context: Option<String>,
    ) -> std::io::Result<()> {
        let message = message.into();

        // Rotate if needed
        self.rotate_if_needed()?;

        // Get exclusive access to state
        let mut seq_guard = self.sequence.lock().unwrap();
        let mut hash_guard = self.prev_hash.lock().unwrap();

        let mut entry = AuditEntry {
            timestamp: Self::now_millis(),
            sequence: *seq_guard,
            severity,
            category,
            message,
            context,
            prev_hash: *hash_guard,
            entry_hash: [0u8; 32],
        };

        // Compute entry hash
        entry.entry_hash = entry.compute_hash();

        // Write to log
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.log_path)?;

        file.write_all(entry.to_log_line().as_bytes())?;
        file.sync_all()?;

        // Update state
        *seq_guard += 1;
        *hash_guard = entry.entry_hash;

        Ok(())
    }

    /// Rotate log if it exceeds maximum size.
    fn rotate_if_needed(&self) -> std::io::Result<()> {
        if !self.log_path.exists() {
            return Ok(());
        }

        let metadata = std::fs::metadata(&self.log_path)?;
        if metadata.len() < MAX_LOG_SIZE {
            return Ok(());
        }

        // Rotate existing logs
        for i in (1..MAX_ROTATED_LOGS).rev() {
            let old_path = self.log_path.with_extension(format!("log.{}", i));
            let new_path = self.log_path.with_extension(format!("log.{}", i + 1));
            if old_path.exists() {
                std::fs::rename(&old_path, &new_path)?;
            }
        }

        // Rotate current log
        let rotated = self.log_path.with_extension("log.1");
        std::fs::rename(&self.log_path, &rotated)?;

        Ok(())
    }

    /// Verify the integrity of the entire audit log chain.
    ///
    /// This verifies ALL log files (including rotated ones) in chronological order,
    /// ensuring the hash chain is unbroken across file boundaries.
    pub fn verify_integrity(&self) -> std::io::Result<VerifyResult> {
        // Collect all log files in order (oldest first)
        let mut log_files = Vec::new();

        // Add rotated logs in reverse order (oldest first: .log.5, .log.4, ..., .log.1)
        for i in (1..=MAX_ROTATED_LOGS).rev() {
            let rotated_path = self.log_path.with_extension(format!("log.{}", i));
            if rotated_path.exists() {
                log_files.push(rotated_path);
            }
        }

        // Add current log file last (newest)
        if self.log_path.exists() {
            log_files.push(self.log_path.clone());
        }

        if log_files.is_empty() {
            return Ok(VerifyResult {
                valid: true,
                entries_checked: 0,
                first_invalid: None,
            });
        }

        // Verify all files in sequence, maintaining hash chain across files
        let mut prev_hash = [0u8; 32];
        let mut entries_checked = 0u64;
        let mut expected_seq = 0u64;

        for log_file in log_files {
            let file = File::open(&log_file)?;
            let reader = BufReader::new(file);

            for line in reader.lines() {
                let line = line?;
                if line.trim().is_empty() {
                    continue;
                }

                let entry = match AuditEntry::from_log_line(&line) {
                    Some(e) => e,
                    None => {
                        return Ok(VerifyResult {
                            valid: false,
                            entries_checked,
                            first_invalid: Some(entries_checked),
                        });
                    }
                };

                // Verify hash chain (continues across file boundaries)
                if entry.prev_hash != prev_hash {
                    return Ok(VerifyResult {
                        valid: false,
                        entries_checked,
                        first_invalid: Some(entries_checked),
                    });
                }

                // Verify entry hash
                if !entry.verify() {
                    return Ok(VerifyResult {
                        valid: false,
                        entries_checked,
                        first_invalid: Some(entries_checked),
                    });
                }

                // Verify sequence (continues across file boundaries)
                if entry.sequence != expected_seq {
                    return Ok(VerifyResult {
                        valid: false,
                        entries_checked,
                        first_invalid: Some(entries_checked),
                    });
                }

                prev_hash = entry.entry_hash;
                expected_seq += 1;
                entries_checked += 1;
            }
        }

        Ok(VerifyResult {
            valid: true,
            entries_checked,
            first_invalid: None,
        })
    }

    /// Verify integrity of just the current log file.
    ///
    /// This is a faster check that only verifies the current log file.
    /// Use `verify_integrity()` for full chain verification across all files.
    ///
    /// # Arguments
    /// * `expected_start_hash` - The expected prev_hash of the first entry.
    ///   Use `[0u8; 32]` for a fresh log, or the last hash from the previous
    ///   rotated file for continuity checking.
    pub fn verify_current_file(
        &self,
        expected_start_hash: [u8; 32],
    ) -> std::io::Result<VerifyResult> {
        if !self.log_path.exists() {
            return Ok(VerifyResult {
                valid: true,
                entries_checked: 0,
                first_invalid: None,
            });
        }

        let file = File::open(&self.log_path)?;
        let reader = BufReader::new(file);

        let mut prev_hash = expected_start_hash;
        let mut entries_checked = 0u64;
        let mut first_entry = true;

        for line in reader.lines() {
            let line = line?;
            if line.trim().is_empty() {
                continue;
            }

            let entry = match AuditEntry::from_log_line(&line) {
                Some(e) => e,
                None => {
                    return Ok(VerifyResult {
                        valid: false,
                        entries_checked,
                        first_invalid: Some(entries_checked),
                    });
                }
            };

            // Verify hash chain
            if entry.prev_hash != prev_hash {
                return Ok(VerifyResult {
                    valid: false,
                    entries_checked,
                    first_invalid: Some(entries_checked),
                });
            }

            // Verify entry hash
            if !entry.verify() {
                return Ok(VerifyResult {
                    valid: false,
                    entries_checked,
                    first_invalid: Some(entries_checked),
                });
            }

            // Note: sequence verification is skipped here since we don't know
            // the starting sequence for a single-file check

            prev_hash = entry.entry_hash;
            entries_checked += 1;
            first_entry = false;
        }

        let _ = first_entry; // Silence unused warning

        Ok(VerifyResult {
            valid: true,
            entries_checked,
            first_invalid: None,
        })
    }

    // Convenience methods for common operations

    /// Log key generation.
    pub fn log_key_generation(&self, key_id: &str) -> std::io::Result<()> {
        self.log(
            Severity::Info,
            EventCategory::KeyManagement,
            "Key pair generated",
            Some(format!("key_id={}", key_id)),
        )
    }

    /// Log signing operation.
    pub fn log_sign(&self, file_hash: &str) -> std::io::Result<()> {
        self.log(
            Severity::Info,
            EventCategory::Signing,
            "File signed",
            Some(format!("file_hash={}", file_hash)),
        )
    }

    /// Log verification success.
    pub fn log_verify_success(&self, file_hash: &str) -> std::io::Result<()> {
        self.log(
            Severity::Info,
            EventCategory::Verification,
            "Signature verified successfully",
            Some(format!("file_hash={}", file_hash)),
        )
    }

    /// Log verification failure.
    pub fn log_verify_failure(&self, file_hash: &str, reason: &str) -> std::io::Result<()> {
        self.log(
            Severity::Error,
            EventCategory::Verification,
            format!("Signature verification failed: {}", reason),
            Some(format!("file_hash={}", file_hash)),
        )
    }

    /// Log authentication success.
    pub fn log_auth_success(&self) -> std::io::Result<()> {
        self.log(
            Severity::Info,
            EventCategory::Authentication,
            "Authentication successful",
            None,
        )
    }

    /// Log authentication failure.
    pub fn log_auth_failure(&self, attempts: u32) -> std::io::Result<()> {
        let severity = if attempts >= 10 {
            Severity::Critical
        } else if attempts >= 5 {
            Severity::Warning
        } else {
            Severity::Error
        };

        self.log(
            severity,
            EventCategory::Authentication,
            format!("Authentication failed (attempt {})", attempts),
            None,
        )
    }

    /// Log license issuance.
    pub fn log_license_issued(&self, license_id: &str, licensee: &str) -> std::io::Result<()> {
        self.log(
            Severity::Info,
            EventCategory::License,
            "License issued",
            Some(format!("license_id={}, licensee={}", license_id, licensee)),
        )
    }

    /// Log license verification.
    pub fn log_license_verified(&self, license_id: &str, valid: bool) -> std::io::Result<()> {
        let severity = if valid {
            Severity::Info
        } else {
            Severity::Warning
        };
        let msg = if valid {
            "License verified"
        } else {
            "License verification failed"
        };
        self.log(
            severity,
            EventCategory::License,
            msg,
            Some(format!("license_id={}", license_id)),
        )
    }

    /// Log key recovery initiation.
    pub fn log_recovery_initiated(&self, threshold: u8, total: u8) -> std::io::Result<()> {
        self.log(
            Severity::Warning,
            EventCategory::Recovery,
            format!(
                "Key recovery initiated ({}/{} shares required)",
                threshold, total
            ),
            None,
        )
    }

    /// Log key recovery completion.
    pub fn log_recovery_completed(&self, success: bool) -> std::io::Result<()> {
        let (severity, msg) = if success {
            (Severity::Warning, "Key recovery completed successfully")
        } else {
            (Severity::Error, "Key recovery failed")
        };
        self.log(severity, EventCategory::Recovery, msg, None)
    }

    /// Log HSM operation.
    pub fn log_hsm_operation(&self, operation: &str, success: bool) -> std::io::Result<()> {
        let severity = if success {
            Severity::Info
        } else {
            Severity::Error
        };
        self.log(
            severity,
            EventCategory::Hsm,
            format!(
                "HSM {}: {}",
                operation,
                if success { "success" } else { "failed" }
            ),
            None,
        )
    }
}

/// Result of log integrity verification.
#[derive(Debug)]
pub struct VerifyResult {
    /// Whether the log is valid.
    pub valid: bool,
    /// Number of entries verified.
    pub entries_checked: u64,
    /// Index of first invalid entry (if any).
    pub first_invalid: Option<u64>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_audit_logging() {
        let temp_dir = TempDir::new().unwrap();
        let logger = AuditLogger::new(temp_dir.path()).unwrap();

        logger.log_key_generation("test-key-123").unwrap();
        logger.log_sign("abc123").unwrap();
        logger.log_verify_success("abc123").unwrap();
        logger.log_auth_failure(1).unwrap();
        logger.log_auth_success().unwrap();

        let result = logger.verify_integrity().unwrap();
        assert!(result.valid);
        assert_eq!(result.entries_checked, 5);
    }

    #[test]
    fn test_hash_chain_integrity() {
        let temp_dir = TempDir::new().unwrap();
        let logger = AuditLogger::new(temp_dir.path()).unwrap();

        for i in 0..10 {
            logger
                .log(
                    Severity::Info,
                    EventCategory::System,
                    format!("Test event {}", i),
                    None,
                )
                .unwrap();
        }

        let result = logger.verify_integrity().unwrap();
        assert!(result.valid);
        assert_eq!(result.entries_checked, 10);
    }

    #[test]
    fn test_entry_serialization() {
        let entry = AuditEntry {
            timestamp: 1234567890123,
            sequence: 42,
            severity: Severity::Warning,
            category: EventCategory::Authentication,
            message: "Test message with | pipe".to_string(),
            context: Some("ctx=value".to_string()),
            prev_hash: [1u8; 32],
            entry_hash: [2u8; 32],
        };

        let line = entry.to_log_line();
        let parsed = AuditEntry::from_log_line(&line).unwrap();

        assert_eq!(parsed.timestamp, entry.timestamp);
        assert_eq!(parsed.sequence, entry.sequence);
        assert_eq!(parsed.message, entry.message);
        assert_eq!(parsed.prev_hash, entry.prev_hash);
    }

    #[test]
    fn test_persistence() {
        let temp_dir = TempDir::new().unwrap();

        // First session
        {
            let logger = AuditLogger::new(temp_dir.path()).unwrap();
            logger.log_key_generation("key1").unwrap();
            logger.log_key_generation("key2").unwrap();
        }

        // Second session - should continue chain
        {
            let logger = AuditLogger::new(temp_dir.path()).unwrap();
            logger.log_key_generation("key3").unwrap();

            let result = logger.verify_integrity().unwrap();
            assert!(result.valid);
            assert_eq!(result.entries_checked, 3);
        }
    }
}
