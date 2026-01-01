//! Error types for private batch operations.

use crate::aead::AeadError;
use crate::merkle::MerkleError;
use crate::mlkem::MlKemError;
use crate::recovery::ShamirError;
use core::fmt;

/// Errors from private batch operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrivateBatchError {
    /// Invalid number of recipients (must be 1-16).
    InvalidRecipientCount,
    /// Invalid threshold (must be 2 <= t <= n).
    InvalidThreshold,
    /// Invalid recipient index.
    InvalidRecipientIndex,
    /// Invalid number of leaves (must be 1-1024).
    InvalidLeafCount,
    /// Decryption failed (AEAD authentication failure).
    DecryptionFailed,
    /// Commitment verification failed after decryption.
    CommitmentMismatch,
    /// Not enough shares for threshold recovery.
    InsufficientShares,
    /// Session key has wrong length (must be 32 bytes).
    InvalidSessionKey,
    /// Batch ID mismatch between components.
    BatchIdMismatch,
    /// Recipient not found in envelope.
    RecipientNotFound,
    /// ML-KEM operation failed.
    MlKem(MlKemError),
    /// Shamir secret sharing error.
    Shamir(ShamirError),
    /// Merkle tree error.
    Merkle(MerkleError),
    /// AEAD error.
    Aead(AeadError),
    /// Random number generation failed.
    RngFailed,
    /// CBOR encoding/decoding error.
    CborError(String),
    /// I/O error.
    IoError(String),
}

impl fmt::Display for PrivateBatchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRecipientCount => write!(f, "invalid recipient count (must be 1-16)"),
            Self::InvalidThreshold => write!(f, "invalid threshold (must be 2 <= t <= n)"),
            Self::InvalidRecipientIndex => write!(f, "invalid recipient index"),
            Self::InvalidLeafCount => write!(f, "invalid leaf count (must be 1-1024)"),
            Self::DecryptionFailed => write!(f, "decryption failed"),
            Self::CommitmentMismatch => write!(f, "commitment verification failed"),
            Self::InsufficientShares => write!(f, "insufficient shares for recovery"),
            Self::InvalidSessionKey => write!(f, "invalid session key length"),
            Self::BatchIdMismatch => write!(f, "batch ID mismatch"),
            Self::RecipientNotFound => write!(f, "recipient not found in envelope"),
            Self::MlKem(e) => write!(f, "ML-KEM error: {}", e),
            Self::Shamir(e) => write!(f, "Shamir error: {:?}", e),
            Self::Merkle(e) => write!(f, "Merkle error: {:?}", e),
            Self::Aead(e) => write!(f, "AEAD error: {}", e),
            Self::RngFailed => write!(f, "random number generation failed"),
            Self::CborError(msg) => write!(f, "CBOR error: {}", msg),
            Self::IoError(msg) => write!(f, "I/O error: {}", msg),
        }
    }
}

impl std::error::Error for PrivateBatchError {}

impl From<MlKemError> for PrivateBatchError {
    fn from(e: MlKemError) -> Self {
        Self::MlKem(e)
    }
}

impl From<ShamirError> for PrivateBatchError {
    fn from(e: ShamirError) -> Self {
        Self::Shamir(e)
    }
}

impl From<MerkleError> for PrivateBatchError {
    fn from(e: MerkleError) -> Self {
        Self::Merkle(e)
    }
}

impl From<AeadError> for PrivateBatchError {
    fn from(e: AeadError) -> Self {
        Self::Aead(e)
    }
}

impl From<getrandom::Error> for PrivateBatchError {
    fn from(_: getrandom::Error) -> Self {
        Self::RngFailed
    }
}
