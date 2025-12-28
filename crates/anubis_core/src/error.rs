//! Unified error types for anubis_core.
//!
//! This module provides a unified `CryptoError` type that wraps all specific
//! error types from submodules, preserving error context and enabling consistent
//! error handling across the library.

use core::fmt;

/// Unified cryptographic error type.
///
/// This enum wraps all specific error types from the library, providing:
/// - Consistent error handling interface
/// - Error context preservation
/// - Conversion from specific error types via `From` implementations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CryptoError {
    /// AEAD encryption/decryption error (ChaCha20Poly1305 via libcrux)
    Aead(crate::aead::AeadError),
    /// CBOR encoding/decoding error (custom encoder)
    Cbor(crate::cbor::CborError),
    /// CBOR encoding/decoding error (ciborium)
    Ciborium(CiboriumErrorKind),
    /// Byte manipulation error
    Bytes(crate::bytes::BytesError),
    /// Key derivation error
    Kdf(crate::kdf::KdfError),
    /// ML-DSA signature error
    MlDsa(crate::mldsa::MlDsaError),
    /// ML-KEM key encapsulation error
    MlKem(crate::mlkem::MlKemError),
    /// Merkle tree error
    Merkle(crate::merkle::MerkleError),
    /// Nonce derivation error
    Nonce(crate::nonce::NonceError),
    /// Receipt error
    Receipt(crate::receipt::ReceiptError),
    /// License error
    License(crate::license::LicenseError),
    /// Generic error with message
    Other(String),
}

/// Simplified ciborium error kind (since ciborium::de::Error doesn't implement Clone/Eq)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CiboriumErrorKind {
    /// Serialization failed
    Serialization(String),
    /// Deserialization failed
    Deserialization(String),
}

impl fmt::Display for CryptoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CryptoError::Aead(e) => write!(f, "AEAD error: {:?}", e),
            CryptoError::Cbor(e) => write!(f, "CBOR error: {:?}", e),
            CryptoError::Ciborium(e) => write!(f, "Ciborium error: {:?}", e),
            CryptoError::Bytes(e) => write!(f, "Bytes error: {:?}", e),
            CryptoError::Kdf(e) => write!(f, "KDF error: {:?}", e),
            CryptoError::MlDsa(e) => write!(f, "ML-DSA error: {:?}", e),
            CryptoError::MlKem(e) => write!(f, "ML-KEM error: {:?}", e),
            CryptoError::Merkle(e) => write!(f, "Merkle error: {:?}", e),
            CryptoError::Nonce(e) => write!(f, "Nonce error: {:?}", e),
            CryptoError::Receipt(e) => write!(f, "Receipt error: {:?}", e),
            CryptoError::License(e) => write!(f, "License error: {:?}", e),
            CryptoError::Other(msg) => write!(f, "{}", msg),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for CryptoError {}

// From implementations for automatic conversion

impl From<crate::aead::AeadError> for CryptoError {
    fn from(e: crate::aead::AeadError) -> Self {
        CryptoError::Aead(e)
    }
}

impl From<crate::cbor::CborError> for CryptoError {
    fn from(e: crate::cbor::CborError) -> Self {
        CryptoError::Cbor(e)
    }
}

impl From<crate::bytes::BytesError> for CryptoError {
    fn from(e: crate::bytes::BytesError) -> Self {
        CryptoError::Bytes(e)
    }
}

impl From<crate::kdf::KdfError> for CryptoError {
    fn from(e: crate::kdf::KdfError) -> Self {
        CryptoError::Kdf(e)
    }
}

impl From<crate::mldsa::MlDsaError> for CryptoError {
    fn from(e: crate::mldsa::MlDsaError) -> Self {
        CryptoError::MlDsa(e)
    }
}

impl From<crate::mlkem::MlKemError> for CryptoError {
    fn from(e: crate::mlkem::MlKemError) -> Self {
        CryptoError::MlKem(e)
    }
}

impl From<crate::merkle::MerkleError> for CryptoError {
    fn from(e: crate::merkle::MerkleError) -> Self {
        CryptoError::Merkle(e)
    }
}

impl From<crate::nonce::NonceError> for CryptoError {
    fn from(e: crate::nonce::NonceError) -> Self {
        CryptoError::Nonce(e)
    }
}

impl From<crate::receipt::ReceiptError> for CryptoError {
    fn from(e: crate::receipt::ReceiptError) -> Self {
        CryptoError::Receipt(e)
    }
}

impl From<crate::license::LicenseError> for CryptoError {
    fn from(e: crate::license::LicenseError) -> Self {
        CryptoError::License(e)
    }
}

impl From<&str> for CryptoError {
    fn from(s: &str) -> Self {
        CryptoError::Other(s.to_string())
    }
}

impl From<String> for CryptoError {
    fn from(s: String) -> Self {
        CryptoError::Other(s)
    }
}

/// Result type using the unified CryptoError
pub type CryptoResult<T> = Result<T, CryptoError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_conversion() {
        let aead_err = crate::aead::AeadError::InvalidKeySize;
        let crypto_err: CryptoError = aead_err.into();
        assert!(matches!(crypto_err, CryptoError::Aead(_)));
    }

    #[test]
    fn test_error_display() {
        let err = CryptoError::Other("test error".to_string());
        assert_eq!(format!("{}", err), "test error");
    }
}
