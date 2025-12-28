//! Production CBOR using ciborium.
//!
//! This module wraps the `ciborium` crate for CBOR serialization/deserialization.
//!
//! ## Production Usage
//!
//! `ciborium` is used in production by:
//! - **Google** (coset crate for COSE)
//! - **AWS** (aws-smithy-types)
//! - **Android** (platform libraries)
//! - **Criterion** (132M+ downloads)
//!
//! ## RFC 8949 Compliance
//!
//! While ciborium follows the "robustness principle" (liberal in what it accepts),
//! encoding is deterministic. For canonical CBOR requirements, use the custom
//! encoder in the parent module which enforces strict RFC 8949 Section 4.2 rules.
//!
//! ## When to Use
//!
//! - **This module**: General CBOR serialization/deserialization with serde
//! - **Custom encoder/decoder**: When you need strict canonical CBOR (e.g., signing)

use ciborium::Value;
use core::fmt;

/// Error type for ciborium operations.
#[derive(Debug)]
pub enum CiboriumError {
    /// Serialization error.
    Serialize(String),
    /// Deserialization error.
    Deserialize(String),
    /// I/O error.
    Io(String),
}

impl fmt::Display for CiboriumError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Serialize(msg) => write!(f, "CBOR serialize error: {}", msg),
            Self::Deserialize(msg) => write!(f, "CBOR deserialize error: {}", msg),
            Self::Io(msg) => write!(f, "CBOR I/O error: {}", msg),
        }
    }
}

/// Serialize a value to CBOR bytes.
///
/// Uses the production-proven `ciborium` crate.
///
/// # Example
///
/// ```rust,ignore
/// use anubis_core::cbor::ciborium_wrapper::to_vec;
/// use serde::Serialize;
///
/// #[derive(Serialize)]
/// struct Receipt {
///     timestamp: u64,
///     hash: Vec<u8>,
/// }
///
/// let receipt = Receipt { timestamp: 12345, hash: vec![1, 2, 3] };
/// let cbor = to_vec(&receipt)?;
/// ```
pub fn to_vec<T: serde::Serialize>(value: &T) -> Result<Vec<u8>, CiboriumError> {
    let mut buffer = Vec::new();
    ciborium::into_writer(value, &mut buffer)
        .map_err(|e| CiboriumError::Serialize(e.to_string()))?;
    Ok(buffer)
}

/// Deserialize CBOR bytes to a value.
///
/// # Example
///
/// ```rust,ignore
/// use anubis_core::cbor::ciborium_wrapper::from_slice;
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct Receipt {
///     timestamp: u64,
///     hash: Vec<u8>,
/// }
///
/// let cbor = &[...];
/// let receipt: Receipt = from_slice(cbor)?;
/// ```
pub fn from_slice<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T, CiboriumError> {
    ciborium::from_reader(bytes)
        .map_err(|e| CiboriumError::Deserialize(e.to_string()))
}

/// Parse CBOR into a generic Value.
///
/// Useful for inspecting CBOR structure without a specific type.
pub fn parse_value(bytes: &[u8]) -> Result<Value, CiboriumError> {
    ciborium::from_reader(bytes)
        .map_err(|e| CiboriumError::Deserialize(e.to_string()))
}

/// Encode a generic Value to CBOR.
pub fn encode_value(value: &Value) -> Result<Vec<u8>, CiboriumError> {
    let mut buffer = Vec::new();
    ciborium::into_writer(value, &mut buffer)
        .map_err(|e| CiboriumError::Serialize(e.to_string()))?;
    Ok(buffer)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Serialize, Deserialize, PartialEq)]
    struct TestStruct {
        name: String,
        value: u64,
        data: Vec<u8>,
    }

    #[test]
    fn test_roundtrip() {
        let original = TestStruct {
            name: "test".to_string(),
            value: 42,
            data: vec![1, 2, 3, 4],
        };

        let cbor = to_vec(&original).unwrap();
        let decoded: TestStruct = from_slice(&cbor).unwrap();

        assert_eq!(original, decoded);
    }

    #[test]
    fn test_integers() {
        // Small positive integer
        let cbor = to_vec(&23u64).unwrap();
        assert_eq!(cbor, vec![23]); // Encoded in 1 byte

        // Larger integer
        let cbor = to_vec(&1000u64).unwrap();
        let decoded: u64 = from_slice(&cbor).unwrap();
        assert_eq!(decoded, 1000);
    }

    #[test]
    fn test_bytes() {
        let data: Vec<u8> = vec![0xDE, 0xAD, 0xBE, 0xEF];
        let cbor = to_vec(&data).unwrap();
        let decoded: Vec<u8> = from_slice(&cbor).unwrap();
        assert_eq!(data, decoded);
    }

    #[test]
    fn test_nested_structure() {
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct Inner {
            id: u32,
        }

        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct Outer {
            inner: Inner,
            list: Vec<Inner>,
        }

        let original = Outer {
            inner: Inner { id: 1 },
            list: vec![Inner { id: 2 }, Inner { id: 3 }],
        };

        let cbor = to_vec(&original).unwrap();
        let decoded: Outer = from_slice(&cbor).unwrap();

        assert_eq!(original, decoded);
    }
}
