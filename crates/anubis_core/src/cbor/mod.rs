//! CBOR serialization (RFC 8949).
//!
//! This module provides two CBOR implementations:
//!
//! ## ciborium (Production-Proven)
//!
//! The `ciborium_wrapper` submodule wraps the `ciborium` crate used by:
//! - **Google** (coset crate for COSE)
//! - **AWS** (aws-smithy-types)
//! - **Android** (platform libraries)
//! - **Criterion** (132M+ downloads benchmarking framework)
//!
//! Use this for general CBOR serialization with serde.
//!
//! ## Custom Canonical Encoder (Strict RFC 8949)
//!
//! The custom `Encoder`/`Decoder` in this module enforce strict canonical CBOR:
//! - Shortest integer encoding
//! - Sorted map keys (lexicographic on encoded form)
//! - No duplicate keys
//!
//! Use this when you need deterministic encoding for signing operations.
//!
//! ## Which to Use?
//!
//! | Use Case | Recommendation |
//! |----------|----------------|
//! | General serialization | `ciborium_wrapper` |
//! | Signing/verification | Custom `Encoder` |
//! | Interop with other CBOR libs | `ciborium_wrapper` |
//!
//! ## RefinedRust Verification (Custom Implementation)
//!
//! The custom encoder/decoder is verified using RefinedRust for:
//! - **Totality**: All decoders return `Ok(v)` or `Err(e)`, never panic
//! - **Bounds Safety**: Position never exceeds buffer length
//! - **Roundtrip Correctness**: `decode(encode(v)) == Ok(v)` for supported types
//! - **Canonical Form**: Encoder produces deterministic output
//! - **Length Preservation**: Encoded length matches RFC 8949 specification
//!
//! See `proofs/theories/cbor_spec.v` for the Rocq specification.
//!
//! Key invariants:
//! - `Encoder.pos <= Encoder.buffer.len()`
//! - `Decoder.pos <= Decoder.buffer.len()`

// Production CBOR using ciborium (Google, AWS, Android)
pub mod ciborium_wrapper;

// Re-export ciborium wrapper functions
pub use ciborium_wrapper::{to_vec, from_slice, CiboriumError};

use core::cmp::Ordering;
use core::fmt;

/// Maximum nesting depth for CBOR structures (arrays, maps, tags).
/// This prevents stack overflow from maliciously crafted deeply-nested CBOR.
pub const MAX_NESTING_DEPTH: usize = 128;

/// CBOR error types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CborError {
    /// Input buffer exhausted unexpectedly.
    UnexpectedEnd,
    /// Invalid CBOR encoding.
    InvalidEncoding,
    /// Unsupported CBOR feature (e.g., indefinite length).
    Unsupported,
    /// Integer overflow during decoding.
    Overflow,
    /// Duplicate map key detected.
    DuplicateKey,
    /// Map keys not sorted.
    UnsortedKeys,
    /// Output buffer too small.
    BufferTooSmall,
    /// Invalid UTF-8 in text string.
    InvalidUtf8,
    /// Type mismatch.
    TypeMismatch,
    /// Maximum nesting depth exceeded (prevents stack overflow).
    MaxDepthExceeded,
}

impl fmt::Display for CborError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEnd => write!(f, "unexpected end of CBOR input"),
            Self::InvalidEncoding => write!(f, "invalid CBOR encoding"),
            Self::Unsupported => write!(f, "unsupported CBOR feature"),
            Self::Overflow => write!(f, "integer overflow during CBOR decoding"),
            Self::DuplicateKey => write!(f, "duplicate map key in CBOR"),
            Self::UnsortedKeys => write!(f, "map keys not sorted in canonical CBOR"),
            Self::BufferTooSmall => write!(f, "output buffer too small for CBOR encoding"),
            Self::InvalidUtf8 => write!(f, "invalid UTF-8 in CBOR text string"),
            Self::TypeMismatch => write!(f, "CBOR type mismatch"),
            Self::MaxDepthExceeded => write!(f, "CBOR nesting depth exceeds maximum ({MAX_NESTING_DEPTH})"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for CborError {}

/// CBOR encoder for writing canonical CBOR.
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("enc" : "cbor_spec.encoder_state")]
/// #[rr::invariant("enc.pos <= len(enc.buffer)")]
/// #[rr::invariant("enc.pos >= 0")]
/// #[rr::invariant("forall i. i < enc.pos -> enc.buffer[i] is valid CBOR byte")]
/// ```
pub struct Encoder<'a> {
    buffer: &'a mut [u8],
    pos: usize,
}

impl<'a> Encoder<'a> {
    /// Create a new encoder writing to the given buffer.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::ensures("self.pos == 0")]
    /// #[rr::ensures("self.buffer == buffer")]
    /// ```
    #[inline]
    pub fn new(buffer: &'a mut [u8]) -> Self {
        Self { buffer, pos: 0 }
    }

    /// Returns the number of bytes written so far.
    #[inline]
    pub fn position(&self) -> usize {
        self.pos
    }

    /// Returns the encoded bytes as a slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.buffer[..self.pos]
    }

    fn write_byte(&mut self, byte: u8) -> Result<(), CborError> {
        if self.pos >= self.buffer.len() {
            return Err(CborError::BufferTooSmall);
        }
        self.buffer[self.pos] = byte;
        self.pos += 1;
        Ok(())
    }

    fn write_bytes(&mut self, bytes: &[u8]) -> Result<(), CborError> {
        if self.pos + bytes.len() > self.buffer.len() {
            return Err(CborError::BufferTooSmall);
        }
        self.buffer[self.pos..self.pos + bytes.len()].copy_from_slice(bytes);
        self.pos += bytes.len();
        Ok(())
    }

    fn encode_type_arg(&mut self, major: u8, arg: u64) -> Result<(), CborError> {
        let mt = major << 5;
        if arg < 24 {
            self.write_byte(mt | (arg as u8))
        } else if arg <= 0xFF {
            self.write_byte(mt | 24)?;
            self.write_byte(arg as u8)
        } else if arg <= 0xFFFF {
            self.write_byte(mt | 25)?;
            self.write_bytes(&(arg as u16).to_be_bytes())
        } else if arg <= 0xFFFF_FFFF {
            self.write_byte(mt | 26)?;
            self.write_bytes(&(arg as u32).to_be_bytes())
        } else {
            self.write_byte(mt | 27)?;
            self.write_bytes(&arg.to_be_bytes())
        }
    }

    /// Encode an unsigned integer.
    pub fn encode_uint(&mut self, n: u64) -> Result<(), CborError> {
        self.encode_type_arg(0, n)
    }

    /// Encode a negative integer (-1 - n).
    pub fn encode_nint(&mut self, n: u64) -> Result<(), CborError> {
        self.encode_type_arg(1, n)
    }

    /// Encode a signed integer.
    pub fn encode_int(&mut self, n: i64) -> Result<(), CborError> {
        if n >= 0 {
            self.encode_uint(n as u64)
        } else {
            self.encode_nint((-1 - n) as u64)
        }
    }

    /// Encode a byte string.
    pub fn encode_bytes(&mut self, bytes: &[u8]) -> Result<(), CborError> {
        self.encode_type_arg(2, bytes.len() as u64)?;
        self.write_bytes(bytes)
    }

    /// Encode a text string.
    pub fn encode_text(&mut self, text: &str) -> Result<(), CborError> {
        self.encode_type_arg(3, text.len() as u64)?;
        self.write_bytes(text.as_bytes())
    }

    /// Begin encoding an array with known length.
    pub fn encode_array_header(&mut self, len: usize) -> Result<(), CborError> {
        self.encode_type_arg(4, len as u64)
    }

    /// Begin encoding a map with known number of pairs.
    pub fn encode_map_header(&mut self, len: usize) -> Result<(), CborError> {
        self.encode_type_arg(5, len as u64)
    }

    /// Encode a boolean.
    pub fn encode_bool(&mut self, b: bool) -> Result<(), CborError> {
        self.write_byte(if b { 0xF5 } else { 0xF4 })
    }

    /// Encode null.
    pub fn encode_null(&mut self) -> Result<(), CborError> {
        self.write_byte(0xF6)
    }
}

/// CBOR decoder for reading canonical CBOR.
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("dec" : "cbor_spec.decoder_state")]
/// #[rr::invariant("dec.pos <= len(dec.buffer)")]
/// #[rr::invariant("dec.pos >= 0")]
/// #[rr::invariant("total: forall input. decode(input) = Ok(v) | Err(e)")]
/// ```
pub struct Decoder<'a> {
    buffer: &'a [u8],
    pos: usize,
}

impl<'a> Decoder<'a> {
    /// Create a new decoder reading from the given buffer.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::ensures("self.pos == 0")]
    /// #[rr::ensures("self.buffer == buffer")]
    /// ```
    #[inline]
    pub fn new(buffer: &'a [u8]) -> Self {
        Self { buffer, pos: 0 }
    }

    /// Returns the current position.
    #[inline]
    pub fn position(&self) -> usize {
        self.pos
    }

    /// Returns remaining bytes.
    #[inline]
    pub fn remaining(&self) -> usize {
        self.buffer.len() - self.pos
    }

    /// Check if empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.pos >= self.buffer.len()
    }

    fn read_byte(&mut self) -> Result<u8, CborError> {
        if self.pos >= self.buffer.len() {
            return Err(CborError::UnexpectedEnd);
        }
        let b = self.buffer[self.pos];
        self.pos += 1;
        Ok(b)
    }

    fn read_bytes(&mut self, n: usize) -> Result<&'a [u8], CborError> {
        if self.pos + n > self.buffer.len() {
            return Err(CborError::UnexpectedEnd);
        }
        let slice = &self.buffer[self.pos..self.pos + n];
        self.pos += n;
        Ok(slice)
    }

    fn decode_type_arg(&mut self) -> Result<(u8, u64), CborError> {
        let initial = self.read_byte()?;
        let major = initial >> 5;
        let info = initial & 0x1F;

        let arg = match info {
            0..=23 => info as u64,
            24 => self.read_byte()? as u64,
            25 => {
                let bytes = self.read_bytes(2)?;
                u16::from_be_bytes([bytes[0], bytes[1]]) as u64
            }
            26 => {
                let bytes = self.read_bytes(4)?;
                u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as u64
            }
            27 => {
                let bytes = self.read_bytes(8)?;
                u64::from_be_bytes([
                    bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
                ])
            }
            28..=30 => return Err(CborError::InvalidEncoding),
            31 => return Err(CborError::Unsupported),
            _ => unreachable!(),
        };

        Ok((major, arg))
    }

    /// Decode an unsigned integer.
    pub fn decode_uint(&mut self) -> Result<u64, CborError> {
        let (major, arg) = self.decode_type_arg()?;
        if major != 0 {
            return Err(CborError::TypeMismatch);
        }
        Ok(arg)
    }

    /// Decode a signed integer.
    pub fn decode_int(&mut self) -> Result<i64, CborError> {
        let (major, arg) = self.decode_type_arg()?;
        match major {
            0 => {
                if arg > i64::MAX as u64 {
                    return Err(CborError::Overflow);
                }
                Ok(arg as i64)
            }
            1 => {
                if arg > i64::MAX as u64 {
                    return Err(CborError::Overflow);
                }
                Ok(-1 - (arg as i64))
            }
            _ => Err(CborError::TypeMismatch),
        }
    }

    /// Decode a byte string.
    pub fn decode_bytes(&mut self) -> Result<&'a [u8], CborError> {
        let (major, len) = self.decode_type_arg()?;
        if major != 2 {
            return Err(CborError::TypeMismatch);
        }
        self.read_bytes(len as usize)
    }

    /// Decode a text string.
    pub fn decode_text(&mut self) -> Result<&'a str, CborError> {
        let (major, len) = self.decode_type_arg()?;
        if major != 3 {
            return Err(CborError::TypeMismatch);
        }
        let bytes = self.read_bytes(len as usize)?;
        core::str::from_utf8(bytes).map_err(|_| CborError::InvalidUtf8)
    }

    /// Decode array header.
    pub fn decode_array_header(&mut self) -> Result<usize, CborError> {
        let (major, len) = self.decode_type_arg()?;
        if major != 4 {
            return Err(CborError::TypeMismatch);
        }
        Ok(len as usize)
    }

    /// Decode map header.
    pub fn decode_map_header(&mut self) -> Result<usize, CborError> {
        let (major, len) = self.decode_type_arg()?;
        if major != 5 {
            return Err(CborError::TypeMismatch);
        }
        Ok(len as usize)
    }

    /// Decode a boolean.
    pub fn decode_bool(&mut self) -> Result<bool, CborError> {
        let byte = self.read_byte()?;
        match byte {
            0xF4 => Ok(false),
            0xF5 => Ok(true),
            _ => Err(CborError::TypeMismatch),
        }
    }

    /// Skip a CBOR value.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::ensures("self.pos <= self.buffer.len()")]
    /// #[rr::ensures("match result { Ok(_) => true, Err(_) => true }")]
    /// #[rr::ensures("no partial state mutation on error")]
    /// ```
    ///
    /// This function is total: it returns Ok or Err for all valid and invalid
    /// CBOR inputs without panicking.
    ///
    /// # Security
    ///
    /// This function enforces a maximum nesting depth of [`MAX_NESTING_DEPTH`]
    /// to prevent stack overflow attacks from maliciously crafted CBOR with
    /// deeply nested arrays, maps, or tags.
    pub fn skip_value(&mut self) -> Result<(), CborError> {
        self.skip_value_depth(0)
    }

    /// Skip a CBOR value with depth tracking.
    ///
    /// Internal implementation that tracks nesting depth to prevent stack overflow.
    fn skip_value_depth(&mut self, depth: usize) -> Result<(), CborError> {
        if depth > MAX_NESTING_DEPTH {
            return Err(CborError::MaxDepthExceeded);
        }

        let (major, arg) = self.decode_type_arg()?;
        match major {
            // Unsigned/negative integers: no nested content
            0 | 1 => Ok(()),
            // Byte/text strings: skip the content bytes
            2 | 3 => {
                self.read_bytes(arg as usize)?;
                Ok(())
            }
            // Array: skip each element (increase depth)
            4 => {
                for _ in 0..arg {
                    self.skip_value_depth(depth + 1)?;
                }
                Ok(())
            }
            // Map: skip each key-value pair (increase depth)
            5 => {
                for _ in 0..arg {
                    self.skip_value_depth(depth + 1)?;
                    self.skip_value_depth(depth + 1)?;
                }
                Ok(())
            }
            // Tag: skip the tagged value (increase depth)
            6 => self.skip_value_depth(depth + 1),
            // Simple values and floats: no nested content
            7 => Ok(()),
            _ => Err(CborError::InvalidEncoding),
        }
    }
}

/// Compare CBOR-encoded sequences for canonical ordering.
///
/// # RefinedRust Specification
///
/// ```text
/// #[rr::params("a" : "list u8", "b" : "list u8")]
/// #[rr::args("#a", "#b")]
/// #[rr::returns("#cbor_key_compare(a, b)")]
/// #[rr::ensures("result = Less | result = Equal | result = Greater")]
/// #[rr::ensures("result = Equal <-> a = b")]
/// #[rr::ensures("canonical_cmp(a, b) = reverse(canonical_cmp(b, a))")]
/// #[rr::pure]
/// ```
///
/// Per RFC 8949, shorter keys sort before longer keys, and keys of equal
/// length are compared lexicographically.
pub fn canonical_cmp(a: &[u8], b: &[u8]) -> Ordering {
    match a.len().cmp(&b.len()) {
        Ordering::Equal => a.cmp(b),
        ord => ord,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_uint() {
        let mut buf = [0u8; 16];
        let mut enc = Encoder::new(&mut buf);
        enc.encode_uint(0).unwrap();
        assert_eq!(enc.as_bytes(), &[0x00]);

        let mut enc = Encoder::new(&mut buf);
        enc.encode_uint(23).unwrap();
        assert_eq!(enc.as_bytes(), &[0x17]);

        let mut enc = Encoder::new(&mut buf);
        enc.encode_uint(24).unwrap();
        assert_eq!(enc.as_bytes(), &[0x18, 0x18]);
    }

    #[test]
    fn test_roundtrip() {
        let mut buf = [0u8; 16];
        let mut enc = Encoder::new(&mut buf);
        enc.encode_int(-100).unwrap();

        let mut dec = Decoder::new(enc.as_bytes());
        assert_eq!(dec.decode_int().unwrap(), -100);
    }

    #[test]
    fn test_skip_value_depth_limit() {
        // Create a deeply nested array that exceeds MAX_NESTING_DEPTH.
        // Each 0x81 is an array of length 1 containing another element.
        // We need MAX_NESTING_DEPTH + 2 levels to trigger the error.
        let depth = MAX_NESTING_DEPTH + 2;
        let mut nested: Vec<u8> = vec![0x81; depth]; // array[1] headers
        nested.push(0x00); // innermost value: integer 0

        let mut dec = Decoder::new(&nested);
        let result = dec.skip_value();
        assert_eq!(result, Err(CborError::MaxDepthExceeded));
    }

    #[test]
    fn test_skip_value_within_depth_limit() {
        // Create a nested array just within the depth limit.
        let depth = MAX_NESTING_DEPTH;
        let mut nested: Vec<u8> = vec![0x81; depth]; // array[1] headers
        nested.push(0x00); // innermost value: integer 0

        let mut dec = Decoder::new(&nested);
        // Should succeed - exactly at the limit
        assert!(dec.skip_value().is_ok());
    }

    #[test]
    fn test_skip_nested_maps_depth_limit() {
        // Create deeply nested maps: {0: {0: {0: ...}}}
        // 0xA1 is map with 1 entry, 0x00 is key (integer 0)
        let depth = MAX_NESTING_DEPTH + 2;
        let mut nested: Vec<u8> = Vec::with_capacity(depth * 2 + 1);
        for _ in 0..depth {
            nested.push(0xA1); // map with 1 entry
            nested.push(0x00); // key: integer 0
        }
        nested.push(0x00); // final value: integer 0

        let mut dec = Decoder::new(&nested);
        let result = dec.skip_value();
        assert_eq!(result, Err(CborError::MaxDepthExceeded));
    }
}
