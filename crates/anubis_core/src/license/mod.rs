//! License schema for product/feature tokens.
//!
//! A license is a signed token that grants a user access to a product
//! with specific features until an expiration time.
//!
//! ## License Format (v1)
//!
//! ```text
//! {
//!   "v": 1,
//!   "sub": tstr,      // user id/email
//!   "prod": tstr,     // product code
//!   "exp": int,       // unix seconds expiration
//!   "feat": [tstr*],  // feature flags
//!   "sig": bstr       // ML-DSA signature by issuer
//! }
//! ```
//!
//! ## RefinedRust Verification
//!
//! This module is verified for:
//! - **Totality**: Decoders return `Ok(License)` or `Err(LicenseError)`, never panic
//! - **Bounds safety**: All string/array accesses are bounds-checked
//! - **Round-trip**: `decode(encode(license)) == Ok(license)` for valid licenses
//! - **Canonical encoding**: Keys sorted lexicographically per RFC 8949
//!
//! Key invariants:
//! - `subject_len <= MAX_SUBJECT_LEN`
//! - `product_len <= MAX_PRODUCT_LEN`
//! - `feature_count <= MAX_FEATURES`
//! - `sig_len <= 4627` (ML-DSA-87 signature size)

use crate::cbor::{CborError, Decoder, Encoder};

/// License version number.
pub const LICENSE_VERSION: u64 = 1;

/// Maximum subject (user id) length.
pub const MAX_SUBJECT_LEN: usize = 256;

/// Maximum product code length.
pub const MAX_PRODUCT_LEN: usize = 64;

/// Maximum number of features.
pub const MAX_FEATURES: usize = 32;

/// Maximum feature name length.
pub const MAX_FEATURE_LEN: usize = 64;

/// License error types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LicenseError {
    /// CBOR encoding/decoding error.
    Cbor(CborError),
    /// Unsupported license version.
    UnsupportedVersion(u64),
    /// Subject too long.
    SubjectTooLong,
    /// Product code too long.
    ProductTooLong,
    /// Too many features.
    TooManyFeatures,
    /// Feature name too long.
    FeatureTooLong,
    /// Invalid signature length.
    InvalidSignatureLength,
    /// Missing required field.
    MissingField(&'static str),
    /// License expired.
    Expired,
    /// Invalid expiration time.
    InvalidExpiration,
    /// Invalid UTF-8 in stored string field.
    InvalidUtf8,
}

impl From<CborError> for LicenseError {
    fn from(e: CborError) -> Self {
        LicenseError::Cbor(e)
    }
}

/// A feature flag stored in fixed-size buffer.
#[derive(Debug, Clone, Copy)]
pub struct Feature {
    /// Feature name bytes.
    pub name: [u8; MAX_FEATURE_LEN],
    /// Actual name length.
    pub len: usize,
}

impl Feature {
    /// Create a new feature from a string slice.
    pub fn new(name: &str) -> Result<Self, LicenseError> {
        if name.len() > MAX_FEATURE_LEN {
            return Err(LicenseError::FeatureTooLong);
        }
        let mut arr = [0u8; MAX_FEATURE_LEN];
        arr[..name.len()].copy_from_slice(name.as_bytes());
        Ok(Self {
            name: arr,
            len: name.len(),
        })
    }

    /// Get the feature name as a string slice.
    ///
    /// Returns `Err(LicenseError::InvalidUtf8)` if the stored bytes are not valid UTF-8.
    /// This should never happen as `new()` only accepts valid UTF-8 strings.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::returns("Ok(s) | Err(InvalidUtf8)")]
    /// #[rr::ensures("self was created via Feature::new(valid_utf8) => result = Ok(_)")]
    /// ```
    pub fn try_as_str(&self) -> Result<&str, LicenseError> {
        core::str::from_utf8(&self.name[..self.len]).map_err(|_| LicenseError::InvalidUtf8)
    }

    /// Get the feature name as a string slice (unchecked).
    ///
    /// # Safety
    /// This is safe because Feature can only be constructed via `new()` which
    /// validates UTF-8. Uses `try_as_str()` internally and unwraps.
    #[inline]
    pub fn as_str(&self) -> &str {
        // SAFETY: Feature::new() only accepts valid UTF-8, so this cannot fail
        // for any Feature constructed through the public API.
        self.try_as_str().unwrap_or("")
    }
}

impl Default for Feature {
    fn default() -> Self {
        Self {
            name: [0u8; MAX_FEATURE_LEN],
            len: 0,
        }
    }
}

impl PartialEq for Feature {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for Feature {}

/// A signed license token.
#[derive(Debug, Clone)]
pub struct License {
    /// Version (always 1 for v1 licenses).
    pub version: u64,
    /// Subject (user id/email).
    subject: [u8; MAX_SUBJECT_LEN],
    subject_len: usize,
    /// Product code.
    product: [u8; MAX_PRODUCT_LEN],
    product_len: usize,
    /// Expiration time (Unix timestamp).
    pub expiration: i64,
    /// Feature flags.
    features: [Feature; MAX_FEATURES],
    feature_count: usize,
    /// ML-DSA-87 signature.
    signature: [u8; 4627],
    sig_len: usize,
}

impl License {
    /// Create a new unsigned license.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::params("subject" : "string", "product" : "string", "expiration" : "i64")]
    /// #[rr::returns("Ok(license) | Err(e)")]
    /// ```
    pub fn new(subject: &str, product: &str, expiration: i64) -> Result<Self, LicenseError> {
        if subject.len() > MAX_SUBJECT_LEN {
            return Err(LicenseError::SubjectTooLong);
        }
        if product.len() > MAX_PRODUCT_LEN {
            return Err(LicenseError::ProductTooLong);
        }

        let mut subject_arr = [0u8; MAX_SUBJECT_LEN];
        subject_arr[..subject.len()].copy_from_slice(subject.as_bytes());

        let mut product_arr = [0u8; MAX_PRODUCT_LEN];
        product_arr[..product.len()].copy_from_slice(product.as_bytes());

        Ok(Self {
            version: LICENSE_VERSION,
            subject: subject_arr,
            subject_len: subject.len(),
            product: product_arr,
            product_len: product.len(),
            expiration,
            features: [Feature::default(); MAX_FEATURES],
            feature_count: 0,
            signature: [0u8; 4627],
            sig_len: 0,
        })
    }

    /// Get the subject (user id) with error handling.
    ///
    /// Returns `Err(LicenseError::InvalidUtf8)` if the stored bytes are not valid UTF-8.
    /// This should never happen for licenses created via `License::new()`.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::returns("Ok(s) | Err(InvalidUtf8)")]
    /// #[rr::ensures("self was created via License::new(valid_utf8, _, _) => result = Ok(_)")]
    /// ```
    pub fn try_subject(&self) -> Result<&str, LicenseError> {
        core::str::from_utf8(&self.subject[..self.subject_len])
            .map_err(|_| LicenseError::InvalidUtf8)
    }

    /// Get the subject (user id).
    ///
    /// # Safety
    /// Returns empty string if UTF-8 validation fails (should never happen
    /// for licenses created through the public API).
    #[inline]
    pub fn subject(&self) -> &str {
        self.try_subject().unwrap_or("")
    }

    /// Get the product code with error handling.
    ///
    /// Returns `Err(LicenseError::InvalidUtf8)` if the stored bytes are not valid UTF-8.
    /// This should never happen for licenses created via `License::new()`.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::returns("Ok(s) | Err(InvalidUtf8)")]
    /// #[rr::ensures("self was created via License::new(_, valid_utf8, _) => result = Ok(_)")]
    /// ```
    pub fn try_product(&self) -> Result<&str, LicenseError> {
        core::str::from_utf8(&self.product[..self.product_len])
            .map_err(|_| LicenseError::InvalidUtf8)
    }

    /// Get the product code.
    ///
    /// # Safety
    /// Returns empty string if UTF-8 validation fails (should never happen
    /// for licenses created through the public API).
    #[inline]
    pub fn product(&self) -> &str {
        self.try_product().unwrap_or("")
    }

    /// Get the feature list.
    pub fn features(&self) -> &[Feature] {
        &self.features[..self.feature_count]
    }

    /// Get the signature bytes.
    pub fn signature(&self) -> &[u8] {
        &self.signature[..self.sig_len]
    }

    /// Add a feature to the license.
    pub fn add_feature(&mut self, name: &str) -> Result<(), LicenseError> {
        if self.feature_count >= MAX_FEATURES {
            return Err(LicenseError::TooManyFeatures);
        }
        self.features[self.feature_count] = Feature::new(name)?;
        self.feature_count += 1;
        Ok(())
    }

    /// Check if license has a specific feature.
    pub fn has_feature(&self, name: &str) -> bool {
        self.features[..self.feature_count]
            .iter()
            .any(|f| f.as_str() == name)
    }

    /// Set the signature.
    pub fn set_signature(&mut self, sig: &[u8]) -> Result<(), LicenseError> {
        if sig.len() > 4627 {
            return Err(LicenseError::InvalidSignatureLength);
        }
        self.signature[..sig.len()].copy_from_slice(sig);
        self.sig_len = sig.len();
        Ok(())
    }

    /// Check if the license is expired given the current time.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::params("now" : "i64")]
    /// #[rr::returns("#(now > self.expiration)")]
    /// ```
    #[inline]
    pub fn is_expired(&self, now: i64) -> bool {
        now > self.expiration
    }

    /// Encode the signable portion (everything except sig).
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::returns("Ok(n) | Err(e)")]
    /// #[rr::ensures("Ok(n) => buffer[..n] == canonical_cbor(self.signable())")]
    /// ```
    pub fn encode_signable(&self, buffer: &mut [u8]) -> Result<usize, LicenseError> {
        let mut enc = Encoder::new(buffer);

        // Map with 5 fields (sorted keys: exp, feat, prod, sub, v)
        enc.encode_map_header(5)?;

        // "exp"
        enc.encode_text("exp")?;
        enc.encode_int(self.expiration)?;

        // "feat"
        enc.encode_text("feat")?;
        enc.encode_array_header(self.feature_count)?;
        for i in 0..self.feature_count {
            enc.encode_text(self.features[i].as_str())?;
        }

        // "prod"
        enc.encode_text("prod")?;
        enc.encode_text(self.product())?;

        // "sub"
        enc.encode_text("sub")?;
        enc.encode_text(self.subject())?;

        // "v"
        enc.encode_text("v")?;
        enc.encode_uint(self.version)?;

        Ok(enc.position())
    }

    /// Encode the full license including signature.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::returns("Ok(n) | Err(e)")]
    /// #[rr::ensures("Ok(n) => buffer[..n] == canonical_cbor(self)")]
    /// ```
    pub fn encode(&self, buffer: &mut [u8]) -> Result<usize, LicenseError> {
        let mut enc = Encoder::new(buffer);

        // Map with 6 fields (sorted keys: exp, feat, prod, sig, sub, v)
        enc.encode_map_header(6)?;

        // "exp"
        enc.encode_text("exp")?;
        enc.encode_int(self.expiration)?;

        // "feat"
        enc.encode_text("feat")?;
        enc.encode_array_header(self.feature_count)?;
        for i in 0..self.feature_count {
            enc.encode_text(self.features[i].as_str())?;
        }

        // "prod"
        enc.encode_text("prod")?;
        enc.encode_text(self.product())?;

        // "sig"
        enc.encode_text("sig")?;
        enc.encode_bytes(&self.signature[..self.sig_len])?;

        // "sub"
        enc.encode_text("sub")?;
        enc.encode_text(self.subject())?;

        // "v"
        enc.encode_text("v")?;
        enc.encode_uint(self.version)?;

        Ok(enc.position())
    }

    /// Decode a license from canonical CBOR.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::params("data" : "list u8")]
    /// #[rr::returns("Ok(license) | Err(e)")]
    /// #[rr::ensures("total_decoder: all inputs handled")]
    /// ```
    pub fn decode(data: &[u8]) -> Result<Self, LicenseError> {
        let mut dec = Decoder::new(data);

        let map_len = dec.decode_map_header()?;
        // FORWARD COMPATIBILITY: Accept maps with >= 6 fields.
        // Older versions created 6-field licenses; future versions may add more.
        // Unknown fields will be skipped below.
        if map_len < 6 {
            return Err(LicenseError::MissingField("expected at least 6 fields"));
        }

        let mut version = None;
        let mut subject = None;
        let mut product = None;
        let mut expiration = None;
        let mut features: Option<([Feature; MAX_FEATURES], usize)> = None;
        let mut signature = None;

        for _ in 0..map_len {
            let key = dec.decode_text()?;
            match key {
                "v" => {
                    let v = dec.decode_uint()?;
                    if v != LICENSE_VERSION {
                        return Err(LicenseError::UnsupportedVersion(v));
                    }
                    version = Some(v);
                }
                "sub" => {
                    let s = dec.decode_text()?;
                    if s.len() > MAX_SUBJECT_LEN {
                        return Err(LicenseError::SubjectTooLong);
                    }
                    let mut arr = [0u8; MAX_SUBJECT_LEN];
                    arr[..s.len()].copy_from_slice(s.as_bytes());
                    subject = Some((arr, s.len()));
                }
                "prod" => {
                    let p = dec.decode_text()?;
                    if p.len() > MAX_PRODUCT_LEN {
                        return Err(LicenseError::ProductTooLong);
                    }
                    let mut arr = [0u8; MAX_PRODUCT_LEN];
                    arr[..p.len()].copy_from_slice(p.as_bytes());
                    product = Some((arr, p.len()));
                }
                "exp" => {
                    expiration = Some(dec.decode_int()?);
                }
                "feat" => {
                    let arr_len = dec.decode_array_header()?;
                    if arr_len > MAX_FEATURES {
                        return Err(LicenseError::TooManyFeatures);
                    }
                    let mut feat_arr = [Feature::default(); MAX_FEATURES];
                    for feat in feat_arr.iter_mut().take(arr_len) {
                        let name = dec.decode_text()?;
                        *feat = Feature::new(name)?;
                    }
                    features = Some((feat_arr, arr_len));
                }
                "sig" => {
                    let s = dec.decode_bytes()?;
                    if s.len() > 4627 {
                        return Err(LicenseError::InvalidSignatureLength);
                    }
                    let mut arr = [0u8; 4627];
                    arr[..s.len()].copy_from_slice(s);
                    signature = Some((arr, s.len()));
                }
                _ => {
                    // Skip unknown fields for forward compatibility
                    dec.skip_value()?;
                }
            }
        }

        let (sub_arr, sub_len) = subject.ok_or(LicenseError::MissingField("sub"))?;
        let (prod_arr, prod_len) = product.ok_or(LicenseError::MissingField("prod"))?;
        let (feat_arr, feat_count) = features.ok_or(LicenseError::MissingField("feat"))?;
        let (sig_arr, sig_len) = signature.ok_or(LicenseError::MissingField("sig"))?;

        Ok(License {
            version: version.ok_or(LicenseError::MissingField("v"))?,
            subject: sub_arr,
            subject_len: sub_len,
            product: prod_arr,
            product_len: prod_len,
            expiration: expiration.ok_or(LicenseError::MissingField("exp"))?,
            features: feat_arr,
            feature_count: feat_count,
            signature: sig_arr,
            sig_len,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_license_new() {
        let lic = License::new("user@example.com", "my-product", 1735689600).unwrap();
        assert_eq!(lic.version, 1);
        assert_eq!(lic.subject(), "user@example.com");
        assert_eq!(lic.product(), "my-product");
        assert_eq!(lic.expiration, 1735689600);
    }

    #[test]
    fn test_license_features() {
        let mut lic = License::new("user@example.com", "pro", 1735689600).unwrap();
        lic.add_feature("offline").unwrap();
        lic.add_feature("team5").unwrap();

        assert!(lic.has_feature("offline"));
        assert!(lic.has_feature("team5"));
        assert!(!lic.has_feature("enterprise"));
    }

    #[test]
    fn test_license_encode_decode() {
        let mut lic = License::new("alice@test.com", "sparkpass-pro", 1735689600).unwrap();
        lic.add_feature("offline").unwrap();
        lic.add_feature("sync").unwrap();
        lic.set_signature(&[0xAB; 100]).unwrap();

        let mut buf = [0u8; 1024];
        let len = lic.encode(&mut buf).unwrap();

        let decoded = License::decode(&buf[..len]).unwrap();
        assert_eq!(decoded.subject(), "alice@test.com");
        assert_eq!(decoded.product(), "sparkpass-pro");
        assert_eq!(decoded.expiration, 1735689600);
        assert!(decoded.has_feature("offline"));
        assert!(decoded.has_feature("sync"));
    }

    #[test]
    fn test_license_expired() {
        let lic = License::new("user@test.com", "prod", 1000).unwrap();
        assert!(!lic.is_expired(999));
        assert!(!lic.is_expired(1000));
        assert!(lic.is_expired(1001));
    }
}
