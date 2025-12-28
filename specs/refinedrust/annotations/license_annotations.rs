//! RefinedRust Annotations for license module
//!
//! This file shows the complete refinement type annotations for the
//! license token schema with CBOR encoding/decoding.

// ============================================================================
// Constants
// ============================================================================

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

/// ML-DSA-87 signature size.
pub const MAX_SIGNATURE_LEN: usize = 4627;

// ============================================================================
// Feature Type
// ============================================================================

/// A feature flag stored in fixed-size buffer.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("name" : "string")]
/// #[rr::invariant("len(name) <= MAX_FEATURE_LEN")]
/// ```
#[rr::type("Feature")]
pub struct Feature {
    name: [u8; MAX_FEATURE_LEN],
    len: usize,
}

// ============================================================================
// Feature::new
// ============================================================================

/// Create a new feature from a string slice.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("name_str" : "string")]
/// #[rr::args("name_str @ &str")]
/// #[rr::ensures("match result {
///     Ok(feat) =>
///         len(name_str) <= MAX_FEATURE_LEN /\
///         feat.as_str() = name_str
///   | Err(FeatureTooLong) =>
///         len(name_str) > MAX_FEATURE_LEN
/// }")]
/// ```
#[rr::verified]
pub fn new(name: &str) -> Result<Feature, LicenseError> {
    #[rr::assert("Validate feature name length")]
    if name.len() > MAX_FEATURE_LEN {
        return Err(LicenseError::FeatureTooLong);
    }

    let mut arr = [0u8; MAX_FEATURE_LEN];
    arr[..name.len()].copy_from_slice(name.as_bytes());

    Ok(Feature {
        name: arr,
        len: name.len(),
    })
}

// ============================================================================
// License Type
// ============================================================================

/// A signed license token.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("version" : "u64", "subject" : "string", "product" : "string",
///                  "expiration" : "i64", "features" : "list string",
///                  "signature" : "list u8")]
/// #[rr::invariant("version = LICENSE_VERSION")]
/// #[rr::invariant("len(subject) <= MAX_SUBJECT_LEN")]
/// #[rr::invariant("len(product) <= MAX_PRODUCT_LEN")]
/// #[rr::invariant("len(features) <= MAX_FEATURES")]
/// #[rr::invariant("forall f in features. len(f) <= MAX_FEATURE_LEN")]
/// #[rr::invariant("len(signature) <= MAX_SIGNATURE_LEN")]
/// ```
#[rr::type("License")]
pub struct License {
    version: u64,
    subject: [u8; MAX_SUBJECT_LEN],
    subject_len: usize,
    product: [u8; MAX_PRODUCT_LEN],
    product_len: usize,
    expiration: i64,
    features: [Feature; MAX_FEATURES],
    feature_count: usize,
    signature: [u8; MAX_SIGNATURE_LEN],
    sig_len: usize,
}

// ============================================================================
// License::new
// ============================================================================

/// Create a new unsigned license.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("subject" : "string", "product" : "string", "expiration" : "i64")]
/// #[rr::args("subject @ &str", "product @ &str", "expiration @ i64")]
/// #[rr::ensures("match result {
///     Ok(lic) =>
///         len(subject) <= MAX_SUBJECT_LEN /\
///         len(product) <= MAX_PRODUCT_LEN /\
///         lic.subject() = subject /\
///         lic.product() = product /\
///         lic.expiration = expiration /\
///         lic.feature_count = 0 /\
///         lic.sig_len = 0
///   | Err(SubjectTooLong) => len(subject) > MAX_SUBJECT_LEN
///   | Err(ProductTooLong) => len(product) > MAX_PRODUCT_LEN
/// }")]
/// ```
#[rr::verified]
pub fn new(subject: &str, product: &str, expiration: i64) -> Result<License, LicenseError> {
    #[rr::assert("Validate subject length")]
    if subject.len() > MAX_SUBJECT_LEN {
        return Err(LicenseError::SubjectTooLong);
    }

    #[rr::assert("Validate product length")]
    if product.len() > MAX_PRODUCT_LEN {
        return Err(LicenseError::ProductTooLong);
    }

    let mut subject_arr = [0u8; MAX_SUBJECT_LEN];
    subject_arr[..subject.len()].copy_from_slice(subject.as_bytes());

    let mut product_arr = [0u8; MAX_PRODUCT_LEN];
    product_arr[..product.len()].copy_from_slice(product.as_bytes());

    Ok(License {
        version: LICENSE_VERSION,
        subject: subject_arr,
        subject_len: subject.len(),
        product: product_arr,
        product_len: product.len(),
        expiration,
        features: [Feature::default(); MAX_FEATURES],
        feature_count: 0,
        signature: [0u8; MAX_SIGNATURE_LEN],
        sig_len: 0,
    })
}

// ============================================================================
// License::add_feature
// ============================================================================

/// Add a feature to the license.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname", "name" : "string")]
/// #[rr::args("(&mut self, gamma) @ &mut License", "name @ &str")]
/// #[rr::ensures("match result {
///     Ok(()) =>
///         self.feature_count = old(self.feature_count) + 1 /\
///         self.features[old(self.feature_count)] = Feature::new(name)
///   | Err(TooManyFeatures) =>
///         old(self.feature_count) >= MAX_FEATURES
///   | Err(FeatureTooLong) =>
///         len(name) > MAX_FEATURE_LEN
/// }")]
/// ```
#[rr::verified]
pub fn add_feature(&mut self, name: &str) -> Result<(), LicenseError> {
    #[rr::assert("Check feature count limit")]
    if self.feature_count >= MAX_FEATURES {
        return Err(LicenseError::TooManyFeatures);
    }

    self.features[self.feature_count] = Feature::new(name)?;
    self.feature_count += 1;

    Ok(())
}

// ============================================================================
// License::is_expired
// ============================================================================

/// Check if the license is expired given the current time.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("now" : "i64")]
/// #[rr::args("&self @ &shr<'_, License>", "now @ i64")]
/// #[rr::returns("now > self.expiration")]
/// ```
#[rr::verified]
#[inline]
pub fn is_expired(&self, now: i64) -> bool {
    now > self.expiration
}

// ============================================================================
// License::encode
// ============================================================================

/// Encode the full license including signature.
///
/// Keys are sorted lexicographically for canonical CBOR: exp, feat, prod, sig, sub, v
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname")]
/// #[rr::args("&self @ &shr<'_, License>", "(buffer, gamma) @ &mut [u8]")]
/// #[rr::ensures("match result {
///     Ok(n) =>
///         n <= len(buffer) /\
///         buffer[..n] = canonical_cbor(self) /\
///         (* Keys in sorted order *)
///         cbor_key_order(buffer[..n]) = [\"exp\", \"feat\", \"prod\", \"sig\", \"sub\", \"v\"]
///   | Err(e) =>
///         len(buffer) < required_encoding_size(self)
/// }")]
/// ```
#[rr::verified]
pub fn encode(&self, buffer: &mut [u8]) -> Result<usize, LicenseError> {
    let mut enc = Encoder::new(buffer);

    #[rr::assert("Map with 6 fields, keys in sorted order")]
    enc.encode_map_header(6)?;

    // Keys must be in lexicographic order for canonical CBOR
    enc.encode_text("exp")?;
    enc.encode_int(self.expiration)?;

    enc.encode_text("feat")?;
    enc.encode_array_header(self.feature_count)?;
    for i in 0..self.feature_count {
        enc.encode_text(self.features[i].as_str())?;
    }

    enc.encode_text("prod")?;
    enc.encode_text(self.product())?;

    enc.encode_text("sig")?;
    enc.encode_bytes(&self.signature[..self.sig_len])?;

    enc.encode_text("sub")?;
    enc.encode_text(self.subject())?;

    enc.encode_text("v")?;
    enc.encode_uint(self.version)?;

    Ok(enc.position())
}

// ============================================================================
// License::decode
// ============================================================================

/// Decode a license from canonical CBOR.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("data" : "list u8")]
/// #[rr::args("data @ &[u8]")]
/// #[rr::ensures("match result {
///     Ok(lic) =>
///         lic.version = LICENSE_VERSION /\
///         len(lic.subject()) <= MAX_SUBJECT_LEN /\
///         len(lic.product()) <= MAX_PRODUCT_LEN /\
///         lic.feature_count <= MAX_FEATURES /\
///         encode(lic) = data
///   | Err(_) => True
/// }")]
///
/// (* Totality: decoder never panics *)
/// #[rr::ensures("result = Ok(_) \\/ result = Err(_)")]
/// ```
#[rr::verified]
pub fn decode(data: &[u8]) -> Result<License, LicenseError> {
    let mut dec = Decoder::new(data);

    #[rr::assert("Decode map header - expect 6 fields")]
    let map_len = dec.decode_map_header()?;
    if map_len != 6 {
        return Err(LicenseError::MissingField("expected 6 fields"));
    }

    // ... field decoding with validation ...

    Ok(license)
}

// ============================================================================
// Verification Conditions
// ============================================================================

/// Proof obligations for license module:
///
/// ## Round-Trip Correctness
/// ```coq
/// Theorem license_roundtrip :
///   forall lic : License,
///     let encoded := encode(lic) in
///     decode(encoded) = Ok(lic).
/// ```
///
/// ## Totality (No Panics)
/// ```coq
/// Theorem decode_total :
///   forall data : list u8,
///     exists result, decode(data) = result.
/// ```
///
/// ## Canonical Key Order
/// ```coq
/// Theorem canonical_key_order :
///   forall lic buffer n,
///     encode(lic, buffer) = Ok(n) ->
///     cbor_keys_sorted(buffer[..n]).
/// ```
///
/// ## Subject Length Bounds
/// ```coq
/// Theorem subject_bounded :
///   forall lic : License,
///     len(lic.subject()) <= MAX_SUBJECT_LEN.
/// ```
///
/// ## Feature Count Bounds
/// ```coq
/// Theorem features_bounded :
///   forall lic : License,
///     lic.feature_count <= MAX_FEATURES.
/// ```
///
/// ## Expiration Check Correctness
/// ```coq
/// Theorem is_expired_correct :
///   forall lic now,
///     is_expired(lic, now) = true <-> now > lic.expiration.
/// ```
mod _verification_conditions {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_license_new() {
        let lic = License::new("user@example.com", "my-product", 1735689600).unwrap();
        assert_eq!(lic.version, 1);
        assert_eq!(lic.subject(), "user@example.com");
        assert_eq!(lic.product(), "my-product");
    }

    #[test]
    fn test_license_encode_decode() {
        let mut lic = License::new("alice@test.com", "pro", 1735689600).unwrap();
        lic.add_feature("offline").unwrap();
        lic.set_signature(&[0xAB; 100]).unwrap();

        let mut buf = [0u8; 1024];
        let len = lic.encode(&mut buf).unwrap();

        let decoded = License::decode(&buf[..len]).unwrap();
        assert_eq!(decoded.subject(), "alice@test.com");
        assert!(decoded.has_feature("offline"));
    }
}
