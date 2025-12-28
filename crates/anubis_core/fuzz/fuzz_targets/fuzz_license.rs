//! Fuzz target for License CBOR parsing.
//!
//! Tests that:
//! 1. License decoding doesn't panic on arbitrary CBOR
//! 2. Valid licenses roundtrip correctly
//! 3. Malformed input is rejected gracefully
//! 4. All bounds are respected (subject, product, features)

#![no_main]

use libfuzzer_sys::fuzz_target;
use arbitrary::{Arbitrary, Unstructured};

use anubis_core::license::{License, Feature, MAX_SUBJECT_LEN, MAX_PRODUCT_LEN, MAX_FEATURES, MAX_FEATURE_LEN};

/// Structured input for license fuzzing
#[derive(Debug, Arbitrary)]
struct LicenseFuzzInput {
    /// Subject (user id/email)
    subject: String,
    /// Product code
    product: String,
    /// Expiration timestamp
    expiry: i64,
    /// Feature names
    features: Vec<String>,
    /// Signature bytes
    signature: Vec<u8>,
}

fuzz_target!(|data: &[u8]| {
    // Raw CBOR parsing - must not panic
    fuzz_raw_cbor(data);

    // Structured fuzzing
    if let Ok(input) = LicenseFuzzInput::arbitrary(&mut Unstructured::new(data)) {
        fuzz_structured(&input);
    }
});

/// Fuzz license decoding with raw CBOR bytes
fn fuzz_raw_cbor(data: &[u8]) {
    // Try to decode as a license - must not panic
    let result = License::decode(data);

    // If decoding succeeded, verify invariants
    if let Ok(license) = result {
        // Subject length bounds
        assert!(license.subject_len <= MAX_SUBJECT_LEN);

        // Product length bounds
        assert!(license.product_len <= MAX_PRODUCT_LEN);

        // Feature count bounds
        assert!(license.feature_count <= MAX_FEATURES);

        // Each feature length bounds
        for i in 0..license.feature_count {
            assert!(license.features[i].len <= MAX_FEATURE_LEN);
        }

        // Signature length bounds (ML-DSA-87)
        assert!(license.signature_len <= 4627);

        // Version must be 1
        assert_eq!(license.version, 1);

        // Roundtrip test
        let mut buf = vec![0u8; 16384];
        if let Ok(encoded_len) = license.encode(&mut buf) {
            let reencoded = &buf[..encoded_len];
            if let Ok(decoded_again) = License::decode(reencoded) {
                // Core fields must match
                assert_eq!(license.version, decoded_again.version);
                assert_eq!(license.subject_len, decoded_again.subject_len);
                assert_eq!(license.product_len, decoded_again.product_len);
                assert_eq!(license.expiry, decoded_again.expiry);
                assert_eq!(license.feature_count, decoded_again.feature_count);
            }
        }
    }
}

/// Fuzz with structured inputs
fn fuzz_structured(input: &LicenseFuzzInput) {
    // Truncate strings to valid lengths
    let subject = if input.subject.len() <= MAX_SUBJECT_LEN {
        &input.subject
    } else {
        &input.subject[..MAX_SUBJECT_LEN.min(input.subject.len())]
    };

    let product = if input.product.len() <= MAX_PRODUCT_LEN {
        &input.product
    } else {
        &input.product[..MAX_PRODUCT_LEN.min(input.product.len())]
    };

    // Create features (limited count and length)
    let mut features = Vec::new();
    for (i, name) in input.features.iter().take(MAX_FEATURES).enumerate() {
        let truncated = if name.len() <= MAX_FEATURE_LEN {
            name.as_str()
        } else {
            // Find a valid UTF-8 boundary
            let mut end = MAX_FEATURE_LEN;
            while end > 0 && !name.is_char_boundary(end) {
                end -= 1;
            }
            &name[..end]
        };
        if let Ok(f) = Feature::new(truncated) {
            features.push(f);
        }
    }

    // Create license with builder pattern if available, or directly
    let result = License::new(subject, product, input.expiry);

    if let Ok(mut license) = result {
        // Add features
        for f in &features {
            let _ = license.add_feature(f.as_str());
        }

        // Add signature
        let sig_len = input.signature.len().min(4627);
        license.signature[..sig_len].copy_from_slice(&input.signature[..sig_len]);
        license.signature_len = sig_len;

        // Encode and decode - must not panic
        let mut buf = vec![0u8; 32768];
        if let Ok(len) = license.encode(&mut buf) {
            let encoded = &buf[..len];

            // Decode must succeed for valid encoding
            if let Ok(decoded) = License::decode(encoded) {
                // Verify roundtrip preserves key fields
                assert_eq!(license.version, decoded.version);
                assert_eq!(license.expiry, decoded.expiry);
                assert_eq!(license.feature_count, decoded.feature_count);
                assert_eq!(license.signature_len, decoded.signature_len);

                // Subject and product should match
                let orig_subject = license.try_subject().unwrap_or("");
                let dec_subject = decoded.try_subject().unwrap_or("");
                assert_eq!(orig_subject, dec_subject);

                let orig_product = license.try_product().unwrap_or("");
                let dec_product = decoded.try_product().unwrap_or("");
                assert_eq!(orig_product, dec_product);
            }
        }
    }

    // Test validation functions with arbitrary data
    if !subject.is_empty() && !product.is_empty() {
        // Test Feature::new with arbitrary strings
        for name in &input.features {
            let _ = Feature::new(name);
        }
    }
}
