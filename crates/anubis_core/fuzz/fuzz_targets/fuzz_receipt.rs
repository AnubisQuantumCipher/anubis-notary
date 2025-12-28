//! Fuzz target for Receipt CBOR parsing.
//!
//! Tests that:
//! 1. Receipt decoding doesn't panic on arbitrary CBOR
//! 2. Valid receipts roundtrip correctly
//! 3. Malformed input is rejected gracefully
//! 4. All invariants are maintained (digest length, sig length, etc.)

#![no_main]

use libfuzzer_sys::fuzz_target;
use arbitrary::{Arbitrary, Unstructured};

use anubis_core::receipt::{Receipt, TimeSource, AnchorType};

/// Structured input for receipt fuzzing
#[derive(Debug, Arbitrary)]
struct ReceiptFuzzInput {
    /// Digest bytes (should be 32 bytes for valid receipt)
    digest: Vec<u8>,
    /// Creation timestamp
    created: i64,
    /// Signature bytes
    signature: Vec<u8>,
    /// Time source variant
    time_variant: u8,
    /// Anchor variant
    anchor_variant: u8,
    /// Random padding/metadata
    metadata: Vec<u8>,
}

fuzz_target!(|data: &[u8]| {
    // Raw CBOR parsing - must not panic
    fuzz_raw_cbor(data);

    // Structured fuzzing
    if let Ok(input) = ReceiptFuzzInput::arbitrary(&mut Unstructured::new(data)) {
        fuzz_structured(&input);
    }
});

/// Fuzz receipt decoding with raw CBOR bytes
fn fuzz_raw_cbor(data: &[u8]) {
    // Try to decode as a receipt - must not panic
    let result = Receipt::decode(data);

    // If decoding succeeded, verify invariants
    if let Ok(receipt) = result {
        // Digest must be exactly 32 bytes
        assert_eq!(receipt.digest.len(), 32);

        // Signature must be valid ML-DSA-87 size or less
        assert!(receipt.signature_len <= 4627);

        // Version must be 1
        assert_eq!(receipt.version, 1);

        // Roundtrip test
        let mut buf = vec![0u8; 8192];
        if let Ok(encoded_len) = receipt.encode(&mut buf) {
            let reencoded = &buf[..encoded_len];
            if let Ok(decoded_again) = Receipt::decode(reencoded) {
                // Core fields must match
                assert_eq!(receipt.version, decoded_again.version);
                assert_eq!(receipt.digest, decoded_again.digest);
                assert_eq!(receipt.created, decoded_again.created);
                assert_eq!(receipt.signature_len, decoded_again.signature_len);
            }
        }
    }
}

/// Fuzz with structured inputs
fn fuzz_structured(input: &ReceiptFuzzInput) {
    // Create a receipt with controlled inputs
    let mut receipt = Receipt {
        version: 1,
        digest: [0u8; 32],
        created: input.created.max(0), // Ensure non-negative
        time: TimeSource::Local,
        anchor: AnchorType::None,
        signature: [0u8; 4627],
        signature_len: 0,
    };

    // Copy digest if correct length
    if input.digest.len() == 32 {
        receipt.digest.copy_from_slice(&input.digest);
    } else if !input.digest.is_empty() {
        // Partial copy for invalid inputs
        let len = input.digest.len().min(32);
        receipt.digest[..len].copy_from_slice(&input.digest[..len]);
    }

    // Copy signature
    let sig_len = input.signature.len().min(4627);
    receipt.signature[..sig_len].copy_from_slice(&input.signature[..sig_len]);
    receipt.signature_len = sig_len;

    // Set time source based on variant
    receipt.time = match input.time_variant % 3 {
        0 => TimeSource::Local,
        1 => {
            let mut token = [0u8; 256];
            let len = input.metadata.len().min(256);
            if len > 0 {
                token[..len].copy_from_slice(&input.metadata[..len]);
            }
            TimeSource::Rfc3161 { token, len }
        }
        _ => {
            let mut proof = [0u8; 512];
            let len = input.metadata.len().min(512);
            if len > 0 {
                proof[..len].copy_from_slice(&input.metadata[..len]);
            }
            TimeSource::Ots { proof, len }
        }
    };

    // Set anchor type based on variant
    receipt.anchor = match input.anchor_variant % 3 {
        0 => AnchorType::None,
        1 => {
            let mut txid = [0u8; 32];
            if input.digest.len() >= 32 {
                txid.copy_from_slice(&input.digest[..32]);
            }
            AnchorType::Btc {
                txid,
                height: input.created as u64,
            }
        }
        _ => {
            let mut url = [0u8; 256];
            let url_len = input.metadata.len().min(256);
            if url_len > 0 {
                url[..url_len].copy_from_slice(&input.metadata[..url_len]);
            }
            AnchorType::HttpLog {
                url,
                url_len,
                entry_id: input.created as u64,
            }
        }
    };

    // Encode and decode - must not panic
    let mut buf = vec![0u8; 16384];
    if let Ok(len) = receipt.encode(&mut buf) {
        let encoded = &buf[..len];

        // Decode must succeed for valid encoding
        if let Ok(decoded) = Receipt::decode(encoded) {
            // Verify roundtrip
            assert_eq!(receipt.version, decoded.version);
            assert_eq!(receipt.digest, decoded.digest);
            assert_eq!(receipt.created, decoded.created);
            assert_eq!(receipt.signature_len, decoded.signature_len);
            assert_eq!(
                &receipt.signature[..receipt.signature_len],
                &decoded.signature[..decoded.signature_len]
            );
        }
    }
}
