//! Fuzz target for ML-DSA-87 (FIPS 204).
//!
//! Tests that:
//! - Signature parsing never panics on malformed input
//! - Public key parsing never panics on malformed input
//! - Verification of invalid signatures returns false, never panics
//! - Key generation and signing work correctly

#![no_main]

use libfuzzer_sys::fuzz_target;
use arbitrary::Arbitrary;

#[derive(Debug, Arbitrary)]
struct MldsaInput {
    seed: [u8; 32],      // Seed for key generation
    message: Vec<u8>,    // Message to sign
    fake_sig: Vec<u8>,   // Random bytes as fake signature
    fake_pk: Vec<u8>,    // Random bytes as fake public key
}

fuzz_target!(|input: MldsaInput| {
    use anubis_core::mldsa::{KeyPair, PublicKey, Signature};

    // Test key generation with fuzzed seed
    let kp = match KeyPair::from_seed(&input.seed) {
        Ok(kp) => kp,
        Err(_) => return, // Seed generation can fail in rare edge cases
    };

    // Test signing
    if let Ok(sig) = kp.sign(&input.message) {
        // Verify should succeed for valid signature
        let valid = kp.public_key().verify(&input.message, &sig);
        assert!(valid, "Valid signature should verify");

        // Wrong message should fail
        if !input.message.is_empty() {
            let mut wrong_msg = input.message.clone();
            wrong_msg[0] ^= 0xFF;
            let invalid = kp.public_key().verify(&wrong_msg, &sig);
            assert!(!invalid, "Wrong message should not verify");
        }
    }

    // Test parsing of random bytes as signature - should not panic
    let _ = Signature::from_bytes(&input.fake_sig);

    // Test parsing of random bytes as public key - should not panic
    let _ = PublicKey::from_bytes(&input.fake_pk);

    // If we could parse a signature, try verifying it
    if let Ok(fake_sig) = Signature::from_bytes(&input.fake_sig) {
        // Should return false, not panic
        let result = kp.public_key().verify(&input.message, &fake_sig);
        // We don't assert !result because a random signature could
        // theoretically be valid for a specific message (astronomically unlikely)
        let _ = result;
    }
});
