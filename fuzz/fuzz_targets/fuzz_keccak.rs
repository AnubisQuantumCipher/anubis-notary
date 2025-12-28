//! Fuzz target for Keccak/SHA3/SHAKE.
//!
//! Tests that arbitrary input sizes are handled correctly without panics.

#![no_main]

use libfuzzer_sys::fuzz_target;
use anubis_core::keccak::{sha3, shake};

fuzz_target!(|data: &[u8]| {
    // SHA3-256
    let hash256 = sha3::sha3_256(data);
    assert_eq!(hash256.len(), 32);

    // SHAKE256 with various output lengths (const generics)
    let out32: [u8; 32] = shake::shake256(data);
    assert_eq!(out32.len(), 32);

    let out64: [u8; 64] = shake::shake256(data);
    assert_eq!(out64.len(), 64);

    let out128: [u8; 128] = shake::shake256(data);
    assert_eq!(out128.len(), 128);

    // Verify first bytes match for prefix consistency
    assert_eq!(out32[..], out64[..32]);
    assert_eq!(out64[..], out128[..64]);

    // Incremental API
    let mut hasher = shake::Shake256::new();
    hasher.absorb(data);
    let fixed: [u8; 32] = hasher.squeeze_fixed();
    assert_eq!(fixed, out32, "Incremental and one-shot should match");
});
