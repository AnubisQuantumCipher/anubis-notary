//! Fuzz target for License CBOR parsing.
//!
//! Tests that malformed license data never causes panics.

#![no_main]

use libfuzzer_sys::fuzz_target;
use anubis_core::license::License;

fuzz_target!(|data: &[u8]| {
    // Try to decode arbitrary bytes as a License
    let decoded = License::decode(data);

    // If decoding succeeded, verify fields are accessible without panic
    if let Ok(license) = decoded {
        // Access all fields to ensure they don't panic
        let _ = license.subject();
        let _ = license.product();
        let _ = license.expiration;
        let _ = license.features();
        let _ = license.signature();

        // Check expiration logic
        let _ = license.is_expired(0);
        let _ = license.is_expired(i64::MAX);

        // Try to re-encode
        let mut buf = [0u8; 8192];
        let _ = license.encode(&mut buf);
        let _ = license.encode_signable(&mut buf);
    }
});
