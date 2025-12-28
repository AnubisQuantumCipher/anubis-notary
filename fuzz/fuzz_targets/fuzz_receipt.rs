//! Fuzz target for Receipt CBOR parsing.
//!
//! Tests that malformed receipt data never causes panics.

#![no_main]

use libfuzzer_sys::fuzz_target;
use anubis_core::receipt::Receipt;

fuzz_target!(|data: &[u8]| {
    // Try to decode arbitrary bytes as a Receipt
    let decoded = Receipt::decode(data);

    // If decoding succeeded, try to re-encode and verify roundtrip
    if let Ok(receipt) = decoded {
        let mut buf = [0u8; 8192];
        if let Ok(len) = receipt.encode(&mut buf) {
            // Re-decode should produce equivalent receipt
            if let Ok(receipt2) = Receipt::decode(&buf[..len]) {
                assert_eq!(receipt.digest, receipt2.digest);
                assert_eq!(receipt.created, receipt2.created);
            }
        }
    }
});
