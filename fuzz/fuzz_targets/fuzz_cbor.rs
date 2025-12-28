//! Fuzz target for CBOR parsing.
//!
//! Tests that malformed CBOR input never causes panics or memory safety issues.

#![no_main]

use libfuzzer_sys::fuzz_target;
use anubis_core::cbor::Decoder;

fuzz_target!(|data: &[u8]| {
    // Create a decoder for arbitrary bytes
    let mut dec = Decoder::new(data);

    // Try various decode operations - should never panic
    while !dec.is_empty() {
        // Try to skip a value
        if dec.skip_value().is_err() {
            break;
        }
    }

    // Fresh decoder - try different decode methods
    let mut dec = Decoder::new(data);
    let _ = dec.decode_uint();

    let mut dec = Decoder::new(data);
    let _ = dec.decode_int();

    let mut dec = Decoder::new(data);
    let _ = dec.decode_bytes();

    let mut dec = Decoder::new(data);
    let _ = dec.decode_text();

    let mut dec = Decoder::new(data);
    let _ = dec.decode_array_header();

    let mut dec = Decoder::new(data);
    let _ = dec.decode_map_header();

    let mut dec = Decoder::new(data);
    let _ = dec.decode_bool();

    // Also test the ciborium wrapper with arbitrary bytes
    let _ = anubis_core::cbor::from_slice::<ciborium::Value>(data);
});
