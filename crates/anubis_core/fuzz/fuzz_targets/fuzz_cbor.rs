//! Comprehensive fuzz target for CBOR encoding/decoding.
//!
//! Tests that:
//! 1. Decoding arbitrary bytes doesn't panic (totality)
//! 2. Encode-decode roundtrip preserves values
//! 3. Valid CBOR never causes undefined behavior
//! 4. Position invariants are maintained
//! 5. Error handling is correct

#![no_main]

use libfuzzer_sys::fuzz_target;
use arbitrary::{Arbitrary, Unstructured};

use anubis_core::cbor::{Decoder, Encoder, canonical_cmp};

/// Structured input for targeted fuzzing
#[derive(Debug, Arbitrary)]
struct CborFuzzInput {
    /// Raw bytes for decoder testing
    raw: Vec<u8>,
    /// Integers for roundtrip testing
    uints: Vec<u64>,
    ints: Vec<i64>,
    /// Bytes for roundtrip testing
    bytes: Vec<Vec<u8>>,
    /// Texts for roundtrip testing (valid UTF-8)
    texts: Vec<String>,
    /// Booleans for roundtrip testing
    bools: Vec<bool>,
    /// Nested structure depth for recursion testing
    depth: u8,
}

fuzz_target!(|data: &[u8]| {
    // Try structured fuzzing first
    if let Ok(input) = CborFuzzInput::arbitrary(&mut Unstructured::new(data)) {
        fuzz_structured(&input);
    }

    // Always do raw byte fuzzing
    fuzz_raw_bytes(data);
});

/// Fuzz with structured, typed inputs
fn fuzz_structured(input: &CborFuzzInput) {
    let mut buf = vec![0u8; 65536];

    // Test uint roundtrip
    for &value in &input.uints {
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_uint(value).is_ok() {
            let encoded = encoder.as_bytes();
            let mut decoder = Decoder::new(encoded);
            if let Ok(decoded) = decoder.decode_uint() {
                assert_eq!(value, decoded, "uint roundtrip failed");
            }
        }
    }

    // Test int roundtrip
    for &value in &input.ints {
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_int(value).is_ok() {
            let encoded = encoder.as_bytes();
            let mut decoder = Decoder::new(encoded);
            if let Ok(decoded) = decoder.decode_int() {
                assert_eq!(value, decoded, "int roundtrip failed");
            }
        }
    }

    // Test bytes roundtrip
    for value in &input.bytes {
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_bytes(value).is_ok() {
            let encoded = encoder.as_bytes();
            let mut decoder = Decoder::new(encoded);
            if let Ok(decoded) = decoder.decode_bytes() {
                assert_eq!(value.as_slice(), decoded, "bytes roundtrip failed");
            }
        }
    }

    // Test text roundtrip
    for value in &input.texts {
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_text(value).is_ok() {
            let encoded = encoder.as_bytes();
            let mut decoder = Decoder::new(encoded);
            if let Ok(decoded) = decoder.decode_text() {
                assert_eq!(value.as_str(), decoded, "text roundtrip failed");
            }
        }
    }

    // Test bool roundtrip
    for &value in &input.bools {
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_bool(value).is_ok() {
            let encoded = encoder.as_bytes();
            let mut decoder = Decoder::new(encoded);
            if let Ok(decoded) = decoder.decode_bool() {
                assert_eq!(value, decoded, "bool roundtrip failed");
            }
        }
    }

    // Test array encoding
    let depth = (input.depth % 8) as usize; // Limit recursion
    if depth > 0 && !input.uints.is_empty() {
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_array_header(input.uints.len().min(16)).is_ok() {
            for &v in input.uints.iter().take(16) {
                let _ = encoder.encode_uint(v);
            }
            let encoded = encoder.as_bytes().to_vec();
            let mut decoder = Decoder::new(&encoded);
            if let Ok(len) = decoder.decode_array_header() {
                for _ in 0..len {
                    let _ = decoder.decode_uint();
                }
            }
        }
    }

    // Test map encoding
    if !input.texts.is_empty() && !input.uints.is_empty() {
        let pairs = input.texts.len().min(input.uints.len()).min(16);
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_map_header(pairs).is_ok() {
            for (t, &u) in input.texts.iter().zip(input.uints.iter()).take(pairs) {
                let _ = encoder.encode_text(t);
                let _ = encoder.encode_uint(u);
            }
            let encoded = encoder.as_bytes().to_vec();
            let mut decoder = Decoder::new(&encoded);
            if let Ok(len) = decoder.decode_map_header() {
                for _ in 0..len {
                    let _ = decoder.decode_text();
                    let _ = decoder.decode_uint();
                }
            }
        }
    }
}

/// Fuzz with raw arbitrary bytes
fn fuzz_raw_bytes(data: &[u8]) {
    // Test 1: skip_value must not panic on any input
    // This exercises the recursive CBOR parser
    {
        let mut decoder = Decoder::new(data);
        let _ = decoder.skip_value();
        // Position invariant: pos <= buffer.len()
        assert!(decoder.position() <= data.len());
    }

    // Test 2: All decode operations must not panic
    {
        let mut decoder = Decoder::new(data);
        let _ = decoder.decode_uint();
        assert!(decoder.position() <= data.len());
    }
    {
        let mut decoder = Decoder::new(data);
        let _ = decoder.decode_int();
        assert!(decoder.position() <= data.len());
    }
    {
        let mut decoder = Decoder::new(data);
        let _ = decoder.decode_bytes();
        assert!(decoder.position() <= data.len());
    }
    {
        let mut decoder = Decoder::new(data);
        let _ = decoder.decode_text();
        assert!(decoder.position() <= data.len());
    }
    {
        let mut decoder = Decoder::new(data);
        let _ = decoder.decode_array_header();
        assert!(decoder.position() <= data.len());
    }
    {
        let mut decoder = Decoder::new(data);
        let _ = decoder.decode_map_header();
        assert!(decoder.position() <= data.len());
    }
    {
        let mut decoder = Decoder::new(data);
        let _ = decoder.decode_bool();
        assert!(decoder.position() <= data.len());
    }

    // Test 3: canonical_cmp must not panic
    if data.len() >= 2 {
        let mid = data.len() / 2;
        let a = &data[..mid];
        let b = &data[mid..];
        let _ = canonical_cmp(a, b);
        let _ = canonical_cmp(b, a);
        // Antisymmetry check
        let cmp_ab = canonical_cmp(a, b);
        let cmp_ba = canonical_cmp(b, a);
        assert_eq!(cmp_ab.reverse(), cmp_ba);
    }

    // Test 4: Multiple sequential decodes
    {
        let mut decoder = Decoder::new(data);
        for _ in 0..10 {
            if decoder.is_empty() {
                break;
            }
            let _ = decoder.skip_value();
        }
        assert!(decoder.position() <= data.len());
    }

    // Test 5: Encode-decode roundtrip for any extractable uint
    if data.len() >= 8 {
        let value = u64::from_le_bytes([
            data[0], data[1], data[2], data[3],
            data[4], data[5], data[6], data[7],
        ]);

        let mut buf = [0u8; 16];
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_uint(value).is_ok() {
            let encoded = encoder.as_bytes();
            let mut decoder = Decoder::new(encoded);
            if let Ok(decoded) = decoder.decode_uint() {
                assert_eq!(value, decoded, "Roundtrip must preserve uint value");
            }
        }
    }

    // Test 6: Signed int roundtrip
    if data.len() >= 8 {
        let value = i64::from_le_bytes([
            data[0], data[1], data[2], data[3],
            data[4], data[5], data[6], data[7],
        ]);

        let mut buf = [0u8; 16];
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_int(value).is_ok() {
            let encoded = encoder.as_bytes();
            let mut decoder = Decoder::new(encoded);
            if let Ok(decoded) = decoder.decode_int() {
                assert_eq!(value, decoded, "Roundtrip must preserve int value");
            }
        }
    }

    // Test 7: Bytes roundtrip
    if !data.is_empty() {
        let mut buf = vec![0u8; data.len() + 16];
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_bytes(data).is_ok() {
            let encoded = encoder.as_bytes().to_vec();
            let mut decoder = Decoder::new(&encoded);
            if let Ok(decoded) = decoder.decode_bytes() {
                assert_eq!(data, decoded, "Roundtrip must preserve bytes");
            }
        }
    }

    // Test 8: Null encoding/decoding
    {
        let mut buf = [0u8; 8];
        let mut encoder = Encoder::new(&mut buf);
        if encoder.encode_null().is_ok() {
            let encoded = encoder.as_bytes();
            // Null should encode to 0xF6
            assert_eq!(encoded, &[0xF6]);
        }
    }
}
