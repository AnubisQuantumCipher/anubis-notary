//! Fuzz target for Keccak-based hash functions.
//!
//! Tests that:
//! 1. Hashing arbitrary inputs doesn't panic
//! 2. Streaming == one-shot hashing
//! 3. SHAKE256 streaming properties hold

#![no_main]

use libfuzzer_sys::fuzz_target;
use arbitrary::Arbitrary;

use anubis_core::keccak::sha3::{sha3_256, Sha3_256};
use anubis_core::keccak::shake::{shake256, Shake256};

#[derive(Debug, Arbitrary)]
struct KeccakInput {
    data: Vec<u8>,
    split_point: usize,
    output_len: usize,
}

fuzz_target!(|input: KeccakInput| {
    // Limit sizes to avoid OOM
    if input.data.len() > 4096 {
        return;
    }

    // Property 1: SHA3-256 one-shot == streaming
    let oneshot = sha3_256(&input.data);

    let mut hasher = Sha3_256::new();
    hasher.update(&input.data);
    let streaming = hasher.finalize();

    assert_eq!(oneshot, streaming, "SHA3-256 one-shot != streaming");

    // Property 2: SHA3-256 split streaming == one-shot
    if !input.data.is_empty() {
        let split = input.split_point % input.data.len();
        let mut hasher = Sha3_256::new();
        hasher.update(&input.data[..split]);
        hasher.update(&input.data[split..]);
        let split_result = hasher.finalize();

        assert_eq!(oneshot, split_result, "SHA3-256 split streaming != one-shot");
    }

    // Property 3: SHAKE256 one-shot == streaming
    let oneshot_shake: [u8; 32] = shake256(&input.data);

    let mut xof = Shake256::new();
    xof.absorb(&input.data);
    let streaming_shake: [u8; 32] = xof.squeeze_fixed();

    assert_eq!(oneshot_shake, streaming_shake, "SHAKE256 one-shot != streaming");

    // Property 4: SHAKE256 split absorb == one absorb
    if !input.data.is_empty() {
        let split = input.split_point % input.data.len();
        let mut xof = Shake256::new();
        xof.absorb(&input.data[..split]);
        xof.absorb(&input.data[split..]);
        let split_result: [u8; 32] = xof.squeeze_fixed();

        assert_eq!(oneshot_shake, split_result, "SHAKE256 split absorb != one absorb");
    }

    // Property 5: SHAKE256 incremental squeeze consistency
    let output_len = (input.output_len % 256).max(1);

    let mut xof1 = Shake256::new();
    xof1.absorb(&input.data);
    let mut full_output = vec![0u8; output_len];
    xof1.squeeze(&mut full_output);

    let mut xof2 = Shake256::new();
    xof2.absorb(&input.data);
    let mut incremental_output = vec![0u8; output_len];
    // Squeeze in 8-byte chunks
    let mut offset = 0;
    while offset < output_len {
        let chunk_size = core::cmp::min(8, output_len - offset);
        xof2.squeeze(&mut incremental_output[offset..offset + chunk_size]);
        offset += chunk_size;
    }

    assert_eq!(full_output, incremental_output, "SHAKE256 incremental squeeze inconsistent");
});
