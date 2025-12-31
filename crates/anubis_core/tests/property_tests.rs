//! Property-based tests for anubis_core cryptographic primitives.
//!
//! These tests use proptest to verify algebraic properties and invariants.

use proptest::prelude::*;

// ============================================================================
// Byte Utilities Property Tests
// ============================================================================

mod bytes_properties {
    use super::*;
    use anubis_core::bytes::*;

    proptest! {
        /// LE32 round-trip: store then load recovers original
        #[test]
        fn le32_roundtrip(word: u32) {
            let mut buf = [0u8; 4];
            store_le32(word, &mut buf);
            prop_assert_eq!(load_le32(&buf), word);
        }

        /// LE64 round-trip: store then load recovers original
        #[test]
        fn le64_roundtrip(word: u64) {
            let mut buf = [0u8; 8];
            store_le64(word, &mut buf);
            prop_assert_eq!(load_le64(&buf), word);
        }

        /// try_load_le32 returns Some iff slice has >= 4 bytes
        #[test]
        fn try_load_le32_totality(bytes in prop::collection::vec(any::<u8>(), 0..10)) {
            let result = try_load_le32(&bytes);
            if bytes.len() >= 4 {
                prop_assert!(result.is_some());
                prop_assert_eq!(result.unwrap(), load_le32(&bytes));
            } else {
                prop_assert!(result.is_none());
            }
        }

        /// try_load_le64 returns Some iff slice has >= 8 bytes
        #[test]
        fn try_load_le64_totality(bytes in prop::collection::vec(any::<u8>(), 0..16)) {
            let result = try_load_le64(&bytes);
            if bytes.len() >= 8 {
                prop_assert!(result.is_some());
                prop_assert_eq!(result.unwrap(), load_le64(&bytes));
            } else {
                prop_assert!(result.is_none());
            }
        }

        /// Rotation left then right is identity
        #[test]
        fn rotation_inverse(word: u64, n in 0u32..64) {
            let rotated = rotl64(word, n);
            let back = rotr64(rotated, n);
            prop_assert_eq!(back, word);
        }

        /// Rotation right then left is identity
        #[test]
        fn rotation_inverse_reverse(word: u64, n in 0u32..64) {
            let rotated = rotr64(word, n);
            let back = rotl64(rotated, n);
            prop_assert_eq!(back, word);
        }

        /// XOR is self-inverse
        #[test]
        fn xor_self_inverse(data in prop::collection::vec(any::<u8>(), 1..100)) {
            let mut buf = data.clone();
            xor_bytes(&data, &mut buf);
            // XOR with self should produce zeros
            prop_assert!(buf.iter().all(|&b| b == 0));
        }

        /// XOR twice is identity
        #[test]
        fn xor_double_identity(
            data in prop::collection::vec(any::<u8>(), 1..100),
            mask in prop::collection::vec(any::<u8>(), 1..100)
        ) {
            let len = data.len().min(mask.len());
            let mut buf = data[..len].to_vec();
            let mask = &mask[..len];

            xor_bytes(mask, &mut buf);
            xor_bytes(mask, &mut buf);

            prop_assert_eq!(&buf[..], &data[..len]);
        }
    }
}

// ============================================================================
// Constant-Time Property Tests
// ============================================================================

mod ct_properties {
    use super::*;
    use anubis_core::ct::*;

    proptest! {
        /// ct_eq is reflexive
        #[test]
        fn ct_eq_reflexive(data in prop::collection::vec(any::<u8>(), 0..100)) {
            prop_assert!(ct_eq(&data, &data));
        }

        /// ct_eq is symmetric
        #[test]
        fn ct_eq_symmetric(
            a in prop::collection::vec(any::<u8>(), 0..50),
            b in prop::collection::vec(any::<u8>(), 0..50)
        ) {
            prop_assert_eq!(ct_eq(&a, &b), ct_eq(&b, &a));
        }

        /// ct_select (u8) with true returns first argument
        #[test]
        fn ct_select_true(a: u8, b: u8) {
            prop_assert_eq!(ct_select(true, a, b), a);
        }

        /// ct_select (u8) with false returns second argument
        #[test]
        fn ct_select_false(a: u8, b: u8) {
            prop_assert_eq!(ct_select(false, a, b), b);
        }

        /// ct_select_u64 with true returns first argument
        #[test]
        fn ct_select_u64_true(a: u64, b: u64) {
            prop_assert_eq!(ct_select_u64(true, a, b), a);
        }

        /// ct_select_u64 with false returns second argument
        #[test]
        fn ct_select_u64_false(a: u64, b: u64) {
            prop_assert_eq!(ct_select_u64(false, a, b), b);
        }

        /// ct_lt_u64 matches standard comparison
        #[test]
        fn ct_lt_matches_std(a: u64, b: u64) {
            let ct_result = ct_lt_u64(a, b);
            let std_result = if a < b { 1u64 } else { 0u64 };
            prop_assert_eq!(ct_result, std_result);
        }

        /// ct_cmov with false preserves original
        #[test]
        fn ct_cmov_false_preserves(
            src in prop::array::uniform32(any::<u8>()),
            original in prop::array::uniform32(any::<u8>())
        ) {
            let mut dst = original;
            ct_cmov(false, &src, &mut dst);
            prop_assert_eq!(dst, original);
        }

        /// ct_cmov with true updates value
        #[test]
        fn ct_cmov_true_updates(
            src in prop::array::uniform32(any::<u8>()),
            original in prop::array::uniform32(any::<u8>())
        ) {
            let mut dst = original;
            ct_cmov(true, &src, &mut dst);
            prop_assert_eq!(dst, src);
        }
    }
}

// ============================================================================
// Keccak/SHA3/SHAKE Property Tests
// ============================================================================

mod keccak_properties {
    use super::*;
    use anubis_core::keccak::sha3::sha3_256;
    use anubis_core::keccak::shake::Shake256;

    proptest! {
        /// SHA3-256 always produces 32 bytes
        #[test]
        fn sha3_output_length(data in prop::collection::vec(any::<u8>(), 0..1000)) {
            let hash = sha3_256(&data);
            prop_assert_eq!(hash.len(), 32);
        }

        /// SHA3-256 is deterministic
        #[test]
        fn sha3_deterministic(data in prop::collection::vec(any::<u8>(), 0..500)) {
            let hash1 = sha3_256(&data);
            let hash2 = sha3_256(&data);
            prop_assert_eq!(hash1, hash2);
        }

        /// SHAKE256 streaming equals one-shot
        #[test]
        fn shake256_streaming_equivalence(data in prop::collection::vec(any::<u8>(), 0..500)) {
            let oneshot: [u8; 32] = anubis_core::keccak::shake::shake256(&data);

            let mut hasher = Shake256::new();
            hasher.absorb(&data);
            let streaming: [u8; 32] = hasher.squeeze_fixed();

            prop_assert_eq!(oneshot, streaming);
        }

        /// SHAKE256 split streaming equals one-shot
        #[test]
        fn shake256_split_streaming(
            data in prop::collection::vec(any::<u8>(), 0..500),
            split_point in 0usize..500
        ) {
            let split = split_point.min(data.len());

            let oneshot: [u8; 32] = anubis_core::keccak::shake::shake256(&data);

            let mut hasher = Shake256::new();
            hasher.absorb(&data[..split]);
            hasher.absorb(&data[split..]);
            let streaming: [u8; 32] = hasher.squeeze_fixed();

            prop_assert_eq!(oneshot, streaming);
        }

        /// SHAKE256 is deterministic
        #[test]
        fn shake_deterministic(
            data in prop::collection::vec(any::<u8>(), 0..200),
            output_len in 1usize..=1024  // Full range up to MAX_SQUEEZE_LEN
        ) {
            let mut shake1 = Shake256::new();
            shake1.absorb(&data);
            let mut out1 = vec![0u8; output_len];
            shake1.squeeze(&mut out1);

            let mut shake2 = Shake256::new();
            shake2.absorb(&data);
            let mut out2 = vec![0u8; output_len];
            shake2.squeeze(&mut out2);

            prop_assert_eq!(out1, out2);
        }

        /// SHAKE256 prefix consistency: shorter output is prefix of longer
        #[test]
        fn shake_prefix_consistency(
            data in prop::collection::vec(any::<u8>(), 0..100),
            short_len in 1usize..512,
            extra_len in 1usize..513
        ) {
            // Ensure both lengths are within MAX_SQUEEZE_LEN (1024)
            let short_len = short_len.min(1024);
            let long_len = (short_len + extra_len).min(1024);

            let mut shake1 = Shake256::new();
            shake1.absorb(&data);
            let mut short_out = vec![0u8; short_len];
            shake1.squeeze(&mut short_out);

            let mut shake2 = Shake256::new();
            shake2.absorb(&data);
            let mut long_out = vec![0u8; long_len];
            shake2.squeeze(&mut long_out);

            prop_assert_eq!(&short_out[..], &long_out[..short_len]);
        }
    }
}

// ============================================================================
// KDF Property Tests
// ============================================================================

mod kdf_properties {
    use super::*;
    use anubis_core::kdf::HkdfShake256;

    proptest! {
        /// HKDF is deterministic
        #[test]
        fn hkdf_deterministic(
            salt in prop::collection::vec(any::<u8>(), 0..64),
            ikm in prop::collection::vec(any::<u8>(), 1..128),
            info in prop::collection::vec(any::<u8>(), 0..64)
        ) {
            let out1: [u8; 32] = HkdfShake256::derive(&salt, &ikm, &info).unwrap();
            let out2: [u8; 32] = HkdfShake256::derive(&salt, &ikm, &info).unwrap();
            prop_assert_eq!(out1, out2);
        }

        /// Different info produces different outputs
        #[test]
        fn hkdf_info_separation(
            salt in prop::collection::vec(any::<u8>(), 16..32),
            ikm in prop::collection::vec(any::<u8>(), 32..64)
        ) {
            let out1: [u8; 32] = HkdfShake256::derive(&salt, &ikm, b"info1").unwrap();
            let out2: [u8; 32] = HkdfShake256::derive(&salt, &ikm, b"info2").unwrap();
            prop_assert_ne!(out1, out2);
        }

        /// Different IKM produces different outputs
        #[test]
        fn hkdf_ikm_separation(
            salt in prop::collection::vec(any::<u8>(), 16..32)
        ) {
            let ikm1 = [1u8; 32];
            let ikm2 = [2u8; 32];
            let out1: [u8; 32] = HkdfShake256::derive(&salt, &ikm1, b"test").unwrap();
            let out2: [u8; 32] = HkdfShake256::derive(&salt, &ikm2, b"test").unwrap();
            prop_assert_ne!(out1, out2);
        }
    }
}

// ============================================================================
// Nonce Derivation Property Tests
// ============================================================================

mod nonce_properties {
    use super::*;
    use anubis_core::nonce::{NonceDeriver, MAX_COUNTER};

    proptest! {
        /// Nonce derivation is deterministic
        #[test]
        fn nonce_deterministic(
            key in prop::array::uniform32(any::<u8>()),
            counter in 0u64..MAX_COUNTER,
            entry_id: u32,
            domain: u8
        ) {
            let deriver = NonceDeriver::new(key);
            let nonce1 = deriver.derive(counter, entry_id, domain).unwrap();
            let nonce2 = deriver.derive(counter, entry_id, domain).unwrap();
            prop_assert_eq!(nonce1, nonce2);
        }

        /// Different counters produce different nonces
        #[test]
        fn nonce_counter_separation(
            key in prop::array::uniform32(any::<u8>()),
            counter1 in 0u64..(MAX_COUNTER - 1),
            entry_id: u32,
            domain: u8
        ) {
            let counter2 = counter1 + 1;
            let deriver = NonceDeriver::new(key);
            let nonce1 = deriver.derive(counter1, entry_id, domain).unwrap();
            let nonce2 = deriver.derive(counter2, entry_id, domain).unwrap();
            prop_assert_ne!(nonce1, nonce2);
        }

        /// Different entry IDs produce different nonces
        #[test]
        fn nonce_entry_separation(
            key in prop::array::uniform32(any::<u8>()),
            counter in 0u64..MAX_COUNTER,
            entry_id1: u32,
            domain: u8
        ) {
            let entry_id2 = entry_id1.wrapping_add(1);
            if entry_id1 != entry_id2 {
                let deriver = NonceDeriver::new(key);
                let nonce1 = deriver.derive(counter, entry_id1, domain).unwrap();
                let nonce2 = deriver.derive(counter, entry_id2, domain).unwrap();
                prop_assert_ne!(nonce1, nonce2);
            }
        }

        /// Counter overflow is rejected
        #[test]
        fn nonce_overflow_rejected(
            key in prop::array::uniform32(any::<u8>()),
            entry_id: u32,
            domain: u8
        ) {
            let deriver = NonceDeriver::new(key);
            let result = deriver.derive(MAX_COUNTER, entry_id, domain);
            prop_assert!(result.is_err());
        }
    }
}

// ============================================================================
// AEAD Property Tests
// ============================================================================

mod aead_properties {
    use super::*;
    use anubis_core::aead::{ChaCha20Poly1305, TAG_SIZE};

    proptest! {
        /// Encrypt-decrypt round-trip
        #[test]
        fn aead_roundtrip(
            key in prop::array::uniform32(any::<u8>()),
            nonce in prop::array::uniform12(any::<u8>()),
            plaintext in prop::collection::vec(any::<u8>(), 0..256),
            aad in prop::collection::vec(any::<u8>(), 0..64)
        ) {
            let aead = ChaCha20Poly1305::new(&key).unwrap();

            let mut ciphertext = vec![0u8; plaintext.len() + TAG_SIZE];
            let ct_len = aead.seal(&nonce, &aad, &plaintext, &mut ciphertext).unwrap();

            let mut decrypted = vec![0u8; plaintext.len()];
            let pt_len = aead.open(&nonce, &aad, &ciphertext[..ct_len], &mut decrypted).unwrap();

            prop_assert_eq!(pt_len, plaintext.len());
            prop_assert_eq!(&decrypted[..pt_len], &plaintext[..]);
        }

        /// Tampered ciphertext is rejected
        #[test]
        fn aead_tamper_detection(
            key in prop::array::uniform32(any::<u8>()),
            nonce in prop::array::uniform12(any::<u8>()),
            plaintext in prop::collection::vec(any::<u8>(), 1..128),
            aad in prop::collection::vec(any::<u8>(), 0..32),
            tamper_pos in any::<usize>()
        ) {
            let aead = ChaCha20Poly1305::new(&key).unwrap();

            let mut ciphertext = vec![0u8; plaintext.len() + TAG_SIZE];
            let ct_len = aead.seal(&nonce, &aad, &plaintext, &mut ciphertext).unwrap();

            // Tamper with ciphertext
            let pos = tamper_pos % ct_len;
            ciphertext[pos] ^= 0xFF;

            let mut decrypted = vec![0u8; plaintext.len()];
            let result = aead.open(&nonce, &aad, &ciphertext[..ct_len], &mut decrypted);

            prop_assert!(result.is_err());
        }

        /// Wrong AAD is rejected
        #[test]
        fn aead_wrong_aad_rejected(
            key in prop::array::uniform32(any::<u8>()),
            nonce in prop::array::uniform12(any::<u8>()),
            plaintext in prop::collection::vec(any::<u8>(), 0..128),
            aad1 in prop::collection::vec(any::<u8>(), 1..32)
        ) {
            let aead = ChaCha20Poly1305::new(&key).unwrap();

            let mut ciphertext = vec![0u8; plaintext.len() + TAG_SIZE];
            let ct_len = aead.seal(&nonce, &aad1, &plaintext, &mut ciphertext).unwrap();

            // Use different AAD for decryption
            let aad2 = vec![0u8; aad1.len()];
            if aad1 != aad2 {
                let mut decrypted = vec![0u8; plaintext.len()];
                let result = aead.open(&nonce, &aad2, &ciphertext[..ct_len], &mut decrypted);
                prop_assert!(result.is_err());
            }
        }
    }
}

// ============================================================================
// CBOR Property Tests
// ============================================================================

mod cbor_properties {
    use super::*;
    use anubis_core::cbor::{Encoder, Decoder};

    proptest! {
        /// Unsigned integer round-trip
        #[test]
        fn cbor_uint_roundtrip(value: u64) {
            let mut buf = [0u8; 16];
            let mut encoder = Encoder::new(&mut buf);
            encoder.encode_uint(value).unwrap();
            let bytes = encoder.as_bytes();

            let mut decoder = Decoder::new(bytes);
            let decoded = decoder.decode_uint();

            prop_assert!(decoded.is_ok());
            prop_assert_eq!(decoded.unwrap(), value);
        }

        /// Signed integer round-trip
        #[test]
        fn cbor_int_roundtrip(value: i64) {
            let mut buf = [0u8; 16];
            let mut encoder = Encoder::new(&mut buf);
            encoder.encode_int(value).unwrap();
            let len = encoder.position();

            let mut decoder = Decoder::new(&buf[..len]);
            let decoded = decoder.decode_int();

            prop_assert!(decoded.is_ok());
            prop_assert_eq!(decoded.unwrap(), value);
        }

        /// Byte string round-trip
        #[test]
        fn cbor_bytes_roundtrip(data in prop::collection::vec(any::<u8>(), 0..200)) {
            let mut buf = vec![0u8; data.len() + 16];
            let mut encoder = Encoder::new(&mut buf);
            encoder.encode_bytes(&data).unwrap();
            let len = encoder.position();

            let mut decoder = Decoder::new(&buf[..len]);
            let decoded = decoder.decode_bytes();

            prop_assert!(decoded.is_ok());
            prop_assert_eq!(decoded.unwrap(), &data[..]);
        }

        /// Text string round-trip
        #[test]
        fn cbor_text_roundtrip(text in "[a-zA-Z0-9 ]{0,100}") {
            let mut buf = vec![0u8; text.len() + 16];
            let mut encoder = Encoder::new(&mut buf);
            encoder.encode_text(&text).unwrap();
            let len = encoder.position();

            let mut decoder = Decoder::new(&buf[..len]);
            let decoded = decoder.decode_text();

            prop_assert!(decoded.is_ok());
            prop_assert_eq!(decoded.unwrap(), &text[..]);
        }

        /// Boolean round-trip
        #[test]
        fn cbor_bool_roundtrip(value: bool) {
            let mut buf = [0u8; 4];
            let mut encoder = Encoder::new(&mut buf);
            encoder.encode_bool(value).unwrap();
            let len = encoder.position();

            let mut decoder = Decoder::new(&buf[..len]);
            let decoded = decoder.decode_bool();

            prop_assert!(decoded.is_ok());
            prop_assert_eq!(decoded.unwrap(), value);
        }
    }
}

// ============================================================================
// Merkle Tree Property Tests
// ============================================================================

mod merkle_properties {
    use super::*;
    use anubis_core::merkle::MerkleTree;

    proptest! {
        /// Merkle tree is deterministic
        #[test]
        fn merkle_deterministic(
            leaves in prop::collection::vec(
                prop::array::uniform32(any::<u8>()),
                1..16
            )
        ) {
            let mut tree1 = MerkleTree::new();
            let mut tree2 = MerkleTree::new();

            for leaf in &leaves {
                tree1.add_leaf(leaf).unwrap();
                tree2.add_leaf(leaf).unwrap();
            }

            let root1 = tree1.compute_root().unwrap();
            let root2 = tree2.compute_root().unwrap();
            prop_assert_eq!(root1, root2);
        }

        /// Proof verification succeeds for valid leaves
        #[test]
        fn merkle_proof_valid(
            leaves in prop::collection::vec(
                prop::array::uniform32(any::<u8>()),
                1..16
            ),
            index in any::<usize>()
        ) {
            let mut tree = MerkleTree::new();
            for leaf in &leaves {
                tree.add_leaf(leaf).unwrap();
            }
            let root = tree.compute_root().unwrap();

            let idx = index % leaves.len();
            let proof = tree.generate_proof(idx).unwrap();
            let verified = proof.verify(&leaves[idx], &root);
            prop_assert!(verified);
        }

        /// Different leaves produce different roots
        #[test]
        fn merkle_collision_resistance(
            leaves1 in prop::collection::vec(
                prop::array::uniform32(any::<u8>()),
                2..8
            ),
            leaves2 in prop::collection::vec(
                prop::array::uniform32(any::<u8>()),
                2..8
            )
        ) {
            if leaves1 != leaves2 {
                let mut tree1 = MerkleTree::new();
                let mut tree2 = MerkleTree::new();

                for leaf in &leaves1 {
                    tree1.add_leaf(leaf).unwrap();
                }
                for leaf in &leaves2 {
                    tree2.add_leaf(leaf).unwrap();
                }

                let root1 = tree1.compute_root().unwrap();
                let root2 = tree2.compute_root().unwrap();
                // Very high probability of different roots for different inputs
                // (only fails if SHA3 collision found)
                prop_assert_ne!(root1, root2);
            }
        }
    }
}
