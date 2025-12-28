//! Integration tests for Anubis Notary.
//!
//! These tests verify end-to-end workflows:
//! - Key generation and storage
//! - Sign → verify workflow
//! - License issuance and verification
//! - Receipt creation and checking

use tempfile::TempDir;

use anubis_core::mldsa::KeyPair;
use anubis_core::keccak::sha3::sha3_256;
use anubis_io::keystore::Keystore;

/// Test the complete sign → verify workflow.
///
/// This test:
/// 1. Creates a new keystore with password protection
/// 2. Generates an ML-DSA-87 keypair
/// 3. Signs a test message
/// 4. Verifies the signature
/// 5. Verifies that tampering with message or signature fails
#[test]
fn test_sign_verify_workflow() {
    // Create temporary keystore
    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let keystore_path = temp_dir.path().join("keystore");

    // Initialize keystore
    let keystore = Keystore::open(&keystore_path).expect("Failed to open keystore");

    // Generate keypair using random seed from OS CSPRNG
    let keypair = KeyPair::generate().expect("Failed to generate keypair");

    // Seal and store the key
    let password = b"test-password-integration-1234";
    let secret_key = keypair.secret_key().to_bytes();
    keystore.seal_and_store_key(password, &secret_key)
        .expect("Failed to seal and store key");

    // Store public key
    keystore.write_public_key(&keypair.public_key().to_bytes())
        .expect("Failed to write public key");

    // Verify key was stored
    assert!(keystore.has_key(), "Key should exist after storage");

    // Unseal the key
    let unsealed = keystore.unseal_stored_key(password)
        .expect("Failed to unseal key");
    assert_eq!(unsealed.as_slice(), &secret_key[..], "Unsealed key should match original");

    // Prepare message for signing
    let message = b"This is a test message for signing verification.";
    let message_hash = sha3_256(message);

    // Sign the message
    let signature = keypair.sign(&message_hash)
        .expect("Failed to sign message");

    // Verify the signature
    assert!(
        keypair.public_key().verify(&message_hash, &signature),
        "Signature should verify successfully"
    );

    // Verify with wrong message fails
    let wrong_message = b"This is a TAMPERED message.";
    let wrong_hash = sha3_256(wrong_message);
    assert!(
        !keypair.public_key().verify(&wrong_hash, &signature),
        "Signature should NOT verify with wrong message"
    );

    // Verify with wrong signature fails
    let wrong_msg_hash = sha3_256(b"different");
    let wrong_signature = keypair.sign(&wrong_msg_hash)
        .expect("Failed to sign");
    assert!(
        !keypair.public_key().verify(&message_hash, &wrong_signature),
        "Wrong signature should NOT verify"
    );

    // Verify password verification works
    assert!(
        keystore.verify_password(password).expect("verify_password failed"),
        "Correct password should verify"
    );
    assert!(
        !keystore.verify_password(b"wrong-password").expect("verify_password failed"),
        "Wrong password should not verify"
    );

    println!("sign → verify workflow: PASSED");
}

/// Test low-memory mode sealing.
#[test]
fn test_low_memory_seal_workflow() {
    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let keystore_path = temp_dir.path().join("keystore_low_mem");

    let keystore = Keystore::open(&keystore_path).expect("Failed to open keystore");

    // Generate keypair
    let keypair = KeyPair::generate().expect("Failed to generate keypair");

    // Seal with low-memory mode
    let password = b"low-memory-test-password";
    let secret_key = keypair.secret_key().to_bytes();
    keystore.seal_and_store_key_low_memory(password, &secret_key)
        .expect("Failed to seal with low memory mode");

    // Unseal should work
    let unsealed = keystore.unseal_stored_key(password)
        .expect("Failed to unseal low-memory sealed key");
    assert_eq!(unsealed.as_slice(), &secret_key[..], "Low-memory unsealed key should match");

    println!("low-memory seal workflow: PASSED");
}

/// Test key rotation workflow.
#[test]
fn test_key_rotation_workflow() {
    use anubis_core::mldsa::PublicKey;
    use anubis_io::{SystemClock, TimeSource};

    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let keystore_path = temp_dir.path().join("keystore_rotation");

    let keystore = Keystore::open(&keystore_path).expect("Failed to open keystore");

    // Generate initial keypair
    let keypair1 = KeyPair::generate().expect("Failed to generate keypair");

    let password = b"rotation-test-password";
    keystore.seal_and_store_key(password, &keypair1.secret_key().to_bytes())
        .expect("Failed to store initial key");
    keystore.write_public_key(&keypair1.public_key().to_bytes())
        .expect("Failed to write initial public key");

    // Archive the current key
    let clock = SystemClock;
    let timestamp = clock.now();
    let archive_id = keystore.archive_current_key(timestamp)
        .expect("Failed to archive key");

    // Generate new keypair
    let keypair2 = KeyPair::generate().expect("Failed to generate new keypair");

    // Store new key
    keystore.seal_and_store_key(password, &keypair2.secret_key().to_bytes())
        .expect("Failed to store new key");
    keystore.write_public_key(&keypair2.public_key().to_bytes())
        .expect("Failed to write new public key");

    // Verify old key is archived
    let archived_ids = keystore.list_archived_keys()
        .expect("Failed to list archived keys");
    assert!(archived_ids.contains(&archive_id), "Archived key should be listed");

    // Verify we can read archived public key
    let archived_pubkey = keystore.read_archived_public_key(&archive_id)
        .expect("Failed to read archived public key");
    assert_eq!(archived_pubkey.as_slice(), &keypair1.public_key().to_bytes()[..],
        "Archived public key should match original");

    // Verify current key is the new one
    let current_pubkey = keystore.read_public_key()
        .expect("Failed to read current public key");
    assert_eq!(current_pubkey.as_slice(), &keypair2.public_key().to_bytes()[..],
        "Current public key should be the new one");

    // Verify signatures from old key still verify with archived key
    let message = sha3_256(b"test message");
    let old_signature = keypair1.sign(&message)
        .expect("Failed to sign with old key");

    let archived_pk = PublicKey::from_bytes(&archived_pubkey)
        .expect("Failed to parse archived public key");
    assert!(
        archived_pk.verify(&message, &old_signature),
        "Old signature should verify with archived key"
    );

    println!("key rotation workflow: PASSED");
}

/// Test license creation and verification.
#[test]
fn test_license_workflow() {
    use anubis_core::license::License;

    // Create a license
    let mut license = License::new(
        "user@example.com",
        "anubis-pro",
        i64::MAX, // Far future expiration
    ).expect("Failed to create license");

    // Add features
    license.add_feature("offline-mode").expect("Failed to add feature");
    license.add_feature("team-sync").expect("Failed to add feature");

    // Verify features
    assert!(license.has_feature("offline-mode"), "Should have offline-mode");
    assert!(license.has_feature("team-sync"), "Should have team-sync");
    assert!(!license.has_feature("enterprise"), "Should not have enterprise");

    // Generate signature for encoding
    let keypair = KeyPair::generate().expect("Failed to generate keypair");
    let mut signable_buf = [0u8; 4096];
    let signable_len = license.encode_signable(&mut signable_buf)
        .expect("Failed to encode signable");
    let sig = keypair.sign(&sha3_256(&signable_buf[..signable_len]))
        .expect("Failed to sign");
    license.set_signature(&sig.to_bytes()).expect("Failed to set signature");

    // Encode and decode
    let mut buffer = [0u8; 8192];
    let encoded_len = license.encode(&mut buffer).expect("Failed to encode");
    assert!(encoded_len > 0, "Encoded license should have non-zero length");

    // Decode the license
    let decoded = License::decode(&buffer[..encoded_len]).expect("Failed to decode");
    assert_eq!(decoded.subject(), "user@example.com");
    assert_eq!(decoded.product(), "anubis-pro");
    assert!(decoded.has_feature("offline-mode"));
    assert!(decoded.has_feature("team-sync"));

    // Test expiration checking
    assert!(!license.is_expired(1_000_000_000), "License should not be expired");

    println!("license workflow: PASSED");
}

/// Test Merkle tree attestation workflow.
#[test]
fn test_merkle_attestation_workflow() {
    use anubis_core::merkle::MerkleTree;

    // Create test data
    let items = vec![
        [0x01u8; 32],
        [0x02u8; 32],
        [0x03u8; 32],
        [0x04u8; 32],
    ];

    // Build Merkle tree
    let mut tree = MerkleTree::new();
    for item in &items {
        tree.add_leaf(item).expect("Failed to add leaf");
    }
    let root = tree.compute_root().expect("Failed to compute root");

    // Generate and verify proofs for each leaf
    for (i, item) in items.iter().enumerate() {
        let proof = tree.generate_proof(i).expect("Failed to generate proof");
        assert!(
            proof.verify(item, &root),
            "Proof should verify for leaf {}", i
        );
    }

    // Verify wrong leaf fails
    let wrong_leaf = [0xFFu8; 32];
    let proof = tree.generate_proof(0).expect("Failed to generate proof");
    assert!(
        !proof.verify(&wrong_leaf, &root),
        "Proof should NOT verify for wrong leaf"
    );

    println!("Merkle attestation workflow: PASSED");
}

/// Test receipt encoding and decoding.
#[test]
fn test_receipt_workflow() {
    use anubis_core::receipt::Receipt;

    let content_hash = sha3_256(b"test file content");
    let timestamp = 1735689600i64; // 2025-01-01

    // Create receipt
    let receipt = Receipt::new(content_hash, timestamp);

    // Encode signable portion (use larger buffer for signature)
    let mut buffer = [0u8; 8192];
    let signable_len = receipt.encode_signable(&mut buffer)
        .expect("Failed to encode signable");

    // Generate keypair and sign
    let keypair = KeyPair::generate().expect("Failed to generate keypair");
    let signable_hash = sha3_256(&buffer[..signable_len]);
    let signature = keypair.sign(&signable_hash)
        .expect("Failed to sign");

    // Create signed receipt
    let signed_receipt = receipt.with_signature(&signature.to_bytes())
        .expect("Failed to set signature");

    // Encode full receipt
    let full_len = signed_receipt.encode(&mut buffer)
        .expect("Failed to encode full receipt");

    assert!(full_len > signable_len, "Full receipt should be larger than signable");

    println!("receipt workflow: PASSED");
}

/// Test atomic file writes.
#[test]
fn test_atomic_write_workflow() {
    use anubis_io::{read_file, write_file_atomic};

    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let file_path = temp_dir.path().join("test_file.bin");

    // Write data atomically
    let data = b"Test data for atomic write verification";
    write_file_atomic(&file_path, data).expect("Failed to write atomically");

    // Read back and verify
    let read_data = read_file(&file_path).expect("Failed to read file");
    assert_eq!(read_data, data, "Read data should match written data");

    // Overwrite atomically
    let new_data = b"Updated data after overwrite";
    write_file_atomic(&file_path, new_data).expect("Failed to overwrite");

    let read_new = read_file(&file_path).expect("Failed to read updated file");
    assert_eq!(read_new, new_data, "Read data should match updated data");

    println!("atomic write workflow: PASSED");
}

/// Test deterministic signing (same seed produces same key).
#[test]
fn test_deterministic_keygen() {
    use anubis_core::mldsa::SEED_SIZE;

    // Generate from fixed seed
    let seed = [0xABu8; SEED_SIZE];
    let keypair1 = KeyPair::from_seed(&seed).expect("Failed from seed 1");
    let keypair2 = KeyPair::from_seed(&seed).expect("Failed from seed 2");

    // Same seed produces same public key
    assert_eq!(
        keypair1.public_key().to_bytes(),
        keypair2.public_key().to_bytes(),
        "Same seed should produce same public key"
    );

    // Different seed produces different key
    let other_seed = [0xCDu8; SEED_SIZE];
    let keypair3 = KeyPair::from_seed(&other_seed).expect("Failed from other seed");
    assert_ne!(
        keypair1.public_key().to_bytes(),
        keypair3.public_key().to_bytes(),
        "Different seeds should produce different keys"
    );

    println!("deterministic keygen: PASSED");
}

/// Test complete attest → check workflow.
///
/// This test simulates the full attestation workflow:
/// 1. Create a file with known content
/// 2. Hash the content (SHA3-256)
/// 3. Create a receipt with the hash and timestamp
/// 4. Sign the receipt with ML-DSA-87
/// 5. Encode the signed receipt
/// 6. Decode the receipt
/// 7. Verify the signature matches the content hash
#[test]
fn test_attest_check_workflow() {
    use anubis_core::receipt::Receipt;

    // Simulate file content
    let file_content = b"This is the content of a file we're attesting to.";
    let content_hash = sha3_256(file_content);

    // Create timestamp (e.g., 2025-01-01 00:00:00 UTC)
    let timestamp = 1735689600i64;

    // Create unsigned receipt
    let receipt = Receipt::new(content_hash, timestamp);

    // Generate keypair for signing
    let keypair = KeyPair::generate().expect("Failed to generate keypair");

    // Encode signable portion and sign
    let mut signable_buf = [0u8; 1024];
    let signable_len = receipt.encode_signable(&mut signable_buf)
        .expect("Failed to encode signable");
    let signable_hash = sha3_256(&signable_buf[..signable_len]);
    let signature = keypair.sign(&signable_hash)
        .expect("Failed to sign receipt");

    // Create signed receipt
    let signed_receipt = receipt.with_signature(&signature.to_bytes())
        .expect("Failed to set signature");

    // Encode the full receipt (this is what gets saved to .receipt file)
    let mut receipt_buf = [0u8; 8192];
    let receipt_len = signed_receipt.encode(&mut receipt_buf)
        .expect("Failed to encode receipt");

    // === CHECK PHASE ===
    // Decode the receipt (as if loading from file)
    let decoded = Receipt::decode(&receipt_buf[..receipt_len])
        .expect("Failed to decode receipt");

    // Verify the digest matches the original content
    assert_eq!(
        decoded.digest, content_hash,
        "Decoded digest should match original content hash"
    );

    // Verify the timestamp
    assert_eq!(decoded.created, timestamp, "Timestamp should match");

    // Re-encode the signable portion to verify signature
    let mut check_buf = [0u8; 1024];
    let mut check_receipt = Receipt::new(decoded.digest, decoded.created);
    check_receipt = check_receipt.with_time_source(decoded.time_source.clone());
    check_receipt = check_receipt.with_anchor(decoded.anchor.clone());
    let check_len = check_receipt.encode_signable(&mut check_buf)
        .expect("Failed to encode signable for verification");
    let check_hash = sha3_256(&check_buf[..check_len]);

    // Reconstruct signature from decoded receipt
    let decoded_sig = anubis_core::mldsa::Signature::from_bytes(
        &decoded.signature[..decoded.sig_len]
    ).expect("Failed to parse signature");

    // Verify signature
    assert!(
        keypair.public_key().verify(&check_hash, &decoded_sig),
        "Signature should verify against original content"
    );

    // Verify tampering detection - different content should fail
    let tampered_content = b"This content has been modified!";
    let tampered_hash = sha3_256(tampered_content);
    assert_ne!(
        tampered_hash, decoded.digest,
        "Tampered content should have different hash"
    );

    // Verify tampering detection - modified receipt should fail verification
    let tampered_receipt = Receipt::new(tampered_hash, decoded.created);
    let mut tampered_buf = [0u8; 1024];
    let tampered_len = tampered_receipt.encode_signable(&mut tampered_buf)
        .expect("Failed to encode tampered signable");
    let tampered_check_hash = sha3_256(&tampered_buf[..tampered_len]);
    assert!(
        !keypair.public_key().verify(&tampered_check_hash, &decoded_sig),
        "Signature should NOT verify with tampered content"
    );

    println!("attest → check workflow: PASSED");
}

/// Test license expiration validation.
///
/// This test verifies:
/// 1. Non-expired licenses pass validation
/// 2. Expired licenses fail validation
/// 3. Edge cases around expiration time
#[test]
fn test_license_expiration_workflow() {
    use anubis_core::license::License;

    // Current time: 2025-06-15 12:00:00 UTC
    let current_time = 1750075200i64;

    // Create license that expires in the future (2025-12-31)
    let future_exp = 1767225600i64;
    let valid_license = License::new(
        "user@example.com",
        "anubis-pro",
        future_exp,
    ).expect("Failed to create valid license");

    // Should NOT be expired
    assert!(
        !valid_license.is_expired(current_time),
        "License with future expiration should not be expired"
    );

    // Create license that expired in the past (2024-12-31)
    let past_exp = 1735689599i64;
    let expired_license = License::new(
        "user@example.com",
        "anubis-pro",
        past_exp,
    ).expect("Failed to create expired license");

    // Should be expired
    assert!(
        expired_license.is_expired(current_time),
        "License with past expiration should be expired"
    );

    // Edge case: license expires exactly NOW
    let edge_license = License::new(
        "user@example.com",
        "anubis-pro",
        current_time,
    ).expect("Failed to create edge case license");

    // At exact expiration time, license is still valid (now > exp is false)
    assert!(
        !edge_license.is_expired(current_time),
        "License at exact expiration time should still be valid"
    );

    // One second after expiration should be expired
    assert!(
        edge_license.is_expired(current_time + 1),
        "License one second after expiration should be expired"
    );

    // One second before expiration should still be valid
    assert!(
        !edge_license.is_expired(current_time - 1),
        "License one second before expiration should be valid"
    );

    println!("license expiration workflow: PASSED");
}

/// Test complete license creation → signing → verification workflow.
///
/// This simulates the full license lifecycle:
/// 1. Create license with features
/// 2. Sign with issuer key
/// 3. Encode to CBOR
/// 4. Decode and verify signature
/// 5. Check features
#[test]
fn test_license_signature_verification_workflow() {
    use anubis_core::license::License;

    // Create license with multiple features
    let mut license = License::new(
        "enterprise@corp.com",
        "anubis-enterprise",
        i64::MAX,
    ).expect("Failed to create license");

    license.add_feature("offline-mode").expect("add feature");
    license.add_feature("team-sync").expect("add feature");
    license.add_feature("audit-log").expect("add feature");
    license.add_feature("api-access").expect("add feature");

    // Generate issuer keypair
    let issuer_keypair = KeyPair::generate().expect("Failed to generate issuer keypair");

    // Sign the license
    let mut signable_buf = [0u8; 4096];
    let signable_len = license.encode_signable(&mut signable_buf)
        .expect("Failed to encode signable");
    let signable_hash = sha3_256(&signable_buf[..signable_len]);
    let signature = issuer_keypair.sign(&signable_hash)
        .expect("Failed to sign license");
    license.set_signature(&signature.to_bytes())
        .expect("Failed to set signature");

    // Encode the full license (what gets distributed to user)
    let mut license_buf = [0u8; 8192];
    let license_len = license.encode(&mut license_buf)
        .expect("Failed to encode license");

    // === VERIFICATION PHASE ===
    // Decode the license (as if loading from file)
    let decoded = License::decode(&license_buf[..license_len])
        .expect("Failed to decode license");

    // Verify all features are present
    assert!(decoded.has_feature("offline-mode"), "Should have offline-mode");
    assert!(decoded.has_feature("team-sync"), "Should have team-sync");
    assert!(decoded.has_feature("audit-log"), "Should have audit-log");
    assert!(decoded.has_feature("api-access"), "Should have api-access");
    assert!(!decoded.has_feature("admin-panel"), "Should NOT have admin-panel");

    // Re-encode signable portion to verify signature
    let mut verify_buf = [0u8; 4096];
    let verify_len = decoded.encode_signable(&mut verify_buf)
        .expect("Failed to encode for verification");
    let verify_hash = sha3_256(&verify_buf[..verify_len]);

    // Get signature bytes from decoded license
    let sig_bytes = decoded.signature();
    let decoded_sig = anubis_core::mldsa::Signature::from_bytes(sig_bytes)
        .expect("Failed to parse decoded signature");

    // Verify with issuer's public key
    assert!(
        issuer_keypair.public_key().verify(&verify_hash, &decoded_sig),
        "License signature should verify with issuer public key"
    );

    // Verify with wrong key fails
    let other_keypair = KeyPair::generate().expect("Failed to generate other keypair");
    assert!(
        !other_keypair.public_key().verify(&verify_hash, &decoded_sig),
        "License signature should NOT verify with different key"
    );

    println!("license signature verification workflow: PASSED");
}

/// Test receipt round-trip with all fields.
#[test]
fn test_receipt_complete_roundtrip() {
    use anubis_core::receipt::Receipt;

    let digest = sha3_256(b"test document content");
    let timestamp = 1735689600i64;

    // Create receipt with local time and no anchor (simple case)
    let receipt1 = Receipt::new(digest, timestamp);

    // Generate signature
    let keypair = KeyPair::generate().expect("keygen");
    let mut sig_buf = [0u8; 1024];
    let sig_len = receipt1.encode_signable(&mut sig_buf).expect("encode");
    let sig = keypair.sign(&sha3_256(&sig_buf[..sig_len])).expect("sign");
    let receipt1 = receipt1.with_signature(&sig.to_bytes()).expect("set sig");

    // Encode and decode
    let mut buf = [0u8; 8192];
    let len = receipt1.encode(&mut buf).expect("encode");
    let decoded = Receipt::decode(&buf[..len]).expect("decode");

    assert_eq!(decoded.digest, digest);
    assert_eq!(decoded.created, timestamp);
    assert_eq!(decoded.sig_len, sig.to_bytes().len());

    println!("receipt complete roundtrip: PASSED");
}
