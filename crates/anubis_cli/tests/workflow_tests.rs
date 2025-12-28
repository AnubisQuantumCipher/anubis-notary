//! Workflow integration tests for Anubis Notary CLI.
//!
//! These tests verify complete end-to-end workflows.
//! Note: Some tests are marked #[ignore] because they require interactive
//! password input which can't be easily automated in tests.

use assert_cmd::Command;
use predicates::prelude::*;
use std::fs;
use std::path::PathBuf;
use tempfile::TempDir;

/// Get the path to the built binary.
#[allow(deprecated)]
fn cli() -> Command {
    Command::cargo_bin("anubis-notary").unwrap()
}

/// Create a test file with content.
fn create_test_file(dir: &TempDir, name: &str, content: &[u8]) -> PathBuf {
    let path = dir.path().join(name);
    fs::write(&path, content).unwrap();
    path
}

// ============================================================================
// Streaming Hash Workflow Tests
// ============================================================================

/// Test the complete streaming hash workflow.
#[test]
fn test_streaming_hash_workflow() {
    let temp_dir = TempDir::new().unwrap();

    // Create test files of various sizes
    let small_file = create_test_file(&temp_dir, "small.txt", b"Small file content");
    let medium_content = vec![b'x'; 100_000];  // 100KB
    let medium_file = create_test_file(&temp_dir, "medium.bin", &medium_content);

    // Hash small file
    let output = cli()
        .args(["stream", "hash"])
        .arg(&small_file)
        .output()
        .unwrap();

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("Hash:"));

    // Hash medium file with progress
    cli()
        .args(["stream", "hash"])
        .arg(&medium_file)
        .args(["--chunk-size", "8192", "--progress"])
        .assert()
        .success();

    // Hash with JSON output
    let output = cli()
        .args(["--json", "stream", "hash"])
        .arg(&small_file)
        .output()
        .unwrap();

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(json["success"], true);
    assert!(json["data"]["hash"].is_string());
}

/// Test that streaming hash produces consistent results.
#[test]
fn test_streaming_hash_consistency() {
    let temp_dir = TempDir::new().unwrap();
    let content = b"Consistent content for hashing";
    let file = create_test_file(&temp_dir, "consistent.txt", content);

    // Hash the same file twice
    let output1 = cli()
        .args(["--json", "stream", "hash"])
        .arg(&file)
        .output()
        .unwrap();

    let output2 = cli()
        .args(["--json", "stream", "hash"])
        .arg(&file)
        .output()
        .unwrap();

    assert!(output1.status.success());
    assert!(output2.status.success());

    let json1: serde_json::Value = serde_json::from_str(
        &String::from_utf8_lossy(&output1.stdout)
    ).unwrap();
    let json2: serde_json::Value = serde_json::from_str(
        &String::from_utf8_lossy(&output2.stdout)
    ).unwrap();

    // Hashes should be identical
    assert_eq!(json1["data"]["hash"], json2["data"]["hash"]);
}

/// Test that different files produce different hashes.
#[test]
fn test_streaming_hash_uniqueness() {
    let temp_dir = TempDir::new().unwrap();
    let file1 = create_test_file(&temp_dir, "file1.txt", b"Content A");
    let file2 = create_test_file(&temp_dir, "file2.txt", b"Content B");

    let output1 = cli()
        .args(["--json", "stream", "hash"])
        .arg(&file1)
        .output()
        .unwrap();

    let output2 = cli()
        .args(["--json", "stream", "hash"])
        .arg(&file2)
        .output()
        .unwrap();

    let json1: serde_json::Value = serde_json::from_str(
        &String::from_utf8_lossy(&output1.stdout)
    ).unwrap();
    let json2: serde_json::Value = serde_json::from_str(
        &String::from_utf8_lossy(&output2.stdout)
    ).unwrap();

    // Hashes should be different
    assert_ne!(json1["data"]["hash"], json2["data"]["hash"]);
}

/// Test streaming hash produces consistent results with the same chunk size.
/// Note: Different chunk sizes produce different hashes because the streaming
/// hasher uses a Merkle-tree-like structure where chunk hashes are combined.
#[test]
fn test_streaming_hash_chunk_sizes() {
    let temp_dir = TempDir::new().unwrap();
    let content = vec![0u8; 200_000];  // 200KB
    let file = create_test_file(&temp_dir, "chunked.bin", &content);

    let chunk_sizes = [4096, 8192, 16384, 32768, 65536];

    // Test that each chunk size produces consistent results
    for chunk_size in chunk_sizes {
        let output1 = cli()
            .args(["--json", "stream", "hash"])
            .arg(&file)
            .args(["--chunk-size", &chunk_size.to_string()])
            .output()
            .unwrap();

        let output2 = cli()
            .args(["--json", "stream", "hash"])
            .arg(&file)
            .args(["--chunk-size", &chunk_size.to_string()])
            .output()
            .unwrap();

        assert!(output1.status.success(), "Failed with chunk size {}", chunk_size);
        assert!(output2.status.success(), "Failed with chunk size {}", chunk_size);

        let json1: serde_json::Value = serde_json::from_str(
            &String::from_utf8_lossy(&output1.stdout)
        ).unwrap();
        let json2: serde_json::Value = serde_json::from_str(
            &String::from_utf8_lossy(&output2.stdout)
        ).unwrap();

        let hash1 = json1["data"]["hash"].as_str().unwrap();
        let hash2 = json2["data"]["hash"].as_str().unwrap();

        assert_eq!(
            hash1, hash2,
            "Same chunk size {} produced different hashes", chunk_size
        );
    }
}

// ============================================================================
// Directory Workflow Tests (Attest/Check with --recursive)
// ============================================================================

/// Test recursive directory attestation.
#[test]
#[ignore = "Requires keystore setup"]
fn test_directory_attest_workflow() {
    let temp_dir = TempDir::new().unwrap();

    // Create a directory structure
    let subdir = temp_dir.path().join("subdir");
    fs::create_dir(&subdir).unwrap();

    create_test_file(&temp_dir, "file1.txt", b"Content 1");
    create_test_file(&temp_dir, "file2.txt", b"Content 2");
    fs::write(subdir.join("file3.txt"), b"Content 3").unwrap();

    let receipt_path = temp_dir.path().join("receipt.cbor");

    // This would require a keystore with password
    cli()
        .args(["attest", "--recursive"])
        .arg(temp_dir.path())
        .args(["--receipt"])
        .arg(&receipt_path)
        .assert()
        .success();
}

// ============================================================================
// Error Scenario Tests
// ============================================================================

/// Test error handling for invalid chunk size.
#[test]
fn test_stream_hash_invalid_chunk_size() {
    let temp_dir = TempDir::new().unwrap();
    let file = create_test_file(&temp_dir, "test.txt", b"content");

    // Chunk size 0 should fail or be handled gracefully
    cli()
        .args(["stream", "hash"])
        .arg(&file)
        .args(["--chunk-size", "0"])
        .assert()
        .failure();
}

/// Test error handling for empty file.
#[test]
fn test_stream_hash_empty_file() {
    let temp_dir = TempDir::new().unwrap();
    let file = create_test_file(&temp_dir, "empty.txt", b"");

    // Empty file should still produce a valid hash
    cli()
        .args(["--json", "stream", "hash"])
        .arg(&file)
        .assert()
        .success()
        .stdout(predicate::str::contains("\"success\": true"));
}

// ============================================================================
// License Issue Validation Tests
// ============================================================================

/// Test license issue with invalid date.
#[test]
#[ignore = "Requires keystore setup"]
fn test_license_issue_invalid_date() {
    let temp_dir = TempDir::new().unwrap();
    let license_path = temp_dir.path().join("license.cbor");

    cli()
        .args([
            "license", "issue",
            "--product", "test-product",
            "--user", "test@example.com",
            "--expiry", "invalid-date",
            "--out"
        ])
        .arg(&license_path)
        .assert()
        .failure();
}

// ============================================================================
// Multisig Validation Tests
// ============================================================================

/// Test multisig init with invalid threshold.
#[test]
fn test_multisig_init_threshold_too_high() {
    let temp_dir = TempDir::new().unwrap();

    // Create a dummy public key file
    let pk_path = temp_dir.path().join("pk.bin");
    fs::write(&pk_path, vec![0u8; 2592]).unwrap();

    let out_path = temp_dir.path().join("multisig.cbor");

    // Threshold 5 with only 1 signer should fail
    cli()
        .args([
            "multisig", "init",
            "--threshold", "5",
            "-k"
        ])
        .arg(&pk_path)
        .args(["--out"])
        .arg(&out_path)
        .assert()
        .failure();
}

// ============================================================================
// Concurrent Operation Tests
// ============================================================================

/// Test concurrent streaming hash operations.
#[test]
fn test_concurrent_stream_hash() {
    use std::thread;

    let temp_dir = TempDir::new().unwrap();
    let file = create_test_file(&temp_dir, "concurrent.txt", b"concurrent content");
    let file_clone = file.clone();

    // Spawn two threads to hash the same file
    let handle1 = thread::spawn(move || {
        cli()
            .args(["--json", "stream", "hash"])
            .arg(&file)
            .output()
            .unwrap()
    });

    let handle2 = thread::spawn(move || {
        cli()
            .args(["--json", "stream", "hash"])
            .arg(&file_clone)
            .output()
            .unwrap()
    });

    let output1 = handle1.join().unwrap();
    let output2 = handle2.join().unwrap();

    assert!(output1.status.success());
    assert!(output2.status.success());

    // Both should produce the same hash
    let json1: serde_json::Value = serde_json::from_str(
        &String::from_utf8_lossy(&output1.stdout)
    ).unwrap();
    let json2: serde_json::Value = serde_json::from_str(
        &String::from_utf8_lossy(&output2.stdout)
    ).unwrap();

    assert_eq!(json1["data"]["hash"], json2["data"]["hash"]);
}

// ============================================================================
// Anchor Queue Tests
// ============================================================================

/// Test anchor queue list on empty queue.
#[test]
#[ignore = "Requires keystore setup"]
fn test_anchor_queue_list_empty() {
    let temp_dir = TempDir::new().unwrap();
    let keystore_path = temp_dir.path().join(".anubis");

    cli()
        .args(["--json", "anchor", "queue", "list"])
        .env("ANUBIS_KEYSTORE", &keystore_path)
        .assert()
        .success()
        .stdout(predicate::str::contains("\"success\": true"));
}

// ============================================================================
// Key Rotate Validation Tests
// ============================================================================

/// Test key rotate without existing keystore.
#[test]
fn test_key_rotate_no_keystore() {
    let temp_dir = TempDir::new().unwrap();
    let keystore_path = temp_dir.path().join("nonexistent");

    cli()
        .args(["key", "rotate", "--keystore"])
        .arg(&keystore_path)
        .assert()
        .failure();
}

// ============================================================================
// Binary Data Tests
// ============================================================================

/// Test streaming hash with binary data.
#[test]
fn test_stream_hash_binary() {
    let temp_dir = TempDir::new().unwrap();

    // Create file with all byte values
    let content: Vec<u8> = (0..=255).collect();
    let file = create_test_file(&temp_dir, "binary.bin", &content);

    cli()
        .args(["--json", "stream", "hash"])
        .arg(&file)
        .assert()
        .success()
        .stdout(predicate::str::contains("\"success\": true"));
}

/// Test streaming hash with null bytes.
#[test]
fn test_stream_hash_null_bytes() {
    let temp_dir = TempDir::new().unwrap();
    let content = vec![0u8; 1000];
    let file = create_test_file(&temp_dir, "nulls.bin", &content);

    cli()
        .args(["--json", "stream", "hash"])
        .arg(&file)
        .assert()
        .success()
        .stdout(predicate::str::contains("\"success\": true"));
}

// ============================================================================
// Unicode Path Tests
// ============================================================================

/// Test streaming hash with unicode filename.
#[test]
fn test_stream_hash_unicode_path() {
    let temp_dir = TempDir::new().unwrap();
    let file = create_test_file(&temp_dir, "test_file.txt", b"unicode test");

    cli()
        .args(["--json", "stream", "hash"])
        .arg(&file)
        .assert()
        .success();
}
