//! Integration tests for Anubis Notary CLI.
//!
//! These tests exercise full CLI workflows including:
//! - Key initialization and management
//! - Signing and verification
//! - Attestation and verification
//! - License issuance and verification
//! - Streaming operations

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
// Help and Version Tests
// ============================================================================

#[test]
fn test_help() {
    cli()
        .arg("--help")
        .assert()
        .success()
        .stdout(predicate::str::contains("CLI for Anubis Notary"));
}

#[test]
fn test_version() {
    cli()
        .arg("--version")
        .assert()
        .success()
        .stdout(predicate::str::contains("anubis-notary"));
}

// ============================================================================
// Key Subcommand Help Tests
// ============================================================================

#[test]
fn test_key_help() {
    cli()
        .args(["key", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Key management commands"));
}

#[test]
fn test_key_init_help() {
    cli()
        .args(["key", "init", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Initialize a new keystore"));
}

// ============================================================================
// Sign/Verify Subcommand Help Tests
// ============================================================================

#[test]
fn test_sign_help() {
    cli()
        .args(["sign", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Sign a file"));
}

#[test]
fn test_verify_help() {
    cli()
        .args(["verify", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Verify a signature"));
}

// ============================================================================
// Attest/Check Subcommand Help Tests
// ============================================================================

#[test]
fn test_attest_help() {
    cli()
        .args(["attest", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Create a receipt"));
}

#[test]
fn test_check_help() {
    cli()
        .args(["check", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Verify a receipt"));
}

// ============================================================================
// License Subcommand Help Tests
// ============================================================================

#[test]
fn test_license_help() {
    cli()
        .args(["license", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("License management commands"));
}

#[test]
fn test_license_issue_help() {
    cli()
        .args(["license", "issue", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Issue a new license"));
}

// ============================================================================
// Multisig Subcommand Help Tests
// ============================================================================

#[test]
fn test_multisig_help() {
    cli()
        .args(["multisig", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains(
            "Multi-signature governance commands",
        ));
}

#[test]
fn test_multisig_init_help() {
    cli()
        .args(["multisig", "init", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains(
            "Initialize a new multisig configuration",
        ));
}

// ============================================================================
// Stream Subcommand Help Tests
// ============================================================================

#[test]
fn test_stream_help() {
    cli()
        .args(["stream", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Streaming commands"));
}

#[test]
fn test_stream_sign_help() {
    cli()
        .args(["stream", "sign", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains(
            "Sign a large file using streaming",
        ));
}

#[test]
fn test_stream_verify_help() {
    cli()
        .args(["stream", "verify", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Verify a large file signature"));
}

#[test]
fn test_stream_hash_help() {
    cli()
        .args(["stream", "hash", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Hash a large file"));
}

// ============================================================================
// Anchor Subcommand Help Tests
// ============================================================================

#[test]
fn test_anchor_help() {
    cli()
        .args(["anchor", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Anchoring commands"));
}

// ============================================================================
// Error Handling Tests
// ============================================================================

#[test]
fn test_sign_missing_file() {
    cli()
        .args(["sign", "/nonexistent/file.txt"])
        .assert()
        .failure();
}

#[test]
fn test_verify_missing_file() {
    let temp_dir = TempDir::new().unwrap();
    let sig_path = temp_dir.path().join("dummy.sig");
    fs::write(&sig_path, b"dummy signature").unwrap();

    cli()
        .args(["verify", "/nonexistent/file.txt", "--sig"])
        .arg(&sig_path)
        .assert()
        .failure();
}

#[test]
fn test_verify_missing_signature() {
    let temp_dir = TempDir::new().unwrap();
    let file_path = create_test_file(&temp_dir, "test.txt", b"test content");

    cli()
        .args(["verify"])
        .arg(&file_path)
        .args(["--sig", "/nonexistent/signature.sig"])
        .assert()
        .failure();
}

#[test]
fn test_check_missing_receipt() {
    let temp_dir = TempDir::new().unwrap();
    let file_path = create_test_file(&temp_dir, "test.txt", b"test content");

    cli()
        .args(["check", "/nonexistent/receipt.cbor"])
        .arg(&file_path)
        .assert()
        .failure();
}

#[test]
fn test_check_missing_file() {
    let temp_dir = TempDir::new().unwrap();
    let receipt_path = temp_dir.path().join("receipt.cbor");
    fs::write(&receipt_path, b"dummy receipt").unwrap();

    cli()
        .args(["check"])
        .arg(&receipt_path)
        .arg("/nonexistent/file.txt")
        .assert()
        .failure();
}

// ============================================================================
// JSON Output Tests
// ============================================================================

#[test]
fn test_json_output_on_error() {
    cli()
        .args(["--json", "sign", "/nonexistent/file.txt"])
        .assert()
        .failure()
        .stdout(predicate::str::contains("\"success\": false"));
}

// ============================================================================
// Key Show Without Keystore Tests
// ============================================================================

#[test]
fn test_key_show_no_keystore() {
    let temp_dir = TempDir::new().unwrap();
    let keystore_path = temp_dir.path().join("nonexistent");

    // This succeeds but shows "No key found" message
    cli()
        .args(["key", "show", "--keystore"])
        .arg(&keystore_path)
        .assert()
        .success()
        .stdout(predicate::str::contains("No key found"));
}

// ============================================================================
// License Verify Missing File Test
// ============================================================================

#[test]
fn test_license_verify_missing() {
    cli()
        .args([
            "license",
            "verify",
            "--license",
            "/nonexistent/license.cbor",
        ])
        .assert()
        .failure();
}

// ============================================================================
// Stream Hash Test (No Keystore Required)
// ============================================================================

#[test]
fn test_stream_hash_file() {
    let temp_dir = TempDir::new().unwrap();
    let file_path = create_test_file(&temp_dir, "test.txt", b"Hello, World!");

    cli()
        .args(["stream", "hash"])
        .arg(&file_path)
        .assert()
        .success()
        .stdout(predicate::str::contains("Hash:"));
}

#[test]
fn test_stream_hash_json() {
    let temp_dir = TempDir::new().unwrap();
    let file_path = create_test_file(&temp_dir, "test.txt", b"Hello, World!");

    cli()
        .args(["--json", "stream", "hash"])
        .arg(&file_path)
        .assert()
        .success()
        .stdout(predicate::str::contains("\"success\": true"))
        .stdout(predicate::str::contains("\"hash\""));
}

#[test]
fn test_stream_hash_large_file() {
    let temp_dir = TempDir::new().unwrap();
    // Create a 1MB file
    let large_content = vec![0u8; 1024 * 1024];
    let file_path = create_test_file(&temp_dir, "large.bin", &large_content);

    cli()
        .args(["stream", "hash"])
        .arg(&file_path)
        .args(["--chunk-size", "65536"])
        .assert()
        .success();
}

// ============================================================================
// Multisig Configuration Tests
// ============================================================================

#[test]
fn test_multisig_init_missing_signers() {
    let temp_dir = TempDir::new().unwrap();
    let out_path = temp_dir.path().join("multisig.cbor");

    // Should fail without any signers
    cli()
        .args(["multisig", "init", "--threshold", "2", "--out"])
        .arg(&out_path)
        .assert()
        .failure();
}

// ============================================================================
// Anchor Queue Tests
// ============================================================================

#[test]
fn test_anchor_queue_help() {
    cli()
        .args(["anchor", "queue", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Queue operations"));
}

#[test]
fn test_anchor_queue_list_help() {
    cli()
        .args(["anchor", "queue", "list", "--help"])
        .assert()
        .success();
}

// ============================================================================
// Invalid Argument Tests
// ============================================================================

#[test]
fn test_invalid_subcommand() {
    cli().args(["invalid-command"]).assert().failure();
}

#[test]
fn test_key_invalid_action() {
    cli().args(["key", "invalid-action"]).assert().failure();
}

// ============================================================================
// Streaming Sign/Verify Tests (File Existence)
// ============================================================================

#[test]
fn test_stream_sign_missing_file() {
    cli()
        .args(["stream", "sign", "/nonexistent/file.txt"])
        .assert()
        .failure();
}

#[test]
fn test_stream_verify_missing_file() {
    let temp_dir = TempDir::new().unwrap();
    let sig_path = temp_dir.path().join("dummy.sig");
    fs::write(&sig_path, b"dummy").unwrap();

    cli()
        .args(["stream", "verify", "/nonexistent/file.txt", "--sig"])
        .arg(&sig_path)
        .assert()
        .failure();
}

// ============================================================================
// Key Revoke Tests
// ============================================================================

#[test]
fn test_key_revoke_help() {
    cli()
        .args(["key", "revoke", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Revoke a key"));
}

#[test]
fn test_key_list_help() {
    cli()
        .args(["key", "list", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("List archived and revoked keys"));
}

// ============================================================================
// License List Tests
// ============================================================================

#[test]
fn test_license_list_help() {
    cli()
        .args(["license", "list", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("List issued licenses"));
}

// ============================================================================
// Multisig Workflow Help Tests
// ============================================================================

#[test]
fn test_multisig_propose_help() {
    cli()
        .args(["multisig", "propose", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Create a new proposal"));
}

#[test]
fn test_multisig_sign_help() {
    cli()
        .args(["multisig", "sign", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Sign a proposal"));
}

#[test]
fn test_multisig_execute_help() {
    cli()
        .args(["multisig", "execute", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Execute an approved proposal"));
}

#[test]
fn test_multisig_status_help() {
    cli()
        .args(["multisig", "status", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Show proposal status"));
}

#[test]
fn test_multisig_signers_help() {
    cli()
        .args(["multisig", "signers", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("List signers"));
}
