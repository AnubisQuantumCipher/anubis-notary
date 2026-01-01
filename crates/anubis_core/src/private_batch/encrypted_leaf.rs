//! Encrypted leaf for private batch anchoring.
//!
//! Each leaf in a private batch is encrypted with a session key before
//! being included in the Merkle tree, hiding the plaintext content.

use crate::aead::{ChaCha20Poly1305, KEY_SIZE, NONCE_SIZE, TAG_SIZE};
use crate::ct::ct_eq;
use crate::keccak::sha3::sha3_256;
use zeroize::Zeroize;

use super::error::PrivateBatchError;

/// Maximum leaf data size (1 MiB for receipts with embedded data).
pub const MAX_LEAF_SIZE: usize = 1024 * 1024;

/// An encrypted leaf in a private batch.
///
/// Structure:
/// - `ciphertext`: AEAD-encrypted original leaf data (includes 16-byte tag)
/// - `commitment`: SHA3-256(plaintext) for verification after decryption
/// - `nonce`: 12-byte unique nonce used for encryption
/// - `index`: Position in the batch (0-based)
///
/// # Security
///
/// - Uses ChaCha20Poly1305 for authenticated encryption
/// - Nonce is deterministically derived from batch_id || index (unique per leaf)
/// - Commitment allows verification that decryption produced correct plaintext
#[derive(Clone)]
pub struct EncryptedLeaf {
    /// AEAD ciphertext (plaintext + 16-byte tag).
    pub ciphertext: Vec<u8>,
    /// SHA3-256 commitment to the plaintext (for verification).
    pub commitment: [u8; 32],
    /// Nonce used for encryption (derived from batch_id || index).
    pub nonce: [u8; NONCE_SIZE],
    /// Index in the batch (0-based).
    pub index: u32,
}

impl EncryptedLeaf {
    /// Encrypt a leaf using the session key.
    ///
    /// # Arguments
    ///
    /// * `session_key` - 32-byte symmetric key for encryption
    /// * `leaf_data` - Plaintext data to encrypt
    /// * `batch_id` - Unique batch identifier (for nonce derivation)
    /// * `index` - Leaf position in batch (for nonce derivation)
    ///
    /// # Security
    ///
    /// - Uses fresh nonce derived from `SHA3-256(batch_id || index)[0..12]`
    /// - Commitment binds plaintext without revealing it
    /// - Each leaf in a batch uses a unique nonce (guaranteed by index)
    pub fn encrypt(
        session_key: &[u8; KEY_SIZE],
        leaf_data: &[u8],
        batch_id: &[u8; 32],
        index: u32,
    ) -> Result<Self, PrivateBatchError> {
        if leaf_data.len() > MAX_LEAF_SIZE {
            return Err(PrivateBatchError::InvalidLeafCount);
        }

        // Derive unique nonce: SHA3-256(batch_id || index)[0..12]
        let nonce = derive_nonce(batch_id, index);

        // Compute commitment before encryption
        let commitment = sha3_256(leaf_data);

        // Encrypt with AEAD
        let cipher = ChaCha20Poly1305::from_key(session_key);
        let ciphertext = cipher.seal_fixed(&nonce, &[], leaf_data);

        Ok(Self {
            ciphertext,
            commitment,
            nonce,
            index,
        })
    }

    /// Decrypt and verify the leaf.
    ///
    /// # Arguments
    ///
    /// * `session_key` - 32-byte symmetric key for decryption
    ///
    /// # Returns
    ///
    /// The decrypted plaintext if successful.
    ///
    /// # Errors
    ///
    /// - `DecryptionFailed`: AEAD authentication failed
    /// - `CommitmentMismatch`: Decrypted data doesn't match commitment
    pub fn decrypt(&self, session_key: &[u8; KEY_SIZE]) -> Result<Vec<u8>, PrivateBatchError> {
        let cipher = ChaCha20Poly1305::from_key(session_key);
        let plaintext = cipher
            .open_fixed(&self.nonce, &[], &self.ciphertext)
            .map_err(|_| PrivateBatchError::DecryptionFailed)?;

        // Verify commitment using constant-time comparison
        let computed_commitment = sha3_256(&plaintext);
        if !ct_eq(&computed_commitment, &self.commitment) {
            return Err(PrivateBatchError::CommitmentMismatch);
        }

        Ok(plaintext)
    }

    /// Get the hash used for Merkle tree inclusion.
    ///
    /// The Merkle hash is computed over `commitment || ciphertext` to bind
    /// both the plaintext (via commitment) and the encrypted form.
    ///
    /// # Security
    ///
    /// Including the commitment ensures that:
    /// 1. The Merkle root commits to the plaintext content
    /// 2. Different plaintexts produce different Merkle hashes
    /// 3. Verification can confirm the right plaintext was decrypted
    pub fn merkle_hash(&self) -> [u8; 32] {
        // Hash: SHA3-256(commitment || ciphertext)
        let mut input = Vec::with_capacity(32 + self.ciphertext.len());
        input.extend_from_slice(&self.commitment);
        input.extend_from_slice(&self.ciphertext);
        sha3_256(&input)
    }

    /// Get the plaintext size (ciphertext length minus tag).
    #[inline]
    pub fn plaintext_size(&self) -> usize {
        self.ciphertext.len().saturating_sub(TAG_SIZE)
    }

    /// Serialize to bytes for storage.
    ///
    /// Format: `[index:4][nonce:12][commitment:32][ciphertext_len:4][ciphertext:N]`
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut result = Vec::with_capacity(4 + NONCE_SIZE + 32 + 4 + self.ciphertext.len());
        result.extend_from_slice(&self.index.to_le_bytes());
        result.extend_from_slice(&self.nonce);
        result.extend_from_slice(&self.commitment);
        result.extend_from_slice(&(self.ciphertext.len() as u32).to_le_bytes());
        result.extend_from_slice(&self.ciphertext);
        result
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, PrivateBatchError> {
        // Minimum size: 4 + 12 + 32 + 4 + 16 (empty plaintext with tag)
        if bytes.len() < 68 {
            return Err(PrivateBatchError::CborError("leaf too short".to_string()));
        }

        let index = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
        let nonce: [u8; NONCE_SIZE] = bytes[4..16].try_into().unwrap();
        let commitment: [u8; 32] = bytes[16..48].try_into().unwrap();
        let ct_len = u32::from_le_bytes(bytes[48..52].try_into().unwrap()) as usize;

        if bytes.len() != 52 + ct_len {
            return Err(PrivateBatchError::CborError("leaf length mismatch".to_string()));
        }

        let ciphertext = bytes[52..].to_vec();

        Ok(Self {
            ciphertext,
            commitment,
            nonce,
            index,
        })
    }
}

impl Drop for EncryptedLeaf {
    fn drop(&mut self) {
        // Ciphertext doesn't need zeroization (not secret)
        // but commitment could reveal plaintext hash
        self.commitment.zeroize();
    }
}

/// Derive a unique nonce from batch_id and leaf index.
///
/// Uses `SHA3-256(batch_id || index)[0..12]` to ensure:
/// - Unique nonce per leaf within a batch
/// - Deterministic (reproducible for verification)
/// - No nonce reuse across different batches (batch_id is random)
#[inline]
fn derive_nonce(batch_id: &[u8; 32], index: u32) -> [u8; NONCE_SIZE] {
    let mut input = [0u8; 36];
    input[..32].copy_from_slice(batch_id);
    input[32..36].copy_from_slice(&index.to_le_bytes());
    let hash = sha3_256(&input);
    let mut nonce = [0u8; NONCE_SIZE];
    nonce.copy_from_slice(&hash[..NONCE_SIZE]);
    nonce
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encrypt_decrypt_roundtrip() {
        let session_key = [0x42u8; 32];
        let plaintext = b"test receipt data for encryption";
        let batch_id = [0xABu8; 32];

        let encrypted = EncryptedLeaf::encrypt(&session_key, plaintext, &batch_id, 0).unwrap();
        let decrypted = encrypted.decrypt(&session_key).unwrap();

        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn test_different_indices_different_nonces() {
        let batch_id = [0xABu8; 32];

        let nonce0 = derive_nonce(&batch_id, 0);
        let nonce1 = derive_nonce(&batch_id, 1);
        let nonce2 = derive_nonce(&batch_id, 2);

        assert_ne!(nonce0, nonce1);
        assert_ne!(nonce1, nonce2);
        assert_ne!(nonce0, nonce2);
    }

    #[test]
    fn test_different_batches_different_nonces() {
        let batch1 = [0xAAu8; 32];
        let batch2 = [0xBBu8; 32];

        let nonce1 = derive_nonce(&batch1, 0);
        let nonce2 = derive_nonce(&batch2, 0);

        assert_ne!(nonce1, nonce2);
    }

    #[test]
    fn test_wrong_key_decryption_fails() {
        let session_key = [0x42u8; 32];
        let wrong_key = [0x43u8; 32];
        let plaintext = b"secret data";
        let batch_id = [0xABu8; 32];

        let encrypted = EncryptedLeaf::encrypt(&session_key, plaintext, &batch_id, 0).unwrap();
        let result = encrypted.decrypt(&wrong_key);

        assert!(matches!(result, Err(PrivateBatchError::DecryptionFailed)));
    }

    #[test]
    fn test_merkle_hash_deterministic() {
        let session_key = [0x42u8; 32];
        let plaintext = b"test data";
        let batch_id = [0xABu8; 32];

        let leaf1 = EncryptedLeaf::encrypt(&session_key, plaintext, &batch_id, 0).unwrap();
        let leaf2 = EncryptedLeaf::encrypt(&session_key, plaintext, &batch_id, 0).unwrap();

        // Same inputs should produce same merkle hash
        assert_eq!(leaf1.merkle_hash(), leaf2.merkle_hash());
    }

    #[test]
    fn test_serialization_roundtrip() {
        let session_key = [0x42u8; 32];
        let plaintext = b"serialization test";
        let batch_id = [0xABu8; 32];

        let original = EncryptedLeaf::encrypt(&session_key, plaintext, &batch_id, 5).unwrap();
        let bytes = original.to_bytes();
        let parsed = EncryptedLeaf::from_bytes(&bytes).unwrap();

        assert_eq!(parsed.index, original.index);
        assert_eq!(parsed.nonce, original.nonce);
        assert_eq!(parsed.commitment, original.commitment);
        assert_eq!(parsed.ciphertext, original.ciphertext);

        // Verify decryption still works
        let decrypted = parsed.decrypt(&session_key).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn test_empty_plaintext() {
        let session_key = [0x42u8; 32];
        let plaintext = b"";
        let batch_id = [0xABu8; 32];

        let encrypted = EncryptedLeaf::encrypt(&session_key, plaintext, &batch_id, 0).unwrap();
        assert_eq!(encrypted.plaintext_size(), 0);

        let decrypted = encrypted.decrypt(&session_key).unwrap();
        assert_eq!(decrypted, plaintext);
    }
}
