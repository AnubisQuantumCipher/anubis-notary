//! Private batch for privacy-preserving collaborative anchoring.
//!
//! Combines encrypted leaves with ML-KEM key distribution for forward-secure,
//! threshold-decryption batch anchoring.

use crate::aead::KEY_SIZE;
use crate::merkle::{MerkleProof, MerkleTree};
use crate::mlkem::MlKemPublicKey;
use zeroize::Zeroize;

use super::encrypted_leaf::EncryptedLeaf;
use super::error::PrivateBatchError;
use super::key_envelope::KeyShareEnvelope;

/// Maximum leaves per private batch (same as Merkle tree limit).
pub const MAX_PRIVATE_BATCH_LEAVES: usize = 1024;

/// A private batch containing encrypted leaves and key envelope.
///
/// The Merkle tree is built over encrypted leaf hashes, hiding
/// the plaintext content while maintaining verifiable inclusion.
///
/// # Workflow
///
/// 1. Create batch with plaintext leaves and recipient public keys
/// 2. System generates ephemeral session key
/// 3. Encrypts each leaf with session key
/// 4. Builds Merkle tree over encrypted leaf hashes
/// 5. Splits session key using Shamir (t-of-n)
/// 6. ML-KEM encapsulates each share to recipient
/// 7. Session key is zeroized
///
/// # Security Properties
///
/// - **Forward secrecy**: Ephemeral keys ensure past batches remain secure
/// - **Privacy**: Encrypted leaves hide content from anchor service
/// - **Verifiability**: Merkle proofs work over encrypted leaves
/// - **Threshold**: t-of-n recipients must collaborate to decrypt
#[derive(Clone)]
pub struct PrivateBatch {
    /// Unique batch identifier (random).
    pub batch_id: [u8; 32],
    /// Encrypted leaves.
    pub leaves: Vec<EncryptedLeaf>,
    /// Key envelope for collaborative decryption.
    pub key_envelope: KeyShareEnvelope,
    /// Merkle root of encrypted leaves.
    pub merkle_root: [u8; 32],
    /// Creation timestamp (Unix epoch seconds).
    pub created_at: u64,
    /// Whether the batch has been anchored.
    pub anchored: bool,
}

impl PrivateBatch {
    /// Create a new private batch from plaintext leaves.
    ///
    /// # Arguments
    ///
    /// * `plaintext_leaves` - Data to include in the batch
    /// * `recipients` - ML-KEM public keys of recipients
    /// * `threshold` - Minimum shares needed to decrypt (2 <= t <= n)
    ///
    /// # Security
    ///
    /// - Session key is randomly generated and zeroized after use
    /// - Each batch has a unique random ID
    /// - Forward secrecy via ephemeral ML-KEM encapsulation
    pub fn create(
        plaintext_leaves: &[&[u8]],
        recipients: &[MlKemPublicKey],
        threshold: u8,
    ) -> Result<Self, PrivateBatchError> {
        // Validate leaf count
        if plaintext_leaves.is_empty() || plaintext_leaves.len() > MAX_PRIVATE_BATCH_LEAVES {
            return Err(PrivateBatchError::InvalidLeafCount);
        }

        // Generate random batch ID and session key
        let mut batch_id = [0u8; 32];
        let mut session_key = [0u8; KEY_SIZE];
        getrandom::getrandom(&mut batch_id)?;
        getrandom::getrandom(&mut session_key)?;

        let created_at = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        // Encrypt each leaf
        let mut encrypted_leaves = Vec::with_capacity(plaintext_leaves.len());
        for (index, leaf) in plaintext_leaves.iter().enumerate() {
            let encrypted =
                EncryptedLeaf::encrypt(&session_key, leaf, &batch_id, index as u32)?;
            encrypted_leaves.push(encrypted);
        }

        // Build Merkle tree over encrypted leaf hashes
        let mut tree = MerkleTree::new();
        for leaf in &encrypted_leaves {
            let hash = leaf.merkle_hash();
            tree.add_leaf(&hash)?;
        }
        let merkle_root = tree.compute_root()?;

        // Create key envelope (splits session key using Shamir + ML-KEM)
        let key_envelope = KeyShareEnvelope::create(
            &session_key,
            batch_id,
            recipients,
            threshold,
            created_at,
        )?;

        // Zeroize session key after use
        session_key.zeroize();

        Ok(Self {
            batch_id,
            leaves: encrypted_leaves,
            key_envelope,
            merkle_root,
            created_at,
            anchored: false,
        })
    }

    /// Mark the batch as anchored.
    pub fn set_anchored(&mut self) {
        self.anchored = true;
    }

    /// Get the number of leaves in the batch.
    #[inline]
    pub fn len(&self) -> usize {
        self.leaves.len()
    }

    /// Check if the batch is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.leaves.is_empty()
    }

    /// Generate Merkle proof for a specific leaf.
    ///
    /// The proof can be used to verify inclusion in the anchored root
    /// after decryption.
    pub fn generate_proof(&self, index: usize) -> Result<MerkleProof, PrivateBatchError> {
        if index >= self.leaves.len() {
            return Err(PrivateBatchError::InvalidRecipientIndex);
        }

        // Rebuild tree to generate proof
        let mut tree = MerkleTree::new();
        for leaf in &self.leaves {
            tree.add_leaf(&leaf.merkle_hash())?;
        }
        tree.compute_root()?;
        tree.generate_proof(index).map_err(PrivateBatchError::from)
    }

    /// Verify that a leaf belongs to this batch.
    ///
    /// Uses the encrypted leaf hash for verification.
    pub fn verify_leaf(&self, index: usize) -> Result<bool, PrivateBatchError> {
        if index >= self.leaves.len() {
            return Err(PrivateBatchError::InvalidRecipientIndex);
        }

        let proof = self.generate_proof(index)?;
        let leaf_hash = self.leaves[index].merkle_hash();

        // Rebuild expected root
        Ok(proof.verify(&leaf_hash, &self.merkle_root))
    }

    /// Serialize to bytes.
    ///
    /// Format:
    /// ```text
    /// [batch_id:32][merkle_root:32][created_at:8][anchored:1]
    /// [num_leaves:4][leaf_data...]
    /// [envelope_len:4][envelope_data...]
    /// ```
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut result = Vec::new();

        // Header
        result.extend_from_slice(&self.batch_id);
        result.extend_from_slice(&self.merkle_root);
        result.extend_from_slice(&self.created_at.to_le_bytes());
        result.push(if self.anchored { 1 } else { 0 });

        // Leaves
        result.extend_from_slice(&(self.leaves.len() as u32).to_le_bytes());
        for leaf in &self.leaves {
            let leaf_bytes = leaf.to_bytes();
            result.extend_from_slice(&(leaf_bytes.len() as u32).to_le_bytes());
            result.extend_from_slice(&leaf_bytes);
        }

        // Envelope
        let envelope_bytes = self.key_envelope.to_bytes();
        result.extend_from_slice(&(envelope_bytes.len() as u32).to_le_bytes());
        result.extend_from_slice(&envelope_bytes);

        result
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, PrivateBatchError> {
        // Minimum header: 32 + 32 + 8 + 1 + 4 + 4 = 81
        if bytes.len() < 81 {
            return Err(PrivateBatchError::CborError("batch too short".to_string()));
        }

        let batch_id: [u8; 32] = bytes[0..32].try_into().unwrap();
        let merkle_root: [u8; 32] = bytes[32..64].try_into().unwrap();
        let created_at = u64::from_le_bytes(bytes[64..72].try_into().unwrap());
        let anchored = bytes[72] != 0;

        let num_leaves = u32::from_le_bytes(bytes[73..77].try_into().unwrap()) as usize;

        let mut offset = 77;
        let mut leaves = Vec::with_capacity(num_leaves);

        for _ in 0..num_leaves {
            if offset + 4 > bytes.len() {
                return Err(PrivateBatchError::CborError("batch truncated".to_string()));
            }
            let leaf_len =
                u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap()) as usize;
            offset += 4;

            if offset + leaf_len > bytes.len() {
                return Err(PrivateBatchError::CborError(
                    "leaf data truncated".to_string(),
                ));
            }

            let leaf = EncryptedLeaf::from_bytes(&bytes[offset..offset + leaf_len])?;
            leaves.push(leaf);
            offset += leaf_len;
        }

        if offset + 4 > bytes.len() {
            return Err(PrivateBatchError::CborError(
                "envelope length missing".to_string(),
            ));
        }
        let envelope_len =
            u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap()) as usize;
        offset += 4;

        if offset + envelope_len > bytes.len() {
            return Err(PrivateBatchError::CborError(
                "envelope data truncated".to_string(),
            ));
        }

        let key_envelope = KeyShareEnvelope::from_bytes(&bytes[offset..offset + envelope_len])?;

        // Verify batch_id matches envelope
        if batch_id != key_envelope.batch_id {
            return Err(PrivateBatchError::BatchIdMismatch);
        }

        Ok(Self {
            batch_id,
            leaves,
            key_envelope,
            merkle_root,
            created_at,
            anchored,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mlkem::MlKemKeyPair;
    use crate::recovery::ShamirSharing;

    #[test]
    fn test_create_private_batch() {
        let leaves = [b"receipt1".as_ref(), b"receipt2", b"receipt3"];

        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();

        let pks = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
        ];

        let batch = PrivateBatch::create(&leaves, &pks, 2).unwrap();

        assert_eq!(batch.len(), 3);
        assert!(!batch.is_empty());
        assert!(!batch.anchored);
        assert_eq!(batch.key_envelope.threshold, 2);
    }

    #[test]
    fn test_merkle_proof_verification() {
        let leaves = [b"leaf1".as_ref(), b"leaf2", b"leaf3"];

        // Threshold must be >= 2, so we need 2 recipients
        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();
        let pks = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
        ];

        let batch = PrivateBatch::create(&leaves, &pks, 2).unwrap();

        // Verify each leaf
        assert!(batch.verify_leaf(0).unwrap());
        assert!(batch.verify_leaf(1).unwrap());
        assert!(batch.verify_leaf(2).unwrap());
    }

    #[test]
    fn test_serialization_roundtrip() {
        let leaves = [b"data1".as_ref(), b"data2"];

        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();

        let pks = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
        ];

        let original = PrivateBatch::create(&leaves, &pks, 2).unwrap();
        let bytes = original.to_bytes();
        let parsed = PrivateBatch::from_bytes(&bytes).unwrap();

        assert_eq!(parsed.batch_id, original.batch_id);
        assert_eq!(parsed.merkle_root, original.merkle_root);
        assert_eq!(parsed.created_at, original.created_at);
        assert_eq!(parsed.anchored, original.anchored);
        assert_eq!(parsed.leaves.len(), original.leaves.len());
    }

    #[test]
    fn test_full_collaborative_decryption() {
        let plaintext1 = b"first receipt data";
        let plaintext2 = b"second receipt data";
        let leaves = [plaintext1.as_ref(), plaintext2.as_ref()];

        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();
        let kp3 = MlKemKeyPair::generate().unwrap();

        let pks = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp3.public_key_bytes()).unwrap(),
        ];

        let batch = PrivateBatch::create(&leaves, &pks, 2).unwrap();

        // Recipients 1 and 2 decrypt their shares
        let (sk1, _) = kp1.into_parts();
        let (sk2, _) = kp2.into_parts();

        let share1 = batch.key_envelope.decrypt_share(0, &sk1).unwrap();
        let share2 = batch.key_envelope.decrypt_share(1, &sk2).unwrap();

        // Combine shares to recover session key
        let session_key_vec = ShamirSharing::combine(&[share1, share2]).unwrap();
        let session_key: [u8; KEY_SIZE] = session_key_vec.try_into().unwrap();

        // Decrypt leaves
        let decrypted1 = batch.leaves[0].decrypt(&session_key).unwrap();
        let decrypted2 = batch.leaves[1].decrypt(&session_key).unwrap();

        assert_eq!(&*decrypted1, plaintext1);
        assert_eq!(&*decrypted2, plaintext2);
    }
}
