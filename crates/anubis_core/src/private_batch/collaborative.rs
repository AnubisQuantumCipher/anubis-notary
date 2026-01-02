//! Collaborative decryption coordinator.
//!
//! Manages the collection of decrypted shares from multiple recipients
//! and reconstructs the session key when threshold is reached.

use crate::aead::KEY_SIZE;
use crate::recovery::{RecoveryCoordinator, Share};
use zeroize::{Zeroize, Zeroizing};

use super::batch::PrivateBatch;
use super::encrypted_leaf::EncryptedLeaf;
use super::error::PrivateBatchError;
use super::key_envelope::KeyShareEnvelope;

/// Coordinator for collaborative batch decryption.
///
/// Collects decrypted shares from multiple recipients until
/// the threshold is reached, then reconstructs the session key.
///
/// # Workflow
///
/// 1. Create coordinator from key envelope
/// 2. Each recipient decrypts their share (using their ML-KEM secret key)
/// 3. Add decrypted shares to coordinator
/// 4. When threshold reached, recover session key
/// 5. Decrypt all leaves in the batch
///
/// # Security
///
/// - Shares are zeroized when coordinator is dropped
/// - Session key is zeroized after batch decryption
/// - Information-theoretic security: t-1 shares reveal nothing
pub struct CollaborativeDecryptor {
    /// Batch ID being decrypted.
    batch_id: [u8; 32],
    /// Required threshold.
    threshold: u8,
    /// Recovery coordinator for Shamir reconstruction.
    coordinator: RecoveryCoordinator,
}

impl CollaborativeDecryptor {
    /// Create a new decryptor from a key envelope.
    pub fn new(envelope: &KeyShareEnvelope) -> Self {
        Self {
            batch_id: envelope.batch_id,
            threshold: envelope.threshold,
            coordinator: RecoveryCoordinator::new(envelope.threshold),
        }
    }

    /// Create from a private batch.
    pub fn from_batch(batch: &PrivateBatch) -> Self {
        Self::new(&batch.key_envelope)
    }

    /// Get the batch ID being decrypted.
    #[inline]
    pub fn batch_id(&self) -> &[u8; 32] {
        &self.batch_id
    }

    /// Get the required threshold.
    #[inline]
    pub fn threshold(&self) -> u8 {
        self.threshold
    }

    /// Add a decrypted share.
    ///
    /// # Returns
    ///
    /// `Ok(true)` when threshold is reached and recovery is possible.
    /// `Ok(false)` when more shares are still needed.
    pub fn add_share(&mut self, share: Share) -> Result<bool, PrivateBatchError> {
        self.coordinator.add_share(share)?;
        Ok(self.coordinator.can_recover())
    }

    /// Get number of shares collected so far.
    #[inline]
    pub fn shares_collected(&self) -> usize {
        self.coordinator.shares_collected()
    }

    /// Get the number of shares still needed.
    #[inline]
    pub fn shares_needed(&self) -> usize {
        self.coordinator.shares_needed()
    }

    /// Check if we have enough shares to recover.
    #[inline]
    pub fn can_recover(&self) -> bool {
        self.coordinator.can_recover()
    }

    /// Reconstruct the session key when threshold is reached.
    ///
    /// # Errors
    ///
    /// - `InsufficientShares`: Not enough shares collected
    /// - `InvalidSessionKey`: Recovered data is not 32 bytes
    pub fn recover_session_key(&self) -> Result<[u8; KEY_SIZE], PrivateBatchError> {
        if !self.coordinator.can_recover() {
            return Err(PrivateBatchError::InsufficientShares);
        }

        let mut recovered = self.coordinator.recover()?;

        if recovered.len() != KEY_SIZE {
            recovered.zeroize();
            return Err(PrivateBatchError::InvalidSessionKey);
        }

        let mut key = [0u8; KEY_SIZE];
        key.copy_from_slice(&recovered);
        // Zeroize intermediate buffer containing session key
        recovered.zeroize();
        Ok(key)
    }

    /// Decrypt all leaves in a batch using the recovered session key.
    ///
    /// # Arguments
    ///
    /// * `leaves` - Encrypted leaves from the batch
    ///
    /// # Returns
    ///
    /// Vector of decrypted plaintext data.
    ///
    /// # Errors
    ///
    /// - `InsufficientShares`: Not enough shares collected
    /// - `DecryptionFailed`: AEAD authentication failure
    /// - `CommitmentMismatch`: Decrypted data doesn't match commitment
    ///
    /// # Security
    ///
    /// Returns `Vec<Zeroizing<Vec<u8>>>` to ensure all decrypted plaintexts
    /// are automatically zeroized when dropped.
    pub fn decrypt_batch(
        &self,
        leaves: &[EncryptedLeaf],
    ) -> Result<Vec<Zeroizing<Vec<u8>>>, PrivateBatchError> {
        let mut session_key = self.recover_session_key()?;

        let mut plaintext_leaves = Vec::with_capacity(leaves.len());
        for leaf in leaves {
            let plaintext = leaf.decrypt(&session_key)?;
            plaintext_leaves.push(plaintext);
        }

        // Zeroize session key after use
        session_key.zeroize();

        Ok(plaintext_leaves)
    }

    /// Decrypt a private batch completely.
    ///
    /// Convenience method that takes the full batch and returns decrypted leaves.
    ///
    /// # Security
    ///
    /// Returns `Vec<Zeroizing<Vec<u8>>>` for automatic plaintext zeroization.
    pub fn decrypt_private_batch(
        &self,
        batch: &PrivateBatch,
    ) -> Result<Vec<Zeroizing<Vec<u8>>>, PrivateBatchError> {
        // Verify batch ID matches
        if batch.batch_id != self.batch_id {
            return Err(PrivateBatchError::BatchIdMismatch);
        }

        self.decrypt_batch(&batch.leaves)
    }

    /// Clear all collected shares.
    pub fn clear(&mut self) {
        self.coordinator.clear();
    }
}

impl Drop for CollaborativeDecryptor {
    fn drop(&mut self) {
        self.coordinator.clear();
    }
}

/// Represents a decrypted share ready for transmission.
///
/// This is used when a recipient decrypts their share and wants to
/// send it to the coordinator without exposing the raw Share type.
#[derive(Clone)]
pub struct DecryptedShare {
    /// The Shamir share data.
    pub share: Share,
    /// Recipient index in the envelope.
    pub recipient_index: u8,
    /// Batch ID this share belongs to.
    pub batch_id: [u8; 32],
}

impl DecryptedShare {
    /// Create a new decrypted share.
    pub fn new(share: Share, recipient_index: u8, batch_id: [u8; 32]) -> Self {
        Self {
            share,
            recipient_index,
            batch_id,
        }
    }

    /// Serialize to bytes for transmission.
    pub fn to_bytes(&self) -> Vec<u8> {
        let share_bytes = self.share.to_bytes();
        let mut result = Vec::with_capacity(33 + share_bytes.len());
        result.extend_from_slice(&self.batch_id);
        result.push(self.recipient_index);
        result.extend_from_slice(&share_bytes);
        result
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, PrivateBatchError> {
        if bytes.len() < 34 {
            return Err(PrivateBatchError::CborError(
                "decrypted share too short".to_string(),
            ));
        }

        let batch_id: [u8; 32] = bytes[0..32].try_into().unwrap();
        let recipient_index = bytes[32];
        let share = Share::from_bytes(&bytes[33..])?;

        Ok(Self {
            share,
            recipient_index,
            batch_id,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mlkem::{MlKemKeyPair, MlKemPublicKey};

    #[test]
    fn test_collaborative_decryption() {
        let plaintext1 = b"first receipt";
        let plaintext2 = b"second receipt";
        let leaves = [plaintext1.as_ref(), plaintext2.as_ref()];

        // Create batch with 2-of-3 threshold
        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();
        let kp3 = MlKemKeyPair::generate().unwrap();

        let pks = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp3.public_key_bytes()).unwrap(),
        ];

        let batch = PrivateBatch::create(&leaves, &pks, 2).unwrap();

        // Create coordinator
        let mut decryptor = CollaborativeDecryptor::from_batch(&batch);
        assert!(!decryptor.can_recover());
        assert_eq!(decryptor.shares_needed(), 2);

        // Recipient 1 decrypts their share
        let (sk1, _) = kp1.into_parts();
        let share1 = batch.key_envelope.decrypt_share(0, &sk1).unwrap();
        assert!(!decryptor.add_share(share1).unwrap());
        assert_eq!(decryptor.shares_collected(), 1);

        // Recipient 3 decrypts their share (skip recipient 2)
        let (sk3, _) = kp3.into_parts();
        let share3 = batch.key_envelope.decrypt_share(2, &sk3).unwrap();
        assert!(decryptor.add_share(share3).unwrap());
        assert!(decryptor.can_recover());

        // Decrypt batch
        let decrypted = decryptor.decrypt_private_batch(&batch).unwrap();
        assert_eq!(&*decrypted[0], plaintext1);
        assert_eq!(&*decrypted[1], plaintext2);
    }

    #[test]
    fn test_insufficient_shares() {
        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();

        let pks = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
        ];

        let batch = PrivateBatch::create(&[b"data".as_ref()], &pks, 2).unwrap();

        // Only add one share
        let mut decryptor = CollaborativeDecryptor::from_batch(&batch);
        let (sk1, _) = kp1.into_parts();
        let share1 = batch.key_envelope.decrypt_share(0, &sk1).unwrap();
        decryptor.add_share(share1).unwrap();

        // Should fail with insufficient shares
        let result = decryptor.recover_session_key();
        assert!(matches!(result, Err(PrivateBatchError::InsufficientShares)));
    }

    #[test]
    fn test_batch_id_mismatch() {
        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();

        let pks = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
        ];

        let batch1 = PrivateBatch::create(&[b"data1".as_ref()], &pks.clone(), 2).unwrap();
        let batch2 = PrivateBatch::create(&[b"data2".as_ref()], &pks, 2).unwrap();

        // Create decryptor for batch1
        let mut decryptor = CollaborativeDecryptor::from_batch(&batch1);

        // Get shares from batch1
        let (sk1, _) = kp1.into_parts();
        let (sk2, _) = kp2.into_parts();
        let share1 = batch1.key_envelope.decrypt_share(0, &sk1).unwrap();
        let share2 = batch1.key_envelope.decrypt_share(1, &sk2).unwrap();

        decryptor.add_share(share1).unwrap();
        decryptor.add_share(share2).unwrap();

        // Try to decrypt batch2 with batch1's decryptor
        let result = decryptor.decrypt_private_batch(&batch2);
        assert!(matches!(result, Err(PrivateBatchError::BatchIdMismatch)));
    }

    #[test]
    fn test_decrypted_share_serialization() {
        let kp = MlKemKeyPair::generate().unwrap();
        let pk = MlKemPublicKey::from_bytes(kp.public_key_bytes()).unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();
        let pk2 = MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap();

        let batch = PrivateBatch::create(&[b"test".as_ref()], &[pk, pk2], 2).unwrap();

        let (sk, _) = kp.into_parts();
        let share = batch.key_envelope.decrypt_share(0, &sk).unwrap();

        let decrypted = DecryptedShare::new(share, 0, batch.batch_id);
        let bytes = decrypted.to_bytes();
        let parsed = DecryptedShare::from_bytes(&bytes).unwrap();

        assert_eq!(parsed.batch_id, decrypted.batch_id);
        assert_eq!(parsed.recipient_index, decrypted.recipient_index);
    }
}
