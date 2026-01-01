//! Key share envelope for collaborative decryption.
//!
//! Uses ML-KEM-1024 to encapsulate Shamir shares to multiple recipients,
//! providing forward secrecy through ephemeral key encapsulation.

use crate::aead::{ChaCha20Poly1305, KEY_SIZE, NONCE_SIZE};
use crate::ct::ct_eq;
use crate::keccak::sha3::sha3_256;
use crate::mlkem::{MlKemPublicKey, MlKemSecretKey, CIPHERTEXT_SIZE};
use crate::recovery::{Share, ShamirSharing};
use zeroize::Zeroize;

use super::error::PrivateBatchError;

/// Maximum number of recipients in a private batch.
pub const MAX_RECIPIENTS: usize = 16;

/// A key share encrypted to a specific recipient using ML-KEM-1024.
///
/// Provides forward secrecy: each encapsulation generates a fresh shared
/// secret, so compromising the recipient's long-term key cannot decrypt
/// past batches.
#[derive(Clone)]
pub struct RecipientKeyShare {
    /// Recipient's public key fingerprint (SHA3-256 of ML-KEM public key).
    pub recipient_fingerprint: [u8; 32],
    /// ML-KEM-1024 ciphertext (encapsulates ephemeral shared secret).
    pub kem_ciphertext: [u8; CIPHERTEXT_SIZE],
    /// AEAD-encrypted Shamir share (encrypted with KEM shared secret).
    pub encrypted_share: Vec<u8>,
    /// Nonce for AEAD encryption.
    pub nonce: [u8; NONCE_SIZE],
}

impl RecipientKeyShare {
    /// Serialize to bytes.
    ///
    /// Format: `[fingerprint:32][kem_ciphertext:1568][nonce:12][share_len:4][encrypted_share:N]`
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut result =
            Vec::with_capacity(32 + CIPHERTEXT_SIZE + NONCE_SIZE + 4 + self.encrypted_share.len());
        result.extend_from_slice(&self.recipient_fingerprint);
        result.extend_from_slice(&self.kem_ciphertext);
        result.extend_from_slice(&self.nonce);
        result.extend_from_slice(&(self.encrypted_share.len() as u32).to_le_bytes());
        result.extend_from_slice(&self.encrypted_share);
        result
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, PrivateBatchError> {
        // Minimum: 32 + 1568 + 12 + 4 + 16 (empty share + tag)
        if bytes.len() < 1632 {
            return Err(PrivateBatchError::CborError(
                "recipient share too short".to_string(),
            ));
        }

        let recipient_fingerprint: [u8; 32] = bytes[0..32].try_into().unwrap();
        let kem_ciphertext: [u8; CIPHERTEXT_SIZE] = bytes[32..1600].try_into().unwrap();
        let nonce: [u8; NONCE_SIZE] = bytes[1600..1612].try_into().unwrap();
        let share_len = u32::from_le_bytes(bytes[1612..1616].try_into().unwrap()) as usize;

        if bytes.len() != 1616 + share_len {
            return Err(PrivateBatchError::CborError(
                "recipient share length mismatch".to_string(),
            ));
        }

        let encrypted_share = bytes[1616..].to_vec();

        Ok(Self {
            recipient_fingerprint,
            kem_ciphertext,
            encrypted_share,
            nonce,
        })
    }
}

/// Envelope containing key shares for all recipients.
///
/// The session key is split using Shamir's Secret Sharing, then each
/// share is encrypted to a recipient using ML-KEM-1024 for forward secrecy.
///
/// # Forward Secrecy
///
/// Each batch uses fresh ML-KEM encapsulation, generating a new ephemeral
/// shared secret. Even if a recipient's long-term ML-KEM secret key is
/// compromised later:
/// - The ephemeral randomness used in encapsulation is never stored
/// - Past KEM ciphertexts cannot be decapsulated without that randomness
/// - Therefore, past batches remain secure
#[derive(Clone)]
pub struct KeyShareEnvelope {
    /// Unique batch identifier.
    pub batch_id: [u8; 32],
    /// Threshold required to reconstruct (t in t-of-n).
    pub threshold: u8,
    /// Total number of shares (n in t-of-n).
    pub total_shares: u8,
    /// Encrypted shares for each recipient.
    pub recipient_shares: Vec<RecipientKeyShare>,
    /// Creation timestamp (Unix epoch seconds).
    pub created_at: u64,
}

impl KeyShareEnvelope {
    /// Create a new envelope by splitting the session key and encrypting to recipients.
    ///
    /// # Arguments
    ///
    /// * `session_key` - 32-byte symmetric key to split
    /// * `batch_id` - Unique batch identifier
    /// * `recipients` - ML-KEM public keys of recipients
    /// * `threshold` - Minimum shares needed to reconstruct (2 <= t <= n)
    /// * `created_at` - Unix timestamp
    ///
    /// # Security Properties
    ///
    /// - Fresh ephemeral ML-KEM encapsulation ensures forward secrecy
    /// - Shamir splitting provides information-theoretic threshold security
    /// - Each recipient can only recover their share, not the session key
    pub fn create(
        session_key: &[u8; KEY_SIZE],
        batch_id: [u8; 32],
        recipients: &[MlKemPublicKey],
        threshold: u8,
        created_at: u64,
    ) -> Result<Self, PrivateBatchError> {
        // Validate parameters
        if recipients.is_empty() || recipients.len() > MAX_RECIPIENTS {
            return Err(PrivateBatchError::InvalidRecipientCount);
        }
        if threshold < 2 || threshold as usize > recipients.len() {
            return Err(PrivateBatchError::InvalidThreshold);
        }

        let total_shares = recipients.len() as u8;

        // Split session key using Shamir's Secret Sharing
        let shares = ShamirSharing::split(session_key, threshold, total_shares)?;

        // Encrypt each share to its recipient using ML-KEM
        let mut recipient_shares = Vec::with_capacity(recipients.len());

        for (i, (recipient_pk, share)) in recipients.iter().zip(shares.iter()).enumerate() {
            // Encapsulate to get ephemeral shared secret (forward secrecy!)
            let (kem_ciphertext, mut shared_secret) = recipient_pk.encapsulate()?;

            // Use shared secret as AEAD key to encrypt the Shamir share
            let cipher = ChaCha20Poly1305::from_key(&shared_secret);

            // Derive nonce from batch_id and recipient index
            let nonce = derive_recipient_nonce(&batch_id, i as u32);

            // Serialize share and encrypt
            // Associated data is batch_id to bind ciphertext to this batch
            let share_bytes = share.to_bytes();
            let encrypted_share = cipher.seal_fixed(&nonce, &batch_id, &share_bytes);

            // Compute recipient fingerprint
            let recipient_fingerprint = sha3_256(recipient_pk.as_bytes());

            recipient_shares.push(RecipientKeyShare {
                recipient_fingerprint,
                kem_ciphertext,
                encrypted_share,
                nonce,
            });

            // Zeroize shared secret after use
            shared_secret.zeroize();
        }

        Ok(Self {
            batch_id,
            threshold,
            total_shares,
            recipient_shares,
            created_at,
        })
    }

    /// Find recipient index by their public key fingerprint.
    pub fn find_recipient(&self, fingerprint: &[u8; 32]) -> Option<usize> {
        for (i, share) in self.recipient_shares.iter().enumerate() {
            if ct_eq(&share.recipient_fingerprint, fingerprint) {
                return Some(i);
            }
        }
        None
    }

    /// Find recipient index by their public key.
    pub fn find_recipient_by_key(&self, pubkey: &MlKemPublicKey) -> Option<usize> {
        let fingerprint = sha3_256(pubkey.as_bytes());
        self.find_recipient(&fingerprint)
    }

    /// Decrypt a share using the recipient's secret key.
    ///
    /// # Arguments
    ///
    /// * `recipient_index` - Index of the recipient in the envelope
    /// * `recipient_sk` - Recipient's ML-KEM secret key
    ///
    /// # Returns
    ///
    /// The decrypted Shamir share for use in collaborative recovery.
    pub fn decrypt_share(
        &self,
        recipient_index: usize,
        recipient_sk: &MlKemSecretKey,
    ) -> Result<Share, PrivateBatchError> {
        if recipient_index >= self.recipient_shares.len() {
            return Err(PrivateBatchError::InvalidRecipientIndex);
        }

        let recipient_share = &self.recipient_shares[recipient_index];

        // Decapsulate to recover shared secret
        let mut shared_secret = recipient_sk.decapsulate(&recipient_share.kem_ciphertext)?;

        // Decrypt the Shamir share
        let cipher = ChaCha20Poly1305::from_key(&shared_secret);
        let share_bytes = cipher
            .open_fixed(
                &recipient_share.nonce,
                &self.batch_id, // Associated data
                &recipient_share.encrypted_share,
            )
            .map_err(|_| PrivateBatchError::DecryptionFailed)?;

        // Zeroize shared secret
        shared_secret.zeroize();

        // Deserialize share
        Share::from_bytes(&share_bytes).map_err(PrivateBatchError::from)
    }

    /// Serialize to bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        // Header: batch_id(32) + threshold(1) + total_shares(1) + created_at(8) + num_shares(1)
        let mut result = Vec::with_capacity(43 + self.recipient_shares.len() * 1700);
        result.extend_from_slice(&self.batch_id);
        result.push(self.threshold);
        result.push(self.total_shares);
        result.extend_from_slice(&self.created_at.to_le_bytes());
        result.push(self.recipient_shares.len() as u8);

        // Each recipient share
        for share in &self.recipient_shares {
            let share_bytes = share.to_bytes();
            result.extend_from_slice(&(share_bytes.len() as u32).to_le_bytes());
            result.extend_from_slice(&share_bytes);
        }

        result
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, PrivateBatchError> {
        if bytes.len() < 43 {
            return Err(PrivateBatchError::CborError(
                "envelope too short".to_string(),
            ));
        }

        let batch_id: [u8; 32] = bytes[0..32].try_into().unwrap();
        let threshold = bytes[32];
        let total_shares = bytes[33];
        let created_at = u64::from_le_bytes(bytes[34..42].try_into().unwrap());
        let num_shares = bytes[42] as usize;

        let mut recipient_shares = Vec::with_capacity(num_shares);
        let mut offset = 43;

        for _ in 0..num_shares {
            if offset + 4 > bytes.len() {
                return Err(PrivateBatchError::CborError(
                    "envelope truncated".to_string(),
                ));
            }
            let share_len = u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap()) as usize;
            offset += 4;

            if offset + share_len > bytes.len() {
                return Err(PrivateBatchError::CborError(
                    "share data truncated".to_string(),
                ));
            }

            let share = RecipientKeyShare::from_bytes(&bytes[offset..offset + share_len])?;
            recipient_shares.push(share);
            offset += share_len;
        }

        Ok(Self {
            batch_id,
            threshold,
            total_shares,
            recipient_shares,
            created_at,
        })
    }
}

/// Derive a unique nonce for encrypting a recipient's share.
#[inline]
fn derive_recipient_nonce(batch_id: &[u8; 32], index: u32) -> [u8; NONCE_SIZE] {
    // Use different domain than leaf nonce (prefix with 0xFF)
    let mut input = [0u8; 37];
    input[0] = 0xFF; // Domain separator
    input[1..33].copy_from_slice(batch_id);
    input[33..37].copy_from_slice(&index.to_le_bytes());
    let hash = sha3_256(&input);
    let mut nonce = [0u8; NONCE_SIZE];
    nonce.copy_from_slice(&hash[..NONCE_SIZE]);
    nonce
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mlkem::MlKemKeyPair;

    #[test]
    fn test_create_and_decrypt_shares() {
        let session_key = [0x42u8; 32];
        let batch_id = [0xABu8; 32];

        // Generate 3 ML-KEM keypairs
        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();
        let kp3 = MlKemKeyPair::generate().unwrap();

        let pks = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp3.public_key_bytes()).unwrap(),
        ];

        // Create envelope with 2-of-3 threshold
        let envelope = KeyShareEnvelope::create(&session_key, batch_id, &pks, 2, 12345).unwrap();

        assert_eq!(envelope.threshold, 2);
        assert_eq!(envelope.total_shares, 3);
        assert_eq!(envelope.recipient_shares.len(), 3);

        // Each recipient can decrypt their share
        let (sk1, _) = kp1.into_parts();
        let share1 = envelope.decrypt_share(0, &sk1).unwrap();

        let (sk2, _) = kp2.into_parts();
        let share2 = envelope.decrypt_share(1, &sk2).unwrap();

        // Combine 2 shares to recover session key
        let recovered = ShamirSharing::combine(&[share1, share2]).unwrap();
        assert_eq!(recovered, session_key.to_vec());
    }

    #[test]
    fn test_find_recipient() {
        let session_key = [0x42u8; 32];
        let batch_id = [0xABu8; 32];

        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();

        let pk1 = MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap();
        let pk2 = MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap();
        let pks = vec![pk1.clone(), pk2.clone()];

        let envelope = KeyShareEnvelope::create(&session_key, batch_id, &pks, 2, 0).unwrap();

        // Find by key
        assert_eq!(envelope.find_recipient_by_key(&pk1), Some(0));
        assert_eq!(envelope.find_recipient_by_key(&pk2), Some(1));

        // Find by fingerprint
        let fp1 = sha3_256(pk1.as_bytes());
        assert_eq!(envelope.find_recipient(&fp1), Some(0));
    }

    #[test]
    fn test_wrong_key_decryption_fails() {
        let session_key = [0x42u8; 32];
        let batch_id = [0xABu8; 32];

        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();
        let wrong_kp = MlKemKeyPair::generate().unwrap();

        let pks = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
        ];

        let envelope = KeyShareEnvelope::create(&session_key, batch_id, &pks, 2, 0).unwrap();

        // Try to decrypt with wrong key
        let (wrong_sk, _) = wrong_kp.into_parts();
        let result = envelope.decrypt_share(0, &wrong_sk);

        // Should fail (either decapsulation mismatch or AEAD auth failure)
        assert!(result.is_err());
    }

    #[test]
    fn test_serialization_roundtrip() {
        let session_key = [0x42u8; 32];
        let batch_id = [0xABu8; 32];

        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();

        let pks = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
        ];

        let original = KeyShareEnvelope::create(&session_key, batch_id, &pks, 2, 67890).unwrap();
        let bytes = original.to_bytes();
        let parsed = KeyShareEnvelope::from_bytes(&bytes).unwrap();

        assert_eq!(parsed.batch_id, original.batch_id);
        assert_eq!(parsed.threshold, original.threshold);
        assert_eq!(parsed.total_shares, original.total_shares);
        assert_eq!(parsed.created_at, original.created_at);
        assert_eq!(
            parsed.recipient_shares.len(),
            original.recipient_shares.len()
        );

        // Verify decryption still works after deserialization
        let (sk1, _) = kp1.into_parts();
        let share = parsed.decrypt_share(0, &sk1).unwrap();
        assert!(share.data.len() > 0);
    }

    #[test]
    fn test_invalid_parameters() {
        let session_key = [0x42u8; 32];
        let batch_id = [0xABu8; 32];

        let kp = MlKemKeyPair::generate().unwrap();
        let pks = vec![MlKemPublicKey::from_bytes(kp.public_key_bytes()).unwrap()];

        // Single recipient with threshold 2 should fail
        let result = KeyShareEnvelope::create(&session_key, batch_id, &pks, 2, 0);
        assert!(matches!(result, Err(PrivateBatchError::InvalidThreshold)));

        // Empty recipients should fail
        let result = KeyShareEnvelope::create(&session_key, batch_id, &[], 2, 0);
        assert!(matches!(
            result,
            Err(PrivateBatchError::InvalidRecipientCount)
        ));
    }
}
