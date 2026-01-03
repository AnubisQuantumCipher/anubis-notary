//! Privacy-Preserving Collaborative Anchoring with Forward-Secure Key Shares.
//!
//! This module provides forward-secure, privacy-preserving batch anchoring
//! using ML-KEM-1024 for ephemeral key encapsulation and Shamir secret sharing
//! for threshold decryption.
//!
//! # Overview
//!
//! Private batches allow multiple receipts to be anchored while hiding their
//! content from the anchor service. The batch creator encrypts leaves with
//! an ephemeral session key, then distributes encrypted shares of that key
//! to multiple recipients using ML-KEM-1024 for forward secrecy.
//!
//! ## Security Properties
//!
//! - **Forward Secrecy**: Each batch uses fresh ML-KEM encapsulation, so
//!   compromising a recipient's long-term key cannot decrypt past batches.
//!
//! - **Privacy**: Encrypted leaves hide content while Merkle proofs still work.
//!
//! - **Threshold Access**: t-of-n recipients must collaborate to decrypt.
//!
//! - **Information-Theoretic Security**: t-1 shares reveal nothing about the
//!   session key (Shamir's Secret Sharing).
//!
//! # Usage
//!
//! ## Creating a Private Batch
//!
//! ```ignore
//! use anubis_core::private_batch::PrivateBatch;
//! use anubis_core::mlkem::{MlKemKeyPair, MlKemPublicKey};
//!
//! // Generate recipient keys
//! let kp1 = MlKemKeyPair::generate()?;
//! let kp2 = MlKemKeyPair::generate()?;
//! let kp3 = MlKemKeyPair::generate()?;
//!
//! let recipients = vec![
//!     MlKemPublicKey::from_bytes(kp1.public_key_bytes())?,
//!     MlKemPublicKey::from_bytes(kp2.public_key_bytes())?,
//!     MlKemPublicKey::from_bytes(kp3.public_key_bytes())?,
//! ];
//!
//! // Create batch with 2-of-3 threshold
//! let leaves = [b"receipt1".as_ref(), b"receipt2"];
//! let batch = PrivateBatch::create(&leaves, &recipients, 2)?;
//!
//! // Anchor the merkle_root to blockchain/log
//! let root = batch.merkle_root;
//! ```
//!
//! ## Collaborative Decryption
//!
//! ```ignore
//! use anubis_core::private_batch::{CollaborativeDecryptor, PrivateBatch};
//!
//! // Each recipient decrypts their share
//! let (sk1, _) = kp1.into_parts();
//! let share1 = batch.key_envelope.decrypt_share(0, &sk1)?;
//!
//! let (sk2, _) = kp2.into_parts();
//! let share2 = batch.key_envelope.decrypt_share(1, &sk2)?;
//!
//! // Coordinator combines shares
//! let mut decryptor = CollaborativeDecryptor::from_batch(&batch);
//! decryptor.add_share(share1)?;
//! decryptor.add_share(share2)?;
//!
//! // Decrypt all leaves
//! let plaintext_leaves = decryptor.decrypt_private_batch(&batch)?;
//! ```
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                    Private Batch Creation                        │
//! ├─────────────────────────────────────────────────────────────────┤
//! │ 1. Generate ephemeral session key (32 bytes)                    │
//! │ 2. Encrypt each receipt leaf with ChaCha20Poly1305              │
//! │ 3. Build Merkle tree over encrypted leaf hashes                 │
//! │ 4. Split session key using Shamir (t-of-n)                      │
//! │ 5. For each recipient:                                          │
//! │    - ML-KEM encapsulate → ephemeral shared secret               │
//! │    - Encrypt Shamir share with shared secret                    │
//! │ 6. Anchor Merkle root to blockchain/log                         │
//! │ 7. Zeroize session key                                          │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Formal Verification
//!
//! The underlying cryptographic primitives are formally verified:
//! - **ML-KEM-1024**: Cryspen libcrux (hax/F*)
//! - **ChaCha20Poly1305**: Cryspen libcrux (hax/F*)
//! - **SHA3-256**: Cryspen libcrux-sha3 (hax/F*)
//!
//! The Shamir implementation uses GF(2^8) arithmetic with standard tables.

mod batch;
mod collaborative;
mod encrypted_leaf;
mod error;
mod key_envelope;

// Re-export main types
pub use batch::{PrivateBatch, MAX_PRIVATE_BATCH_LEAVES};
pub use collaborative::{CollaborativeDecryptor, DecryptedShare};
pub use encrypted_leaf::{EncryptedLeaf, MAX_LEAF_SIZE};
pub use error::PrivateBatchError;
pub use key_envelope::{KeyShareEnvelope, RecipientKeyShare, MAX_RECIPIENTS};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mlkem::{MlKemKeyPair, MlKemPublicKey};

    /// Integration test: full workflow from creation to decryption.
    #[test]
    fn test_full_private_batch_workflow() {
        // Original data
        let receipt1 = b"CBOR receipt data for document A";
        let receipt2 = b"CBOR receipt data for document B";
        let receipt3 = b"CBOR receipt data for document C";
        let leaves = [receipt1.as_ref(), receipt2.as_ref(), receipt3.as_ref()];

        // Generate 3 recipient keypairs
        let kp_alice = MlKemKeyPair::generate().unwrap();
        let kp_bob = MlKemKeyPair::generate().unwrap();
        let kp_carol = MlKemKeyPair::generate().unwrap();

        let recipients = vec![
            MlKemPublicKey::from_bytes(kp_alice.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp_bob.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp_carol.public_key_bytes()).unwrap(),
        ];

        // Create private batch with 2-of-3 threshold
        let batch = PrivateBatch::create(&leaves, &recipients, 2).unwrap();

        // Verify batch properties
        assert_eq!(batch.len(), 3);
        assert_eq!(batch.key_envelope.threshold, 2);
        assert_eq!(batch.key_envelope.total_shares, 3);
        assert!(!batch.anchored);

        // Simulate: anchor the merkle_root (would go to blockchain)
        let _anchored_root = batch.merkle_root;

        // Alice decrypts her share
        let (sk_alice, _) = kp_alice.into_parts();
        let alice_share = batch.key_envelope.decrypt_share(0, &sk_alice).unwrap();

        // Carol decrypts her share (Bob is unavailable)
        let (sk_carol, _) = kp_carol.into_parts();
        let carol_share = batch.key_envelope.decrypt_share(2, &sk_carol).unwrap();

        // Coordinator combines shares
        let mut decryptor = CollaborativeDecryptor::from_batch(&batch);
        assert!(!decryptor.add_share(alice_share).unwrap());
        assert!(decryptor.add_share(carol_share).unwrap());
        assert!(decryptor.can_recover());

        // Decrypt all leaves
        let decrypted = decryptor.decrypt_private_batch(&batch).unwrap();

        // Verify content (use &* to deref Zeroizing<Vec<u8>> to &[u8])
        assert_eq!(&*decrypted[0], receipt1);
        assert_eq!(&*decrypted[1], receipt2);
        assert_eq!(&*decrypted[2], receipt3);

        // Verify Merkle proofs still work
        assert!(batch.verify_leaf(0).unwrap());
        assert!(batch.verify_leaf(1).unwrap());
        assert!(batch.verify_leaf(2).unwrap());
    }

    /// Test serialization/deserialization of complete batch.
    #[test]
    fn test_batch_round_trip() {
        let kp1 = MlKemKeyPair::generate().unwrap();
        let kp2 = MlKemKeyPair::generate().unwrap();

        let recipients = vec![
            MlKemPublicKey::from_bytes(kp1.public_key_bytes()).unwrap(),
            MlKemPublicKey::from_bytes(kp2.public_key_bytes()).unwrap(),
        ];

        let original = PrivateBatch::create(&[b"test data".as_ref()], &recipients, 2).unwrap();

        // Serialize
        let bytes = original.to_bytes();

        // Deserialize
        let restored = PrivateBatch::from_bytes(&bytes).unwrap();

        // Verify all fields match
        assert_eq!(restored.batch_id, original.batch_id);
        assert_eq!(restored.merkle_root, original.merkle_root);
        assert_eq!(restored.leaves.len(), original.leaves.len());
        assert_eq!(
            restored.key_envelope.threshold,
            original.key_envelope.threshold
        );

        // Verify decryption still works after round-trip
        let (sk1, _) = kp1.into_parts();
        let (sk2, _) = kp2.into_parts();

        let share1 = restored.key_envelope.decrypt_share(0, &sk1).unwrap();
        let share2 = restored.key_envelope.decrypt_share(1, &sk2).unwrap();

        let mut decryptor = CollaborativeDecryptor::from_batch(&restored);
        decryptor.add_share(share1).unwrap();
        decryptor.add_share(share2).unwrap();

        let decrypted = decryptor.decrypt_private_batch(&restored).unwrap();
        assert_eq!(&*decrypted[0], b"test data");
    }
}
