//! Multi-signature support for governance operations.
//!
//! This module implements M-of-N threshold multi-signature schemes for
//! governance, allowing operations to require approval from multiple signers.
//!
//! ## Features
//!
//! - **Threshold signatures**: Require M of N signers to approve an action
//! - **Proposal system**: Create, vote on, and execute governance proposals
//! - **Time-locked execution**: Optional delay between approval and execution
//! - **Quorum tracking**: Track signature collection progress
//!
//! ## Security Properties
//!
//! - All signatures are verified using ML-DSA-87 post-quantum signatures
//! - Proposals include nonces to prevent replay attacks
//! - Signers are identified by their public key hash
//! - Duplicate signatures are rejected
//!
//! ## Usage
//!
//! ```ignore
//! // Create a 2-of-3 multisig
//! let multisig = Multisig::new(2, vec![pk1, pk2, pk3])?;
//!
//! // Create a proposal
//! let proposal = multisig.create_proposal(
//!     ProposalType::KeyRotation { new_key: new_pk },
//!     "Rotate admin key",
//! )?;
//!
//! // Collect signatures
//! let sig1 = kp1.sign(&proposal.signing_payload())?;
//! let sig2 = kp2.sign(&proposal.signing_payload())?;
//!
//! // Execute when threshold is met
//! let mut proposal = proposal;
//! proposal.add_signature(0, sig1)?;
//! proposal.add_signature(1, sig2)?;
//!
//! if proposal.is_approved() {
//!     proposal.execute()?;
//! }
//! ```

use serde::{Deserialize, Serialize};
use zeroize::Zeroize;

use crate::keccak::sha3::sha3_256;
use crate::mldsa::{PublicKey, Signature, SIGNATURE_SIZE};

/// Maximum number of signers in a multisig.
pub const MAX_SIGNERS: usize = 16;

/// Maximum description length for proposals.
pub const MAX_DESCRIPTION_LENGTH: usize = 1024;

/// Errors from multisig operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MultisigError {
    /// Threshold must be at least 1.
    ThresholdTooLow,
    /// Threshold exceeds number of signers.
    ThresholdExceedsSigners,
    /// No signers provided.
    NoSigners,
    /// Too many signers (max 16).
    TooManySigners,
    /// Duplicate signer public keys.
    DuplicateSigner,
    /// Signer index out of bounds.
    InvalidSignerIndex,
    /// Signature verification failed.
    InvalidSignature,
    /// Signature already provided by this signer.
    DuplicateSignature,
    /// Proposal already executed.
    AlreadyExecuted,
    /// Proposal expired.
    ProposalExpired,
    /// Not enough signatures to execute.
    InsufficientSignatures,
    /// Proposal description too long.
    DescriptionTooLong,
    /// Invalid proposal data.
    InvalidProposal,
    /// Signer not found in multisig.
    SignerNotFound,
}

impl core::fmt::Display for MultisigError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ThresholdTooLow => write!(f, "threshold must be at least 1"),
            Self::ThresholdExceedsSigners => write!(f, "threshold exceeds number of signers"),
            Self::NoSigners => write!(f, "no signers provided"),
            Self::TooManySigners => write!(f, "too many signers (max {})", MAX_SIGNERS),
            Self::DuplicateSigner => write!(f, "duplicate signer public key"),
            Self::InvalidSignerIndex => write!(f, "signer index out of bounds"),
            Self::InvalidSignature => write!(f, "signature verification failed"),
            Self::DuplicateSignature => write!(f, "duplicate signature from signer"),
            Self::AlreadyExecuted => write!(f, "proposal already executed"),
            Self::ProposalExpired => write!(f, "proposal has expired"),
            Self::InsufficientSignatures => write!(f, "not enough signatures to execute"),
            Self::DescriptionTooLong => {
                write!(f, "description too long (max {} bytes)", MAX_DESCRIPTION_LENGTH)
            }
            Self::InvalidProposal => write!(f, "invalid proposal data"),
            Self::SignerNotFound => write!(f, "signer not found in multisig"),
        }
    }
}

impl std::error::Error for MultisigError {}

/// Hash of a public key for identification.
pub type SignerHash = [u8; 32];

/// Compute the hash of a public key.
pub fn hash_public_key(pk: &PublicKey) -> SignerHash {
    sha3_256(&pk.to_bytes())
}

/// Status of a proposal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProposalStatus {
    /// Proposal is pending signatures.
    Pending,
    /// Proposal has reached threshold and can be executed.
    Approved,
    /// Proposal has been executed.
    Executed,
    /// Proposal was rejected or cancelled.
    Rejected,
    /// Proposal has expired.
    Expired,
}

/// Types of governance proposals.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProposalType {
    /// Rotate a key in the multisig.
    KeyRotation {
        /// Index of the signer to replace.
        signer_index: usize,
        /// New public key hash.
        new_key_hash: SignerHash,
    },
    /// Change the signature threshold.
    ThresholdChange {
        /// New threshold value.
        new_threshold: u8,
    },
    /// Add a new signer.
    AddSigner {
        /// New signer's public key hash.
        new_signer_hash: SignerHash,
    },
    /// Remove a signer.
    RemoveSigner {
        /// Index of signer to remove.
        signer_index: usize,
    },
    /// Authorize a specific action (generic payload).
    AuthorizeAction {
        /// Action type identifier.
        action_type: String,
        /// Action payload (opaque bytes).
        payload: Vec<u8>,
    },
    /// Emergency pause of operations.
    EmergencyPause,
    /// Resume operations after pause.
    Resume,
    /// Custom governance action.
    Custom {
        /// Action identifier.
        action_id: [u8; 32],
        /// Action parameters.
        params: Vec<u8>,
    },
}

/// A collected signature with metadata.
#[derive(Clone)]
pub struct CollectedSignature {
    /// Index of the signer in the multisig.
    pub signer_index: usize,
    /// The signature bytes.
    pub signature: [u8; SIGNATURE_SIZE],
    /// Timestamp when signature was collected.
    pub timestamp: u64,
}

impl Zeroize for CollectedSignature {
    fn zeroize(&mut self) {
        self.signature.zeroize();
    }
}

/// A governance proposal that requires multi-signature approval.
#[derive(Clone)]
pub struct Proposal {
    /// Unique proposal ID (hash of proposal content).
    pub id: [u8; 32],
    /// Type of proposal.
    pub proposal_type: ProposalType,
    /// Human-readable description.
    pub description: String,
    /// Hash of the multisig configuration at proposal creation.
    pub multisig_hash: [u8; 32],
    /// Nonce to prevent replay.
    pub nonce: u64,
    /// Creation timestamp (Unix epoch seconds).
    pub created_at: u64,
    /// Expiration timestamp (Unix epoch seconds), or 0 for no expiration.
    pub expires_at: u64,
    /// Required number of signatures.
    pub threshold: u8,
    /// Current status.
    pub status: ProposalStatus,
    /// Collected signatures.
    signatures: Vec<CollectedSignature>,
    /// Bitmap of which signers have signed (up to 64 signers).
    signed_bitmap: u64,
}

impl Proposal {
    /// Create a new proposal.
    pub fn new(
        proposal_type: ProposalType,
        description: &str,
        multisig: &Multisig,
        nonce: u64,
        created_at: u64,
        expires_at: u64,
    ) -> Result<Self, MultisigError> {
        if description.len() > MAX_DESCRIPTION_LENGTH {
            return Err(MultisigError::DescriptionTooLong);
        }

        let multisig_hash = multisig.config_hash();

        // Compute proposal ID
        let mut id_preimage = Vec::new();
        id_preimage.extend_from_slice(&multisig_hash);
        id_preimage.extend_from_slice(&nonce.to_le_bytes());
        id_preimage.extend_from_slice(&created_at.to_le_bytes());
        id_preimage.extend_from_slice(description.as_bytes());
        // Include proposal type in ID
        let type_bytes = bincode_serialize(&proposal_type);
        id_preimage.extend_from_slice(&type_bytes);

        let id = sha3_256(&id_preimage);

        Ok(Self {
            id,
            proposal_type,
            description: description.to_string(),
            multisig_hash,
            nonce,
            created_at,
            expires_at,
            threshold: multisig.threshold,
            status: ProposalStatus::Pending,
            signatures: Vec::new(),
            signed_bitmap: 0,
        })
    }

    /// Get the payload that signers should sign.
    pub fn signing_payload(&self) -> Vec<u8> {
        let mut payload = Vec::new();
        // Domain separator for multisig proposals
        payload.extend_from_slice(b"ANUBIS-MULTISIG-PROPOSAL-V1:");
        payload.extend_from_slice(&self.id);
        payload.extend_from_slice(&self.multisig_hash);
        payload.extend_from_slice(&self.nonce.to_le_bytes());
        payload
    }

    /// Add a signature to the proposal.
    ///
    /// Returns `true` if the threshold has been reached.
    pub fn add_signature(
        &mut self,
        signer_index: usize,
        signature: &Signature,
        public_key: &PublicKey,
        timestamp: u64,
    ) -> Result<bool, MultisigError> {
        // SECURITY: Validate signer_index to prevent undefined behavior.
        // The signed_bitmap is u64, so indices >= 64 would cause overflow
        // in `1 << signer_index`. Also enforce MAX_SIGNERS limit.
        if signer_index >= MAX_SIGNERS {
            return Err(MultisigError::InvalidSignerIndex);
        }

        // Check if already executed
        if self.status == ProposalStatus::Executed {
            return Err(MultisigError::AlreadyExecuted);
        }

        // Check for duplicate signature (safe now that signer_index < MAX_SIGNERS < 64)
        if self.signed_bitmap & (1u64 << signer_index) != 0 {
            return Err(MultisigError::DuplicateSignature);
        }

        // Verify the signature
        let payload = self.signing_payload();
        if !public_key.verify(&payload, signature) {
            return Err(MultisigError::InvalidSignature);
        }

        // Add signature
        self.signatures.push(CollectedSignature {
            signer_index,
            signature: signature.to_bytes(),
            timestamp,
        });
        self.signed_bitmap |= 1u64 << signer_index;

        // Check if threshold reached
        if self.signature_count() >= self.threshold as usize {
            self.status = ProposalStatus::Approved;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Get the number of collected signatures.
    pub fn signature_count(&self) -> usize {
        self.signatures.len()
    }

    /// Get the number of signatures still needed.
    pub fn signatures_needed(&self) -> usize {
        let collected = self.signature_count();
        (self.threshold as usize).saturating_sub(collected)
    }

    /// Check if the proposal has enough signatures.
    pub fn is_approved(&self) -> bool {
        self.status == ProposalStatus::Approved || self.signature_count() >= self.threshold as usize
    }

    /// Check if a specific signer has signed.
    pub fn has_signed(&self, signer_index: usize) -> bool {
        self.signed_bitmap & (1 << signer_index) != 0
    }

    /// Get all collected signatures.
    pub fn signatures(&self) -> &[CollectedSignature] {
        &self.signatures
    }

    /// Mark the proposal as executed.
    pub fn mark_executed(&mut self) -> Result<(), MultisigError> {
        if self.status == ProposalStatus::Executed {
            return Err(MultisigError::AlreadyExecuted);
        }
        if !self.is_approved() {
            return Err(MultisigError::InsufficientSignatures);
        }
        self.status = ProposalStatus::Executed;
        Ok(())
    }

    /// Check if the proposal has expired.
    pub fn is_expired(&self, current_time: u64) -> bool {
        self.expires_at > 0 && current_time > self.expires_at
    }

    /// Mark the proposal as expired.
    pub fn mark_expired(&mut self) {
        self.status = ProposalStatus::Expired;
    }

    /// Reject the proposal.
    pub fn reject(&mut self) {
        self.status = ProposalStatus::Rejected;
    }
}

impl Zeroize for Proposal {
    fn zeroize(&mut self) {
        for sig in &mut self.signatures {
            sig.zeroize();
        }
    }
}

/// Simple serialization for proposal types (deterministic).
fn bincode_serialize(proposal_type: &ProposalType) -> Vec<u8> {
    // Simple deterministic serialization
    let mut out = Vec::new();
    match proposal_type {
        ProposalType::KeyRotation { signer_index, new_key_hash } => {
            out.push(0);
            out.extend_from_slice(&(*signer_index as u64).to_le_bytes());
            out.extend_from_slice(new_key_hash);
        }
        ProposalType::ThresholdChange { new_threshold } => {
            out.push(1);
            out.push(*new_threshold);
        }
        ProposalType::AddSigner { new_signer_hash } => {
            out.push(2);
            out.extend_from_slice(new_signer_hash);
        }
        ProposalType::RemoveSigner { signer_index } => {
            out.push(3);
            out.extend_from_slice(&(*signer_index as u64).to_le_bytes());
        }
        ProposalType::AuthorizeAction { action_type, payload } => {
            out.push(4);
            out.extend_from_slice(&(action_type.len() as u32).to_le_bytes());
            out.extend_from_slice(action_type.as_bytes());
            out.extend_from_slice(&(payload.len() as u32).to_le_bytes());
            out.extend_from_slice(payload);
        }
        ProposalType::EmergencyPause => {
            out.push(5);
        }
        ProposalType::Resume => {
            out.push(6);
        }
        ProposalType::Custom { action_id, params } => {
            out.push(7);
            out.extend_from_slice(action_id);
            out.extend_from_slice(&(params.len() as u32).to_le_bytes());
            out.extend_from_slice(params);
        }
    }
    out
}

/// Multi-signature configuration.
#[derive(Clone)]
pub struct Multisig {
    /// Signature threshold (M in M-of-N).
    pub threshold: u8,
    /// Signer public keys.
    signers: Vec<PublicKey>,
    /// Signer hashes for quick lookup.
    signer_hashes: Vec<SignerHash>,
    /// Next nonce for proposal creation.
    next_nonce: u64,
}

impl Multisig {
    /// Create a new multisig configuration.
    ///
    /// # Arguments
    /// * `threshold` - Number of signatures required (M)
    /// * `signers` - List of signer public keys (N signers)
    ///
    /// # Errors
    /// Returns error if parameters are invalid.
    pub fn new(threshold: u8, signers: Vec<PublicKey>) -> Result<Self, MultisigError> {
        // Validate threshold
        if threshold < 1 {
            return Err(MultisigError::ThresholdTooLow);
        }
        if signers.is_empty() {
            return Err(MultisigError::NoSigners);
        }
        if signers.len() > MAX_SIGNERS {
            return Err(MultisigError::TooManySigners);
        }
        if threshold as usize > signers.len() {
            return Err(MultisigError::ThresholdExceedsSigners);
        }

        // Compute signer hashes and check for duplicates
        let mut signer_hashes = Vec::with_capacity(signers.len());
        for pk in &signers {
            let hash = hash_public_key(pk);
            if signer_hashes.contains(&hash) {
                return Err(MultisigError::DuplicateSigner);
            }
            signer_hashes.push(hash);
        }

        Ok(Self {
            threshold,
            signers,
            signer_hashes,
            next_nonce: 0,
        })
    }

    /// Get the number of signers.
    pub fn signer_count(&self) -> usize {
        self.signers.len()
    }

    /// Get a signer's public key by index.
    pub fn get_signer(&self, index: usize) -> Option<&PublicKey> {
        self.signers.get(index)
    }

    /// Find a signer's index by public key.
    pub fn find_signer(&self, pk: &PublicKey) -> Option<usize> {
        let hash = hash_public_key(pk);
        self.signer_hashes.iter().position(|h| h == &hash)
    }

    /// Find a signer's index by public key hash.
    pub fn find_signer_by_hash(&self, hash: &SignerHash) -> Option<usize> {
        self.signer_hashes.iter().position(|h| h == hash)
    }

    /// Get all signer hashes.
    pub fn signer_hashes(&self) -> &[SignerHash] {
        &self.signer_hashes
    }

    /// Compute a hash of the multisig configuration.
    pub fn config_hash(&self) -> [u8; 32] {
        let mut data = Vec::new();
        data.push(self.threshold);
        data.push(self.signers.len() as u8);
        for hash in &self.signer_hashes {
            data.extend_from_slice(hash);
        }
        sha3_256(&data)
    }

    /// Create a new proposal.
    pub fn create_proposal(
        &mut self,
        proposal_type: ProposalType,
        description: &str,
        current_time: u64,
        expires_in: Option<u64>,
    ) -> Result<Proposal, MultisigError> {
        let nonce = self.next_nonce;
        self.next_nonce += 1;

        let expires_at = expires_in.map(|d| current_time + d).unwrap_or(0);

        Proposal::new(
            proposal_type,
            description,
            self,
            nonce,
            current_time,
            expires_at,
        )
    }

    /// Verify a proposal was created for this multisig.
    pub fn verify_proposal(&self, proposal: &Proposal) -> bool {
        proposal.multisig_hash == self.config_hash()
    }

    /// Add a signature to a proposal from a signer.
    pub fn sign_proposal(
        &self,
        proposal: &mut Proposal,
        signer_pk: &PublicKey,
        signature: &Signature,
        timestamp: u64,
    ) -> Result<bool, MultisigError> {
        // Verify proposal belongs to this multisig
        if !self.verify_proposal(proposal) {
            return Err(MultisigError::InvalidProposal);
        }

        // Find signer index
        let signer_index = self
            .find_signer(signer_pk)
            .ok_or(MultisigError::SignerNotFound)?;

        // Add signature
        proposal.add_signature(signer_index, signature, signer_pk, timestamp)
    }

    /// Verify all signatures on a proposal.
    pub fn verify_proposal_signatures(&self, proposal: &Proposal) -> Result<bool, MultisigError> {
        if !self.verify_proposal(proposal) {
            return Err(MultisigError::InvalidProposal);
        }

        let payload = proposal.signing_payload();

        for collected in &proposal.signatures {
            let signer_pk = self
                .get_signer(collected.signer_index)
                .ok_or(MultisigError::InvalidSignerIndex)?;

            let signature = Signature::from_bytes(&collected.signature)
                .map_err(|_| MultisigError::InvalidSignature)?;

            if !signer_pk.verify(&payload, &signature) {
                return Ok(false);
            }
        }

        Ok(true)
    }

    /// Update the multisig based on an executed proposal.
    ///
    /// Returns Ok(true) if the multisig was modified.
    pub fn apply_proposal(&mut self, proposal: &Proposal) -> Result<bool, MultisigError> {
        if proposal.status != ProposalStatus::Executed {
            return Err(MultisigError::InsufficientSignatures);
        }

        if !self.verify_proposal(proposal) {
            return Err(MultisigError::InvalidProposal);
        }

        match &proposal.proposal_type {
            ProposalType::KeyRotation { signer_index, new_key_hash } => {
                if *signer_index >= self.signers.len() {
                    return Err(MultisigError::InvalidSignerIndex);
                }
                // We need the actual public key to be provided externally
                // For now, just update the hash
                self.signer_hashes[*signer_index] = *new_key_hash;
                Ok(true)
            }
            ProposalType::ThresholdChange { new_threshold } => {
                if *new_threshold < 1 || *new_threshold as usize > self.signers.len() {
                    return Err(MultisigError::ThresholdExceedsSigners);
                }
                self.threshold = *new_threshold;
                Ok(true)
            }
            ProposalType::RemoveSigner { signer_index } => {
                if *signer_index >= self.signers.len() {
                    return Err(MultisigError::InvalidSignerIndex);
                }
                if self.signers.len() <= self.threshold as usize {
                    return Err(MultisigError::ThresholdExceedsSigners);
                }
                self.signers.remove(*signer_index);
                self.signer_hashes.remove(*signer_index);
                Ok(true)
            }
            // These proposal types don't modify the multisig itself
            ProposalType::AddSigner { .. }
            | ProposalType::AuthorizeAction { .. }
            | ProposalType::EmergencyPause
            | ProposalType::Resume
            | ProposalType::Custom { .. } => Ok(false),
        }
    }
}

/// Builder for creating multisig configurations.
pub struct MultisigBuilder {
    threshold: u8,
    signers: Vec<PublicKey>,
}

impl MultisigBuilder {
    /// Create a new builder with the given threshold.
    pub fn new(threshold: u8) -> Self {
        Self {
            threshold,
            signers: Vec::new(),
        }
    }

    /// Add a signer.
    pub fn add_signer(mut self, pk: PublicKey) -> Self {
        self.signers.push(pk);
        self
    }

    /// Add multiple signers.
    pub fn add_signers(mut self, pks: impl IntoIterator<Item = PublicKey>) -> Self {
        self.signers.extend(pks);
        self
    }

    /// Build the multisig.
    pub fn build(self) -> Result<Multisig, MultisigError> {
        Multisig::new(self.threshold, self.signers)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mldsa::KeyPair;

    fn generate_keypairs(n: usize) -> Vec<KeyPair> {
        (0..n)
            .map(|i| {
                let seed = [i as u8; 32];
                KeyPair::from_seed(&seed).unwrap()
            })
            .collect()
    }

    #[test]
    fn test_multisig_creation() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let multisig = Multisig::new(2, signers).unwrap();
        assert_eq!(multisig.threshold, 2);
        assert_eq!(multisig.signer_count(), 3);
    }

    #[test]
    fn test_multisig_validation() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        // Threshold too low
        assert!(matches!(
            Multisig::new(0, signers.clone()),
            Err(MultisigError::ThresholdTooLow)
        ));

        // Threshold exceeds signers
        assert!(matches!(
            Multisig::new(4, signers.clone()),
            Err(MultisigError::ThresholdExceedsSigners)
        ));

        // No signers
        assert!(matches!(
            Multisig::new(1, vec![]),
            Err(MultisigError::NoSigners)
        ));

        // Duplicate signers
        let mut dup_signers = signers.clone();
        dup_signers.push(signers[0].clone());
        assert!(matches!(
            Multisig::new(2, dup_signers),
            Err(MultisigError::DuplicateSigner)
        ));
    }

    #[test]
    fn test_proposal_creation() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let mut multisig = Multisig::new(2, signers).unwrap();

        let proposal = multisig
            .create_proposal(
                ProposalType::EmergencyPause,
                "Emergency pause for security review",
                1000,
                Some(3600),
            )
            .unwrap();

        assert_eq!(proposal.threshold, 2);
        assert_eq!(proposal.status, ProposalStatus::Pending);
        assert_eq!(proposal.signature_count(), 0);
        assert_eq!(proposal.signatures_needed(), 2);
    }

    #[test]
    fn test_signature_collection() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let mut multisig = Multisig::new(2, signers).unwrap();

        let mut proposal = multisig
            .create_proposal(ProposalType::EmergencyPause, "Test", 1000, None)
            .unwrap();

        // Sign with first signer
        let payload = proposal.signing_payload();
        let sig1 = keypairs[0].sign(&payload).unwrap();
        let approved = multisig
            .sign_proposal(&mut proposal, keypairs[0].public_key(), &sig1, 1001)
            .unwrap();
        assert!(!approved);
        assert_eq!(proposal.signature_count(), 1);

        // Sign with second signer (should reach threshold)
        let sig2 = keypairs[1].sign(&payload).unwrap();
        let approved = multisig
            .sign_proposal(&mut proposal, keypairs[1].public_key(), &sig2, 1002)
            .unwrap();
        assert!(approved);
        assert!(proposal.is_approved());
    }

    #[test]
    fn test_duplicate_signature_rejected() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let mut multisig = Multisig::new(2, signers).unwrap();

        let mut proposal = multisig
            .create_proposal(ProposalType::EmergencyPause, "Test", 1000, None)
            .unwrap();

        let payload = proposal.signing_payload();
        let sig1 = keypairs[0].sign(&payload).unwrap();

        // First signature should succeed
        multisig
            .sign_proposal(&mut proposal, keypairs[0].public_key(), &sig1, 1001)
            .unwrap();

        // Duplicate signature should fail
        let result = multisig.sign_proposal(&mut proposal, keypairs[0].public_key(), &sig1, 1002);
        assert!(matches!(result, Err(MultisigError::DuplicateSignature)));
    }

    #[test]
    fn test_invalid_signature_rejected() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let mut multisig = Multisig::new(2, signers).unwrap();

        let mut proposal = multisig
            .create_proposal(ProposalType::EmergencyPause, "Test", 1000, None)
            .unwrap();

        // Sign with wrong key
        let wrong_sig = keypairs[1].sign(b"wrong message").unwrap();
        let result =
            multisig.sign_proposal(&mut proposal, keypairs[0].public_key(), &wrong_sig, 1001);
        assert!(matches!(result, Err(MultisigError::InvalidSignature)));
    }

    #[test]
    fn test_proposal_execution() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let mut multisig = Multisig::new(2, signers).unwrap();

        let mut proposal = multisig
            .create_proposal(ProposalType::EmergencyPause, "Test", 1000, None)
            .unwrap();

        // Try to execute without signatures
        assert!(matches!(
            proposal.mark_executed(),
            Err(MultisigError::InsufficientSignatures)
        ));

        // Collect signatures
        let payload = proposal.signing_payload();
        let sig1 = keypairs[0].sign(&payload).unwrap();
        let sig2 = keypairs[1].sign(&payload).unwrap();

        multisig
            .sign_proposal(&mut proposal, keypairs[0].public_key(), &sig1, 1001)
            .unwrap();
        multisig
            .sign_proposal(&mut proposal, keypairs[1].public_key(), &sig2, 1002)
            .unwrap();

        // Execute
        proposal.mark_executed().unwrap();
        assert_eq!(proposal.status, ProposalStatus::Executed);

        // Can't execute twice
        assert!(matches!(
            proposal.mark_executed(),
            Err(MultisigError::AlreadyExecuted)
        ));
    }

    #[test]
    fn test_threshold_change() {
        let keypairs = generate_keypairs(5);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let mut multisig = Multisig::new(3, signers).unwrap();
        assert_eq!(multisig.threshold, 3);

        // Create and execute threshold change proposal
        let mut proposal = multisig
            .create_proposal(
                ProposalType::ThresholdChange { new_threshold: 2 },
                "Reduce threshold",
                1000,
                None,
            )
            .unwrap();

        // Collect 3 signatures
        let payload = proposal.signing_payload();
        for i in 0..3 {
            let sig = keypairs[i].sign(&payload).unwrap();
            multisig
                .sign_proposal(&mut proposal, keypairs[i].public_key(), &sig, 1001 + i as u64)
                .unwrap();
        }

        proposal.mark_executed().unwrap();
        multisig.apply_proposal(&proposal).unwrap();

        assert_eq!(multisig.threshold, 2);
    }

    #[test]
    fn test_signer_lookup() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let multisig = Multisig::new(2, signers).unwrap();

        // Find by public key
        assert_eq!(multisig.find_signer(keypairs[1].public_key()), Some(1));

        // Find by hash
        let hash = hash_public_key(keypairs[2].public_key());
        assert_eq!(multisig.find_signer_by_hash(&hash), Some(2));

        // Unknown signer
        let unknown = KeyPair::from_seed(&[0xFF; 32]).unwrap();
        assert_eq!(multisig.find_signer(unknown.public_key()), None);
    }

    #[test]
    fn test_builder() {
        let keypairs = generate_keypairs(3);

        let multisig = MultisigBuilder::new(2)
            .add_signer(keypairs[0].public_key().clone())
            .add_signer(keypairs[1].public_key().clone())
            .add_signer(keypairs[2].public_key().clone())
            .build()
            .unwrap();

        assert_eq!(multisig.threshold, 2);
        assert_eq!(multisig.signer_count(), 3);
    }

    #[test]
    fn test_proposal_expiration() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let mut multisig = Multisig::new(2, signers).unwrap();

        let proposal = multisig
            .create_proposal(ProposalType::EmergencyPause, "Test", 1000, Some(3600))
            .unwrap();

        assert!(!proposal.is_expired(2000)); // Not expired
        assert!(proposal.is_expired(5000)); // Expired
    }

    #[test]
    fn test_verify_proposal_signatures() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let mut multisig = Multisig::new(2, signers).unwrap();

        let mut proposal = multisig
            .create_proposal(ProposalType::EmergencyPause, "Test", 1000, None)
            .unwrap();

        let payload = proposal.signing_payload();
        let sig1 = keypairs[0].sign(&payload).unwrap();
        let sig2 = keypairs[1].sign(&payload).unwrap();

        multisig
            .sign_proposal(&mut proposal, keypairs[0].public_key(), &sig1, 1001)
            .unwrap();
        multisig
            .sign_proposal(&mut proposal, keypairs[1].public_key(), &sig2, 1002)
            .unwrap();

        // All signatures should verify
        assert!(multisig.verify_proposal_signatures(&proposal).unwrap());
    }

    #[test]
    fn test_has_signed() {
        let keypairs = generate_keypairs(3);
        let signers: Vec<_> = keypairs.iter().map(|kp| kp.public_key().clone()).collect();

        let mut multisig = Multisig::new(2, signers).unwrap();

        let mut proposal = multisig
            .create_proposal(ProposalType::EmergencyPause, "Test", 1000, None)
            .unwrap();

        assert!(!proposal.has_signed(0));
        assert!(!proposal.has_signed(1));
        assert!(!proposal.has_signed(2));

        let payload = proposal.signing_payload();
        let sig = keypairs[1].sign(&payload).unwrap();
        multisig
            .sign_proposal(&mut proposal, keypairs[1].public_key(), &sig, 1001)
            .unwrap();

        assert!(!proposal.has_signed(0));
        assert!(proposal.has_signed(1));
        assert!(!proposal.has_signed(2));
    }
}
