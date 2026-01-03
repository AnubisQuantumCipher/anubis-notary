//! Marriage document schema for blockchain-anchored marriage contracts.
//!
//! This module provides types and functions for creating, signing, and verifying
//! marriage documents that can be anchored to the Starknet blockchain.
//!
//! ## Marriage Document Format (v1)
//!
//! ```text
//! {
//!   "v": 1,
//!   "type": "marriage",
//!   "parties": [
//!     {
//!       "name": "string",
//!       "public_key": bstr,
//!       "starknet_address": "string" (optional)
//!     }
//!   ],
//!   "terms": {
//!     "asset_split": "50/50" | "proportional" | "custom",
//!     "divorce_conditions": ["mutual_consent", ...],
//!     "custom_clauses": [...]
//!   },
//!   "witnesses": [...],
//!   "jurisdiction": "string",
//!   "created": int,
//!   "signatures": [bstr, ...]
//! }
//! ```
//!
//! ## Security Properties
//!
//! - **Multi-party consent**: All parties must sign before on-chain creation
//! - **Post-quantum signatures**: Uses ML-DSA-87 (FIPS 204)
//! - **Privacy**: Sensitive terms can be encrypted with ML-KEM-1024
//! - **Immutability**: Once anchored, records cannot be modified

use crate::cbor::{CborError, Encoder};
use crate::keccak::sha3_256;
use crate::mldsa::{MlDsaError, PublicKey, SecretKey, Signature};

/// Marriage document version number.
pub const MARRIAGE_VERSION: u8 = 1;

/// Maximum number of parties in a marriage (for gas efficiency).
pub const MAX_PARTIES: usize = 10;

/// Maximum number of witnesses.
pub const MAX_WITNESSES: usize = 5;

/// Maximum name length in bytes.
pub const MAX_NAME_LENGTH: usize = 128;

/// Maximum custom clause length in bytes.
pub const MAX_CLAUSE_LENGTH: usize = 1024;

/// Maximum number of custom clauses.
pub const MAX_CLAUSES: usize = 20;

/// Maximum CBOR encoding buffer size.
const MAX_CBOR_SIZE: usize = 64 * 1024; // 64 KiB

/// Starknet contract addresses for marriage system.
pub mod contracts {
    /// Marriage Oracle contract address on Sepolia testnet.
    pub const MARRIAGE_ORACLE_SEPOLIA: &str =
        "0x0457be1c094b09a3f27690388b8a4d70c908fec9b7de45bfb5d152488acd2181";

    /// Marriage Ring NFT contract address on Sepolia testnet.
    pub const MARRIAGE_RING_SEPOLIA: &str =
        "0x07f579e725cbd8dbac8974245d05824f1024bc0c041d98e0a6133dbd5cdc7090";

    /// Marriage Oracle contract address on Mainnet.
    pub const MARRIAGE_ORACLE_MAINNET: &str =
        "0x005d0a4cc5757e6d63dd6f7835c11a373af002e4c2603f040e2f5bf702a71ff8";

    /// Marriage Ring NFT contract address on Mainnet.
    pub const MARRIAGE_RING_MAINNET: &str =
        "0x00884842791e3542c42140d581edd7ab0327bf6ec276ca9d6201c9168c9f63d3";
}

/// Marriage error types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MarriageError {
    /// CBOR encoding/decoding error.
    Cbor(CborError),
    /// Signature error.
    Signature(MlDsaError),
    /// Invalid document version.
    InvalidVersion(u8),
    /// Too few parties (need at least 2).
    TooFewParties,
    /// Too many parties.
    TooManyParties,
    /// Party name too long.
    NameTooLong,
    /// Clause too long.
    ClauseTooLong,
    /// Too many clauses.
    TooManyClauses,
    /// Missing required signature.
    MissingSignature,
    /// Invalid signature.
    InvalidSignature,
    /// Signature verification failed.
    SignatureVerificationFailed,
    /// Party not found.
    PartyNotFound,
    /// Document not fully signed.
    NotFullySigned,
    /// Invalid asset split format.
    InvalidAssetSplit,
    /// Missing required field.
    MissingField(&'static str),
}

impl From<CborError> for MarriageError {
    fn from(e: CborError) -> Self {
        MarriageError::Cbor(e)
    }
}

impl From<MlDsaError> for MarriageError {
    fn from(e: MlDsaError) -> Self {
        MarriageError::Signature(e)
    }
}

impl core::fmt::Display for MarriageError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            MarriageError::Cbor(e) => write!(f, "CBOR error: {:?}", e),
            MarriageError::Signature(e) => write!(f, "Signature error: {:?}", e),
            MarriageError::InvalidVersion(v) => write!(f, "Invalid version: {}", v),
            MarriageError::TooFewParties => write!(f, "Need at least 2 parties"),
            MarriageError::TooManyParties => write!(f, "Too many parties (max {})", MAX_PARTIES),
            MarriageError::NameTooLong => {
                write!(f, "Name too long (max {} bytes)", MAX_NAME_LENGTH)
            }
            MarriageError::ClauseTooLong => {
                write!(f, "Clause too long (max {} bytes)", MAX_CLAUSE_LENGTH)
            }
            MarriageError::TooManyClauses => write!(f, "Too many clauses (max {})", MAX_CLAUSES),
            MarriageError::MissingSignature => write!(f, "Missing required signature"),
            MarriageError::InvalidSignature => write!(f, "Invalid signature format"),
            MarriageError::SignatureVerificationFailed => {
                write!(f, "Signature verification failed")
            }
            MarriageError::PartyNotFound => write!(f, "Party not found"),
            MarriageError::NotFullySigned => write!(f, "Document not fully signed by all parties"),
            MarriageError::InvalidAssetSplit => write!(f, "Invalid asset split format"),
            MarriageError::MissingField(field) => write!(f, "Missing required field: {}", field),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for MarriageError {}

/// Asset split configuration for divorce.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssetSplit {
    /// Equal 50/50 split.
    Equal,
    /// Proportional based on contribution.
    Proportional,
    /// Custom percentages per party.
    Custom(Vec<u8>), // Percentages for each party (must sum to 100)
}

impl Default for AssetSplit {
    fn default() -> Self {
        AssetSplit::Equal
    }
}

/// Divorce condition types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DivorceCondition {
    /// Mutual consent required from all parties.
    MutualConsent,
    /// Time-locked (minimum marriage duration before divorce).
    TimeLock {
        /// Minimum number of days before divorce is allowed.
        minimum_days: u32,
    },
    /// Threshold consent (M-of-N parties).
    Threshold {
        /// Number of parties required to agree to divorce.
        required: u8,
    },
    /// No-fault divorce allowed.
    NoFault,
    /// Custom condition with description.
    Custom(String),
}

/// Witness role in the marriage ceremony.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WitnessRole {
    /// Official who performs the ceremony.
    Officiant,
    /// General witness.
    Witness,
    /// Legal representative.
    Legal,
}

/// A party in the marriage contract.
#[derive(Clone)]
pub struct Party {
    /// Party's legal name.
    pub name: String,
    /// ML-DSA-87 public key for signing.
    pub public_key: PublicKey,
    /// Optional Starknet address for on-chain operations.
    pub starknet_address: Option<String>,
}

impl core::fmt::Debug for Party {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Party")
            .field("name", &self.name)
            .field("public_key", &"<PublicKey>")
            .field("starknet_address", &self.starknet_address)
            .finish()
    }
}

/// A witness to the marriage.
#[derive(Clone)]
pub struct Witness {
    /// Witness name.
    pub name: String,
    /// ML-DSA-87 public key.
    pub public_key: PublicKey,
    /// Role in the ceremony.
    pub role: WitnessRole,
}

impl core::fmt::Debug for Witness {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Witness")
            .field("name", &self.name)
            .field("public_key", &"<PublicKey>")
            .field("role", &self.role)
            .finish()
    }
}

/// Marriage terms and conditions.
#[derive(Debug, Clone, Default)]
pub struct MarriageTerms {
    /// Asset split on divorce.
    pub asset_split: AssetSplit,
    /// Conditions under which divorce is allowed.
    pub divorce_conditions: Vec<DivorceCondition>,
    /// Custom clauses (e.g., prenup terms).
    pub custom_clauses: Vec<String>,
}

/// Party signature on the marriage document.
#[derive(Clone)]
pub struct PartySignature {
    /// Index of the party in the parties array.
    pub party_index: usize,
    /// ML-DSA-87 signature.
    pub signature: Signature,
}

impl core::fmt::Debug for PartySignature {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PartySignature")
            .field("party_index", &self.party_index)
            .field("signature", &"<Signature>")
            .finish()
    }
}

/// Complete marriage document.
#[derive(Debug, Clone)]
pub struct MarriageDocument {
    /// Document version (currently 1).
    pub version: u8,
    /// Parties to the marriage (2-10).
    pub parties: Vec<Party>,
    /// Marriage terms.
    pub terms: MarriageTerms,
    /// Witnesses (optional).
    pub witnesses: Vec<Witness>,
    /// Jurisdiction (e.g., "US-CA", "UK").
    pub jurisdiction: String,
    /// Creation timestamp (seconds since UNIX epoch).
    pub created_at: u64,
    /// Signatures from parties.
    pub signatures: Vec<PartySignature>,
}

impl MarriageDocument {
    /// Create a new marriage document.
    ///
    /// # Arguments
    /// * `parties` - The parties to the marriage (2-10 required)
    /// * `terms` - Marriage terms and conditions
    /// * `jurisdiction` - Legal jurisdiction
    /// * `created_at` - Creation timestamp
    ///
    /// # Returns
    /// A new unsigned marriage document.
    pub fn new(
        parties: Vec<Party>,
        terms: MarriageTerms,
        jurisdiction: String,
        created_at: u64,
    ) -> Result<Self, MarriageError> {
        // Validate party count
        if parties.len() < 2 {
            return Err(MarriageError::TooFewParties);
        }
        if parties.len() > MAX_PARTIES {
            return Err(MarriageError::TooManyParties);
        }

        // Validate names
        for party in &parties {
            if party.name.len() > MAX_NAME_LENGTH {
                return Err(MarriageError::NameTooLong);
            }
        }

        // Validate clauses
        if terms.custom_clauses.len() > MAX_CLAUSES {
            return Err(MarriageError::TooManyClauses);
        }
        for clause in &terms.custom_clauses {
            if clause.len() > MAX_CLAUSE_LENGTH {
                return Err(MarriageError::ClauseTooLong);
            }
        }

        Ok(MarriageDocument {
            version: MARRIAGE_VERSION,
            parties,
            terms,
            witnesses: Vec::new(),
            jurisdiction,
            created_at,
            signatures: Vec::new(),
        })
    }

    /// Add a witness to the document.
    pub fn add_witness(&mut self, witness: Witness) -> Result<(), MarriageError> {
        if self.witnesses.len() >= MAX_WITNESSES {
            return Err(MarriageError::TooManyClauses); // Reusing error for witnesses limit
        }
        self.witnesses.push(witness);
        Ok(())
    }

    /// Get the document digest for signing.
    ///
    /// This computes SHA3-256 of the canonical CBOR encoding of the document
    /// (excluding signatures).
    pub fn signing_digest(&self) -> [u8; 32] {
        // Create a copy without signatures for hashing
        let unsigned = MarriageDocument {
            version: self.version,
            parties: self.parties.clone(),
            terms: self.terms.clone(),
            witnesses: self.witnesses.clone(),
            jurisdiction: self.jurisdiction.clone(),
            created_at: self.created_at,
            signatures: Vec::new(),
        };

        // Encode to CBOR and hash
        let cbor_data = encode_marriage_document(&unsigned);
        sha3_256(&cbor_data)
    }

    /// Sign the document as a party.
    ///
    /// # Arguments
    /// * `party_index` - Index of the signing party
    /// * `secret_key` - Party's ML-DSA-87 secret key
    pub fn sign(
        &mut self,
        party_index: usize,
        secret_key: &SecretKey,
    ) -> Result<(), MarriageError> {
        if party_index >= self.parties.len() {
            return Err(MarriageError::PartyNotFound);
        }

        // Check if already signed
        for sig in &self.signatures {
            if sig.party_index == party_index {
                return Ok(()); // Already signed
            }
        }

        // Compute digest and sign
        let digest = self.signing_digest();
        let signature = secret_key.sign(&digest)?;

        self.signatures.push(PartySignature {
            party_index,
            signature,
        });

        Ok(())
    }

    /// Verify all signatures.
    pub fn verify_signatures(&self) -> Result<bool, MarriageError> {
        let digest = self.signing_digest();

        for sig in &self.signatures {
            if sig.party_index >= self.parties.len() {
                return Err(MarriageError::PartyNotFound);
            }

            let party = &self.parties[sig.party_index];
            if !party.public_key.verify(&digest, &sig.signature) {
                return Err(MarriageError::SignatureVerificationFailed);
            }
        }

        Ok(true)
    }

    /// Check if the document is fully signed by all parties.
    pub fn is_fully_signed(&self) -> bool {
        if self.signatures.len() != self.parties.len() {
            return false;
        }

        // Verify all parties have signed
        for i in 0..self.parties.len() {
            if !self.signatures.iter().any(|s| s.party_index == i) {
                return false;
            }
        }

        true
    }

    /// Get the certificate hash for on-chain anchoring.
    ///
    /// Returns the SHA3-256 hash of the full signed document.
    pub fn certificate_hash(&self) -> Result<[u8; 32], MarriageError> {
        if !self.is_fully_signed() {
            return Err(MarriageError::NotFullySigned);
        }

        let cbor_data = encode_marriage_document(self);
        Ok(sha3_256(&cbor_data))
    }
}

/// Encode a marriage document to CBOR bytes.
fn encode_marriage_document(doc: &MarriageDocument) -> Vec<u8> {
    let mut buffer = vec![0u8; MAX_CBOR_SIZE];
    let mut encoder = Encoder::new(&mut buffer);

    // Start map with 7 fields
    let _ = encoder.encode_map_header(7);

    // version
    let _ = encoder.encode_text("v");
    let _ = encoder.encode_uint(doc.version as u64);

    // type
    let _ = encoder.encode_text("type");
    let _ = encoder.encode_text("marriage");

    // parties
    let _ = encoder.encode_text("parties");
    let _ = encoder.encode_array_header(doc.parties.len());
    for party in &doc.parties {
        let map_size = if party.starknet_address.is_some() {
            3
        } else {
            2
        };
        let _ = encoder.encode_map_header(map_size);
        let _ = encoder.encode_text("name");
        let _ = encoder.encode_text(&party.name);
        let _ = encoder.encode_text("pubkey");
        let _ = encoder.encode_bytes(&party.public_key.to_bytes());
        if let Some(addr) = &party.starknet_address {
            let _ = encoder.encode_text("starknet");
            let _ = encoder.encode_text(addr);
        }
    }

    // terms
    let _ = encoder.encode_text("terms");
    let _ = encoder.encode_map_header(3);
    let _ = encoder.encode_text("asset_split");
    match &doc.terms.asset_split {
        AssetSplit::Equal => {
            let _ = encoder.encode_text("50/50");
        }
        AssetSplit::Proportional => {
            let _ = encoder.encode_text("proportional");
        }
        AssetSplit::Custom(pcts) => {
            let _ = encoder.encode_array_header(pcts.len());
            for p in pcts {
                let _ = encoder.encode_uint(*p as u64);
            }
        }
    }
    let _ = encoder.encode_text("divorce");
    let _ = encoder.encode_array_header(doc.terms.divorce_conditions.len());
    for cond in &doc.terms.divorce_conditions {
        match cond {
            DivorceCondition::MutualConsent => {
                let _ = encoder.encode_text("mutual_consent");
            }
            DivorceCondition::NoFault => {
                let _ = encoder.encode_text("no_fault");
            }
            DivorceCondition::TimeLock { minimum_days } => {
                let _ = encoder.encode_map_header(1);
                let _ = encoder.encode_text("time_lock");
                let _ = encoder.encode_uint(*minimum_days as u64);
            }
            DivorceCondition::Threshold { required } => {
                let _ = encoder.encode_map_header(1);
                let _ = encoder.encode_text("threshold");
                let _ = encoder.encode_uint(*required as u64);
            }
            DivorceCondition::Custom(desc) => {
                let _ = encoder.encode_map_header(1);
                let _ = encoder.encode_text("custom");
                let _ = encoder.encode_text(desc);
            }
        }
    }
    let _ = encoder.encode_text("clauses");
    let _ = encoder.encode_array_header(doc.terms.custom_clauses.len());
    for clause in &doc.terms.custom_clauses {
        let _ = encoder.encode_text(clause);
    }

    // jurisdiction
    let _ = encoder.encode_text("jurisdiction");
    let _ = encoder.encode_text(&doc.jurisdiction);

    // created
    let _ = encoder.encode_text("created");
    let _ = encoder.encode_uint(doc.created_at);

    // signatures
    let _ = encoder.encode_text("signatures");
    let _ = encoder.encode_array_header(doc.signatures.len());
    for sig in &doc.signatures {
        let _ = encoder.encode_map_header(2);
        let _ = encoder.encode_text("party");
        let _ = encoder.encode_uint(sig.party_index as u64);
        let _ = encoder.encode_text("sig");
        let _ = encoder.encode_bytes(&sig.signature.to_bytes());
    }

    // Truncate to actual size and return
    let pos = encoder.position();
    buffer.truncate(pos);
    buffer
}

/// Divorce document for ending a marriage.
#[derive(Debug, Clone)]
pub struct DivorceDocument {
    /// Associated marriage document hash.
    pub marriage_hash: [u8; 32],
    /// Reason for divorce.
    pub reason: String,
    /// Parties agreeing to the divorce.
    pub agreeing_parties: Vec<usize>,
    /// Creation timestamp.
    pub created_at: u64,
    /// Signatures from agreeing parties.
    pub signatures: Vec<PartySignature>,
}

impl DivorceDocument {
    /// Create a new divorce document.
    pub fn new(marriage_hash: [u8; 32], reason: String, created_at: u64) -> Self {
        DivorceDocument {
            marriage_hash,
            reason,
            agreeing_parties: Vec::new(),
            created_at,
            signatures: Vec::new(),
        }
    }

    /// Get the divorce hash for on-chain anchoring.
    pub fn divorce_hash(&self) -> [u8; 32] {
        let mut data = Vec::new();
        data.extend_from_slice(&self.marriage_hash);
        data.extend_from_slice(self.reason.as_bytes());
        sha3_256(&data)
    }
}

/// Generate a new ML-DSA-87 keypair for marriage signing.
pub fn generate_keypair() -> Result<crate::mldsa::KeyPair, MlDsaError> {
    crate::mldsa::KeyPair::generate()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mldsa::KeyPair;

    #[test]
    fn test_create_marriage_document() {
        let keypair1 = KeyPair::generate().unwrap();
        let keypair2 = KeyPair::generate().unwrap();

        let parties = vec![
            Party {
                name: "Alice".to_string(),
                public_key: keypair1.public.clone(),
                starknet_address: Some("0x123".to_string()),
            },
            Party {
                name: "Bob".to_string(),
                public_key: keypair2.public.clone(),
                starknet_address: Some("0x456".to_string()),
            },
        ];

        let terms = MarriageTerms {
            asset_split: AssetSplit::Equal,
            divorce_conditions: vec![DivorceCondition::MutualConsent],
            custom_clauses: vec![],
        };

        let doc = MarriageDocument::new(parties, terms, "US-CA".to_string(), 1704067200).unwrap();

        assert_eq!(doc.version, 1);
        assert_eq!(doc.parties.len(), 2);
        assert!(!doc.is_fully_signed());
    }

    #[test]
    fn test_sign_marriage_document() {
        let keypair1 = KeyPair::generate().unwrap();
        let keypair2 = KeyPair::generate().unwrap();

        let parties = vec![
            Party {
                name: "Alice".to_string(),
                public_key: keypair1.public.clone(),
                starknet_address: None,
            },
            Party {
                name: "Bob".to_string(),
                public_key: keypair2.public.clone(),
                starknet_address: None,
            },
        ];

        let terms = MarriageTerms::default();
        let mut doc =
            MarriageDocument::new(parties, terms, "US-NY".to_string(), 1704067200).unwrap();

        // Sign by both parties
        doc.sign(0, keypair1.secret_key()).unwrap();
        doc.sign(1, keypair2.secret_key()).unwrap();

        assert!(doc.is_fully_signed());
        assert!(doc.verify_signatures().unwrap());

        // Get certificate hash
        let hash = doc.certificate_hash().unwrap();
        assert_eq!(hash.len(), 32);
    }

    #[test]
    fn test_too_few_parties() {
        let keypair = KeyPair::generate().unwrap();
        let parties = vec![Party {
            name: "Alice".to_string(),
            public_key: keypair.public.clone(),
            starknet_address: None,
        }];

        let result = MarriageDocument::new(parties, MarriageTerms::default(), "US".to_string(), 0);
        assert!(matches!(result, Err(MarriageError::TooFewParties)));
    }

    #[test]
    fn test_polygamy_three_parties() {
        let keypair1 = KeyPair::generate().unwrap();
        let keypair2 = KeyPair::generate().unwrap();
        let keypair3 = KeyPair::generate().unwrap();

        let parties = vec![
            Party {
                name: "Alice".to_string(),
                public_key: keypair1.public.clone(),
                starknet_address: None,
            },
            Party {
                name: "Bob".to_string(),
                public_key: keypair2.public.clone(),
                starknet_address: None,
            },
            Party {
                name: "Charlie".to_string(),
                public_key: keypair3.public.clone(),
                starknet_address: None,
            },
        ];

        let terms = MarriageTerms {
            asset_split: AssetSplit::Custom(vec![33, 33, 34]), // 33% + 33% + 34% = 100%
            divorce_conditions: vec![DivorceCondition::Threshold { required: 2 }],
            custom_clauses: vec![],
        };

        let mut doc = MarriageDocument::new(parties, terms, "NL".to_string(), 1704067200).unwrap();

        assert_eq!(doc.parties.len(), 3);

        // Sign by all parties
        doc.sign(0, keypair1.secret_key()).unwrap();
        doc.sign(1, keypair2.secret_key()).unwrap();
        doc.sign(2, keypair3.secret_key()).unwrap();

        assert!(doc.is_fully_signed());
        assert!(doc.verify_signatures().unwrap());
    }
}
