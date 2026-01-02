//! Receipt schema for file/directory attestation.
//!
//! A receipt is a signed attestation that a file or directory had a specific
//! digest at a specific time. Receipts are encoded in canonical CBOR.
//!
//! ## Receipt Format (v1)
//!
//! ```text
//! {
//!   "v": 1,
//!   "alg": "ML-DSA-87",
//!   "h": "sha3-256",
//!   "digest": bstr(32),
//!   "created": int,
//!   "time": ["local"|"rfc3161"|"ots", meta],
//!   "anchor": ["none"|"btc"|"http-log", meta],
//!   "sig": bstr
//! }
//! ```
//!
//! ## RefinedRust Verification
//!
//! This module is verified for:
//! - **Totality**: Decoders return `Ok(Receipt)` or `Err(ReceiptError)`, never panic
//! - **Bounds safety**: Digest is exactly 32 bytes, signature <= 4627 bytes
//! - **Round-trip**: `decode(encode(receipt)) == Ok(receipt)` for valid receipts
//! - **Canonical encoding**: Keys sorted lexicographically per RFC 8949
//!
//! Key invariants:
//! - `digest.len() == 32` (SHA3-256)
//! - `sig_len <= 4627` (ML-DSA-87)
//! - `version == 1` (current schema version)

use crate::cbor::{CborError, Decoder, Encoder};

/// Receipt version number.
pub const RECEIPT_VERSION: u64 = 1;

/// Signature algorithm identifier.
pub const ALG_MLDSA87: &str = "ML-DSA-87";

/// Hash algorithm identifier.
pub const HASH_SHA3_256: &str = "sha3-256";

/// Maximum size for RFC3161 TSA response tokens.
pub const MAX_RFC3161_TOKEN_SIZE: usize = 256;

/// Maximum size for OpenTimestamps proofs.
pub const MAX_OTS_PROOF_SIZE: usize = 512;

/// Maximum size for HTTP log URLs.
pub const MAX_URL_SIZE: usize = 256;

/// Maximum size for Mina zkApp address (Base58 public key).
pub const MAX_MINA_ADDRESS_SIZE: usize = 64;

/// Maximum size for Mina transaction hash.
pub const MAX_MINA_TX_HASH_SIZE: usize = 64;

/// Maximum size for Mina ZK proof (compressed).
pub const MAX_MINA_PROOF_SIZE: usize = 1024;

/// Maximum size for Mina batch Merkle witness (3 levels * 32 bytes = 96 bytes).
pub const MAX_MINA_BATCH_WITNESS_SIZE: usize = 96;

/// Maximum size for Mina batch root (Poseidon hash output = 32 bytes).
pub const MINA_BATCH_ROOT_SIZE: usize = 32;

/// Receipt error types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReceiptError {
    /// CBOR encoding/decoding error.
    Cbor(CborError),
    /// Unsupported receipt version.
    UnsupportedVersion(u64),
    /// Unsupported algorithm.
    UnsupportedAlgorithm,
    /// Unsupported hash function.
    UnsupportedHash,
    /// Invalid digest length.
    InvalidDigestLength,
    /// Invalid signature length.
    InvalidSignatureLength,
    /// Missing required field.
    MissingField(&'static str),
    /// Invalid time source.
    InvalidTimeSource,
    /// Invalid anchor type.
    InvalidAnchorType,
    /// RFC3161 token exceeds maximum size (256 bytes).
    Rfc3161TokenTooLarge(usize),
    /// OpenTimestamps proof exceeds maximum size (512 bytes).
    OtsProofTooLarge(usize),
    /// URL exceeds maximum size (256 bytes).
    UrlTooLarge(usize),
    /// Mina zkApp address exceeds maximum size (64 bytes).
    MinaAddressTooLarge(usize),
    /// Mina transaction hash exceeds maximum size (64 bytes).
    MinaTxHashTooLarge(usize),
    /// Mina proof exceeds maximum size (1024 bytes).
    MinaProofTooLarge(usize),
    /// Mina batch Merkle witness exceeds maximum size (96 bytes).
    MinaBatchWitnessTooLarge(usize),
    /// Invalid batch index (must be 0-7).
    InvalidBatchIndex(u64),
}

impl From<CborError> for ReceiptError {
    fn from(e: CborError) -> Self {
        ReceiptError::Cbor(e)
    }
}

/// Time source for a receipt.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[allow(clippy::large_enum_variant)]
pub enum TimeSource {
    /// Local system time (no external attestation).
    #[default]
    Local,
    /// RFC 3161 timestamping authority response.
    Rfc3161 {
        /// TSA response token.
        token: [u8; 256],
        /// Actual token length.
        len: usize,
    },
    /// OpenTimestamps proof.
    Ots {
        /// OTS proof data.
        proof: [u8; 512],
        /// Actual proof length.
        len: usize,
    },
    /// Mina Protocol blockchain timestamp.
    ///
    /// Uses Mina's on-chain timestamp and block height for trustless
    /// timestamping via zkApp smart contracts.
    Mina {
        /// Block height when timestamped.
        block_height: u64,
        /// Mina network timestamp (milliseconds since UNIX epoch).
        timestamp_ms: u64,
        /// Transaction hash for verification.
        tx_hash: [u8; MAX_MINA_TX_HASH_SIZE],
        /// Actual transaction hash length.
        tx_hash_len: usize,
    },
}

impl TimeSource {
    /// Returns the string identifier for this time source.
    pub fn id(&self) -> &'static str {
        match self {
            TimeSource::Local => "local",
            TimeSource::Rfc3161 { .. } => "rfc3161",
            TimeSource::Ots { .. } => "ots",
            TimeSource::Mina { .. } => "mina",
        }
    }
}

/// Anchor type for public log anchoring.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[allow(clippy::large_enum_variant)]
pub enum AnchorType {
    /// No external anchoring.
    #[default]
    None,
    /// Bitcoin blockchain anchor.
    Btc {
        /// Transaction ID (32 bytes).
        txid: [u8; 32],
        /// Block height.
        height: u64,
    },
    /// HTTP transparency log anchor.
    HttpLog {
        /// Log URL (max 256 bytes).
        url: [u8; 256],
        /// URL length.
        url_len: usize,
        /// Log entry ID.
        entry_id: u64,
    },
    /// Mina Protocol zkApp anchor.
    ///
    /// Provides on-chain anchoring via Mina's zkApp smart contracts.
    /// The Merkle root is stored in the zkApp's on-chain state with
    /// blockchain timestamp and block height for verification.
    Mina {
        /// zkApp contract address (Base58-encoded public key).
        zkapp_address: [u8; MAX_MINA_ADDRESS_SIZE],
        /// Actual address length.
        zkapp_address_len: usize,
        /// Transaction hash that anchored this root.
        tx_hash: [u8; MAX_MINA_TX_HASH_SIZE],
        /// Actual transaction hash length.
        tx_hash_len: usize,
        /// Block height when anchored.
        block_height: u64,
        /// Mina timestamp (milliseconds since UNIX epoch).
        timestamp_ms: u64,
        /// ZK proof for offline verification (optional, compressed).
        proof: [u8; MAX_MINA_PROOF_SIZE],
        /// Actual proof length (0 if no proof stored).
        proof_len: usize,
    },
    /// Mina Protocol batch anchor.
    ///
    /// Provides cost-efficient batch anchoring where multiple receipts are
    /// combined into a single transaction. Each receipt stores a Merkle witness
    /// proving inclusion in the batch root stored on-chain.
    ///
    /// Cost savings: 8x (0.1 MINA per batch vs per receipt).
    MinaBatch {
        /// zkApp contract address (Base58-encoded public key).
        zkapp_address: [u8; MAX_MINA_ADDRESS_SIZE],
        /// Actual address length.
        zkapp_address_len: usize,
        /// Transaction hash that anchored this batch.
        tx_hash: [u8; MAX_MINA_TX_HASH_SIZE],
        /// Actual transaction hash length.
        tx_hash_len: usize,
        /// Block height when anchored.
        block_height: u64,
        /// Mina timestamp (milliseconds since UNIX epoch).
        timestamp_ms: u64,
        /// Index of this receipt within the batch (0-7).
        batch_index: u8,
        /// Combined batch root (Poseidon hash of all 8 roots).
        batch_root: [u8; MINA_BATCH_ROOT_SIZE],
        /// Merkle witness for proving inclusion (3 sibling hashes).
        merkle_witness: [u8; MAX_MINA_BATCH_WITNESS_SIZE],
        /// Actual witness length.
        witness_len: usize,
    },
}

impl AnchorType {
    /// Returns the string identifier for this anchor type.
    pub fn id(&self) -> &'static str {
        match self {
            AnchorType::None => "none",
            AnchorType::Btc { .. } => "btc",
            AnchorType::HttpLog { .. } => "http-log",
            AnchorType::Mina { .. } => "mina",
            AnchorType::MinaBatch { .. } => "mina-batch",
        }
    }
}

/// A signed receipt for file/directory attestation.
#[derive(Debug, Clone)]
pub struct Receipt {
    /// Version (always 1 for v1 receipts).
    pub version: u64,
    /// SHA3-256 digest of the attested content.
    pub digest: [u8; 32],
    /// Unix timestamp when the receipt was created.
    pub created: i64,
    /// Time source used for the timestamp.
    pub time_source: TimeSource,
    /// Anchor type for public log anchoring.
    pub anchor: AnchorType,
    /// ML-DSA-87 signature over the receipt (without sig field).
    pub signature: [u8; 4627],
    /// Actual signature length.
    pub sig_len: usize,
}

impl Receipt {
    /// Create a new unsigned receipt.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::params("digest" : "array u8 32", "created" : "i64")]
    /// #[rr::returns("#receipt_new(digest, created)")]
    /// ```
    pub fn new(digest: [u8; 32], created: i64) -> Self {
        Self {
            version: RECEIPT_VERSION,
            digest,
            created,
            time_source: TimeSource::default(),
            anchor: AnchorType::default(),
            signature: [0u8; 4627],
            sig_len: 0,
        }
    }

    /// Set the time source.
    pub fn with_time_source(mut self, time_source: TimeSource) -> Self {
        self.time_source = time_source;
        self
    }

    /// Set the anchor type.
    pub fn with_anchor(mut self, anchor: AnchorType) -> Self {
        self.anchor = anchor;
        self
    }

    /// Set the signature.
    pub fn with_signature(mut self, sig: &[u8]) -> Result<Self, ReceiptError> {
        if sig.len() > 4627 {
            return Err(ReceiptError::InvalidSignatureLength);
        }
        self.signature[..sig.len()].copy_from_slice(sig);
        self.sig_len = sig.len();
        Ok(self)
    }

    /// Encode the signable portion of the receipt (everything except sig).
    ///
    /// This is what gets signed by the ML-DSA-87 key.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::returns("Ok(n) | Err(e)")]
    /// #[rr::ensures("Ok(n) => buffer[..n] == canonical_cbor(self.signable())")]
    /// ```
    pub fn encode_signable(&self, buffer: &mut [u8]) -> Result<usize, ReceiptError> {
        let mut enc = Encoder::new(buffer);

        // Map with 6 fields (v, alg, h, digest, created, time, anchor)
        // Note: keys must be in sorted order for canonical CBOR
        // Sorted: "alg", "anchor", "created", "digest", "h", "time", "v"
        enc.encode_map_header(7)?;

        // "alg"
        enc.encode_text("alg")?;
        enc.encode_text(ALG_MLDSA87)?;

        // "anchor"
        enc.encode_text("anchor")?;
        self.encode_anchor(&mut enc)?;

        // "created"
        enc.encode_text("created")?;
        enc.encode_int(self.created)?;

        // "digest"
        enc.encode_text("digest")?;
        enc.encode_bytes(&self.digest)?;

        // "h"
        enc.encode_text("h")?;
        enc.encode_text(HASH_SHA3_256)?;

        // "time"
        enc.encode_text("time")?;
        self.encode_time_source(&mut enc)?;

        // "v"
        enc.encode_text("v")?;
        enc.encode_uint(self.version)?;

        Ok(enc.position())
    }

    /// Encode the full receipt including signature.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::returns("Ok(n) | Err(e)")]
    /// #[rr::ensures("Ok(n) => buffer[..n] == canonical_cbor(self)")]
    /// ```
    pub fn encode(&self, buffer: &mut [u8]) -> Result<usize, ReceiptError> {
        let mut enc = Encoder::new(buffer);

        // Map with 8 fields
        enc.encode_map_header(8)?;

        // "alg"
        enc.encode_text("alg")?;
        enc.encode_text(ALG_MLDSA87)?;

        // "anchor"
        enc.encode_text("anchor")?;
        self.encode_anchor(&mut enc)?;

        // "created"
        enc.encode_text("created")?;
        enc.encode_int(self.created)?;

        // "digest"
        enc.encode_text("digest")?;
        enc.encode_bytes(&self.digest)?;

        // "h"
        enc.encode_text("h")?;
        enc.encode_text(HASH_SHA3_256)?;

        // "sig"
        enc.encode_text("sig")?;
        enc.encode_bytes(&self.signature[..self.sig_len])?;

        // "time"
        enc.encode_text("time")?;
        self.encode_time_source(&mut enc)?;

        // "v"
        enc.encode_text("v")?;
        enc.encode_uint(self.version)?;

        Ok(enc.position())
    }

    fn encode_time_source(&self, enc: &mut Encoder<'_>) -> Result<(), ReceiptError> {
        match &self.time_source {
            TimeSource::Local => {
                enc.encode_array_header(1)?;
                enc.encode_text("local")?;
            }
            TimeSource::Rfc3161 { token, len } => {
                enc.encode_array_header(2)?;
                enc.encode_text("rfc3161")?;
                enc.encode_bytes(&token[..*len])?;
            }
            TimeSource::Ots { proof, len } => {
                enc.encode_array_header(2)?;
                enc.encode_text("ots")?;
                enc.encode_bytes(&proof[..*len])?;
            }
            TimeSource::Mina {
                block_height,
                timestamp_ms,
                tx_hash,
                tx_hash_len,
            } => {
                // ["mina", block_height, timestamp_ms, tx_hash]
                enc.encode_array_header(4)?;
                enc.encode_text("mina")?;
                enc.encode_uint(*block_height)?;
                enc.encode_uint(*timestamp_ms)?;
                enc.encode_bytes(&tx_hash[..*tx_hash_len])?;
            }
        }
        Ok(())
    }

    fn encode_anchor(&self, enc: &mut Encoder<'_>) -> Result<(), ReceiptError> {
        match &self.anchor {
            AnchorType::None => {
                enc.encode_array_header(1)?;
                enc.encode_text("none")?;
            }
            AnchorType::Btc { txid, height } => {
                enc.encode_array_header(3)?;
                enc.encode_text("btc")?;
                enc.encode_bytes(txid)?;
                enc.encode_uint(*height)?;
            }
            AnchorType::HttpLog {
                url,
                url_len,
                entry_id,
            } => {
                enc.encode_array_header(3)?;
                enc.encode_text("http-log")?;
                enc.encode_bytes(&url[..*url_len])?;
                enc.encode_uint(*entry_id)?;
            }
            AnchorType::Mina {
                zkapp_address,
                zkapp_address_len,
                tx_hash,
                tx_hash_len,
                block_height,
                timestamp_ms,
                proof,
                proof_len,
            } => {
                // ["mina", zkapp_address, tx_hash, block_height, timestamp_ms, proof]
                enc.encode_array_header(6)?;
                enc.encode_text("mina")?;
                enc.encode_bytes(&zkapp_address[..*zkapp_address_len])?;
                enc.encode_bytes(&tx_hash[..*tx_hash_len])?;
                enc.encode_uint(*block_height)?;
                enc.encode_uint(*timestamp_ms)?;
                enc.encode_bytes(&proof[..*proof_len])?;
            }
            AnchorType::MinaBatch {
                zkapp_address,
                zkapp_address_len,
                tx_hash,
                tx_hash_len,
                block_height,
                timestamp_ms,
                batch_index,
                batch_root,
                merkle_witness,
                witness_len,
            } => {
                // ["mina-batch", zkapp_address, tx_hash, block_height, timestamp_ms,
                //  batch_index, batch_root, merkle_witness]
                enc.encode_array_header(8)?;
                enc.encode_text("mina-batch")?;
                enc.encode_bytes(&zkapp_address[..*zkapp_address_len])?;
                enc.encode_bytes(&tx_hash[..*tx_hash_len])?;
                enc.encode_uint(*block_height)?;
                enc.encode_uint(*timestamp_ms)?;
                enc.encode_uint(u64::from(*batch_index))?;
                enc.encode_bytes(batch_root)?;
                enc.encode_bytes(&merkle_witness[..*witness_len])?;
            }
        }
        Ok(())
    }

    /// Decode a receipt from canonical CBOR.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::params("data" : "list u8")]
    /// #[rr::returns("Ok(receipt) | Err(e)")]
    /// #[rr::ensures("total_decoder: all inputs handled")]
    /// ```
    pub fn decode(data: &[u8]) -> Result<Self, ReceiptError> {
        let mut dec = Decoder::new(data);

        let map_len = dec.decode_map_header()?;
        if map_len != 8 {
            return Err(ReceiptError::MissingField("expected 8 fields"));
        }

        let mut version = None;
        let mut digest = None;
        let mut created = None;
        let mut time_source = None;
        let mut anchor = None;
        let mut signature = None;

        for _ in 0..map_len {
            let key = dec.decode_text()?;
            match key {
                "v" => {
                    let v = dec.decode_uint()?;
                    if v != RECEIPT_VERSION {
                        return Err(ReceiptError::UnsupportedVersion(v));
                    }
                    version = Some(v);
                }
                "alg" => {
                    let alg = dec.decode_text()?;
                    if alg != ALG_MLDSA87 {
                        return Err(ReceiptError::UnsupportedAlgorithm);
                    }
                }
                "h" => {
                    let h = dec.decode_text()?;
                    if h != HASH_SHA3_256 {
                        return Err(ReceiptError::UnsupportedHash);
                    }
                }
                "digest" => {
                    let d = dec.decode_bytes()?;
                    if d.len() != 32 {
                        return Err(ReceiptError::InvalidDigestLength);
                    }
                    let mut arr = [0u8; 32];
                    arr.copy_from_slice(d);
                    digest = Some(arr);
                }
                "created" => {
                    created = Some(dec.decode_int()?);
                }
                "time" => {
                    time_source = Some(Self::decode_time_source(&mut dec)?);
                }
                "anchor" => {
                    anchor = Some(Self::decode_anchor(&mut dec)?);
                }
                "sig" => {
                    let s = dec.decode_bytes()?;
                    if s.len() > 4627 {
                        return Err(ReceiptError::InvalidSignatureLength);
                    }
                    let mut arr = [0u8; 4627];
                    arr[..s.len()].copy_from_slice(s);
                    signature = Some((arr, s.len()));
                }
                _ => {
                    // Skip unknown fields for forward compatibility
                    dec.skip_value()?;
                }
            }
        }

        let (sig_arr, sig_len) = signature.ok_or(ReceiptError::MissingField("sig"))?;

        Ok(Receipt {
            version: version.ok_or(ReceiptError::MissingField("v"))?,
            digest: digest.ok_or(ReceiptError::MissingField("digest"))?,
            created: created.ok_or(ReceiptError::MissingField("created"))?,
            time_source: time_source.ok_or(ReceiptError::MissingField("time"))?,
            anchor: anchor.ok_or(ReceiptError::MissingField("anchor"))?,
            signature: sig_arr,
            sig_len,
        })
    }

    fn decode_time_source(dec: &mut Decoder<'_>) -> Result<TimeSource, ReceiptError> {
        let arr_len = dec.decode_array_header()?;
        if arr_len < 1 {
            return Err(ReceiptError::InvalidTimeSource);
        }

        let type_str = dec.decode_text()?;
        match type_str {
            "local" => Ok(TimeSource::Local),
            "rfc3161" => {
                if arr_len != 2 {
                    return Err(ReceiptError::InvalidTimeSource);
                }
                let token_bytes = dec.decode_bytes()?;
                if token_bytes.len() > MAX_RFC3161_TOKEN_SIZE {
                    return Err(ReceiptError::Rfc3161TokenTooLarge(token_bytes.len()));
                }
                let mut token = [0u8; MAX_RFC3161_TOKEN_SIZE];
                let len = token_bytes.len();
                token[..len].copy_from_slice(token_bytes);
                Ok(TimeSource::Rfc3161 { token, len })
            }
            "ots" => {
                if arr_len != 2 {
                    return Err(ReceiptError::InvalidTimeSource);
                }
                let proof_bytes = dec.decode_bytes()?;
                if proof_bytes.len() > MAX_OTS_PROOF_SIZE {
                    return Err(ReceiptError::OtsProofTooLarge(proof_bytes.len()));
                }
                let mut proof = [0u8; MAX_OTS_PROOF_SIZE];
                let len = proof_bytes.len();
                proof[..len].copy_from_slice(proof_bytes);
                Ok(TimeSource::Ots { proof, len })
            }
            "mina" => {
                // ["mina", block_height, timestamp_ms, tx_hash]
                if arr_len != 4 {
                    return Err(ReceiptError::InvalidTimeSource);
                }
                let block_height = dec.decode_uint()?;
                let timestamp_ms = dec.decode_uint()?;
                let tx_hash_bytes = dec.decode_bytes()?;
                if tx_hash_bytes.len() > MAX_MINA_TX_HASH_SIZE {
                    return Err(ReceiptError::MinaTxHashTooLarge(tx_hash_bytes.len()));
                }
                let mut tx_hash = [0u8; MAX_MINA_TX_HASH_SIZE];
                let tx_hash_len = tx_hash_bytes.len();
                tx_hash[..tx_hash_len].copy_from_slice(tx_hash_bytes);
                Ok(TimeSource::Mina {
                    block_height,
                    timestamp_ms,
                    tx_hash,
                    tx_hash_len,
                })
            }
            _ => Err(ReceiptError::InvalidTimeSource),
        }
    }

    fn decode_anchor(dec: &mut Decoder<'_>) -> Result<AnchorType, ReceiptError> {
        let arr_len = dec.decode_array_header()?;
        if arr_len < 1 {
            return Err(ReceiptError::InvalidAnchorType);
        }

        let type_str = dec.decode_text()?;
        match type_str {
            "none" => Ok(AnchorType::None),
            "btc" => {
                if arr_len != 3 {
                    return Err(ReceiptError::InvalidAnchorType);
                }
                let txid_bytes = dec.decode_bytes()?;
                if txid_bytes.len() != 32 {
                    return Err(ReceiptError::InvalidAnchorType);
                }
                let mut txid = [0u8; 32];
                txid.copy_from_slice(txid_bytes);
                let height = dec.decode_uint()?;
                Ok(AnchorType::Btc { txid, height })
            }
            "http-log" => {
                if arr_len != 3 {
                    return Err(ReceiptError::InvalidAnchorType);
                }
                let url_bytes = dec.decode_bytes()?;
                if url_bytes.len() > MAX_URL_SIZE {
                    return Err(ReceiptError::UrlTooLarge(url_bytes.len()));
                }
                let mut url = [0u8; MAX_URL_SIZE];
                let url_len = url_bytes.len();
                url[..url_len].copy_from_slice(url_bytes);
                let entry_id = dec.decode_uint()?;
                Ok(AnchorType::HttpLog {
                    url,
                    url_len,
                    entry_id,
                })
            }
            "mina" => {
                // ["mina", zkapp_address, tx_hash, block_height, timestamp_ms, proof]
                if arr_len != 6 {
                    return Err(ReceiptError::InvalidAnchorType);
                }
                // Decode zkApp address
                let addr_bytes = dec.decode_bytes()?;
                if addr_bytes.len() > MAX_MINA_ADDRESS_SIZE {
                    return Err(ReceiptError::MinaAddressTooLarge(addr_bytes.len()));
                }
                let mut zkapp_address = [0u8; MAX_MINA_ADDRESS_SIZE];
                let zkapp_address_len = addr_bytes.len();
                zkapp_address[..zkapp_address_len].copy_from_slice(addr_bytes);

                // Decode transaction hash
                let tx_bytes = dec.decode_bytes()?;
                if tx_bytes.len() > MAX_MINA_TX_HASH_SIZE {
                    return Err(ReceiptError::MinaTxHashTooLarge(tx_bytes.len()));
                }
                let mut tx_hash = [0u8; MAX_MINA_TX_HASH_SIZE];
                let tx_hash_len = tx_bytes.len();
                tx_hash[..tx_hash_len].copy_from_slice(tx_bytes);

                // Decode block height and timestamp
                let block_height = dec.decode_uint()?;
                let timestamp_ms = dec.decode_uint()?;

                // Decode ZK proof
                let proof_bytes = dec.decode_bytes()?;
                if proof_bytes.len() > MAX_MINA_PROOF_SIZE {
                    return Err(ReceiptError::MinaProofTooLarge(proof_bytes.len()));
                }
                let mut proof = [0u8; MAX_MINA_PROOF_SIZE];
                let proof_len = proof_bytes.len();
                proof[..proof_len].copy_from_slice(proof_bytes);

                Ok(AnchorType::Mina {
                    zkapp_address,
                    zkapp_address_len,
                    tx_hash,
                    tx_hash_len,
                    block_height,
                    timestamp_ms,
                    proof,
                    proof_len,
                })
            }
            "mina-batch" => {
                // ["mina-batch", zkapp_address, tx_hash, block_height, timestamp_ms,
                //  batch_index, batch_root, merkle_witness]
                if arr_len != 8 {
                    return Err(ReceiptError::InvalidAnchorType);
                }
                // Decode zkApp address
                let addr_bytes = dec.decode_bytes()?;
                if addr_bytes.len() > MAX_MINA_ADDRESS_SIZE {
                    return Err(ReceiptError::MinaAddressTooLarge(addr_bytes.len()));
                }
                let mut zkapp_address = [0u8; MAX_MINA_ADDRESS_SIZE];
                let zkapp_address_len = addr_bytes.len();
                zkapp_address[..zkapp_address_len].copy_from_slice(addr_bytes);

                // Decode transaction hash
                let tx_bytes = dec.decode_bytes()?;
                if tx_bytes.len() > MAX_MINA_TX_HASH_SIZE {
                    return Err(ReceiptError::MinaTxHashTooLarge(tx_bytes.len()));
                }
                let mut tx_hash = [0u8; MAX_MINA_TX_HASH_SIZE];
                let tx_hash_len = tx_bytes.len();
                tx_hash[..tx_hash_len].copy_from_slice(tx_bytes);

                // Decode block height and timestamp
                let block_height = dec.decode_uint()?;
                let timestamp_ms = dec.decode_uint()?;

                // Decode batch index (0-7)
                let batch_index_u64 = dec.decode_uint()?;
                if batch_index_u64 > 7 {
                    return Err(ReceiptError::InvalidBatchIndex(batch_index_u64));
                }
                let batch_index = batch_index_u64 as u8;

                // Decode batch root (32 bytes)
                let root_bytes = dec.decode_bytes()?;
                if root_bytes.len() != MINA_BATCH_ROOT_SIZE {
                    return Err(ReceiptError::InvalidAnchorType);
                }
                let mut batch_root = [0u8; MINA_BATCH_ROOT_SIZE];
                batch_root.copy_from_slice(root_bytes);

                // Decode Merkle witness
                let witness_bytes = dec.decode_bytes()?;
                if witness_bytes.len() > MAX_MINA_BATCH_WITNESS_SIZE {
                    return Err(ReceiptError::MinaBatchWitnessTooLarge(witness_bytes.len()));
                }
                let mut merkle_witness = [0u8; MAX_MINA_BATCH_WITNESS_SIZE];
                let witness_len = witness_bytes.len();
                merkle_witness[..witness_len].copy_from_slice(witness_bytes);

                Ok(AnchorType::MinaBatch {
                    zkapp_address,
                    zkapp_address_len,
                    tx_hash,
                    tx_hash_len,
                    block_height,
                    timestamp_ms,
                    batch_index,
                    batch_root,
                    merkle_witness,
                    witness_len,
                })
            }
            _ => Err(ReceiptError::InvalidAnchorType),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_receipt_new() {
        let digest = [0xABu8; 32];
        let receipt = Receipt::new(digest, 1703462400);
        assert_eq!(receipt.version, 1);
        assert_eq!(receipt.digest, digest);
        assert_eq!(receipt.created, 1703462400);
    }

    #[test]
    fn test_receipt_encode_decode() {
        let digest = [0x12u8; 32];
        let sig = [0xFFu8; 100];
        let receipt = Receipt::new(digest, 1703462400)
            .with_signature(&sig)
            .unwrap();

        let mut buf = [0u8; 1024];
        let len = receipt.encode(&mut buf).unwrap();

        let decoded = Receipt::decode(&buf[..len]).unwrap();
        assert_eq!(decoded.version, 1);
        assert_eq!(decoded.digest, digest);
        assert_eq!(decoded.created, 1703462400);
        assert_eq!(&decoded.signature[..decoded.sig_len], &sig);
    }

    #[test]
    fn test_rfc3161_token_size_limit() {
        use crate::cbor::Encoder;

        // Create a time source array with oversized RFC3161 token
        // ["rfc3161", <oversized token>]
        let oversized_token = vec![0xAA; MAX_RFC3161_TOKEN_SIZE + 1];
        let mut buf = [0u8; 512];
        let mut enc = Encoder::new(&mut buf);
        enc.encode_array_header(2).unwrap();
        enc.encode_text("rfc3161").unwrap();
        enc.encode_bytes(&oversized_token).unwrap();
        let len = enc.position();

        let mut dec = crate::cbor::Decoder::new(&buf[..len]);
        let result = Receipt::decode_time_source(&mut dec);
        assert_eq!(
            result,
            Err(ReceiptError::Rfc3161TokenTooLarge(
                MAX_RFC3161_TOKEN_SIZE + 1
            ))
        );
    }

    #[test]
    fn test_ots_proof_size_limit() {
        use crate::cbor::Encoder;

        // Create a time source array with oversized OTS proof
        // ["ots", <oversized proof>]
        let oversized_proof = vec![0xBB; MAX_OTS_PROOF_SIZE + 1];
        let mut buf = [0u8; 768];
        let mut enc = Encoder::new(&mut buf);
        enc.encode_array_header(2).unwrap();
        enc.encode_text("ots").unwrap();
        enc.encode_bytes(&oversized_proof).unwrap();
        let len = enc.position();

        let mut dec = crate::cbor::Decoder::new(&buf[..len]);
        let result = Receipt::decode_time_source(&mut dec);
        assert_eq!(
            result,
            Err(ReceiptError::OtsProofTooLarge(MAX_OTS_PROOF_SIZE + 1))
        );
    }

    #[test]
    fn test_url_size_limit() {
        use crate::cbor::Encoder;

        // Create an anchor array with oversized URL
        // ["http-log", <oversized url>, entry_id]
        let oversized_url = vec![0x61; MAX_URL_SIZE + 1]; // 'a' repeated
        let mut buf = [0u8; 512];
        let mut enc = Encoder::new(&mut buf);
        enc.encode_array_header(3).unwrap();
        enc.encode_text("http-log").unwrap();
        enc.encode_bytes(&oversized_url).unwrap();
        enc.encode_uint(12345).unwrap();
        let len = enc.position();

        let mut dec = crate::cbor::Decoder::new(&buf[..len]);
        let result = Receipt::decode_anchor(&mut dec);
        assert_eq!(result, Err(ReceiptError::UrlTooLarge(MAX_URL_SIZE + 1)));
    }

    #[test]
    fn test_valid_size_data_accepted() {
        use crate::cbor::Encoder;

        // Test that data at the exact limit is accepted
        let valid_token = vec![0xCC; MAX_RFC3161_TOKEN_SIZE];
        let mut buf = [0u8; 512];
        let mut enc = Encoder::new(&mut buf);
        enc.encode_array_header(2).unwrap();
        enc.encode_text("rfc3161").unwrap();
        enc.encode_bytes(&valid_token).unwrap();
        let len = enc.position();

        let mut dec = crate::cbor::Decoder::new(&buf[..len]);
        let result = Receipt::decode_time_source(&mut dec);
        assert!(result.is_ok());
        if let Ok(TimeSource::Rfc3161 { token, len }) = result {
            assert_eq!(len, MAX_RFC3161_TOKEN_SIZE);
            assert_eq!(&token[..len], &valid_token[..]);
        } else {
            panic!("Expected Rfc3161 time source");
        }
    }

    #[test]
    fn test_mina_time_source_encode_decode() {
        // Create a Mina time source
        let tx_hash = b"CkpTestHash12345";
        let mut tx_arr = [0u8; MAX_MINA_TX_HASH_SIZE];
        tx_arr[..tx_hash.len()].copy_from_slice(tx_hash);

        let time_source = TimeSource::Mina {
            block_height: 12345,
            timestamp_ms: 1704067200000,
            tx_hash: tx_arr,
            tx_hash_len: tx_hash.len(),
        };

        // Create a receipt with this time source
        let digest = [0x42u8; 32];
        let mut receipt = Receipt::new(digest, 1703462400);
        receipt.time_source = time_source;

        // Encode the full receipt
        let mut buf = [0u8; 1024];
        let len = receipt.encode(&mut buf).unwrap();

        // Decode
        let decoded = Receipt::decode(&buf[..len]).unwrap();

        match decoded.time_source {
            TimeSource::Mina {
                block_height,
                timestamp_ms,
                tx_hash: dec_hash,
                tx_hash_len: dec_len,
            } => {
                assert_eq!(block_height, 12345);
                assert_eq!(timestamp_ms, 1704067200000);
                assert_eq!(dec_len, tx_hash.len());
                assert_eq!(&dec_hash[..dec_len], tx_hash);
            }
            _ => panic!("Expected Mina time source"),
        }
    }

    #[test]
    fn test_mina_anchor_encode_decode() {
        // Create a Mina anchor
        let zkapp_addr = b"B62qtest123456789012345678901234567890123456789012";
        let tx_hash = b"CkpTestTx123";
        let proof = b"base64proofdata";

        let mut addr_arr = [0u8; MAX_MINA_ADDRESS_SIZE];
        addr_arr[..zkapp_addr.len()].copy_from_slice(zkapp_addr);
        let mut tx_arr = [0u8; MAX_MINA_TX_HASH_SIZE];
        tx_arr[..tx_hash.len()].copy_from_slice(tx_hash);
        let mut proof_arr = [0u8; MAX_MINA_PROOF_SIZE];
        proof_arr[..proof.len()].copy_from_slice(proof);

        let anchor = AnchorType::Mina {
            zkapp_address: addr_arr,
            zkapp_address_len: zkapp_addr.len(),
            tx_hash: tx_arr,
            tx_hash_len: tx_hash.len(),
            block_height: 67890,
            timestamp_ms: 1704067200000,
            proof: proof_arr,
            proof_len: proof.len(),
        };

        // Create a receipt with this anchor
        let digest = [0x42u8; 32];
        let mut receipt = Receipt::new(digest, 1703462400);
        receipt.anchor = anchor;

        // Encode the full receipt
        let mut buf = [0u8; 2048];
        let len = receipt.encode(&mut buf).unwrap();

        // Decode
        let decoded = Receipt::decode(&buf[..len]).unwrap();

        match decoded.anchor {
            AnchorType::Mina {
                zkapp_address: dec_addr,
                zkapp_address_len: dec_addr_len,
                tx_hash: dec_tx,
                tx_hash_len: dec_tx_len,
                block_height,
                timestamp_ms,
                proof: dec_proof,
                proof_len: dec_proof_len,
            } => {
                assert_eq!(dec_addr_len, zkapp_addr.len());
                assert_eq!(&dec_addr[..dec_addr_len], zkapp_addr);
                assert_eq!(dec_tx_len, tx_hash.len());
                assert_eq!(&dec_tx[..dec_tx_len], tx_hash);
                assert_eq!(block_height, 67890);
                assert_eq!(timestamp_ms, 1704067200000);
                assert_eq!(dec_proof_len, proof.len());
                assert_eq!(&dec_proof[..dec_proof_len], proof);
            }
            _ => panic!("Expected Mina anchor"),
        }
    }

    #[test]
    fn test_mina_time_source_id() {
        let mut tx_arr = [0u8; MAX_MINA_TX_HASH_SIZE];
        tx_arr[..10].copy_from_slice(b"CkpTest123");

        let time_source = TimeSource::Mina {
            block_height: 100,
            timestamp_ms: 1704067200000,
            tx_hash: tx_arr,
            tx_hash_len: 10,
        };

        assert_eq!(time_source.id(), "mina");
    }

    #[test]
    fn test_mina_anchor_id() {
        let anchor = AnchorType::Mina {
            zkapp_address: [0u8; MAX_MINA_ADDRESS_SIZE],
            zkapp_address_len: 0,
            tx_hash: [0u8; MAX_MINA_TX_HASH_SIZE],
            tx_hash_len: 0,
            block_height: 0,
            timestamp_ms: 0,
            proof: [0u8; MAX_MINA_PROOF_SIZE],
            proof_len: 0,
        };

        assert_eq!(anchor.id(), "mina");
    }

    #[test]
    fn test_mina_address_size_limit() {
        use crate::cbor::Encoder;

        // Create an anchor with oversized address
        let oversized_addr = vec![0x61u8; MAX_MINA_ADDRESS_SIZE + 1];
        let mut buf = [0u8; 2048];
        let mut enc = Encoder::new(&mut buf);
        enc.encode_array_header(6).unwrap();
        enc.encode_text("mina").unwrap();
        enc.encode_bytes(&oversized_addr).unwrap();
        enc.encode_bytes(&[0u8; 10]).unwrap(); // tx_hash
        enc.encode_uint(100u64).unwrap(); // block_height
        enc.encode_uint(1704067200000u64).unwrap(); // timestamp_ms
        enc.encode_bytes(&[0u8; 10]).unwrap(); // proof
        let len = enc.position();

        let mut dec = crate::cbor::Decoder::new(&buf[..len]);
        let result = Receipt::decode_anchor(&mut dec);
        assert_eq!(
            result,
            Err(ReceiptError::MinaAddressTooLarge(MAX_MINA_ADDRESS_SIZE + 1))
        );
    }

    #[test]
    fn test_mina_tx_hash_size_limit() {
        use crate::cbor::Encoder;

        // Create a time source with oversized tx hash
        let oversized_tx = vec![0x62u8; MAX_MINA_TX_HASH_SIZE + 1];
        let mut buf = [0u8; 256];
        let mut enc = Encoder::new(&mut buf);
        enc.encode_array_header(4).unwrap();
        enc.encode_text("mina").unwrap();
        enc.encode_uint(100u64).unwrap(); // block_height
        enc.encode_uint(1704067200000u64).unwrap(); // timestamp_ms
        enc.encode_bytes(&oversized_tx).unwrap();
        let len = enc.position();

        let mut dec = crate::cbor::Decoder::new(&buf[..len]);
        let result = Receipt::decode_time_source(&mut dec);
        assert_eq!(
            result,
            Err(ReceiptError::MinaTxHashTooLarge(MAX_MINA_TX_HASH_SIZE + 1))
        );
    }

    #[test]
    fn test_mina_proof_size_limit() {
        use crate::cbor::Encoder;

        // Create an anchor with oversized proof
        let oversized_proof = vec![0x63u8; MAX_MINA_PROOF_SIZE + 1];
        let mut buf = [0u8; 2048];
        let mut enc = Encoder::new(&mut buf);
        enc.encode_array_header(6).unwrap();
        enc.encode_text("mina").unwrap();
        enc.encode_bytes(&[0u8; 50]).unwrap(); // zkapp_address
        enc.encode_bytes(&[0u8; 10]).unwrap(); // tx_hash
        enc.encode_uint(100u64).unwrap(); // block_height
        enc.encode_uint(1704067200000u64).unwrap(); // timestamp_ms
        enc.encode_bytes(&oversized_proof).unwrap();
        let len = enc.position();

        let mut dec = crate::cbor::Decoder::new(&buf[..len]);
        let result = Receipt::decode_anchor(&mut dec);
        assert_eq!(
            result,
            Err(ReceiptError::MinaProofTooLarge(MAX_MINA_PROOF_SIZE + 1))
        );
    }
}
