//! # anubis_core
//!
//! Production cryptographic core for Anubis Notary with formally verified dependencies.
//!
//! ## Formal Verification & Audit Status
//!
//! | Component | Status | Reference |
//! |-----------|--------|-----------|
//! | ChaCha20Poly1305 | **Formally Verified** | Cryspen libcrux (hax/F*) |
//! | SHA3/SHAKE256 | **Formally Verified** | Cryspen libcrux-sha3 (hax/F*) |
//! | HKDF | **Formally Verified** | Cryspen libcrux-hkdf (hax/F*) |
//! | ML-KEM-1024 | **Formally Verified** | Cryspen libcrux-ml-kem (hax/F*) |
//! | ML-DSA-87 | **Formally Verified** | Cryspen libcrux-ml-dsa (hax/F*) |
//! | subtle (CT ops) | **Quarkslab Audited** | dalek ecosystem |
//! | zeroize | **Mozilla/Google Audited** | secure memory clearing |
//! | CBOR (ciborium) | Production-proven | Google, AWS, Android |
//!
//! See `SECURITY.md` for full details.

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![warn(clippy::all)]

pub use subtle;
pub use zeroize;

/// Unified error types for consistent error handling
pub mod error;

/// Constant-time operations (mask select, cmov, equality) - uses audited `subtle` crate
pub mod ct;

/// Byte manipulation utilities (LE load/store, zeroize types)
pub mod bytes;

/// Keccak-f\[1600\] permutation, SHA3-256, SHAKE256
/// Enable `sha3-audited` feature for RustCrypto implementation
pub mod keccak;

/// AEAD encryption - ChaCha20Poly1305 (formally verified via libcrux)
pub mod aead;

/// Key derivation: HKDF(SHAKE256) and Argon2id parameter validation
pub mod kdf;

/// Deterministic nonce derivation with injectivity guarantees
pub mod nonce;

/// CBOR serialization
/// - `ciborium_wrapper`: Production-proven (Google, AWS, Android)
/// - Custom encoder: Strict canonical RFC 8949
pub mod cbor;

/// Receipt schema for file/directory attestation
pub mod receipt;

/// License schema for product/feature tokens
pub mod license;

/// Merkle tree for batch anchoring
pub mod merkle;

/// ML-DSA-87 (FIPS 204) post-quantum signatures
/// Status: Formally verified with hax/F* by Cryspen (libcrux-ml-dsa)
pub mod mldsa;

/// ML-KEM-1024 (FIPS 203) post-quantum key encapsulation
/// Status: Formally verified with hax/F* by Cryspen
pub mod mlkem;

/// Fault injection countermeasures
/// Provides redundant computation, result verification, and control flow integrity
pub mod fault;

/// Audit logging for security-critical operations
/// Provides tamper-evident hash-chained audit trail
pub mod audit;

/// Key recovery using Shamir's Secret Sharing
/// Enables (t,n) threshold recovery for password-protected keys
pub mod recovery;

/// Hardware Security Module (HSM) abstraction
/// Supports software, PKCS#11, and cloud HSM backends
pub mod hsm;

/// Multi-signature support for governance operations
/// Provides M-of-N threshold signatures and proposal voting
pub mod multisig;

/// Streaming interfaces for large files
/// Memory-efficient processing of large data with progress tracking
pub mod streaming;

/// Prelude with commonly used types
pub mod prelude {
    // Unified error type
    pub use crate::error::{CryptoError, CryptoResult};

    // AEAD - formally verified ChaCha20Poly1305 via libcrux
    pub use crate::aead::{AeadError, ChaCha20Poly1305};

    // Bytes and CT
    pub use crate::bytes::{SecretBytes, ZeroizeOnDrop};
    pub use crate::ct::{ct_eq, ct_select};

    // CBOR - production-proven ciborium
    pub use crate::cbor::{from_slice, to_vec, CiboriumError};
    pub use crate::cbor::{CborError, Decoder, Encoder};

    // KDF
    #[allow(deprecated)]
    pub use crate::kdf::{Argon2idParams, HkdfShake256, ValidatedArgon2idParams};

    // Hashing - formally verified via libcrux-sha3
    pub use crate::keccak::{sha3_256, shake256};

    // Receipts and Licenses
    pub use crate::license::{License, LicenseError};
    pub use crate::receipt::{Receipt, ReceiptError};

    // Merkle
    pub use crate::merkle::MerkleTree;

    // Post-Quantum Crypto - formally verified via libcrux
    pub use crate::mldsa::{KeyPair, MlDsaError, PublicKey, SecretKey, Signature};
    pub use crate::mlkem::{MlKemError, MlKemKeyPair, MlKemPublicKey, MlKemSecretKey};

    // Nonce derivation
    pub use crate::nonce::NonceDeriver;
    #[cfg(feature = "std")]
    pub use crate::nonce::PersistentNonceCounter;

    // Audit logging
    pub use crate::audit::{AuditEntry, AuditLogger, EventCategory, Severity};

    // Key recovery
    pub use crate::recovery::{RecoveryCoordinator, ShamirError, ShamirSharing, Share};

    // HSM support
    pub use crate::hsm::{HsmError, HsmProvider, KeyAttributes, KeyHandle, KeyType};

    // Multi-signature governance
    pub use crate::multisig::{
        Multisig, MultisigBuilder, MultisigError, Proposal, ProposalStatus, ProposalType,
    };

    // Streaming interfaces
    pub use crate::streaming::{
        ChunkedData, StreamingError, StreamingHasher, StreamingSigner, StreamingVerifier,
    };
}
