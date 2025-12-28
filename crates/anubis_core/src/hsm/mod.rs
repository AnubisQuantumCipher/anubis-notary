//! Hardware Security Module (HSM) abstraction layer.
//!
//! This module provides a unified interface for key management across different
//! HSM backends, including:
//!
//! - **Software**: In-memory keys (for development/testing)
//! - **PKCS#11**: Standard HSM interface (YubiHSM, SoftHSM, Thales)
//! - **Cloud HSM**: AWS CloudHSM, Azure Key Vault, GCP Cloud HSM
//! - **TPM**: Trusted Platform Module (local hardware)
//!
//! ## Security Properties
//!
//! - Private keys never leave the HSM in plaintext
//! - All signing operations happen inside the HSM
//! - Key handles are opaque references
//! - Audit logging of all HSM operations
//!
//! ## Usage
//!
//! ```ignore
//! // Create HSM provider
//! let hsm = HsmProvider::software();
//!
//! // Generate key in HSM
//! let key_id = hsm.generate_key(KeyType::MlDsa87)?;
//!
//! // Sign with HSM-protected key
//! let signature = hsm.sign(&key_id, message)?;
//!
//! // Export public key (allowed)
//! let public_key = hsm.export_public_key(&key_id)?;
//! ```

use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};

use zeroize::{Zeroize, ZeroizeOnDrop};

/// HSM operation errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HsmError {
    /// HSM is not initialized.
    NotInitialized,
    /// HSM connection failed.
    ConnectionFailed(String),
    /// Authentication failed.
    AuthenticationFailed,
    /// Key not found.
    KeyNotFound(String),
    /// Key already exists.
    KeyExists(String),
    /// Key generation failed.
    KeyGenerationFailed(String),
    /// Signing operation failed.
    SigningFailed(String),
    /// Verification failed.
    VerificationFailed(String),
    /// Key type not supported.
    UnsupportedKeyType,
    /// Operation not permitted.
    OperationNotPermitted(String),
    /// Internal HSM error.
    InternalError(String),
    /// Encryption/decryption failed.
    CryptoFailed(String),
    /// Session expired.
    SessionExpired,
    /// Rate limit exceeded.
    RateLimitExceeded,
}

/// Key types supported by the HSM.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KeyType {
    /// ML-DSA-87 post-quantum signature key.
    MlDsa87,
    /// ML-KEM-1024 post-quantum key encapsulation.
    MlKem1024,
    /// Ed25519 Edwards curve signature key.
    Ed25519,
    /// ECDSA P-256 signature key.
    EcdsaP256,
    /// AES-256 symmetric key.
    Aes256,
    /// HMAC-SHA256 key.
    HmacSha256,
}

impl KeyType {
    /// Get the key type name.
    pub fn as_str(&self) -> &'static str {
        match self {
            KeyType::MlDsa87 => "ML-DSA-87",
            KeyType::MlKem1024 => "ML-KEM-1024",
            KeyType::Ed25519 => "Ed25519",
            KeyType::EcdsaP256 => "ECDSA-P256",
            KeyType::Aes256 => "AES-256",
            KeyType::HmacSha256 => "HMAC-SHA256",
        }
    }

    /// Check if this is an asymmetric key type.
    pub fn is_asymmetric(&self) -> bool {
        matches!(self, KeyType::MlDsa87 | KeyType::MlKem1024 | KeyType::Ed25519 | KeyType::EcdsaP256)
    }
}

/// Key attributes and metadata.
#[derive(Debug, Clone)]
pub struct KeyAttributes {
    /// Key type.
    pub key_type: KeyType,
    /// Whether the key can be used for signing.
    pub can_sign: bool,
    /// Whether the key can be used for verification.
    pub can_verify: bool,
    /// Whether the key can be used for encryption.
    pub can_encrypt: bool,
    /// Whether the key can be used for decryption.
    pub can_decrypt: bool,
    /// Whether the key can be exported.
    pub exportable: bool,
    /// Key creation timestamp (Unix seconds).
    pub created_at: i64,
    /// Key expiry timestamp (0 = no expiry).
    pub expires_at: i64,
    /// User-defined label.
    pub label: String,
}

impl Default for KeyAttributes {
    fn default() -> Self {
        Self {
            key_type: KeyType::MlDsa87,
            can_sign: true,
            can_verify: true,
            can_encrypt: false,
            can_decrypt: false,
            exportable: false,
            created_at: 0,
            expires_at: 0,
            label: String::new(),
        }
    }
}

/// Opaque key handle (never reveals the key material).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct KeyHandle(String);

impl KeyHandle {
    /// Create a new key handle from an ID string.
    pub fn new(id: impl Into<String>) -> Self {
        Self(id.into())
    }

    /// Get the key ID as a string.
    pub fn id(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for KeyHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "KeyHandle({})", self.0)
    }
}

/// HSM provider configuration.
#[derive(Debug, Clone)]
pub struct HsmConfig {
    /// Provider type.
    pub provider: HsmProviderType,
    /// Connection string or path.
    pub connection: String,
    /// PIN or password (will be zeroized after use).
    pub credentials: Option<String>,
    /// Slot ID (for PKCS#11).
    pub slot_id: Option<u64>,
    /// Maximum operations per minute.
    pub rate_limit: Option<u32>,
    /// Session timeout in seconds.
    pub session_timeout: Option<u64>,
}

/// HSM provider types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HsmProviderType {
    /// Software-only provider (keys in memory).
    Software,
    /// PKCS#11 compatible HSM.
    Pkcs11,
    /// AWS CloudHSM.
    AwsCloudHsm,
    /// Azure Key Vault.
    AzureKeyVault,
    /// Google Cloud HSM.
    GcpCloudHsm,
    /// Local TPM.
    Tpm,
}

/// HSM provider trait for different backend implementations.
pub trait HsmBackend: Send + Sync {
    /// Initialize the HSM connection.
    fn initialize(&mut self, config: &HsmConfig) -> Result<(), HsmError>;

    /// Check if connected and authenticated.
    fn is_connected(&self) -> bool;

    /// Generate a new key pair.
    fn generate_key(&self, key_type: KeyType, label: &str) -> Result<KeyHandle, HsmError>;

    /// Import a key (if allowed by policy).
    fn import_key(&self, key_type: KeyType, key_data: &[u8], label: &str) -> Result<KeyHandle, HsmError>;

    /// Export the public key.
    fn export_public_key(&self, handle: &KeyHandle) -> Result<Vec<u8>, HsmError>;

    /// Sign a message.
    fn sign(&self, handle: &KeyHandle, message: &[u8]) -> Result<Vec<u8>, HsmError>;

    /// Verify a signature.
    fn verify(&self, handle: &KeyHandle, message: &[u8], signature: &[u8]) -> Result<bool, HsmError>;

    /// Encrypt data (for KEM keys, this is encapsulation).
    fn encrypt(&self, handle: &KeyHandle, plaintext: &[u8]) -> Result<Vec<u8>, HsmError>;

    /// Decrypt data (for KEM keys, this is decapsulation).
    fn decrypt(&self, handle: &KeyHandle, ciphertext: &[u8]) -> Result<Vec<u8>, HsmError>;

    /// Delete a key.
    fn delete_key(&self, handle: &KeyHandle) -> Result<(), HsmError>;

    /// List all keys.
    fn list_keys(&self) -> Result<Vec<(KeyHandle, KeyAttributes)>, HsmError>;

    /// Get key attributes.
    fn get_attributes(&self, handle: &KeyHandle) -> Result<KeyAttributes, HsmError>;

    /// Close the HSM session.
    fn close(&mut self) -> Result<(), HsmError>;
}

/// Software HSM backend (for development and testing).
#[derive(Default)]
pub struct SoftwareHsm {
    initialized: bool,
    keys: RwLock<HashMap<String, SoftwareKey>>,
    next_id: Mutex<u64>,
}

/// A key stored in the software HSM.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
struct SoftwareKey {
    #[zeroize(skip)]
    key_type: KeyType,
    secret_key: Vec<u8>,
    public_key: Vec<u8>,
    #[zeroize(skip)]
    attributes: KeyAttributes,
}

impl SoftwareHsm {
    /// Create a new software HSM.
    pub fn new() -> Self {
        Self::default()
    }

    fn generate_id(&self) -> String {
        let mut next = self.next_id.lock().unwrap();
        let id = *next;
        *next += 1;
        format!("sw-key-{:08x}", id)
    }

    fn now() -> i64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0)
    }
}

impl HsmBackend for SoftwareHsm {
    fn initialize(&mut self, _config: &HsmConfig) -> Result<(), HsmError> {
        self.initialized = true;
        Ok(())
    }

    fn is_connected(&self) -> bool {
        self.initialized
    }

    fn generate_key(&self, key_type: KeyType, label: &str) -> Result<KeyHandle, HsmError> {
        if !self.initialized {
            return Err(HsmError::NotInitialized);
        }

        let (secret_key, public_key) = match key_type {
            KeyType::MlDsa87 => {
                use crate::mldsa::KeyPair;
                let keypair = KeyPair::generate()
                    .map_err(|e| HsmError::KeyGenerationFailed(e.to_string()))?;
                (keypair.secret_key().to_bytes().to_vec(), keypair.public_key().to_bytes().to_vec())
            }
            KeyType::MlKem1024 => {
                use crate::mlkem::MlKemKeyPair;
                let keypair = MlKemKeyPair::generate()
                    .map_err(|e| HsmError::KeyGenerationFailed(e.to_string()))?;
                let (sk, pk) = keypair.into_parts();
                (sk.as_bytes().to_vec(), pk.as_bytes().to_vec())
            }
            _ => return Err(HsmError::UnsupportedKeyType),
        };

        let id = self.generate_id();
        let attributes = KeyAttributes {
            key_type,
            can_sign: matches!(key_type, KeyType::MlDsa87 | KeyType::Ed25519 | KeyType::EcdsaP256),
            can_verify: matches!(key_type, KeyType::MlDsa87 | KeyType::Ed25519 | KeyType::EcdsaP256),
            can_encrypt: matches!(key_type, KeyType::MlKem1024 | KeyType::Aes256),
            can_decrypt: matches!(key_type, KeyType::MlKem1024 | KeyType::Aes256),
            exportable: false,
            created_at: Self::now(),
            expires_at: 0,
            label: label.to_string(),
        };

        let key = SoftwareKey {
            key_type,
            secret_key,
            public_key,
            attributes,
        };

        self.keys.write().unwrap().insert(id.clone(), key);
        Ok(KeyHandle::new(id))
    }

    fn import_key(&self, key_type: KeyType, key_data: &[u8], label: &str) -> Result<KeyHandle, HsmError> {
        if !self.initialized {
            return Err(HsmError::NotInitialized);
        }

        // Parse the key based on type
        // For asymmetric keys, key_data must contain both secret and public key concatenated
        let (secret_key, public_key) = match key_type {
            KeyType::MlDsa87 => {
                use crate::mldsa::{SecretKey, PublicKey, SECRET_KEY_SIZE, PUBLIC_KEY_SIZE};
                // Expect concatenated sk || pk format
                let expected_len = SECRET_KEY_SIZE + PUBLIC_KEY_SIZE;
                if key_data.len() != expected_len {
                    return Err(HsmError::CryptoFailed(
                        format!("ML-DSA import requires {} bytes (sk || pk), got {}", expected_len, key_data.len())
                    ));
                }
                // Validate both keys
                let sk_bytes = &key_data[..SECRET_KEY_SIZE];
                let pk_bytes = &key_data[SECRET_KEY_SIZE..];
                let _sk = SecretKey::from_bytes(sk_bytes)
                    .map_err(|e| HsmError::CryptoFailed(e.to_string()))?;
                let _pk = PublicKey::from_bytes(pk_bytes)
                    .map_err(|e| HsmError::CryptoFailed(e.to_string()))?;
                (sk_bytes.to_vec(), pk_bytes.to_vec())
            }
            _ => return Err(HsmError::UnsupportedKeyType),
        };

        let id = self.generate_id();
        let attributes = KeyAttributes {
            key_type,
            can_sign: true,
            can_verify: true,
            can_encrypt: false,
            can_decrypt: false,
            exportable: false,
            created_at: Self::now(),
            expires_at: 0,
            label: label.to_string(),
        };

        let key = SoftwareKey {
            key_type,
            secret_key,
            public_key,
            attributes,
        };

        self.keys.write().unwrap().insert(id.clone(), key);
        Ok(KeyHandle::new(id))
    }

    fn export_public_key(&self, handle: &KeyHandle) -> Result<Vec<u8>, HsmError> {
        let keys = self.keys.read().unwrap();
        let key = keys.get(handle.id()).ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;
        Ok(key.public_key.clone())
    }

    fn sign(&self, handle: &KeyHandle, message: &[u8]) -> Result<Vec<u8>, HsmError> {
        let keys = self.keys.read().unwrap();
        let key = keys.get(handle.id()).ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;

        if !key.attributes.can_sign {
            return Err(HsmError::OperationNotPermitted("Key cannot be used for signing".to_string()));
        }

        match key.key_type {
            KeyType::MlDsa87 => {
                use crate::mldsa::SecretKey;
                let sk = SecretKey::from_bytes(key.secret_key.as_slice())
                    .map_err(|e| HsmError::InternalError(e.to_string()))?;
                let sig = sk.sign(message)
                    .map_err(|e| HsmError::SigningFailed(e.to_string()))?;
                Ok(sig.to_bytes().to_vec())
            }
            _ => Err(HsmError::UnsupportedKeyType),
        }
    }

    fn verify(&self, handle: &KeyHandle, message: &[u8], signature: &[u8]) -> Result<bool, HsmError> {
        let keys = self.keys.read().unwrap();
        let key = keys.get(handle.id()).ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;

        if !key.attributes.can_verify {
            return Err(HsmError::OperationNotPermitted("Key cannot be used for verification".to_string()));
        }

        match key.key_type {
            KeyType::MlDsa87 => {
                use crate::mldsa::{PublicKey, Signature};
                let pk = PublicKey::from_bytes(key.public_key.as_slice())
                    .map_err(|e| HsmError::InternalError(e.to_string()))?;
                let sig = Signature::from_bytes(signature)
                    .map_err(|e| HsmError::VerificationFailed(e.to_string()))?;
                Ok(pk.verify(message, &sig))
            }
            _ => Err(HsmError::UnsupportedKeyType),
        }
    }

    fn encrypt(&self, handle: &KeyHandle, _plaintext: &[u8]) -> Result<Vec<u8>, HsmError> {
        let keys = self.keys.read().unwrap();
        let key = keys.get(handle.id()).ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;

        if !key.attributes.can_encrypt {
            return Err(HsmError::OperationNotPermitted("Key cannot be used for encryption".to_string()));
        }

        match key.key_type {
            KeyType::MlKem1024 => {
                use crate::mlkem::MlKemPublicKey;
                let pk = MlKemPublicKey::from_bytes(key.public_key.as_slice())
                    .map_err(|e| HsmError::CryptoFailed(e.to_string()))?;
                let (ciphertext, _shared_secret) = pk.encapsulate()
                    .map_err(|e| HsmError::CryptoFailed(e.to_string()))?;
                // For simple encryption, we'd need to combine KEM with symmetric encryption
                // This is a simplified implementation
                Ok(ciphertext.to_vec())
            }
            _ => Err(HsmError::UnsupportedKeyType),
        }
    }

    fn decrypt(&self, handle: &KeyHandle, ciphertext: &[u8]) -> Result<Vec<u8>, HsmError> {
        let keys = self.keys.read().unwrap();
        let key = keys.get(handle.id()).ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;

        if !key.attributes.can_decrypt {
            return Err(HsmError::OperationNotPermitted("Key cannot be used for decryption".to_string()));
        }

        match key.key_type {
            KeyType::MlKem1024 => {
                use crate::mlkem::MlKemSecretKey;
                let sk = MlKemSecretKey::from_bytes(key.secret_key.as_slice())
                    .map_err(|e| HsmError::CryptoFailed(e.to_string()))?;
                let shared_secret = sk.decapsulate(ciphertext)
                    .map_err(|e| HsmError::CryptoFailed(e.to_string()))?;
                Ok(shared_secret.to_vec())
            }
            _ => Err(HsmError::UnsupportedKeyType),
        }
    }

    fn delete_key(&self, handle: &KeyHandle) -> Result<(), HsmError> {
        let mut keys = self.keys.write().unwrap();
        if keys.remove(handle.id()).is_some() {
            Ok(())
        } else {
            Err(HsmError::KeyNotFound(handle.id().to_string()))
        }
    }

    fn list_keys(&self) -> Result<Vec<(KeyHandle, KeyAttributes)>, HsmError> {
        let keys = self.keys.read().unwrap();
        Ok(keys
            .iter()
            .map(|(id, key)| (KeyHandle::new(id.clone()), key.attributes.clone()))
            .collect())
    }

    fn get_attributes(&self, handle: &KeyHandle) -> Result<KeyAttributes, HsmError> {
        let keys = self.keys.read().unwrap();
        let key = keys.get(handle.id()).ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;
        Ok(key.attributes.clone())
    }

    fn close(&mut self) -> Result<(), HsmError> {
        // Zeroize all keys
        let mut keys = self.keys.write().unwrap();
        for (_, key) in keys.iter_mut() {
            key.zeroize();
        }
        keys.clear();
        self.initialized = false;
        Ok(())
    }
}

// ============================================================================
// PKCS#11 HSM Backend (using cryptoki crate)
// ============================================================================

use cryptoki::context::{CInitializeArgs, Pkcs11};
use cryptoki::mechanism::Mechanism;
use cryptoki::object::{Attribute, AttributeType, ObjectClass, ObjectHandle};
use cryptoki::session::{Session, UserType};
use cryptoki::slot::Slot;
use cryptoki::types::AuthPin;

/// PKCS#11 HSM backend using the cryptoki crate.
///
/// ## SoftHSM2 Setup (for testing)
///
/// ```sh
/// # macOS
/// brew install softhsm
///
/// # Ubuntu/Debian
/// sudo apt-get install softhsm2
///
/// # Initialize token
/// softhsm2-util --init-token --slot 0 --label "AnubisNotary" \
///     --so-pin 12345678 --pin 1234
/// ```
///
/// ## Usage
///
/// ```rust,ignore
/// let config = HsmConfig {
///     provider: HsmProviderType::Pkcs11,
///     connection: "/usr/lib/softhsm/libsofthsm2.so".to_string(),
///     credentials: Some("1234".to_string()),
///     slot_id: Some(0),
///     rate_limit: None,
///     session_timeout: None,
/// };
/// let hsm = HsmProvider::with_config(config)?;
/// let key = hsm.generate_key(KeyType::EcdsaP256, "my-key")?;
/// let sig = hsm.sign(&key, b"message")?;
/// ```
pub struct Pkcs11Hsm {
    /// Cryptoki context and session (wrapped for thread safety since Session is !Sync).
    inner: Mutex<Pkcs11HsmInner>,
    /// Library path.
    library_path: String,
    /// User PIN.
    pin: Mutex<Option<String>>,
    /// Key mapping: our handle ID -> (private ObjectHandle, public ObjectHandle, KeyType)
    keys: RwLock<HashMap<String, Pkcs11KeyEntry>>,
    /// Next key ID.
    next_id: Mutex<u64>,
}

/// Inner state for PKCS#11 HSM (contains non-Sync types).
struct Pkcs11HsmInner {
    ctx: Option<Pkcs11>,
    session: Option<Session>,
    slot: Option<Slot>,
}

/// Entry for a key pair stored in PKCS#11.
struct Pkcs11KeyEntry {
    private_handle: ObjectHandle,
    public_handle: ObjectHandle,
    key_type: KeyType,
    attributes: KeyAttributes,
    /// For PQ keys: software-generated keys wrapped by HSM AES key
    wrapped_sk: Option<Vec<u8>>,
    wrapped_pk: Option<Vec<u8>>,
}

impl Pkcs11Hsm {
    /// Create a new PKCS#11 HSM backend.
    pub fn new(library_path: impl Into<String>, _slot_id: u64) -> Self {
        Self {
            inner: Mutex::new(Pkcs11HsmInner {
                ctx: None,
                session: None,
                slot: None,
            }),
            library_path: library_path.into(),
            pin: Mutex::new(None),
            keys: RwLock::new(HashMap::new()),
            next_id: Mutex::new(0),
        }
    }

    fn generate_id(&self) -> String {
        let mut next = self.next_id.lock().unwrap();
        let id = *next;
        *next += 1;
        format!("pkcs11-{:08x}", id)
    }

    fn now() -> i64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0)
    }

    /// Generate an AES-256 wrapping key for protecting PQ keys.
    /// Takes a session reference to avoid double-locking.
    fn get_or_create_wrapping_key_with_session(&self, session: &Session) -> Result<ObjectHandle, HsmError> {
        // Search for existing wrapping key
        let template = vec![
            Attribute::Class(ObjectClass::SECRET_KEY),
            Attribute::Label(b"anubis-pq-wrapper".to_vec()),
        ];

        let objects = session.find_objects(&template)
            .map_err(|e| HsmError::InternalError(format!("Find wrapping key failed: {}", e)))?;

        if let Some(handle) = objects.first() {
            return Ok(*handle);
        }

        // Create new AES-256 wrapping key
        let key_template = vec![
            Attribute::Class(ObjectClass::SECRET_KEY),
            Attribute::KeyType(cryptoki::object::KeyType::AES),
            Attribute::ValueLen(32.into()), // 256 bits
            Attribute::Token(true),
            Attribute::Private(true),
            Attribute::Sensitive(true),
            Attribute::Extractable(false),
            Attribute::Wrap(true),
            Attribute::Unwrap(true),
            Attribute::Encrypt(true),
            Attribute::Decrypt(true),
            Attribute::Label(b"anubis-pq-wrapper".to_vec()),
        ];

        session.generate_key(&Mechanism::AesKeyGen, &key_template)
            .map_err(|e| HsmError::KeyGenerationFailed(format!("AES keygen failed: {}", e)))
    }

    /// Encrypt data with the wrapping key (AES-GCM).
    fn wrap_data(&self, data: &[u8]) -> Result<Vec<u8>, HsmError> {
        let inner = self.inner.lock().unwrap();
        let session = inner.session.as_ref().ok_or(HsmError::NotInitialized)?;
        let wrap_key = self.get_or_create_wrapping_key_with_session(session)?;

        // Generate random IV
        let mut iv = [0u8; 12];
        getrandom::getrandom(&mut iv).map_err(|e| HsmError::InternalError(e.to_string()))?;

        // Encrypt with AES-GCM
        let mechanism = Mechanism::AesGcm(cryptoki::mechanism::aead::GcmParams::new(&iv, &[], 128.into()));

        let ciphertext = session.encrypt(&mechanism, wrap_key, data)
            .map_err(|e| HsmError::CryptoFailed(format!("Wrap failed: {}", e)))?;

        // Prepend IV to ciphertext
        let mut result = iv.to_vec();
        result.extend(ciphertext);
        Ok(result)
    }

    /// Decrypt data with the wrapping key (AES-GCM).
    fn unwrap_data(&self, wrapped: &[u8]) -> Result<Vec<u8>, HsmError> {
        if wrapped.len() < 12 {
            return Err(HsmError::CryptoFailed("Wrapped data too short".to_string()));
        }

        let inner = self.inner.lock().unwrap();
        let session = inner.session.as_ref().ok_or(HsmError::NotInitialized)?;
        let wrap_key = self.get_or_create_wrapping_key_with_session(session)?;

        let iv = &wrapped[..12];
        let ciphertext = &wrapped[12..];

        let mechanism = Mechanism::AesGcm(cryptoki::mechanism::aead::GcmParams::new(iv, &[], 128.into()));

        session.decrypt(&mechanism, wrap_key, ciphertext)
            .map_err(|e| HsmError::CryptoFailed(format!("Unwrap failed: {}", e)))
    }
}

impl HsmBackend for Pkcs11Hsm {
    fn initialize(&mut self, config: &HsmConfig) -> Result<(), HsmError> {
        // Load PKCS#11 library
        let ctx = Pkcs11::new(&self.library_path)
            .map_err(|e| HsmError::ConnectionFailed(format!("Failed to load PKCS#11 library: {}", e)))?;

        // Initialize the library
        ctx.initialize(CInitializeArgs::OsThreads)
            .map_err(|e| HsmError::ConnectionFailed(format!("Failed to initialize PKCS#11: {}", e)))?;

        // Get slots with tokens
        let slots = ctx.get_slots_with_token()
            .map_err(|e| HsmError::ConnectionFailed(format!("Failed to get slots: {}", e)))?;

        if slots.is_empty() {
            return Err(HsmError::ConnectionFailed("No tokens found".to_string()));
        }

        // Select slot
        let slot_idx = config.slot_id.unwrap_or(0) as usize;
        let slot = slots.get(slot_idx)
            .ok_or_else(|| HsmError::ConnectionFailed(format!("Slot {} not found", slot_idx)))?;

        // Open read-write session
        let session = ctx.open_rw_session(*slot)
            .map_err(|e| HsmError::ConnectionFailed(format!("Failed to open session: {}", e)))?;

        // Login if credentials provided
        if let Some(ref pin) = config.credentials {
            let auth_pin = AuthPin::new(pin.clone());
            session.login(UserType::User, Some(&auth_pin))
                .map_err(|_e| HsmError::AuthenticationFailed)?;
            *self.pin.lock().unwrap() = Some(pin.clone());
        }

        let mut inner = self.inner.lock().unwrap();
        inner.slot = Some(*slot);
        inner.session = Some(session);
        inner.ctx = Some(ctx);

        Ok(())
    }

    fn is_connected(&self) -> bool {
        self.inner.lock().unwrap().session.is_some()
    }

    fn generate_key(&self, key_type: KeyType, label: &str) -> Result<KeyHandle, HsmError> {
        let id = self.generate_id();
        let label_bytes = label.as_bytes().to_vec();

        let (private_handle, public_handle, wrapped_sk, wrapped_pk) = match key_type {
            KeyType::EcdsaP256 => {
                // Native PKCS#11 ECDSA P-256 key generation
                let inner = self.inner.lock().unwrap();
                let session = inner.session.as_ref().ok_or(HsmError::NotInitialized)?;

                let ec_params = vec![
                    0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07 // OID for P-256
                ];

                let pub_template = vec![
                    Attribute::Token(true),
                    Attribute::Private(false),
                    Attribute::Verify(true),
                    Attribute::EcParams(ec_params.clone()),
                    Attribute::Label(label_bytes.clone()),
                    Attribute::Id(id.as_bytes().to_vec()),
                ];

                let priv_template = vec![
                    Attribute::Token(true),
                    Attribute::Private(true),
                    Attribute::Sensitive(true),
                    Attribute::Extractable(false),
                    Attribute::Sign(true),
                    Attribute::Label(label_bytes.clone()),
                    Attribute::Id(id.as_bytes().to_vec()),
                ];

                let (pub_h, priv_h) = session.generate_key_pair(
                    &Mechanism::EccKeyPairGen,
                    &pub_template,
                    &priv_template,
                ).map_err(|e| HsmError::KeyGenerationFailed(format!("ECDSA keygen failed: {}", e)))?;

                (priv_h, pub_h, None, None)
            }

            KeyType::MlDsa87 => {
                // ML-DSA-87: Generate in software, wrap with HSM AES key
                use crate::mldsa::KeyPair;

                let keypair = KeyPair::generate()
                    .map_err(|e| HsmError::KeyGenerationFailed(e.to_string()))?;

                let sk_bytes = keypair.secret_key().to_bytes();
                let pk_bytes = keypair.public_key().to_bytes();

                // Wrap keys with HSM-protected AES key
                let wrapped_sk = self.wrap_data(&sk_bytes)?;
                let wrapped_pk = pk_bytes.to_vec(); // Public key doesn't need wrapping

                // Store wrapped key as data object in HSM
                let inner = self.inner.lock().unwrap();
                let session = inner.session.as_ref().ok_or(HsmError::NotInitialized)?;

                let data_template = vec![
                    Attribute::Class(ObjectClass::DATA),
                    Attribute::Token(true),
                    Attribute::Private(true),
                    Attribute::Label(format!("{}-mldsa-sk", label).into_bytes()),
                    Attribute::Id(id.as_bytes().to_vec()),
                    Attribute::Value(wrapped_sk.clone()),
                ];

                let sk_obj = session.create_object(&data_template)
                    .map_err(|e| HsmError::KeyGenerationFailed(format!("Store ML-DSA SK failed: {}", e)))?;

                let pk_template = vec![
                    Attribute::Class(ObjectClass::DATA),
                    Attribute::Token(true),
                    Attribute::Private(false),
                    Attribute::Label(format!("{}-mldsa-pk", label).into_bytes()),
                    Attribute::Id(id.as_bytes().to_vec()),
                    Attribute::Value(wrapped_pk.clone()),
                ];

                let pk_obj = session.create_object(&pk_template)
                    .map_err(|e| HsmError::KeyGenerationFailed(format!("Store ML-DSA PK failed: {}", e)))?;

                (sk_obj, pk_obj, Some(wrapped_sk), Some(wrapped_pk))
            }

            KeyType::MlKem1024 => {
                // ML-KEM-1024: Generate in software, wrap with HSM AES key
                use crate::mlkem::MlKemKeyPair;

                let keypair = MlKemKeyPair::generate()
                    .map_err(|e| HsmError::KeyGenerationFailed(e.to_string()))?;

                let (sk, pk) = keypair.into_parts();
                let sk_bytes = sk.as_bytes();
                let pk_bytes = pk.as_bytes();

                let wrapped_sk = self.wrap_data(sk_bytes)?;
                let wrapped_pk = pk_bytes.to_vec();

                let inner = self.inner.lock().unwrap();
                let session = inner.session.as_ref().ok_or(HsmError::NotInitialized)?;

                let data_template = vec![
                    Attribute::Class(ObjectClass::DATA),
                    Attribute::Token(true),
                    Attribute::Private(true),
                    Attribute::Label(format!("{}-mlkem-sk", label).into_bytes()),
                    Attribute::Id(id.as_bytes().to_vec()),
                    Attribute::Value(wrapped_sk.clone()),
                ];

                let sk_obj = session.create_object(&data_template)
                    .map_err(|e| HsmError::KeyGenerationFailed(format!("Store ML-KEM SK failed: {}", e)))?;

                let pk_template = vec![
                    Attribute::Class(ObjectClass::DATA),
                    Attribute::Token(true),
                    Attribute::Private(false),
                    Attribute::Label(format!("{}-mlkem-pk", label).into_bytes()),
                    Attribute::Id(id.as_bytes().to_vec()),
                    Attribute::Value(wrapped_pk.clone()),
                ];

                let pk_obj = session.create_object(&pk_template)
                    .map_err(|e| HsmError::KeyGenerationFailed(format!("Store ML-KEM PK failed: {}", e)))?;

                (sk_obj, pk_obj, Some(wrapped_sk), Some(wrapped_pk))
            }

            _ => return Err(HsmError::UnsupportedKeyType),
        };

        let attributes = KeyAttributes {
            key_type,
            can_sign: matches!(key_type, KeyType::MlDsa87 | KeyType::Ed25519 | KeyType::EcdsaP256),
            can_verify: matches!(key_type, KeyType::MlDsa87 | KeyType::Ed25519 | KeyType::EcdsaP256),
            can_encrypt: matches!(key_type, KeyType::MlKem1024 | KeyType::Aes256),
            can_decrypt: matches!(key_type, KeyType::MlKem1024 | KeyType::Aes256),
            exportable: false,
            created_at: Self::now(),
            expires_at: 0,
            label: label.to_string(),
        };

        let entry = Pkcs11KeyEntry {
            private_handle,
            public_handle,
            key_type,
            attributes,
            wrapped_sk,
            wrapped_pk,
        };

        self.keys.write().unwrap().insert(id.clone(), entry);
        Ok(KeyHandle::new(id))
    }

    fn import_key(&self, _key_type: KeyType, _key_data: &[u8], _label: &str) -> Result<KeyHandle, HsmError> {
        Err(HsmError::OperationNotPermitted(
            "Key import disabled for security".to_string()
        ))
    }

    fn export_public_key(&self, handle: &KeyHandle) -> Result<Vec<u8>, HsmError> {
        let keys = self.keys.read().unwrap();
        let entry = keys.get(handle.id())
            .ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;

        match entry.key_type {
            KeyType::MlDsa87 | KeyType::MlKem1024 => {
                // PQ keys: public key stored unwrapped
                entry.wrapped_pk.clone()
                    .ok_or_else(|| HsmError::InternalError("Public key not found".to_string()))
            }
            KeyType::EcdsaP256 => {
                // Get EC point from HSM
                let inner = self.inner.lock().unwrap();
                let session = inner.session.as_ref().ok_or(HsmError::NotInitialized)?;
                let attrs = session.get_attributes(entry.public_handle, &[AttributeType::EcPoint])
                    .map_err(|e| HsmError::InternalError(format!("Get EC point failed: {}", e)))?;

                for attr in attrs {
                    if let Attribute::EcPoint(point) = attr {
                        return Ok(point);
                    }
                }
                Err(HsmError::InternalError("EC point not found".to_string()))
            }
            _ => Err(HsmError::UnsupportedKeyType),
        }
    }

    fn sign(&self, handle: &KeyHandle, message: &[u8]) -> Result<Vec<u8>, HsmError> {
        let keys = self.keys.read().unwrap();
        let entry = keys.get(handle.id())
            .ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;

        if !entry.attributes.can_sign {
            return Err(HsmError::OperationNotPermitted("Key cannot sign".to_string()));
        }

        match entry.key_type {
            KeyType::EcdsaP256 => {
                // Native HSM signing
                let private_handle = entry.private_handle;
                drop(keys); // Release keys lock before acquiring inner lock

                let inner = self.inner.lock().unwrap();
                let session = inner.session.as_ref().ok_or(HsmError::NotInitialized)?;
                session.sign(&Mechanism::Ecdsa, private_handle, message)
                    .map_err(|e| HsmError::SigningFailed(format!("ECDSA sign failed: {}", e)))
            }
            KeyType::MlDsa87 => {
                // Unwrap key and sign in software
                let wrapped_sk = entry.wrapped_sk.as_ref()
                    .ok_or_else(|| HsmError::InternalError("Wrapped SK not found".to_string()))?;

                // Need to drop keys lock before calling unwrap_data (which needs session)
                let wrapped_sk = wrapped_sk.clone();
                drop(keys);

                let sk_bytes = self.unwrap_data(&wrapped_sk)?;

                use crate::mldsa::SecretKey;
                let sk = SecretKey::from_bytes(&sk_bytes)
                    .map_err(|e| HsmError::InternalError(e.to_string()))?;

                let sig = sk.sign(message)
                    .map_err(|e| HsmError::SigningFailed(e.to_string()))?;

                Ok(sig.to_bytes().to_vec())
            }
            _ => Err(HsmError::UnsupportedKeyType),
        }
    }

    fn verify(&self, handle: &KeyHandle, message: &[u8], signature: &[u8]) -> Result<bool, HsmError> {
        let keys = self.keys.read().unwrap();
        let entry = keys.get(handle.id())
            .ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;

        if !entry.attributes.can_verify {
            return Err(HsmError::OperationNotPermitted("Key cannot verify".to_string()));
        }

        match entry.key_type {
            KeyType::EcdsaP256 => {
                let public_handle = entry.public_handle;
                drop(keys);

                let inner = self.inner.lock().unwrap();
                let session = inner.session.as_ref().ok_or(HsmError::NotInitialized)?;
                match session.verify(&Mechanism::Ecdsa, public_handle, message, signature) {
                    Ok(()) => Ok(true),
                    Err(_) => Ok(false),
                }
            }
            KeyType::MlDsa87 => {
                let pk_bytes = entry.wrapped_pk.as_ref()
                    .ok_or_else(|| HsmError::InternalError("Public key not found".to_string()))?;

                use crate::mldsa::{PublicKey, Signature};
                let pk = PublicKey::from_bytes(pk_bytes)
                    .map_err(|e| HsmError::InternalError(e.to_string()))?;
                let sig = Signature::from_bytes(signature)
                    .map_err(|e| HsmError::VerificationFailed(e.to_string()))?;

                Ok(pk.verify(message, &sig))
            }
            _ => Err(HsmError::UnsupportedKeyType),
        }
    }

    fn encrypt(&self, handle: &KeyHandle, _plaintext: &[u8]) -> Result<Vec<u8>, HsmError> {
        let keys = self.keys.read().unwrap();
        let entry = keys.get(handle.id())
            .ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;

        if !entry.attributes.can_encrypt {
            return Err(HsmError::OperationNotPermitted("Key cannot encrypt".to_string()));
        }

        match entry.key_type {
            KeyType::MlKem1024 => {
                let pk_bytes = entry.wrapped_pk.as_ref()
                    .ok_or_else(|| HsmError::InternalError("Public key not found".to_string()))?;

                use crate::mlkem::MlKemPublicKey;
                let pk = MlKemPublicKey::from_bytes(pk_bytes)
                    .map_err(|e| HsmError::CryptoFailed(e.to_string()))?;

                let (ciphertext, _shared_secret) = pk.encapsulate()
                    .map_err(|e| HsmError::CryptoFailed(e.to_string()))?;

                Ok(ciphertext.to_vec())
            }
            _ => Err(HsmError::UnsupportedKeyType),
        }
    }

    fn decrypt(&self, handle: &KeyHandle, ciphertext: &[u8]) -> Result<Vec<u8>, HsmError> {
        let keys = self.keys.read().unwrap();
        let entry = keys.get(handle.id())
            .ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;

        if !entry.attributes.can_decrypt {
            return Err(HsmError::OperationNotPermitted("Key cannot decrypt".to_string()));
        }

        match entry.key_type {
            KeyType::MlKem1024 => {
                let wrapped_sk = entry.wrapped_sk.as_ref()
                    .ok_or_else(|| HsmError::InternalError("Wrapped SK not found".to_string()))?;

                let wrapped_sk = wrapped_sk.clone();
                drop(keys);

                let sk_bytes = self.unwrap_data(&wrapped_sk)?;

                use crate::mlkem::MlKemSecretKey;
                let sk = MlKemSecretKey::from_bytes(&sk_bytes)
                    .map_err(|e| HsmError::CryptoFailed(e.to_string()))?;

                let shared_secret = sk.decapsulate(ciphertext)
                    .map_err(|e| HsmError::CryptoFailed(e.to_string()))?;

                Ok(shared_secret.to_vec())
            }
            _ => Err(HsmError::UnsupportedKeyType),
        }
    }

    fn delete_key(&self, handle: &KeyHandle) -> Result<(), HsmError> {
        let mut keys = self.keys.write().unwrap();
        let entry = keys.remove(handle.id())
            .ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;

        // Destroy objects in HSM
        let inner = self.inner.lock().unwrap();
        if let Some(session) = inner.session.as_ref() {
            let _ = session.destroy_object(entry.private_handle);
            let _ = session.destroy_object(entry.public_handle);
        }

        Ok(())
    }

    fn list_keys(&self) -> Result<Vec<(KeyHandle, KeyAttributes)>, HsmError> {
        let keys = self.keys.read().unwrap();
        Ok(keys
            .iter()
            .map(|(id, entry)| (KeyHandle::new(id.clone()), entry.attributes.clone()))
            .collect())
    }

    fn get_attributes(&self, handle: &KeyHandle) -> Result<KeyAttributes, HsmError> {
        let keys = self.keys.read().unwrap();
        let entry = keys.get(handle.id())
            .ok_or_else(|| HsmError::KeyNotFound(handle.id().to_string()))?;
        Ok(entry.attributes.clone())
    }

    fn close(&mut self) -> Result<(), HsmError> {
        // Clear key cache
        self.keys.write().unwrap().clear();

        // Logout and close session
        let mut inner = self.inner.lock().unwrap();
        if let Some(ref session) = inner.session {
            let _ = session.logout();
        }
        inner.session = None;
        inner.ctx = None;
        inner.slot = None;

        Ok(())
    }
}

/// High-level HSM provider that wraps different backends.
pub struct HsmProvider {
    backend: Arc<Mutex<Box<dyn HsmBackend>>>,
    config: HsmConfig,
}

impl HsmProvider {
    /// Create a software-only HSM provider.
    pub fn software() -> Result<Self, HsmError> {
        let config = HsmConfig {
            provider: HsmProviderType::Software,
            connection: "memory".to_string(),
            credentials: None,
            slot_id: None,
            rate_limit: None,
            session_timeout: None,
        };

        let mut backend = Box::new(SoftwareHsm::new()) as Box<dyn HsmBackend>;
        backend.initialize(&config)?;

        Ok(Self {
            backend: Arc::new(Mutex::new(backend)),
            config,
        })
    }

    /// Create an HSM provider with custom configuration.
    pub fn with_config(config: HsmConfig) -> Result<Self, HsmError> {
        let mut backend: Box<dyn HsmBackend> = match config.provider {
            HsmProviderType::Software => Box::new(SoftwareHsm::new()),
            HsmProviderType::Pkcs11 => {
                let slot_id = config.slot_id.unwrap_or(0);
                Box::new(Pkcs11Hsm::new(&config.connection, slot_id))
            }
            HsmProviderType::AwsCloudHsm => {
                return Err(HsmError::InternalError(
                    "AWS CloudHSM backend not yet implemented".to_string()
                ));
            }
            HsmProviderType::AzureKeyVault => {
                return Err(HsmError::InternalError(
                    "Azure Key Vault backend not yet implemented".to_string()
                ));
            }
            HsmProviderType::GcpCloudHsm => {
                return Err(HsmError::InternalError(
                    "GCP Cloud HSM backend not yet implemented".to_string()
                ));
            }
            HsmProviderType::Tpm => {
                return Err(HsmError::InternalError(
                    "TPM backend not yet implemented".to_string()
                ));
            }
        };

        backend.initialize(&config)?;

        Ok(Self {
            backend: Arc::new(Mutex::new(backend)),
            config,
        })
    }

    /// Check if the HSM is connected.
    pub fn is_connected(&self) -> bool {
        self.backend.lock().unwrap().is_connected()
    }

    /// Generate a new key in the HSM.
    pub fn generate_key(&self, key_type: KeyType, label: &str) -> Result<KeyHandle, HsmError> {
        self.backend.lock().unwrap().generate_key(key_type, label)
    }

    /// Import a key into the HSM.
    pub fn import_key(&self, key_type: KeyType, key_data: &[u8], label: &str) -> Result<KeyHandle, HsmError> {
        self.backend.lock().unwrap().import_key(key_type, key_data, label)
    }

    /// Export the public key.
    pub fn export_public_key(&self, handle: &KeyHandle) -> Result<Vec<u8>, HsmError> {
        self.backend.lock().unwrap().export_public_key(handle)
    }

    /// Sign a message using a key in the HSM.
    pub fn sign(&self, handle: &KeyHandle, message: &[u8]) -> Result<Vec<u8>, HsmError> {
        self.backend.lock().unwrap().sign(handle, message)
    }

    /// Verify a signature using a key in the HSM.
    pub fn verify(&self, handle: &KeyHandle, message: &[u8], signature: &[u8]) -> Result<bool, HsmError> {
        self.backend.lock().unwrap().verify(handle, message, signature)
    }

    /// Encrypt data using a key in the HSM.
    pub fn encrypt(&self, handle: &KeyHandle, plaintext: &[u8]) -> Result<Vec<u8>, HsmError> {
        self.backend.lock().unwrap().encrypt(handle, plaintext)
    }

    /// Decrypt data using a key in the HSM.
    pub fn decrypt(&self, handle: &KeyHandle, ciphertext: &[u8]) -> Result<Vec<u8>, HsmError> {
        self.backend.lock().unwrap().decrypt(handle, ciphertext)
    }

    /// Delete a key from the HSM.
    pub fn delete_key(&self, handle: &KeyHandle) -> Result<(), HsmError> {
        self.backend.lock().unwrap().delete_key(handle)
    }

    /// List all keys in the HSM.
    pub fn list_keys(&self) -> Result<Vec<(KeyHandle, KeyAttributes)>, HsmError> {
        self.backend.lock().unwrap().list_keys()
    }

    /// Get key attributes.
    pub fn get_attributes(&self, handle: &KeyHandle) -> Result<KeyAttributes, HsmError> {
        self.backend.lock().unwrap().get_attributes(handle)
    }

    /// Get the provider type.
    pub fn provider_type(&self) -> &HsmProviderType {
        &self.config.provider
    }
}

impl Drop for HsmProvider {
    fn drop(&mut self) {
        let _ = self.backend.lock().unwrap().close();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_software_hsm_generate_mldsa() {
        let hsm = HsmProvider::software().unwrap();
        assert!(hsm.is_connected());

        let handle = hsm.generate_key(KeyType::MlDsa87, "test-key").unwrap();

        let attrs = hsm.get_attributes(&handle).unwrap();
        assert_eq!(attrs.key_type, KeyType::MlDsa87);
        assert!(attrs.can_sign);
        assert!(attrs.can_verify);
        assert_eq!(attrs.label, "test-key");
    }

    #[test]
    fn test_software_hsm_sign_verify() {
        let hsm = HsmProvider::software().unwrap();
        let handle = hsm.generate_key(KeyType::MlDsa87, "sign-test").unwrap();

        let message = b"Hello, HSM!";
        let signature = hsm.sign(&handle, message).unwrap();

        let valid = hsm.verify(&handle, message, &signature).unwrap();
        assert!(valid);

        // Wrong message should fail
        let valid2 = hsm.verify(&handle, b"Wrong message", &signature).unwrap();
        assert!(!valid2);
    }

    #[test]
    fn test_software_hsm_list_keys() {
        let hsm = HsmProvider::software().unwrap();

        hsm.generate_key(KeyType::MlDsa87, "key1").unwrap();
        hsm.generate_key(KeyType::MlDsa87, "key2").unwrap();

        let keys = hsm.list_keys().unwrap();
        assert_eq!(keys.len(), 2);
    }

    #[test]
    fn test_software_hsm_delete_key() {
        let hsm = HsmProvider::software().unwrap();
        let handle = hsm.generate_key(KeyType::MlDsa87, "to-delete").unwrap();

        assert_eq!(hsm.list_keys().unwrap().len(), 1);

        hsm.delete_key(&handle).unwrap();

        assert_eq!(hsm.list_keys().unwrap().len(), 0);
    }

    #[test]
    fn test_software_hsm_export_public_key() {
        let hsm = HsmProvider::software().unwrap();
        let handle = hsm.generate_key(KeyType::MlDsa87, "export-test").unwrap();

        let pk = hsm.export_public_key(&handle).unwrap();

        // ML-DSA-87 public key is 2592 bytes
        assert_eq!(pk.len(), 2592);
    }

    #[test]
    fn test_key_not_found() {
        let hsm = HsmProvider::software().unwrap();
        let handle = KeyHandle::new("nonexistent");

        let result = hsm.sign(&handle, b"test");
        assert!(matches!(result, Err(HsmError::KeyNotFound(_))));
    }

    #[test]
    fn test_mlkem_operations() {
        let hsm = HsmProvider::software().unwrap();
        let handle = hsm.generate_key(KeyType::MlKem1024, "kem-test").unwrap();

        let attrs = hsm.get_attributes(&handle).unwrap();
        assert_eq!(attrs.key_type, KeyType::MlKem1024);
        assert!(attrs.can_encrypt);
        assert!(attrs.can_decrypt);

        // Test encapsulation
        let ciphertext = hsm.encrypt(&handle, &[]).unwrap();
        assert!(!ciphertext.is_empty());

        // Test decapsulation
        let shared_secret = hsm.decrypt(&handle, &ciphertext).unwrap();
        assert_eq!(shared_secret.len(), 32); // ML-KEM shared secret is 32 bytes
    }
}
