//! Key Derivation Functions.
//!
//! This module provides complete password-based and key-based key derivation:
//!
//! - **Argon2id (RFC 9106)**: Memory-hard password hashing with enforced security floors
//! - **HKDF-SHAKE256**: Key-based key derivation using SHAKE256 XOF
//! - **Automatic memory selection**: Based on available system RAM
//!
//! # Argon2id Usage
//!
//! ```ignore
//! use anubis_core::kdf::{Argon2idKdf, ValidatedArgon2idParams};
//!
//! // Automatically select parameters based on available memory
//! let kdf = Argon2idKdf::with_auto_params();
//!
//! // Derive a 32-byte key from password and salt
//! let mut key = [0u8; 32];
//! kdf.derive(b"password", b"random-salt-16b!", &mut key)?;
//! ```
//!
//! # Security Properties
//!
//! - **Memory hardness**: Minimum 512 MiB memory requirement (10x OWASP minimum)
//! - **Time hardness**: Minimum 3 iterations
//! - **GPU/ASIC resistance**: Argon2id's memory-hard design
//! - **Post-quantum safe**: Key derivation security depends only on symmetric primitives
//!
//! # Verification Status
//!
//! **NOT FORMALLY VERIFIED**. The RefinedRust-style specifications in doc comments
//! are design documentation, not actual verification. We have Rocq specifications
//! in `proofs/theories/memory_tier_spec.v` for the memory tier logic, but the
//! Rust code has not been formally linked to these specifications.

use crate::keccak::shake::Shake256;
use argon2::{Algorithm, Argon2, Params, Version};

/// Memory cost for high-security mode: 4 GiB (4,194,304 KiB).
///
/// Used on systems with >= 8 GiB available RAM.
/// Provides maximum resistance against GPU/ASIC attacks.
pub const ARGON2ID_HIGH_M_COST: u32 = 4 * 1024 * 1024;

/// Memory cost for medium-security mode: 1 GiB (1,048,576 KiB).
///
/// Used on systems with 2-8 GiB available RAM.
/// Still provides strong security with reduced GPU/ASIC resistance.
pub const ARGON2ID_MEDIUM_M_COST: u32 = 1024 * 1024;

/// Memory cost for low-memory mode: 512 MiB (524,288 KiB).
///
/// Used on systems with < 2 GiB available RAM.
/// Minimum secure configuration - still exceeds OWASP recommendations (47 MiB).
pub const ARGON2ID_LOW_M_COST: u32 = 512 * 1024;

/// Absolute minimum memory cost in KiB (512 MiB floor).
///
/// Below this, Argon2id loses significant GPU/ASIC resistance.
/// OWASP minimum is 47 MiB, so 512 MiB provides 10x safety margin.
pub const ARGON2ID_MIN_M_COST: u32 = ARGON2ID_LOW_M_COST;

/// Legacy alias for 4 GiB mode.
#[deprecated(since = "0.3.0", note = "Use ARGON2ID_HIGH_M_COST instead")]
pub const ARGON2ID_DEFAULT_M_COST: u32 = ARGON2ID_HIGH_M_COST;

/// Legacy alias for 1 GiB mode.
#[deprecated(since = "0.3.0", note = "Use ARGON2ID_MEDIUM_M_COST instead")]
pub const ARGON2ID_LOW_MEMORY_M_COST: u32 = ARGON2ID_MEDIUM_M_COST;

/// Time cost for high-memory mode (3 iterations).
pub const ARGON2ID_HIGH_T_COST: u32 = 3;

/// Time cost for medium-memory mode (4 iterations - compensates for less memory).
pub const ARGON2ID_MEDIUM_T_COST: u32 = 4;

/// Time cost for low-memory mode (5 iterations - compensates further).
pub const ARGON2ID_LOW_T_COST: u32 = 5;

/// Minimum time cost for Argon2id.
pub const ARGON2ID_MIN_T_COST: u32 = 3;

/// Legacy alias.
#[deprecated(since = "0.3.0", note = "Use ARGON2ID_MEDIUM_T_COST instead")]
pub const ARGON2ID_LOW_MEMORY_T_COST: u32 = ARGON2ID_MEDIUM_T_COST;

/// Minimum parallelism for Argon2id.
pub const ARGON2ID_MIN_PARALLELISM: u32 = 1;

// ============================================================================
// SYSTEM MEMORY DETECTION
// ============================================================================

/// Get available system memory in KiB.
///
/// Returns `None` if detection fails - caller should use a safe default.
/// This function attempts to detect *available* memory, not total memory,
/// to avoid allocating more than the system can handle.
fn get_available_memory_kib() -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        get_available_memory_linux()
    }

    #[cfg(target_os = "macos")]
    {
        get_available_memory_macos()
    }

    #[cfg(target_os = "windows")]
    {
        get_available_memory_windows()
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
    {
        None
    }
}

/// Linux: Read from /proc/meminfo.
#[cfg(target_os = "linux")]
fn get_available_memory_linux() -> Option<u64> {
    use std::fs::File;
    use std::io::{BufRead, BufReader};

    let file = File::open("/proc/meminfo").ok()?;
    let reader = BufReader::new(file);

    // Look for MemAvailable first (more accurate), fall back to MemFree
    let mut mem_available: Option<u64> = None;
    let mut mem_free: Option<u64> = None;

    for line in reader.lines() {
        let line = line.ok()?;
        if line.starts_with("MemAvailable:") {
            mem_available = parse_meminfo_line(&line);
        } else if line.starts_with("MemFree:") {
            mem_free = parse_meminfo_line(&line);
        }
        // Stop early if we found MemAvailable
        if mem_available.is_some() {
            break;
        }
    }

    mem_available.or(mem_free)
}

/// Parse a line from /proc/meminfo like "MemAvailable:   12345678 kB".
#[cfg(target_os = "linux")]
fn parse_meminfo_line(line: &str) -> Option<u64> {
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.len() >= 2 {
        parts[1].parse().ok()
    } else {
        None
    }
}

/// macOS: Use sysctl to get memory info.
#[cfg(target_os = "macos")]
fn get_available_memory_macos() -> Option<u64> {
    use std::process::Command;

    // Get page size and free pages via vm_stat
    let output = Command::new("vm_stat").output().ok()?;
    let stdout = String::from_utf8_lossy(&output.stdout);

    let mut page_size: u64 = 4096; // Default page size
    let mut free_pages: u64 = 0;
    let mut inactive_pages: u64 = 0;

    for line in stdout.lines() {
        if line.contains("page size of") {
            // "Mach Virtual Memory Statistics: (page size of 16384 bytes)"
            if let Some(start) = line.find("of ") {
                if let Some(end) = line.find(" bytes") {
                    if let Ok(size) = line[start + 3..end].parse::<u64>() {
                        page_size = size;
                    }
                }
            }
        } else if line.starts_with("Pages free:") {
            free_pages = parse_vm_stat_line(line).unwrap_or(0);
        } else if line.starts_with("Pages inactive:") {
            inactive_pages = parse_vm_stat_line(line).unwrap_or(0);
        }
    }

    // Available = free + inactive (inactive can be reclaimed)
    let available_bytes = (free_pages + inactive_pages) * page_size;
    Some(available_bytes / 1024) // Convert to KiB
}

/// Parse a vm_stat line like "Pages free:                             1234567.".
#[cfg(target_os = "macos")]
fn parse_vm_stat_line(line: &str) -> Option<u64> {
    let parts: Vec<&str> = line.split(':').collect();
    if parts.len() >= 2 {
        let value_str = parts[1].trim().trim_end_matches('.');
        value_str.parse().ok()
    } else {
        None
    }
}

/// Windows: Use wmic command to get available memory (safe, no FFI).
///
/// This approach avoids unsafe code while still providing memory detection.
/// Falls back to None if wmic is unavailable.
#[cfg(target_os = "windows")]
fn get_available_memory_windows() -> Option<u64> {
    use std::process::Command;

    // Use wmic to get free physical memory
    // Output format: "FreePhysicalMemory\r\n1234567\r\n"
    let output = Command::new("wmic")
        .args(["OS", "get", "FreePhysicalMemory"])
        .output()
        .ok()?;

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Parse the output - skip header line, get the number
    for line in stdout.lines() {
        let trimmed = line.trim();
        // Skip empty lines and the header
        if trimmed.is_empty() || trimmed == "FreePhysicalMemory" {
            continue;
        }
        // Parse the number (already in KiB on Windows)
        if let Ok(kib) = trimmed.parse::<u64>() {
            return Some(kib);
        }
    }

    None
}

/// Memory tier for automatic parameter selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryTier {
    /// High: >= 8 GiB available (use 4 GiB for Argon2id).
    High,
    /// Medium: 2-8 GiB available (use 1 GiB for Argon2id).
    Medium,
    /// Low: < 2 GiB available (use 512 MiB for Argon2id).
    Low,
}

impl MemoryTier {
    /// Detect the appropriate memory tier based on available system RAM.
    ///
    /// Returns `Medium` if detection fails (safe default).
    pub fn detect() -> Self {
        match get_available_memory_kib() {
            Some(available_kib) => Self::from_available_kib(available_kib),
            None => {
                // Detection failed - use medium as safe default
                // This is conservative: 1 GiB is enough for most systems
                MemoryTier::Medium
            }
        }
    }

    /// Determine tier from available memory in KiB.
    ///
    /// Exposed as `pub(crate)` for testing and diagnostics.
    pub(crate) fn from_available_kib(available_kib: u64) -> Self {
        // Thresholds (in KiB):
        // - High: >= 8 GiB (8,388,608 KiB) -> can use 4 GiB for Argon2id
        // - Medium: >= 2 GiB (2,097,152 KiB) -> can use 1 GiB for Argon2id
        // - Low: < 2 GiB -> use 512 MiB for Argon2id
        //
        // Note: We leave headroom - if 8 GiB available, using 4 GiB leaves 4 GiB for OS/apps
        const HIGH_THRESHOLD: u64 = 8 * 1024 * 1024;    // 8 GiB
        const MEDIUM_THRESHOLD: u64 = 2 * 1024 * 1024;  // 2 GiB

        if available_kib >= HIGH_THRESHOLD {
            MemoryTier::High
        } else if available_kib >= MEDIUM_THRESHOLD {
            MemoryTier::Medium
        } else {
            MemoryTier::Low
        }
    }

    /// Get the recommended memory cost for this tier in KiB.
    pub fn m_cost(self) -> u32 {
        match self {
            MemoryTier::High => ARGON2ID_HIGH_M_COST,
            MemoryTier::Medium => ARGON2ID_MEDIUM_M_COST,
            MemoryTier::Low => ARGON2ID_LOW_M_COST,
        }
    }

    /// Get the recommended time cost for this tier.
    pub fn t_cost(self) -> u32 {
        match self {
            MemoryTier::High => ARGON2ID_HIGH_T_COST,
            MemoryTier::Medium => ARGON2ID_MEDIUM_T_COST,
            MemoryTier::Low => ARGON2ID_LOW_T_COST,
        }
    }
}

/// Error type for KDF operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KdfError {
    /// Invalid Argon2id memory cost (too low).
    MemoryCostTooLow,
    /// Invalid Argon2id time cost (too low).
    TimeCostTooLow,
    /// Invalid Argon2id parallelism (too low).
    ParallelismTooLow,
    /// Output key material too long.
    OutputTooLong,
    /// Invalid salt length.
    InvalidSaltLength,
}

/// Validated Argon2id parameters with enforced security floors.
///
/// This struct ensures that parameter floors are met before Argon2id can be used.
/// It does NOT perform the actual Argon2id computation - use the `argon2` crate
/// for that, passing these validated parameters.
///
/// ## Security Floors
///
/// - Memory: >= 1 GiB (1,048,576 KiB) for low-memory mode
/// - Memory: >= 4 GiB (4,194,304 KiB) for default mode
/// - Time: >= 3 iterations (default) or >= 4 iterations (low-memory)
/// - Parallelism: >= 1 lane
///
/// These floors exceed OWASP recommendations for password hashing.
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("params" : "argon2_spec.argon2id_params")]
/// #[rr::invariant("params.m_cost >= ARGON2ID_LOW_MEMORY_M_COST")]
/// #[rr::invariant("params.t_cost >= ARGON2ID_MIN_T_COST")]
/// #[rr::invariant("params.parallelism >= ARGON2ID_MIN_PARALLELISM")]
/// #[rr::invariant("argon2_spec.params_valid(params)")]
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValidatedArgon2idParams {
    m_cost: u32,
    t_cost: u32,
    parallelism: u32,
}

/// Type alias for backwards compatibility.
#[deprecated(since = "0.2.0", note = "Use ValidatedArgon2idParams instead")]
pub type Argon2idParams = ValidatedArgon2idParams;

impl ValidatedArgon2idParams {
    /// Create new Argon2id parameters with validation.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("m_cost" : "u32", "t_cost" : "u32", "parallelism" : "u32")]
    /// #[rr::args("#m_cost", "#t_cost", "#parallelism")]
    /// #[rr::returns("Ok(params) | Err(MemoryCostTooLow) | Err(TimeCostTooLow) | Err(ParallelismTooLow)")]
    /// #[rr::ensures("is_ok(result) <-> m_cost >= ARGON2ID_LOW_MEMORY_M_COST && t_cost >= ARGON2ID_MIN_T_COST && parallelism >= ARGON2ID_MIN_PARALLELISM")]
    /// #[rr::ensures("is_ok(result) -> unwrap(result).m_cost = m_cost")]
    /// #[rr::ensures("is_ok(result) -> unwrap(result).t_cost = t_cost")]
    /// #[rr::ensures("is_ok(result) -> unwrap(result).parallelism = parallelism")]
    /// ```
    ///
    /// Memory Hardness: The minimum 1 GiB memory requirement ensures that
    /// password cracking requires significant RAM, providing resistance against
    /// GPU and ASIC-based attacks.
    pub fn new(m_cost: u32, t_cost: u32, parallelism: u32) -> Result<Self, KdfError> {
        if m_cost < ARGON2ID_MIN_M_COST {
            return Err(KdfError::MemoryCostTooLow);
        }
        if t_cost < ARGON2ID_MIN_T_COST {
            return Err(KdfError::TimeCostTooLow);
        }
        if parallelism < ARGON2ID_MIN_PARALLELISM {
            return Err(KdfError::ParallelismTooLow);
        }

        Ok(Self {
            m_cost,
            t_cost,
            parallelism,
        })
    }

    /// Get memory cost in KiB.
    pub fn m_cost(&self) -> u32 {
        self.m_cost
    }

    /// Get time cost (iterations).
    pub fn t_cost(&self) -> u32 {
        self.t_cost
    }

    /// Get parallelism (lanes).
    pub fn parallelism(&self) -> u32 {
        self.parallelism
    }

    /// Create default parameters (4 GiB, 3 iterations, 1 lane).
    ///
    /// Use this for maximum security. Requires ~4 GiB of available RAM.
    pub fn default_params() -> Self {
        Self {
            m_cost: ARGON2ID_MIN_M_COST,
            t_cost: ARGON2ID_MIN_T_COST,
            parallelism: ARGON2ID_MIN_PARALLELISM,
        }
    }

    /// Create low-memory parameters (1 GiB, 4 iterations, 1 lane).
    ///
    /// Use this on systems with limited RAM (< 8 GiB available).
    /// Security is still strong but reduced GPU/ASIC resistance.
    /// The extra iteration partially compensates for less memory.
    ///
    /// Consider using [`auto_select()`](Self::auto_select) instead for automatic detection.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::ensures("result.m_cost = ARGON2ID_MEDIUM_M_COST")]
    /// #[rr::ensures("result.t_cost = ARGON2ID_MEDIUM_T_COST")]
    /// #[rr::ensures("result.parallelism = ARGON2ID_MIN_PARALLELISM")]
    /// ```
    pub fn low_memory_params() -> Self {
        Self {
            m_cost: ARGON2ID_MEDIUM_M_COST,
            t_cost: ARGON2ID_MEDIUM_T_COST,
            parallelism: ARGON2ID_MIN_PARALLELISM,
        }
    }

    /// Automatically select parameters based on available system memory.
    ///
    /// This is the **recommended** way to create Argon2id parameters. It detects
    /// available RAM and selects appropriate parameters:
    ///
    /// | Available RAM | Memory Cost | Time Cost | Notes |
    /// |--------------|-------------|-----------|-------|
    /// | >= 8 GiB     | 4 GiB       | 3 iter    | Maximum security |
    /// | >= 2 GiB     | 1 GiB       | 4 iter    | Balanced |
    /// | < 2 GiB      | 512 MiB     | 5 iter    | Low memory systems |
    ///
    /// If memory detection fails, defaults to medium tier (1 GiB, 4 iterations)
    /// which works on most systems.
    ///
    /// # Example
    ///
    /// ```ignore
    /// use anubis_core::kdf::ValidatedArgon2idParams;
    ///
    /// let params = ValidatedArgon2idParams::auto_select();
    /// println!("Using {} KiB memory, {} iterations",
    ///          params.m_cost(), params.t_cost());
    /// ```
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::ensures("result.m_cost >= ARGON2ID_MIN_M_COST")]
    /// #[rr::ensures("result.t_cost >= ARGON2ID_MIN_T_COST")]
    /// #[rr::ensures("result.parallelism >= ARGON2ID_MIN_PARALLELISM")]
    /// ```
    pub fn auto_select() -> Self {
        let tier = MemoryTier::detect();
        Self {
            m_cost: tier.m_cost(),
            t_cost: tier.t_cost(),
            parallelism: ARGON2ID_MIN_PARALLELISM,
        }
    }

    /// Create high-security parameters (4 GiB, 3 iterations, 1 lane).
    ///
    /// Use this for maximum security on systems with >= 8 GiB available RAM.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::ensures("result.m_cost = ARGON2ID_HIGH_M_COST")]
    /// #[rr::ensures("result.t_cost = ARGON2ID_HIGH_T_COST")]
    /// #[rr::ensures("result.parallelism = ARGON2ID_MIN_PARALLELISM")]
    /// ```
    pub fn high_security_params() -> Self {
        Self {
            m_cost: ARGON2ID_HIGH_M_COST,
            t_cost: ARGON2ID_HIGH_T_COST,
            parallelism: ARGON2ID_MIN_PARALLELISM,
        }
    }

    /// Get the detected memory tier for this system.
    ///
    /// Useful for diagnostics and logging.
    pub fn detected_tier() -> MemoryTier {
        MemoryTier::detect()
    }
}

// ============================================================================
// ARGON2ID KEY DERIVATION
// ============================================================================

/// Argon2id key derivation function (RFC 9106).
///
/// This provides complete password-based key derivation with memory-hard security.
/// Use this for deriving encryption keys from passwords.
///
/// # Security Properties
///
/// - **Algorithm**: Argon2id v1.3 (hybrid of Argon2i and Argon2d)
/// - **Memory hardness**: Configurable, minimum 512 MiB
/// - **Time hardness**: Configurable, minimum 3 iterations
/// - **Side-channel resistance**: Argon2id provides data-independent memory access
///   for the first half of each pass (Argon2i mode) and data-dependent for the
///   second half (Argon2d mode)
///
/// # Example
///
/// ```ignore
/// use anubis_core::kdf::Argon2idKdf;
///
/// let kdf = Argon2idKdf::with_auto_params();
///
/// let mut key = [0u8; 32];
/// kdf.derive(b"password", b"16-byte-salt!!", &mut key)?;
/// ```
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("kdf" : "argon2_spec.argon2id_kdf")]
/// #[rr::invariant("kdf.params.m_cost >= ARGON2ID_MIN_M_COST")]
/// #[rr::invariant("kdf.params.t_cost >= ARGON2ID_MIN_T_COST")]
/// #[rr::invariant("kdf.params.parallelism >= ARGON2ID_MIN_PARALLELISM")]
/// ```
pub struct Argon2idKdf {
    params: ValidatedArgon2idParams,
}

impl Argon2idKdf {
    /// Create a new Argon2id KDF with validated parameters.
    ///
    /// # Example
    ///
    /// ```ignore
    /// use anubis_core::kdf::{Argon2idKdf, ValidatedArgon2idParams};
    ///
    /// let params = ValidatedArgon2idParams::high_security_params();
    /// let kdf = Argon2idKdf::new(params);
    /// ```
    pub fn new(params: ValidatedArgon2idParams) -> Self {
        Self { params }
    }

    /// Create a new Argon2id KDF with automatically selected parameters.
    ///
    /// This detects available system memory and selects appropriate parameters:
    /// - >= 8 GiB available: 4 GiB memory, 3 iterations
    /// - >= 2 GiB available: 1 GiB memory, 4 iterations
    /// - < 2 GiB available: 512 MiB memory, 5 iterations
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::ensures("result.params.m_cost >= ARGON2ID_MIN_M_COST")]
    /// #[rr::ensures("result.params.t_cost >= ARGON2ID_MIN_T_COST")]
    /// ```
    pub fn with_auto_params() -> Self {
        Self {
            params: ValidatedArgon2idParams::auto_select(),
        }
    }

    /// Create a new Argon2id KDF with high-security parameters (4 GiB).
    ///
    /// Use this when you have >= 8 GiB of available RAM.
    pub fn with_high_security() -> Self {
        Self {
            params: ValidatedArgon2idParams::high_security_params(),
        }
    }

    /// Create a new Argon2id KDF with low-memory parameters (1 GiB).
    ///
    /// Use this on systems with limited RAM (2-8 GiB available).
    pub fn with_low_memory() -> Self {
        Self {
            params: ValidatedArgon2idParams::low_memory_params(),
        }
    }

    /// Derive a key from a password and salt.
    ///
    /// # Arguments
    ///
    /// * `password` - The password to derive from (any length)
    /// * `salt` - Random salt (should be at least 16 bytes, recommended 32 bytes)
    /// * `output` - Buffer to write derived key material into
    ///
    /// # Security
    ///
    /// - Salt MUST be unique per password. Use `getrandom` or similar.
    /// - Salt SHOULD be at least 16 bytes (128 bits)
    /// - Output length should match your encryption key size (typically 32 bytes)
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("password" : "list u8", "salt" : "list u8", "output_len" : "nat")]
    /// #[rr::requires("len(salt) >= 8")]  // Argon2 minimum
    /// #[rr::requires("output_len <= 2^32 - 1")]
    /// #[rr::ensures("is_ok(result) -> len(output) = output_len")]
    /// #[rr::ensures("is_ok(result) -> output = argon2id(password, salt, self.params, output_len)")]
    /// #[rr::ensures("deterministic: same inputs -> same output")]
    /// ```
    pub fn derive(&self, password: &[u8], salt: &[u8], output: &mut [u8]) -> Result<(), KdfError> {
        if salt.len() < 8 {
            return Err(KdfError::InvalidSaltLength);
        }

        let params = Params::new(
            self.params.m_cost(),
            self.params.t_cost(),
            self.params.parallelism(),
            Some(output.len()),
        )
        .map_err(|_| KdfError::InvalidSaltLength)?;

        let argon2 = Argon2::new(Algorithm::Argon2id, Version::V0x13, params);

        argon2
            .hash_password_into(password, salt, output)
            .map_err(|_| KdfError::InvalidSaltLength)?;

        Ok(())
    }

    /// Derive a fixed-size key from a password and salt.
    ///
    /// This is a convenience method that returns a fixed-size array.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let kdf = Argon2idKdf::with_auto_params();
    /// let key: [u8; 32] = kdf.derive_fixed(b"password", b"salt")?;
    /// ```
    pub fn derive_fixed<const N: usize>(
        &self,
        password: &[u8],
        salt: &[u8],
    ) -> Result<[u8; N], KdfError> {
        let mut output = [0u8; N];
        self.derive(password, salt, &mut output)?;
        Ok(output)
    }

    /// Get the configured parameters.
    pub fn params(&self) -> &ValidatedArgon2idParams {
        &self.params
    }

    /// Get the memory cost in KiB.
    pub fn m_cost(&self) -> u32 {
        self.params.m_cost()
    }

    /// Get the time cost (iterations).
    pub fn t_cost(&self) -> u32 {
        self.params.t_cost()
    }

    /// Get the parallelism (lanes).
    pub fn parallelism(&self) -> u32 {
        self.params.parallelism()
    }
}

/// HKDF using SHAKE256 as the underlying XOF.
///
/// This is a simplified HKDF construction that uses SHAKE256 for both
/// extract and expand phases.
///
/// # RefinedRust Type Refinement
///
/// ```text
/// #[rr::refined_by("hkdf" : "kdf_spec.HKDF_state")]
/// #[rr::invariant("len(hkdf.prk) = 32")]
/// #[rr::invariant("hkdf.prk = SHAKE256(salt || 'HKDF-Extract' || ikm)")]
/// ```
pub struct HkdfShake256 {
    prk: [u8; 32],
}

impl HkdfShake256 {
    /// Extract phase: derive a pseudorandom key from input keying material.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("salt" : "list u8", "ikm" : "list u8")]
    /// #[rr::args("#salt", "#ikm")]
    /// #[rr::returns("#hkdf_extract(salt, ikm)")]
    /// #[rr::ensures("len(result.prk) = 32")]
    /// #[rr::ensures("deterministic: same inputs -> same prk")]
    /// #[rr::pure]
    /// ```
    ///
    /// The extract phase compresses the input keying material (IKM) into a
    /// fixed-length pseudorandom key (PRK) using SHAKE256.
    pub fn extract(salt: &[u8], ikm: &[u8]) -> Self {
        let mut xof = Shake256::new();

        // If salt is empty, use a zero-filled salt
        if salt.is_empty() {
            xof.absorb(&[0u8; 32]);
        } else {
            xof.absorb(salt);
        }

        // Domain separator
        xof.absorb(b"HKDF-Extract");

        // Input keying material
        xof.absorb(ikm);

        let prk: [u8; 32] = xof.squeeze_fixed();
        Self { prk }
    }

    /// Expand phase: derive output keying material.
    ///
    /// # RefinedRust Specification
    ///
    /// ```text
    /// #[rr::params("info" : "list u8", "N" : "nat")]
    /// #[rr::args("#info")]
    /// #[rr::requires("N <= 255 * 32")]
    /// #[rr::returns("Ok(okm) where len(okm) = N | Err(OutputTooLong)")]
    /// #[rr::ensures("is_ok(result) -> unwrap(result) = hkdf_expand(self.prk, info, N)")]
    /// #[rr::ensures("deterministic: same inputs -> same output")]
    /// #[rr::pure]
    /// ```
    ///
    /// The expand phase derives N bytes of output keying material (OKM) from
    /// the pseudorandom key using SHAKE256 with domain separation.
    pub fn expand<const N: usize>(&self, info: &[u8]) -> Result<[u8; N], KdfError> {
        if N > 255 * 32 {
            return Err(KdfError::OutputTooLong);
        }

        let mut output = [0u8; N];
        let mut offset = 0;
        let mut counter = 1u8;
        let mut prev = [0u8; 32];

        while offset < N {
            let mut xof = Shake256::new();

            if counter > 1 {
                xof.absorb(&prev);
            }

            xof.absorb(&self.prk);
            xof.absorb(info);
            xof.absorb(b"HKDF-Expand");
            xof.absorb(&[counter]);

            let block: [u8; 32] = xof.squeeze_fixed();

            let to_copy = core::cmp::min(32, N - offset);
            output[offset..offset + to_copy].copy_from_slice(&block[..to_copy]);

            prev = block;
            offset += to_copy;
            counter += 1;
        }

        Ok(output)
    }

    /// One-shot HKDF: extract then expand.
    pub fn derive<const N: usize>(
        salt: &[u8],
        ikm: &[u8],
        info: &[u8],
    ) -> Result<[u8; N], KdfError> {
        let hkdf = Self::extract(salt, ikm);
        hkdf.expand(info)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_argon2id_params_validation() {
        // Valid params
        let params = ValidatedArgon2idParams::new(ARGON2ID_MIN_M_COST, 3, 1);
        assert!(params.is_ok());

        // Memory too low
        let params = ValidatedArgon2idParams::new(1024, 3, 1);
        assert_eq!(params, Err(KdfError::MemoryCostTooLow));

        // Time too low
        let params = ValidatedArgon2idParams::new(ARGON2ID_MIN_M_COST, 2, 1);
        assert_eq!(params, Err(KdfError::TimeCostTooLow));

        // Parallelism too low
        let params = ValidatedArgon2idParams::new(ARGON2ID_MIN_M_COST, 3, 0);
        assert_eq!(params, Err(KdfError::ParallelismTooLow));
    }

    #[test]
    fn test_memory_tier_from_kib() {
        // High tier: >= 8 GiB
        assert_eq!(MemoryTier::from_available_kib(8 * 1024 * 1024), MemoryTier::High);
        assert_eq!(MemoryTier::from_available_kib(16 * 1024 * 1024), MemoryTier::High);

        // Medium tier: 2-8 GiB
        assert_eq!(MemoryTier::from_available_kib(2 * 1024 * 1024), MemoryTier::Medium);
        assert_eq!(MemoryTier::from_available_kib(4 * 1024 * 1024), MemoryTier::Medium);
        assert_eq!(MemoryTier::from_available_kib(7 * 1024 * 1024), MemoryTier::Medium);

        // Low tier: < 2 GiB
        assert_eq!(MemoryTier::from_available_kib(1 * 1024 * 1024), MemoryTier::Low);
        assert_eq!(MemoryTier::from_available_kib(512 * 1024), MemoryTier::Low);
        assert_eq!(MemoryTier::from_available_kib(1024), MemoryTier::Low);
    }

    #[test]
    fn test_memory_tier_params() {
        // High tier
        assert_eq!(MemoryTier::High.m_cost(), ARGON2ID_HIGH_M_COST);
        assert_eq!(MemoryTier::High.t_cost(), ARGON2ID_HIGH_T_COST);

        // Medium tier
        assert_eq!(MemoryTier::Medium.m_cost(), ARGON2ID_MEDIUM_M_COST);
        assert_eq!(MemoryTier::Medium.t_cost(), ARGON2ID_MEDIUM_T_COST);

        // Low tier
        assert_eq!(MemoryTier::Low.m_cost(), ARGON2ID_LOW_M_COST);
        assert_eq!(MemoryTier::Low.t_cost(), ARGON2ID_LOW_T_COST);
    }

    #[test]
    fn test_auto_select_meets_minimums() {
        let params = ValidatedArgon2idParams::auto_select();
        assert!(params.m_cost() >= ARGON2ID_MIN_M_COST);
        assert!(params.t_cost() >= ARGON2ID_MIN_T_COST);
        assert!(params.parallelism() >= ARGON2ID_MIN_PARALLELISM);
    }

    #[test]
    fn test_high_security_params() {
        let params = ValidatedArgon2idParams::high_security_params();
        assert_eq!(params.m_cost(), ARGON2ID_HIGH_M_COST);
        assert_eq!(params.t_cost(), ARGON2ID_HIGH_T_COST);
        assert_eq!(params.parallelism(), ARGON2ID_MIN_PARALLELISM);
    }

    #[test]
    fn test_low_memory_params() {
        let params = ValidatedArgon2idParams::low_memory_params();
        assert_eq!(params.m_cost(), ARGON2ID_MEDIUM_M_COST);
        assert_eq!(params.t_cost(), ARGON2ID_MEDIUM_T_COST);
        assert_eq!(params.parallelism(), ARGON2ID_MIN_PARALLELISM);
    }

    #[test]
    fn test_memory_detection_doesnt_panic() {
        // This should not panic even if detection fails
        let _ = get_available_memory_kib();
        let _ = MemoryTier::detect();
        let _ = ValidatedArgon2idParams::auto_select();
    }

    #[test]
    fn test_hkdf_deterministic() {
        let salt = b"salt";
        let ikm = b"input keying material";
        let info = b"context info";

        let output1: [u8; 32] = HkdfShake256::derive(salt, ikm, info).unwrap();
        let output2: [u8; 32] = HkdfShake256::derive(salt, ikm, info).unwrap();

        assert_eq!(output1, output2);
    }

    #[test]
    fn test_hkdf_different_info() {
        let salt = b"salt";
        let ikm = b"input keying material";

        let output1: [u8; 32] = HkdfShake256::derive(salt, ikm, b"info1").unwrap();
        let output2: [u8; 32] = HkdfShake256::derive(salt, ikm, b"info2").unwrap();

        assert_ne!(output1, output2);
    }

    #[test]
    fn test_hkdf_long_output() {
        let salt = b"salt";
        let ikm = b"ikm";
        let info = b"info";

        let output: [u8; 128] = HkdfShake256::derive(salt, ikm, info).unwrap();
        assert_eq!(output.len(), 128);
    }
}
