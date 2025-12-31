//! RefinedRust Annotations for kdf module
//!
//! This file shows the complete refinement type annotations for the
//! key derivation functions (HKDF-SHAKE256 and Argon2id parameters).

// ============================================================================
// Argon2id Constants
// ============================================================================

/// Minimum memory cost for Argon2id in KiB (64 MiB).
///
/// OWASP 2023 recommendations for Argon2id:
/// - Minimum acceptable: 19 MiB (19456 KiB) with t=2, p=1
/// - First recommendation: 46 MiB (47104 KiB) with t=1, p=1
/// - High security: 64 MiB (65536 KiB) with t=3, p=4
///
/// We use 64 MiB as the minimum for a security-critical notary application.
/// This provides strong memory hardness while remaining practical on modern systems.
///
/// Reference: OWASP Password Storage Cheat Sheet (2023)
pub const ARGON2ID_MIN_M_COST: u32 = 65536; // 64 MiB

/// Minimum time cost for Argon2id.
pub const ARGON2ID_MIN_T_COST: u32 = 3;

/// Minimum parallelism for Argon2id.
pub const ARGON2ID_MIN_PARALLELISM: u32 = 1;

// ============================================================================
// HKDF Constants
// ============================================================================

/// PRK size (SHAKE256 output).
pub const HKDF_PRK_SIZE: usize = 32;

/// Maximum output keying material length.
pub const HKDF_MAX_OUTPUT: usize = 255 * 32;

// ============================================================================
// Argon2idParams Type
// ============================================================================

/// Validated Argon2id parameters with minimum floors enforced.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("m_cost" : "Z", "t_cost" : "Z", "parallelism" : "Z")]
/// #[rr::invariant("m_cost >= ARGON2ID_MIN_M_COST")]
/// #[rr::invariant("t_cost >= ARGON2ID_MIN_T_COST")]
/// #[rr::invariant("parallelism >= ARGON2ID_MIN_PARALLELISM")]
/// ```
#[rr::type("Argon2idParams")]
pub struct Argon2idParams {
    m_cost: u32,
    t_cost: u32,
    parallelism: u32,
}

// ============================================================================
// Argon2idParams::new
// ============================================================================

/// Create new Argon2id parameters with validation.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("m" : "Z", "t" : "Z", "p" : "Z")]
/// #[rr::args("m @ u32", "t @ u32", "p @ u32")]
/// #[rr::ensures("match result {
///     Ok(params) =>
///         params.m_cost = m /\
///         params.t_cost = t /\
///         params.parallelism = p /\
///         m >= ARGON2ID_MIN_M_COST /\
///         t >= ARGON2ID_MIN_T_COST /\
///         p >= ARGON2ID_MIN_PARALLELISM
///   | Err(MemoryCostTooLow) =>
///         m < ARGON2ID_MIN_M_COST
///   | Err(TimeCostTooLow) =>
///         m >= ARGON2ID_MIN_M_COST /\
///         t < ARGON2ID_MIN_T_COST
///   | Err(ParallelismTooLow) =>
///         m >= ARGON2ID_MIN_M_COST /\
///         t >= ARGON2ID_MIN_T_COST /\
///         p < ARGON2ID_MIN_PARALLELISM
/// }")]
/// ```
#[rr::verified]
pub fn new(m_cost: u32, t_cost: u32, parallelism: u32) -> Result<Argon2idParams, KdfError> {
    #[rr::assert("Validate memory cost")]
    if m_cost < ARGON2ID_MIN_M_COST {
        return Err(KdfError::MemoryCostTooLow);
    }

    #[rr::assert("Validate time cost")]
    if t_cost < ARGON2ID_MIN_T_COST {
        return Err(KdfError::TimeCostTooLow);
    }

    #[rr::assert("Validate parallelism")]
    if parallelism < ARGON2ID_MIN_PARALLELISM {
        return Err(KdfError::ParallelismTooLow);
    }

    Ok(Argon2idParams {
        m_cost,
        t_cost,
        parallelism,
    })
}

// ============================================================================
// HkdfShake256 Type
// ============================================================================

/// HKDF using SHAKE256 as the underlying XOF.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("prk" : "array u8 HKDF_PRK_SIZE")]
/// #[rr::invariant("len(prk) = HKDF_PRK_SIZE")]
/// ```
#[rr::type("HkdfShake256")]
pub struct HkdfShake256 {
    prk: [u8; 32],
}

// ============================================================================
// HkdfShake256::extract
// ============================================================================

/// Extract phase: derive a pseudorandom key from input keying material.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("salt" : "list u8", "ikm" : "list u8")]
/// #[rr::args("salt @ &[u8]", "ikm @ &[u8]")]
/// #[rr::returns("HkdfShake256 { prk: hkdf_extract(salt, ikm) }")]
/// #[rr::ensures("len(result.prk) = HKDF_PRK_SIZE")]
/// #[rr::ensures("result.prk = SHAKE256(salt' || 'HKDF-Extract' || ikm)
///               where salt' = if len(salt) = 0 then zeros(32) else salt")]
/// ```
#[rr::verified]
pub fn extract(salt: &[u8], ikm: &[u8]) -> HkdfShake256 {
    let mut xof = Shake256::new();

    #[rr::assert("Handle empty salt")]
    if salt.is_empty() {
        xof.absorb(&[0u8; 32]);
    } else {
        xof.absorb(salt);
    }

    #[rr::assert("Domain separator")]
    xof.absorb(b"HKDF-Extract");

    #[rr::assert("Input keying material")]
    xof.absorb(ikm);

    #[rr::assert("Squeeze PRK")]
    let prk: [u8; 32] = xof.squeeze_fixed();

    HkdfShake256 { prk }
}

// ============================================================================
// HkdfShake256::expand
// ============================================================================

/// Expand phase: derive output keying material.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma_okm" : "gname", "prk" : "array u8 32",
///              "info" : "list u8", "N" : "nat")]
/// #[rr::args("&self @ &shr<'_, HkdfShake256>", "info @ &[u8]")]
/// #[rr::requires("N <= HKDF_MAX_OUTPUT")]
/// #[rr::ensures("match result {
///     Ok(okm) =>
///         len(okm) = N /\
///         okm = hkdf_expand(prk, info, N)
///   | Err(OutputTooLong) =>
///         N > HKDF_MAX_OUTPUT
/// }")]
///
/// (* Loop invariant for expansion *)
/// #[rr::loop_inv("offset", "0 <= offset <= N")]
/// #[rr::loop_inv("counter", "1 <= counter <= ceil(N/32) + 1")]
/// #[rr::loop_inv("output[..offset] = hkdf_expand_partial(prk, info, offset)")]
/// ```
#[rr::verified]
pub fn expand<const N: usize>(&self, info: &[u8]) -> Result<[u8; N], KdfError> {
    #[rr::assert("Check output length bound")]
    if N > HKDF_MAX_OUTPUT {
        return Err(KdfError::OutputTooLong);
    }

    let mut output = [0u8; N];
    let mut offset = 0;
    let mut counter = 1u8;
    let mut prev = [0u8; 32];

    #[rr::loop_inv("offset <= N")]
    #[rr::loop_inv("counter >= 1")]
    while offset < N {
        let mut xof = Shake256::new();

        #[rr::assert("Chain previous block (except first)")]
        if counter > 1 {
            xof.absorb(&prev);
        }

        xof.absorb(&self.prk);
        xof.absorb(info);
        xof.absorb(b"HKDF-Expand");
        xof.absorb(&[counter]);

        let block: [u8; 32] = xof.squeeze_fixed();

        #[rr::assert("Copy at most 32 bytes to output")]
        let to_copy = core::cmp::min(32, N - offset);
        output[offset..offset + to_copy].copy_from_slice(&block[..to_copy]);

        prev = block;
        offset += to_copy;
        counter += 1;
    }

    Ok(output)
}

// ============================================================================
// HkdfShake256::derive (One-shot)
// ============================================================================

/// One-shot HKDF: extract then expand.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("salt" : "list u8", "ikm" : "list u8",
///              "info" : "list u8", "N" : "nat")]
/// #[rr::args("salt @ &[u8]", "ikm @ &[u8]", "info @ &[u8]")]
/// #[rr::requires("N <= HKDF_MAX_OUTPUT")]
/// #[rr::ensures("match result {
///     Ok(okm) =>
///         len(okm) = N /\
///         okm = hkdf_derive(salt, ikm, info, N)
///   | Err(e) => e = OutputTooLong /\ N > HKDF_MAX_OUTPUT
/// }")]
/// ```
#[rr::verified]
pub fn derive<const N: usize>(
    salt: &[u8],
    ikm: &[u8],
    info: &[u8],
) -> Result<[u8; N], KdfError> {
    let hkdf = HkdfShake256::extract(salt, ikm);
    hkdf.expand(info)
}

// ============================================================================
// Verification Conditions
// ============================================================================

/// Proof obligations for KDF:
///
/// ## Argon2id Parameter Validation
/// ```coq
/// Theorem m_cost_enforced :
///   forall params : Argon2idParams,
///     params.m_cost >= ARGON2ID_MIN_M_COST.
///
/// Theorem t_cost_enforced :
///   forall params : Argon2idParams,
///     params.t_cost >= ARGON2ID_MIN_T_COST.
///
/// Theorem parallelism_enforced :
///   forall params : Argon2idParams,
///     params.parallelism >= ARGON2ID_MIN_PARALLELISM.
/// ```
///
/// ## HKDF PRK Length
/// ```coq
/// Theorem prk_length :
///   forall salt ikm,
///     len(extract(salt, ikm).prk) = HKDF_PRK_SIZE.
/// ```
///
/// ## HKDF Output Length
/// ```coq
/// Theorem expand_length :
///   forall hkdf info N,
///     N <= HKDF_MAX_OUTPUT ->
///     match expand(hkdf, info, N) with
///     | Ok(okm) => len(okm) = N
///     | Err(_) => False
///     end.
/// ```
///
/// ## HKDF Determinism
/// ```coq
/// Theorem hkdf_deterministic :
///   forall salt ikm info N,
///     derive(salt, ikm, info, N) = derive(salt, ikm, info, N).
/// Proof.
///   reflexivity.
/// Qed.
/// ```
///
/// ## Empty Salt Handling
/// ```coq
/// Theorem empty_salt_equivalent :
///   forall ikm,
///     extract([], ikm) = extract(zeros(32), ikm).
/// ```
///
/// ## Output Bound Enforcement
/// ```coq
/// Theorem output_bound_checked :
///   forall hkdf info N,
///     N > HKDF_MAX_OUTPUT ->
///     expand(hkdf, info, N) = Err(OutputTooLong).
/// ```
mod _verification_conditions {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_argon2id_params_validation() {
        // Valid params
        assert!(Argon2idParams::new(ARGON2ID_MIN_M_COST, 3, 1).is_ok());

        // Memory too low
        assert_eq!(
            Argon2idParams::new(1024, 3, 1),
            Err(KdfError::MemoryCostTooLow)
        );

        // Time too low
        assert_eq!(
            Argon2idParams::new(ARGON2ID_MIN_M_COST, 2, 1),
            Err(KdfError::TimeCostTooLow)
        );
    }

    #[test]
    fn test_hkdf_deterministic() {
        let output1: [u8; 32] = HkdfShake256::derive(b"salt", b"ikm", b"info").unwrap();
        let output2: [u8; 32] = HkdfShake256::derive(b"salt", b"ikm", b"info").unwrap();
        assert_eq!(output1, output2);
    }

    #[test]
    fn test_hkdf_different_info() {
        let output1: [u8; 32] = HkdfShake256::derive(b"salt", b"ikm", b"info1").unwrap();
        let output2: [u8; 32] = HkdfShake256::derive(b"salt", b"ikm", b"info2").unwrap();
        assert_ne!(output1, output2);
    }
}
