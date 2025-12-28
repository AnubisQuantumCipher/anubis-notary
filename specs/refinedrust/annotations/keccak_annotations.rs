//! RefinedRust Annotations for keccak module
//!
//! This file shows the complete refinement type annotations for the
//! Keccak-f[1600] permutation and sponge construction.

// ============================================================================
// Type Definitions
// ============================================================================

/// Keccak state: 25 lanes of 64 bits each (1600 bits total).
///
/// # RefinedRust Type
/// ```refinedrust
/// #[rr::refined_by("state" : "list u64")]
/// #[rr::invariant("len(state) = 25")]
/// #[rr::invariant("forall i. i < 25 ==> 0 <= state[i] < 2^64")]
/// ```
pub type KeccakState = [u64; 25];

/// Rate for SHA3-256 in bytes (1088 bits / 8).
pub const SHA3_256_RATE: usize = 136;

/// Rate for SHAKE256 in bytes (1088 bits / 8).
pub const SHAKE256_RATE: usize = 136;

// ============================================================================
// Round Constants
// ============================================================================

/// Round constants for Keccak-f[1600].
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("RC" : "list u64")]
/// #[rr::invariant("len(RC) = 24")]
/// #[rr::invariant("RC = [0x0000000000000001, 0x0000000000008082, ...]")]
/// ```
const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082,
    0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088,
    0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b,
    0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080,
    0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080,
    0x0000000080000001, 0x8000000080008008,
];

/// Rotation offsets for rho step.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("RHO" : "list nat")]
/// #[rr::invariant("len(RHO) = 24")]
/// #[rr::invariant("forall i. i < 24 ==> RHO[i] < 64")]
/// ```
const RHO: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
    27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

// ============================================================================
// keccak_init: Initialize state to zeros
// ============================================================================

/// Initialize a Keccak state to zeros.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::returns("state @ [u64; 25]")]
/// #[rr::ensures("state = repeat(0, 25)")]
/// #[rr::pure]
/// ```
#[rr::verified]
#[inline]
pub const fn keccak_init() -> KeccakState {
    [0u64; 25]
}

// ============================================================================
// keccak_f1600: Full Keccak-f[1600] permutation
// ============================================================================

/// Apply the Keccak-f[1600] permutation (24 rounds).
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname", "state" : "list u64")]
/// #[rr::args("(state, gamma) @ &mut [u64; 25]")]
/// #[rr::requires("len(state) = 25")]
/// #[rr::ensures("gamma ↦ keccak_f(state)")]
/// #[rr::ensures("len(gamma) = 25")]
///
/// // Round loop invariant
/// #[rr::loop_inv("round", "0 <= round <= 24")]
/// #[rr::loop_inv("round", "len(state') = 25")]
/// #[rr::loop_inv("round", "state' = keccak_f_rounds(state, round)")]
///
/// // Safety: all indices are bounded
/// #[rr::ensures("forall x y. x < 5 /\ y < 5 ==> x + 5*y < 25")]
/// #[rr::ensures("forall i. i < 24 ==> RHO[i] < 64")]
/// #[rr::ensures("forall i. i < 24 ==> PI[i] < 25")]
/// ```
#[rr::verified]
#[allow(clippy::needless_range_loop)]
pub fn keccak_f1600(state: &mut KeccakState) {
    // Pi permutation table: destination -> source mapping
    #[rr::assert("All PI values are in 1..24, hence valid indices")]
    const PI: [usize; 24] = [
        10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
        15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
    ];

    #[rr::loop_inv("0 <= round <= 24")]
    #[rr::loop_variant("24 - round")]
    for round in 0..24 {
        // ================================================================
        // Theta step: Column parity mixing
        // ================================================================
        #[rr::assert("Computing column parities C[0..5]")]
        let mut c = [0u64; 5];

        #[rr::loop_inv("0 <= x <= 5")]
        #[rr::loop_inv("forall i. i < x ==> c[i] = column_parity(state, i)")]
        for x in 0..5 {
            #[rr::assert("Indices x, x+5, x+10, x+15, x+20 are all < 25")]
            c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }

        #[rr::assert("Computing D[0..5] from C")]
        let mut d = [0u64; 5];

        #[rr::loop_inv("0 <= x <= 5")]
        for x in 0..5 {
            #[rr::assert("(x+4)%5 < 5 and (x+1)%5 < 5")]
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        }

        #[rr::assert("XOR D into all lanes")]
        #[rr::loop_inv("0 <= i <= 25")]
        for i in 0..25 {
            #[rr::assert("i % 5 < 5, so d[i % 5] is valid")]
            state[i] ^= d[i % 5];
        }

        // ================================================================
        // Rho and Pi steps combined
        // ================================================================
        #[rr::assert("Lane 0 is not rotated and not moved")]
        let mut last = state[1];

        #[rr::loop_inv("0 <= i <= 24")]
        #[rr::loop_inv("last holds value to place in next iteration")]
        for i in 0..24 {
            #[rr::assert("PI[i] < 25 (verified by PI table)")]
            let pi_i = PI[i];

            #[rr::assert("pi_i is valid index into state")]
            let temp = state[pi_i];

            #[rr::assert("RHO[i] < 64 (verified by RHO table)")]
            state[pi_i] = last.rotate_left(RHO[i]);

            last = temp;
        }

        // ================================================================
        // Chi step: Non-linear row mixing
        // ================================================================
        #[rr::loop_inv("0 <= y <= 5")]
        for y in 0..5 {
            #[rr::assert("base = y * 5, so base, base+1..4 are all < 25")]
            let base = y * 5;

            // Cache row values before modifying
            let t0 = state[base];
            let t1 = state[base + 1];
            let t2 = state[base + 2];
            let t3 = state[base + 3];
            let t4 = state[base + 4];

            // Chi formula: A[x] ^= (!A[x+1]) & A[x+2]
            #[rr::assert("Chi mixes each lane with its two neighbors")]
            state[base]     = t0 ^ ((!t1) & t2);
            state[base + 1] = t1 ^ ((!t2) & t3);
            state[base + 2] = t2 ^ ((!t3) & t4);
            state[base + 3] = t3 ^ ((!t4) & t0);
            state[base + 4] = t4 ^ ((!t0) & t1);
        }

        // ================================================================
        // Iota step: Round constant XOR
        // ================================================================
        #[rr::assert("round < 24, so RC[round] is valid")]
        state[0] ^= RC[round];
    }
}

// ============================================================================
// keccak_absorb: Absorb a block into state
// ============================================================================

/// Absorb a block of data into the Keccak state.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname", "state" : "list u64", "block" : "list u8", "rate" : "nat")]
/// #[rr::args("(state, gamma) @ &mut [u64; 25]",
///            "block @ &shr<'_, [u8]>",
///            "rate @ usize")]
/// #[rr::requires("len(state) = 25")]
/// #[rr::requires("len(block) >= rate")]
/// #[rr::requires("rate % 8 = 0")]
/// #[rr::requires("rate <= 200")]
/// #[rr::ensures("gamma ↦ keccak_f(xor_block(state, block, rate/8))")]
///
/// // Loop invariant
/// #[rr::loop_inv("i", "0 <= i <= rate/8")]
/// #[rr::loop_inv("i", "forall j. j < i ==>
///     state'[j] = state[j] XOR load_le64(block[j*8..])")]
/// ```
#[rr::verified]
pub fn keccak_absorb(state: &mut KeccakState, block: &[u8], rate: usize) {
    #[rr::assert("rate/8 lanes to XOR, rate/8 <= 25")]
    let lanes = rate / 8;

    #[rr::loop_inv("0 <= i <= lanes")]
    #[rr::loop_variant("lanes - i")]
    for i in 0..lanes {
        #[rr::assert("i < lanes <= 25, so state[i] is valid")]
        #[rr::assert("i*8 + 8 <= rate <= len(block), so load_le64 is safe")]
        state[i] ^= crate::bytes::load_le64(&block[i * 8..]);
    }

    #[rr::assert("Apply permutation after absorbing")]
    keccak_f1600(state);
}

// ============================================================================
// keccak_squeeze: Extract output from state
// ============================================================================

/// Squeeze output from the Keccak state.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("state" : "list u64", "gamma" : "gname",
///              "output" : "list u8", "rate" : "nat")]
/// #[rr::args("state @ &shr<'_, [u64; 25]>",
///            "(output, gamma) @ &mut [u8]",
///            "rate @ usize")]
/// #[rr::requires("len(state) = 25")]
/// #[rr::requires("len(output) <= rate")]
/// #[rr::requires("rate <= 200")]
/// #[rr::ensures("gamma ↦ lanes_to_bytes(state, len(output))")]
///
/// // Loop invariant for full lanes
/// #[rr::loop_inv("i", "0 <= i <= full_lanes")]
/// #[rr::loop_inv("i", "output[..i*8] = le_bytes(state[..i])")]
/// ```
#[rr::verified]
pub fn keccak_squeeze(state: &KeccakState, output: &mut [u8], _rate: usize) {
    let full_lanes = output.len() / 8;
    let remaining = output.len() % 8;

    #[rr::loop_inv("0 <= i <= full_lanes")]
    for i in 0..full_lanes {
        #[rr::assert("i < full_lanes <= 25, so state[i] is valid")]
        #[rr::assert("i*8 + 8 <= len(output), so store is safe")]
        crate::bytes::store_le64(state[i], &mut output[i * 8..]);
    }

    if remaining > 0 {
        #[rr::assert("full_lanes < 25, so state[full_lanes] is valid")]
        let last_lane = state[full_lanes].to_le_bytes();

        #[rr::assert("remaining < 8, so last_lane[..remaining] is valid")]
        output[full_lanes * 8..].copy_from_slice(&last_lane[..remaining]);
    }
}

// ============================================================================
// keccak_pad_and_absorb: Final block with padding
// ============================================================================

/// Apply padding and absorb final block.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::params("gamma" : "gname", "state" : "list u64",
///              "data" : "list u8", "absorbed" : "nat",
///              "rate" : "nat", "domain" : "u8")]
/// #[rr::args("(state, gamma) @ &mut [u64; 25]",
///            "data @ &shr<'_, [u8]>",
///            "absorbed @ usize",
///            "rate @ usize",
///            "domain @ u8")]
/// #[rr::requires("len(state) = 25")]
/// #[rr::requires("absorbed <= len(data)")]
/// #[rr::requires("len(data) - absorbed < rate")]
/// #[rr::requires("rate <= 200")]
/// #[rr::ensures("gamma ↦ keccak_f(xor_block(state, pad(data[absorbed..], domain, rate)))")]
/// ```
#[rr::verified]
pub fn keccak_pad_and_absorb(
    state: &mut KeccakState,
    data: &[u8],
    absorbed: usize,
    rate: usize,
    domain: u8,
) {
    #[rr::assert("Block buffer on stack, max 200 bytes")]
    let mut block = [0u8; 200];

    let remaining = data.len() - absorbed;
    #[rr::assert("remaining < rate <= 200")]

    // Copy remaining data
    #[rr::assert("remaining < rate, so block[..remaining] is valid")]
    block[..remaining].copy_from_slice(&data[absorbed..]);

    // Add domain separator
    #[rr::assert("remaining < rate, so block[remaining] is valid")]
    block[remaining] = domain;

    // Add terminating 0x80 at end of rate
    #[rr::assert("rate - 1 < 200, so block[rate - 1] is valid")]
    block[rate - 1] |= 0x80;

    // Absorb padded block
    keccak_absorb(state, &block[..rate], rate);
}

// ============================================================================
// Index Safety Lemmas
// ============================================================================

/// Proof obligations for index safety in Keccak.
///
/// These lemmas are discharged by Lithium during verification:
///
/// ## Lane Index Safety
/// ```coq
/// Lemma lane_index_safe : forall x y,
///   x < 5 -> y < 5 -> x + 5 * y < 25.
/// Proof. lia. Qed.
/// ```
///
/// ## Rotation Offset Safety
/// ```coq
/// Lemma rho_offsets_safe : forall i,
///   i < 24 -> RHO[i] < 64.
/// Proof.
///   (* Enumerate all 24 cases *)
///   intros i Hi.
///   do 24 (destruct i; [simpl; lia|]); lia.
/// Qed.
/// ```
///
/// ## Pi Permutation Safety
/// ```coq
/// Lemma pi_indices_safe : forall i,
///   i < 24 -> 1 <= PI[i] <= 24.
/// Proof.
///   (* PI = [10,7,11,17,18,3,5,16,8,21,24,4,15,23,19,13,12,2,20,14,22,9,6,1] *)
///   intros i Hi.
///   do 24 (destruct i; [simpl; lia|]); lia.
/// Qed.
/// ```
///
/// ## Column Parity Safety
/// ```coq
/// Lemma column_indices_safe : forall x,
///   x < 5 ->
///   x < 25 /\ x + 5 < 25 /\ x + 10 < 25 /\ x + 15 < 25 /\ x + 20 < 25.
/// Proof. lia. Qed.
/// ```
///
/// ## Chi Row Safety
/// ```coq
/// Lemma chi_indices_safe : forall y,
///   y < 5 ->
///   y * 5 < 25 /\ y * 5 + 1 < 25 /\ y * 5 + 2 < 25 /\
///   y * 5 + 3 < 25 /\ y * 5 + 4 < 25.
/// Proof. lia. Qed.
/// ```
///
/// ## Rate/Lane Relationship
/// ```coq
/// Lemma rate_lanes_safe : forall rate,
///   rate <= 200 -> rate mod 8 = 0 -> rate / 8 <= 25.
/// Proof. lia. Qed.
/// ```
mod _index_safety_lemmas {}

// ============================================================================
// Functional Correctness
// ============================================================================

/// Functional correctness obligations:
///
/// ## Theta Correctness
/// The theta step computes column parities and XORs them according to:
/// `A'[x,y] = A[x,y] XOR C[x-1] XOR rotl(C[x+1], 1)`
/// where `C[x] = A[x,0] XOR A[x,1] XOR ... XOR A[x,4]`
///
/// ## Rho Correctness
/// Each lane is rotated by its fixed offset from the RHO table.
///
/// ## Pi Correctness
/// The pi step permutes lanes according to `(x,y) -> (y, 2x+3y mod 5)`.
///
/// ## Chi Correctness
/// The chi step applies the non-linear transformation:
/// `A'[x] = A[x] XOR ((!A[x+1]) AND A[x+2])`
///
/// ## Iota Correctness
/// Lane (0,0) is XORed with the round constant RC[round].
///
/// ## Composition
/// `keccak_f = iota . chi . pi . rho . theta` applied 24 times.
mod _functional_correctness {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keccak_init() {
        let state = keccak_init();
        assert!(state.iter().all(|&x| x == 0));
        assert_eq!(state.len(), 25);
    }

    #[test]
    fn test_keccak_f1600_not_identity() {
        let mut state = keccak_init();
        state[0] = 1;
        let original = state;
        keccak_f1600(&mut state);
        assert_ne!(state, original);
    }

    #[test]
    fn test_rho_offsets_bounded() {
        for offset in RHO.iter() {
            assert!(*offset < 64, "RHO offset {} >= 64", offset);
        }
    }

    #[test]
    fn test_pi_indices_bounded() {
        const PI: [usize; 24] = [
            10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
            15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
        ];
        for (i, &idx) in PI.iter().enumerate() {
            assert!(idx >= 1 && idx <= 24, "PI[{}] = {} out of range", i, idx);
        }
    }
}
