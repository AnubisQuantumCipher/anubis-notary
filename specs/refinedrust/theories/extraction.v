(** * Extraction Module for Anubis Notary

    This module provides Rocq extraction of verified specifications
    to OCaml, enabling the verification bridge to be compiled and
    used alongside the Rust implementation.

    The extraction includes:
    1. Pure model functions (merkle, nonce operations)
    2. Specification validators
    3. Test oracle functions for property testing

    ╔═══════════════════════════════════════════════════════════════════════╗
    ║  ⚠️  WARNING: EXTRACTED CODE IS NOT CONSTANT-TIME  ⚠️                 ║
    ╠═══════════════════════════════════════════════════════════════════════╣
    ║                                                                       ║
    ║  The functions in this module are SPECIFICATION MODELS, not          ║
    ║  production implementations. When extracted to OCaml:                ║
    ║                                                                       ║
    ║  • Coq's Z type becomes case analysis (if z=0, if z>0, else)        ║
    ║  • Bitwise operations use recursive bit-by-bit decomposition        ║
    ║  • Every operation has DATA-DEPENDENT BRANCHES                       ║
    ║                                                                       ║
    ║  DO NOT use extracted OCaml for cryptographic operations!            ║
    ║  Use the Rust implementation which uses actual constant-time code.   ║
    ║                                                                       ║
    ║  These models exist for:                                             ║
    ║  • Proving functional correctness of the specification               ║
    ║  • Property-based testing against the Rust implementation            ║
    ║  • Generating test oracles for verification                          ║
    ║                                                                       ║
    ╚═══════════════════════════════════════════════════════════════════════╝
*)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Stdlib Require Import ZArith List String Bool.
From Stdlib Require Import ExtrOcamlNatInt ExtrOcamlZInt.

(** ------------------------------------------------------------------ *)
(** ** Extraction Configuration                                        *)
(** ------------------------------------------------------------------ *)

(* Use efficient OCaml integers for Z *)
Extract Inductive Z => "int" [ "0" "(fun x -> x)" "(fun x -> -x)" ]
  "(fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))".

(* Extract bool to OCaml bool *)
Extract Inductive bool => "bool" [ "true" "false" ].

(* Extract option to OCaml option *)
Extract Inductive option => "option" [ "Some" "None" ].

(* Extract list to OCaml list *)
Extract Inductive list => "list" [ "[]" "(::)" ].

(* Extract prod to OCaml tuple *)
Extract Inductive prod => "(*)" [ "(,)" ].

(** ------------------------------------------------------------------ *)
(** ** Pure Model Functions for Extraction                             *)
(** ------------------------------------------------------------------ *)

Module ExtractedModels.

  (** Merkle tree index operations *)
  Definition merkle_parent (i : Z) : Z := Z.div i 2.
  Definition merkle_left_child (i : Z) : Z := 2 * i.
  Definition merkle_right_child (i : Z) : Z := 2 * i + 1.
  Definition merkle_sibling (i : Z) : Z := Z.lxor i 1.
  Definition is_left_child (i : Z) : bool := Z.even i.
  Definition is_right_child (i : Z) : bool := Z.odd i.
  Definition tree_height (n : Z) : Z := Z.log2_up n.

  (** ================================================================== *)
  (** SPECIFICATION MODELS for conditional selection and comparison     *)
  (**                                                                    *)
  (** ⚠️  WARNING: NOT CONSTANT-TIME IN EXTRACTED CODE  ⚠️              *)
  (**                                                                    *)
  (** These definitions model the SEMANTICS of constant-time operations *)
  (** but the extracted OCaml code is NOT constant-time because:        *)
  (**   - Z operations use case analysis (if z=0, if z>0, else)         *)
  (**   - Bitwise ops recurse bit-by-bit with data-dependent branches   *)
  (**                                                                    *)
  (** The Rust implementation uses ACTUAL constant-time primitives:     *)
  (**   - subtle::Choice, subtle::ConditionallySelectable              *)
  (**   - subtle::ConstantTimeEq, subtle::ConstantTimeLess             *)
  (**                                                                    *)
  (** These models are for PROVING correctness, not for execution.      *)
  (** ================================================================== *)

  (** model_select: Specification model of conditional selection.
      Semantics: if choice=1 return a, if choice=0 return b.

      NOTE: This models the Rust subtle::conditional_select semantics.
      The extracted OCaml is NOT constant-time - use Rust for that. *)
  Definition model_select (a b choice : Z) : Z :=
    let mask := Z.opp choice in  (* -choice: 0 -> 0, 1 -> -1 (all 1s) *)
    Z.lor (Z.land a mask) (Z.land b (Z.lnot mask)).

  (** Backward-compatible alias - DEPRECATED, use model_select *)
  Definition ct_select := model_select.

  (** model_eq: Specification model of constant-time equality.
      Semantics: returns 1 if a = b, 0 otherwise.

      NOTE: This models the Rust subtle::ct_eq semantics.
      The extracted OCaml is NOT constant-time - use Rust for that. *)
  Definition model_eq (a b : Z) : Z :=
    let diff := Z.lxor a b in
    let collapsed := Z.shiftr (Z.lor diff (Z.opp diff)) 7 in
    Z.lxor (Z.land collapsed 1) 1.

  (** Backward-compatible alias - DEPRECATED, use model_eq *)
  Definition ct_eq := model_eq.

  (** model_lt: Specification model of constant-time less-than.
      Semantics: returns 1 if a < b, 0 otherwise.

      NOTE: This models the Rust subtle::ct_lt semantics.
      The extracted OCaml is NOT constant-time - use Rust for that. *)
  Definition model_lt (a b : Z) : Z :=
    let not_a := Z.lnot a in
    let xor_ab := Z.lxor a b in
    let not_xor := Z.lnot xor_ab in
    let diff := Z.sub a b in
    let term1 := Z.land not_a b in
    let term2 := Z.land not_xor diff in
    Z.land (Z.shiftr (Z.lor term1 term2) 63) 1.

  (** Backward-compatible alias - DEPRECATED, use model_lt *)
  Definition ct_lt := model_lt.

  (** Nonce operations *)
  Definition nonce_index (key_id counter : Z) : Z :=
    Z.lor (Z.shiftl key_id 32) counter.

  Definition nonce_key_id (idx : Z) : Z :=
    Z.shiftr idx 32.

  Definition nonce_counter (idx : Z) : Z :=
    Z.land idx (Z.sub (Z.pow 2 32) 1).

  (** Threshold signature operations *)
  Definition valid_threshold (threshold n_signers : Z) : bool :=
    Z.leb threshold n_signers.

  Definition signatures_needed (current threshold : Z) : Z :=
    Z.max 0 (threshold - current).

End ExtractedModels.

(** ------------------------------------------------------------------ *)
(** ** Test Oracles for Property Testing                               *)
(** ------------------------------------------------------------------ *)

Module TestOracles.
  Import ExtractedModels.

  (** Oracle: verify merkle parent-child relationship *)
  Definition oracle_parent_child (i : Z) : bool :=
    let left := merkle_left_child i in
    let right := merkle_right_child i in
    Z.eqb (merkle_parent left) i && Z.eqb (merkle_parent right) i.

  (** Oracle: verify sibling involution *)
  Definition oracle_sibling_involutive (i : Z) : bool :=
    if Z.ltb i 1 then true (* skip invalid indices *)
    else Z.eqb (merkle_sibling (merkle_sibling i)) i.

  (** Oracle: verify model_select correctness
      NOTE: Tests semantic correctness, not timing behavior *)
  Definition oracle_model_select (a b : Z) : bool :=
    Z.eqb (model_select a b 1) a &&
    Z.eqb (model_select a b 0) b.

  (** Backward-compatible alias *)
  Definition oracle_ct_select := oracle_model_select.

  (** Oracle: verify nonce roundtrip *)
  Definition oracle_nonce_roundtrip (key_id counter : Z) : bool :=
    if Z.ltb key_id 0 then true else
    if Z.ltb counter 0 then true else
    if Z.leb (Z.pow 2 32) key_id then true else
    if Z.leb (Z.pow 2 32) counter then true else
    let idx := nonce_index key_id counter in
    Z.eqb (nonce_key_id idx) key_id &&
    Z.eqb (nonce_counter idx) counter.

  (** Oracle: verify threshold monotonicity *)
  Definition oracle_threshold_monotonic (threshold n1 n2 : Z) : bool :=
    if Z.leb n2 n1 then true (* n1 <= n2 required *)
    else if valid_threshold threshold n1
         then valid_threshold threshold n2
         else true.

End TestOracles.

(** ------------------------------------------------------------------ *)
(** ** Specification Validators                                        *)
(** ------------------------------------------------------------------ *)

Module SpecValidators.
  Import ExtractedModels.

  (** Validate index is in valid range for tree operations *)
  Definition validate_index (i max_nodes : Z) : bool :=
    Z.leb 0 i && Z.ltb i max_nodes.

  (** Validate threshold parameters *)
  Definition validate_threshold_params (threshold n_signers : Z) : bool :=
    Z.ltb 0 threshold && Z.ltb 0 n_signers &&
    Z.leb threshold n_signers.

  (** Validate nonce parameters *)
  Definition validate_nonce_params (key_id counter : Z) : bool :=
    Z.leb 0 key_id && Z.ltb key_id (Z.pow 2 32) &&
    Z.leb 0 counter && Z.ltb counter (Z.pow 2 32).

  (** Validate byte value for model operations *)
  Definition validate_byte (v : Z) : bool :=
    Z.leb 0 v && Z.ltb v 256.

  (** Validate u64 value *)
  Definition validate_u64 (v : Z) : bool :=
    Z.leb 0 v && Z.ltb v (Z.pow 2 64).

End SpecValidators.

(** ------------------------------------------------------------------ *)
(** ** Extraction Targets                                              *)
(** ------------------------------------------------------------------ *)

(* Extract model functions *)
Extraction "anubis_models.ml"
  ExtractedModels.merkle_parent
  ExtractedModels.merkle_left_child
  ExtractedModels.merkle_right_child
  ExtractedModels.merkle_sibling
  ExtractedModels.is_left_child
  ExtractedModels.is_right_child
  ExtractedModels.tree_height
  ExtractedModels.model_select
  ExtractedModels.model_eq
  ExtractedModels.model_lt
  ExtractedModels.ct_select      (* deprecated alias *)
  ExtractedModels.ct_eq          (* deprecated alias *)
  ExtractedModels.ct_lt          (* deprecated alias *)
  ExtractedModels.nonce_index
  ExtractedModels.nonce_key_id
  ExtractedModels.nonce_counter
  ExtractedModels.valid_threshold
  ExtractedModels.signatures_needed.

(* Extract test oracles *)
Extraction "anubis_oracles.ml"
  TestOracles.oracle_parent_child
  TestOracles.oracle_sibling_involutive
  TestOracles.oracle_model_select
  TestOracles.oracle_ct_select   (* deprecated alias *)
  TestOracles.oracle_nonce_roundtrip
  TestOracles.oracle_threshold_monotonic.

(* Extract validators *)
Extraction "anubis_validators.ml"
  SpecValidators.validate_index
  SpecValidators.validate_threshold_params
  SpecValidators.validate_nonce_params
  SpecValidators.validate_byte
  SpecValidators.validate_u64.
