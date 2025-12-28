(** * Proof Automation Tactics for Anubis Notary

    This module provides custom tactics for automating proofs in the
    Anubis Notary verification. The tactics handle:

    1. Byte-level reasoning (bounds, arithmetic)
    2. List/array operations
    3. Cryptographic property discharge
    4. Separation logic frame reasoning
    5. Constant-time verification conditions

    These tactics integrate with RefinedRust's Lithium proof automation.
*)

From Stdlib Require Import Lia ZArith List Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Psatz.
Import ListNotations.

(** Import specifications *)
Require Import anubis_proofs.theories.crypto_model.
Require Import anubis_proofs.theories.mldsa_spec.
Require Import anubis_proofs.theories.aead_spec.
Require Import anubis_proofs.theories.cbor_spec.
Require Import anubis_proofs.theories.argon2_spec.
Require Import anubis_proofs.theories.merkle_spec.
Require Import anubis_proofs.refinements.crypto_refinements.

Open Scope Z_scope.

(** ** Byte Bounds Tactics *)

(** Prove a value is a valid byte (0 <= x < 256) *)
Ltac byte_bounds :=
  unfold byte_refined;
  try lia;
  try (split; [lia | lia]).

(** Prove all elements of a list are valid bytes *)
Ltac bytes_valid :=
  unfold Forall;
  repeat match goal with
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [byte_bounds | ]
  end;
  try assumption.

(** Simplify byte arithmetic modulo 256 *)
Ltac byte_mod_simpl :=
  repeat match goal with
  | |- context[?x mod 256] =>
      let H := fresh in
      assert (H: 0 <= x mod 256 < 256) by (apply Z.mod_pos_bound; lia);
      try lia
  | H: context[?x mod 256] |- _ =>
      let H' := fresh in
      assert (H': 0 <= x mod 256 < 256) by (apply Z.mod_pos_bound; lia)
  end.

(** ** List/Array Tactics *)

(** Prove list List.length equality *)
Ltac list_length :=
  repeat match goal with
  | |- List.length [] = _ => reflexivity
  | |- List.length (_ :: _) = S _ => simpl; f_equal; list_length
  | |- List.length (repeat _ ?n) = ?n => apply repeat_length
  | |- List.length (_ ++ _) = _ => rewrite app_length; list_length
  | |- List.length (map _ _) = List.length _ => rewrite map_length; list_length
  | |- List.length (map2 _ _ _) = _ => rewrite map2_length; list_length
  | |- List.length (firstn ?n _) = _ =>
      rewrite firstn_length; try lia
  | |- _ => lia
  end.

(** Prove list bounds for nth access *)
Ltac list_bounds :=
  match goal with
  | |- (?i < List.length ?l)%nat =>
      list_length; try lia
  | |- (List.length ?l <= ?n)%nat =>
      list_length; try lia
  | |- (List.length ?l >= ?n)%nat =>
      list_length; try lia
  end.

(** Simplify list operations *)
Ltac list_simpl :=
  repeat match goal with
  | |- context[List.length ([] ++ ?l)] => rewrite app_nil_l
  | |- context[List.length (?l ++ [])] => rewrite app_nil_r
  | |- context[firstn 0 _] => rewrite firstn_O
  | |- context[skipn 0 _] => rewrite skipn_O
  | |- context[nth 0 (_ :: _) _] => simpl
  | H: context[List.length ([] ++ ?l)] |- _ => rewrite app_nil_l in H
  end.

(** ** Size Constraint Tactics *)

(** ML-DSA-87 size constraints *)
Ltac mldsa_sizes :=
  unfold MLDSA87_Params.seed_size,
         MLDSA87_Params.sk_size,
         MLDSA87_Params.pk_size,
         MLDSA87_Params.sig_size in *;
  try lia.

(** ChaCha20-Poly1305 size constraints *)
Ltac aead_sizes :=
  unfold aead_spec.Params.key_size,
         aead_spec.Params.nonce_size,
         aead_spec.Params.tag_size,
         aead_spec.Params.block_size in *;
  try lia.

(** Argon2id parameter constraints *)
Ltac argon2_params :=
  unfold argon2_spec.min_m_cost_low,
         argon2_spec.min_m_cost_default,
         argon2_spec.min_t_cost_default,
         argon2_spec.min_t_cost_low,
         argon2_spec.min_parallelism,
         argon2_spec.max_tag_len in *;
  try lia.

(** Hash/digest size constraints *)
Ltac hash_sizes :=
  unfold merkle_spec.hash_size in *;
  try lia.

(** Combined size tactic *)
Ltac crypto_sizes :=
  try mldsa_sizes;
  try aead_sizes;
  try argon2_params;
  try hash_sizes.

(** ** Cryptographic Property Tactics *)

(** Solve determinism goals *)
Ltac determinism :=
  match goal with
  | |- ?f ?x = ?f ?x => reflexivity
  | |- ?f ?x ?y = ?f ?x ?y => reflexivity
  | |- ?f ?x ?y ?z = ?f ?x ?y ?z => reflexivity
  end.

(** Collision resistance is an axiom - we assume it holds for SHA3-256 *)
Axiom sha3_collision_resistance_axiom : crypto_model.SHA3_256.collision_resistant.

(** Introduce collision resistance assumption *)
Ltac use_collision_resistance :=
  match goal with
  | H: crypto_model.SHA3_256.collision_resistant |- _ => idtac
  | |- _ =>
      let Hcr := fresh "Hcr" in
      pose proof sha3_collision_resistance_axiom as Hcr
  end.

(** Apply signature correctness *)
Ltac sig_correct :=
  match goal with
  | |- mldsa_spec.Verify.verify _ _ (mldsa_spec.Sign.sign _ _ _) = true =>
      apply mldsa_spec.Verify.sign_verify_correct; auto
  end.

(** Apply AEAD correctness *)
Ltac aead_correct :=
  match goal with
  | |- aead_spec.aead_decrypt ?k ?n ?aad ?ct ?tag = Some ?pt =>
      (* The goal must match the form where ct,tag came from aead_encrypt k n aad pt *)
      (* We need to rewrite using the fact that (ct, tag) = aead_encrypt k n aad pt *)
      (* Then apply aead_roundtrip *)
      let Henc := fresh "Henc" in
      match goal with
      | H: (?ct', ?tag') = aead_spec.aead_encrypt ?k' ?n' ?aad' ?pt' |- _ =>
          rewrite <- H; apply aead_spec.aead_roundtrip
      | _ =>
          (* Try direct application if goal already matches *)
          apply aead_spec.aead_roundtrip
      end
  end.

(** ** Domain Separation Tactics *)

(** Check domain prefixes are distinct *)
Ltac domain_distinct :=
  unfold crypto_model.DomainSeparation.domain_separated;
  intro Heq;
  discriminate Heq.

(** Apply domain separation theorem *)
Ltac domain_sep :=
  match goal with
  | |- crypto_model.DomainSeparation.with_domain ?d1 _ <>
       crypto_model.DomainSeparation.with_domain ?d2 _ =>
      apply crypto_model.DomainSeparation.domain_separation_security;
      domain_distinct
  end.

(** ** CBOR Encoding Tactics *)

(** Prove CBOR encoding is canonical *)
Ltac cbor_canonical :=
  unfold cbor_spec.map_canonical, cbor_spec.keys_canonical, cbor_spec.keys_unique;
  split;
  [ (* Keys sorted *)
    repeat constructor; auto
  | (* Keys unique *)
    apply NoDup_cons; [intro Hin; inversion Hin | ]
  ].

(** Prove CBOR roundtrip *)
Ltac cbor_roundtrip :=
  apply cbor_spec.decode_encode_roundtrip;
  (* Prove well-formedness *)
  unfold cbor_spec.cbor_wf;
  repeat (split; try lia; try bytes_valid).

(** ** Argon2id Parameter Validation *)

(** Prove parameters are valid *)
Ltac argon2_valid_params :=
  unfold argon2_spec.params_valid;
  repeat split;
  argon2_params.

(** Prove H' List.length *)
Ltac h_prime_length :=
  apply argon2_spec.h_prime_length;
  lia.

(** ** Merkle Tree Tactics *)

(** Prove Merkle proof correctness *)
Ltac merkle_proof :=
  apply merkle_spec.proof_correctness;
  list_bounds.

(** Prove root validity *)
Ltac merkle_root_valid :=
  apply merkle_spec.compute_root_valid.

(** ** Separation Logic Tactics (Iris-style) *)

(** Frame introduction *)
Ltac frame_intro :=
  match goal with
  | |- crypto_refinements.SepLogic_Specs.own_bytes _ _ =>
      unfold crypto_refinements.SepLogic_Specs.own_bytes
  | |- crypto_refinements.sep _ _ =>
      apply crypto_refinements.sep
  end.

(** Ownership transfer *)
Ltac own_transfer :=
  match goal with
  | H: crypto_refinements.own _ _ |- crypto_refinements.own _ _ =>
      exact H
  end.

(** ** Constant-Time Verification *)

(** Prove constant-time property *)
Ltac ct_verify :=
  match goal with
  | |- crypto_refinements.ConstantTime_Refinements.ct_function _ =>
      (* All operations are masked/branchless *)
      unfold crypto_refinements.ConstantTime_Refinements.ct_function;
      trivial
  end.

(** ** Zeroization Tactics *)

(** Prove zeroization completeness *)
Ltac zeroize_complete :=
  unfold crypto_refinements.Zeroization_Refinements.zeroized;
  apply Forall_forall;
  intros x Hin;
  (* All bytes are 0 *)
  apply repeat_spec in Hin;
  assumption.

(** ** Combined Automation *)

(** Main proof automation tactic *)
Ltac crypto_auto :=
  repeat match goal with
  (* Byte bounds *)
  | |- 0 <= _ < 256 => byte_bounds
  | |- Forall byte_refined _ => bytes_valid

  (* List operations *)
  | |- List.length _ = _ => list_length
  | |- (_ < List.length _)%nat => list_bounds

  (* Size constraints *)
  | |- List.length _ = MLDSA87_Params.seed_size => mldsa_sizes
  | |- List.length _ = MLDSA87_Params.sk_size => mldsa_sizes
  | |- List.length _ = MLDSA87_Params.pk_size => mldsa_sizes
  | |- List.length _ = MLDSA87_Params.sig_size => mldsa_sizes
  | |- List.length _ = aead_spec.Params.key_size => aead_sizes
  | |- List.length _ = aead_spec.Params.nonce_size => aead_sizes
  | |- List.length _ = aead_spec.Params.tag_size => aead_sizes
  | |- List.length _ = merkle_spec.hash_size => hash_sizes

  (* Parameter validation *)
  | |- argon2_spec.params_valid _ => argon2_valid_params

  (* Determinism *)
  | |- ?x = ?x => reflexivity

  (* Signature correctness *)
  | |- mldsa_spec.Verify.verify _ _ _ = true => sig_correct

  (* Constant-time *)
  | |- crypto_refinements.ConstantTime_Refinements.ct_function _ => ct_verify

  (* Zeroization *)
  | |- crypto_refinements.Zeroization_Refinements.zeroized _ => zeroize_complete

  (* Fallback *)
  | |- _ => try lia; try assumption; try reflexivity
  end.

(** ** Hint Database *)

(** Create hint database for automated proof search *)
Create HintDb crypto_hints.

(** Add byte bounds hints *)
#[export] Hint Resolve Z.mod_pos_bound : crypto_hints.

(** Add list List.length hints *)
#[export] Hint Rewrite repeat_length app_length map_length map2_length : crypto_hints.

(** Add size hints *)
#[export] Hint Unfold MLDSA87_Params.seed_size
                     MLDSA87_Params.sk_size
                     MLDSA87_Params.pk_size
                     MLDSA87_Params.sig_size
                     aead_spec.Params.key_size
                     aead_spec.Params.nonce_size
                     aead_spec.Params.tag_size
                     merkle_spec.hash_size : crypto_hints.

(** Add validity hints *)
#[export] Hint Resolve cbor_spec.poly_zero_valid : crypto_hints.
#[export] Hint Resolve merkle_spec.compute_root_valid : crypto_hints.
#[export] Hint Resolve merkle_spec.hash_leaf_valid : crypto_hints.
#[export] Hint Resolve merkle_spec.hash_internal_valid : crypto_hints.

(** ** Example Proof Using Automation *)

Example byte_array_valid_example :
  forall (arr : list Z),
    List.length arr = 32%nat ->
    Forall (fun b => 0 <= b < 256) arr ->
    List.length arr = merkle_spec.hash_size.
Proof.
  intros arr Hlen Hvalid.
  crypto_auto.
Qed.

Example mldsa_keygen_size_example :
  MLDSA87_Params.sk_size = 4896%nat.
Proof.
  crypto_auto.
Qed.

Example argon2_default_valid_example :
  argon2_spec.params_valid argon2_spec.default_params.
Proof.
  crypto_auto.
Qed.

(** ** Lithium Integration Hints *)

(** For RefinedRust's Lithium solver, we provide lemmas in the right form *)

Lemma lithium_byte_bounds : forall b : Z,
  0 <= b < 256 ->
  byte_refined b.
Proof.
  intros b H. exact H.
Qed.

Lemma lithium_list_length : forall {A : Type} (l : list A) (n : nat),
  List.length l = n ->
  (List.length l <= n)%nat.
Proof.
  intros A l n H. lia.
Qed.

Lemma lithium_forall_nth : forall {A : Type} (P : A -> Prop) (l : list A) (d : A) (i : nat),
  Forall P l ->
  (i < List.length l)%nat ->
  P (nth i l d).
Proof.
  intros A P l d i Hall Hi.
  apply Forall_nth; assumption.
Qed.

(** Export hints for Lithium *)
#[export] Hint Resolve lithium_byte_bounds lithium_list_length lithium_forall_nth : lithium.

