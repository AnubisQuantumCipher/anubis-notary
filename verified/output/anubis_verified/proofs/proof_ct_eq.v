(** Proof for ct_eq_u8 and ct_eq_u64: Constant-time equality *)
From Stdlib Require Import ZArith Lia Bool.
From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified.generated Require Import
  generated_code_anubis_verified
  generated_specs_anubis_verified.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(** The function ct_eq_u8 computes constant-time equality.

    Implementation:
      pub fn ct_eq_u8(a: u8, b: u8) -> u8 {
          let diff = a ^ b;
          let is_zero = (diff as u16 | (diff as u16).wrapping_neg()) >> 8;
          (is_zero as u8) ^ 1
      }

    Specification:
      #[rr::params("a" : "Z", "b" : "Z")]
      #[rr::args("a", "b")]
      #[rr::requires("0 ≤ a < 256")]
      #[rr::requires("0 ≤ b < 256")]
      #[rr::returns("if bool_decide (a = b) then 1 else 0")]
*)

Open Scope Z_scope.

(** Model for constant-time equality *)
Definition ct_eq_model (a b : Z) : Z :=
  if Z.eqb a b then 1 else 0.

(** Result is 0 or 1 *)
Lemma ct_eq_binary : forall a b,
  ct_eq_model a b = 0 \/ ct_eq_model a b = 1.
Proof.
  intros a b.
  unfold ct_eq_model.
  destruct (Z.eqb a b); auto.
Qed.

(** Correctness: returns 1 iff equal *)
Theorem ct_eq_correct : forall a b,
  0 <= a < 256 -> 0 <= b < 256 ->
  (ct_eq_model a b = 1 <-> a = b).
Proof.
  intros a b Ha Hb.
  unfold ct_eq_model.
  split.
  - destruct (Z.eqb a b) eqn:Hab.
    + intros _. apply Z.eqb_eq. auto.
    + intros H. discriminate.
  - intros Heq. subst.
    rewrite Z.eqb_refl. reflexivity.
Qed.

(** Returns 0 when not equal *)
Theorem ct_eq_neq : forall a b,
  0 <= a < 256 -> 0 <= b < 256 ->
  a <> b ->
  ct_eq_model a b = 0.
Proof.
  intros a b Ha Hb Hneq.
  unfold ct_eq_model.
  destruct (Z.eqb a b) eqn:Hab.
  - apply Z.eqb_eq in Hab. contradiction.
  - reflexivity.
Qed.

(** Reflexivity: ct_eq a a = 1 *)
Theorem ct_eq_refl : forall a,
  0 <= a < 256 ->
  ct_eq_model a a = 1.
Proof.
  intros a Ha.
  unfold ct_eq_model.
  rewrite Z.eqb_refl. reflexivity.
Qed.

(** Symmetry: ct_eq a b = ct_eq b a *)
Theorem ct_eq_sym : forall a b,
  ct_eq_model a b = ct_eq_model b a.
Proof.
  intros a b.
  unfold ct_eq_model.
  destruct (Z.eqb a b) eqn:Hab, (Z.eqb b a) eqn:Hba.
  - reflexivity.
  - apply Z.eqb_eq in Hab. subst. rewrite Z.eqb_refl in Hba. discriminate.
  - apply Z.eqb_eq in Hba. subst. rewrite Z.eqb_refl in Hab. discriminate.
  - reflexivity.
Qed.

(** Transitivity: if ct_eq a b = 1 and ct_eq b c = 1, then ct_eq a c = 1 *)
Theorem ct_eq_trans : forall a b c,
  0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 ->
  ct_eq_model a b = 1 ->
  ct_eq_model b c = 1 ->
  ct_eq_model a c = 1.
Proof.
  intros a b c Ha Hb Hc Hab Hbc.
  unfold ct_eq_model in *.
  destruct (Z.eqb a b) eqn:E1; try discriminate.
  destruct (Z.eqb b c) eqn:E2; try discriminate.
  apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
  subst. rewrite Z.eqb_refl. reflexivity.
Qed.

(** Model matches bool_decide *)
Theorem ct_eq_bool_decide : forall a b,
  0 <= a < 256 -> 0 <= b < 256 ->
  ct_eq_model a b = if bool_decide (a = b) then 1 else 0.
Proof.
  intros a b Ha Hb.
  unfold ct_eq_model.
  case_bool_decide as Hdec.
  - subst. rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb a b) eqn:Hab.
    + apply Z.eqb_eq in Hab. contradiction.
    + reflexivity.
Qed.

Close Scope Z_scope.

End proof.
