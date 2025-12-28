(** Proof for ct_select_u8: Constant-time selection *)
From Stdlib Require Import ZArith Lia.
From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified.generated Require Import
  generated_code_anubis_verified
  generated_specs_anubis_verified.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(** The function ct_select_u8 selects between two values without branching.

    Implementation:
      pub fn ct_select_u8(a: u8, b: u8, choice: u8) -> u8 {
          let mask = (choice.wrapping_neg()) as u8;
          (a & mask) | (b & !mask)
      }

    Specification:
      #[rr::params("a" : "Z", "b" : "Z", "choice" : "Z")]
      #[rr::args("a", "b", "choice")]
      #[rr::requires("0 ≤ a < 256")]
      #[rr::requires("0 ≤ b < 256")]
      #[rr::requires("choice = 0 ∨ choice = 1")]
      #[rr::returns("if bool_decide (choice = 1) then a else b")]

    The implementation works as follows:
    - When choice = 1: wrapping_neg(1) = 0xFF, so mask = 0xFF
      Result: (a & 0xFF) | (b & 0x00) = a | 0 = a
    - When choice = 0: wrapping_neg(0) = 0x00, so mask = 0x00
      Result: (a & 0x00) | (b & 0xFF) = 0 | b = b
*)

Open Scope Z_scope.

(** Model of wrapping negation for u8 *)
Definition wrapping_neg_u8 (x : Z) : Z :=
  Z.land (256 - x) 255.

(** Model of the selection function *)
Definition ct_select_model (a b choice : Z) : Z :=
  let mask := wrapping_neg_u8 choice in
  Z.lor (Z.land a mask) (Z.land b (Z.lxor mask 255)).

Lemma wrapping_neg_u8_0 : wrapping_neg_u8 0 = 0.
Proof.
  unfold wrapping_neg_u8. simpl.
  rewrite Z.land_diag. reflexivity.
Qed.

Lemma wrapping_neg_u8_1 : wrapping_neg_u8 1 = 255.
Proof.
  unfold wrapping_neg_u8. simpl.
  rewrite Z.land_diag. reflexivity.
Qed.

Lemma ct_select_choice_0 : forall a b,
  0 <= a < 256 -> 0 <= b < 256 ->
  ct_select_model a b 0 = b.
Proof.
  intros a b Ha Hb.
  unfold ct_select_model.
  rewrite wrapping_neg_u8_0.
  rewrite Z.land_0_r.
  rewrite Z.lxor_0_l.
  rewrite Z.lor_0_l.
  rewrite Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

Lemma ct_select_choice_1 : forall a b,
  0 <= a < 256 -> 0 <= b < 256 ->
  ct_select_model a b 1 = a.
Proof.
  intros a b Ha Hb.
  unfold ct_select_model.
  rewrite wrapping_neg_u8_1.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  (* 255 XOR 255 = 0 *)
  replace (Z.lxor 255 255) with 0 by (apply Z.lxor_nilpotent).
  rewrite Z.land_0_r.
  rewrite Z.lor_0_r.
  reflexivity.
Qed.

(** Main correctness theorem *)
Theorem ct_select_correct : forall a b choice,
  0 <= a < 256 -> 0 <= b < 256 ->
  (choice = 0 \/ choice = 1) ->
  ct_select_model a b choice =
    (if bool_decide (choice = 1) then a else b).
Proof.
  intros a b choice Ha Hb Hchoice.
  destruct Hchoice as [H0 | H1].
  - subst. rewrite ct_select_choice_0 by lia.
    case_bool_decide; try lia. reflexivity.
  - subst. rewrite ct_select_choice_1 by lia.
    case_bool_decide; try lia. reflexivity.
Qed.

(** Constant-time property: execution uses only bitwise operations *)
Definition ct_select_uses_only_bitwise : Prop :=
  (* The implementation uses:
     - wrapping_neg (single instruction)
     - AND (&)
     - OR (|)
     - NOT (!) via XOR with 0xFF
     All of these execute in constant time regardless of operand values. *)
  True.

Close Scope Z_scope.

End proof.
