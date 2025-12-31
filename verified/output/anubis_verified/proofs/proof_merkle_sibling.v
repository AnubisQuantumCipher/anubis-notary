(** Proof for merkle_sibling: Get sibling index via XOR *)
From Stdlib Require Import ZArith Lia.
From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified.generated Require Import
  generated_code_anubis_verified
  generated_specs_anubis_verified.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(** The function merkle_sibling returns index XOR 1.

    Implementation:
      pub fn merkle_sibling(index: usize) -> usize { index ^ 1 }

    Specification:
      #[rr::params("i" : "Z")]
      #[rr::args("i")]
      #[rr::requires("0 < i")]
      #[rr::returns("Z.lxor i 1")]

    Key properties:
    1. XOR with 1 flips the least significant bit
    2. For even i: sibling = i + 1 (right sibling)
    3. For odd i: sibling = i - 1 (left sibling)
    4. Involutive: sibling(sibling(i)) = i
*)

Open Scope Z_scope.

Lemma merkle_sibling_involutive : forall i,
  0 < i -> Z.lxor (Z.lxor i 1) 1 = i.
Proof.
  intros i Hi.
  rewrite Z.lxor_assoc.
  rewrite Z.lxor_nilpotent.
  rewrite Z.lxor_0_r.
  reflexivity.
Qed.

Lemma merkle_sibling_changes_parity : forall i,
  0 < i -> Z.even (Z.lxor i 1) = negb (Z.even i).
Proof.
  intros i Hi.
  rewrite Z.lxor_comm.
  rewrite Z.lxor_spec.
  (* XOR with 1 in bit 0 flips parity *)
  destruct (Z.even i) eqn:He.
  - (* i even, sibling odd *)
    simpl. reflexivity.
  - (* i odd, sibling even *)
    simpl. reflexivity.
Qed.

(** Helper: testbit 1 for n > 0 is false, since 1 = 2^0 *)
Lemma testbit_1_above_0 : forall n, 0 < n -> Z.testbit 1 n = false.
Proof.
  intros n Hn.
  replace 1 with (2^0) by reflexivity.
  apply Z.pow2_bits_false.
  lia.
Qed.

(** Key lemma: XOR with 1 only changes bit 0, so higher bits are preserved *)
Lemma lxor_1_higher_bits : forall i n, 0 <= i -> 0 < n ->
  Z.testbit (Z.lxor i 1) n = Z.testbit i n.
Proof.
  intros i n Hi Hn.
  rewrite Z.lxor_spec.
  rewrite testbit_1_above_0 by lia.
  rewrite Bool.xorb_false_r.
  reflexivity.
Qed.

(** Right shift by 1 is preserved under XOR with 1 *)
Lemma shiftr_lxor_1 : forall i, 0 <= i ->
  Z.shiftr (Z.lxor i 1) 1 = Z.shiftr i 1.
Proof.
  intros i Hi.
  apply Z.bits_inj'.
  intros n Hn.
  rewrite !Z.shiftr_spec by lia.
  apply lxor_1_higher_bits; lia.
Qed.

(** Z.shiftr i 1 = i / 2 for non-negative i *)
Lemma shiftr_1_div_2 : forall i, 0 <= i -> Z.shiftr i 1 = i / 2.
Proof.
  intros i Hi.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2^1) with 2 by reflexivity.
  reflexivity.
Qed.

(** XOR with 1 preserves non-negativity *)
Lemma lxor_1_nonneg : forall i, 0 <= i -> 0 <= Z.lxor i 1.
Proof.
  intros i Hi.
  apply Z.lxor_nonneg; lia.
Qed.

(** Main theorem: sibling index has the same parent.
    In Merkle trees, parent(i) = i / 2 = i quot 2.
    XOR with 1 only changes bit 0, which is discarded by division by 2.
*)
Lemma merkle_sibling_same_parent : forall i,
  0 < i -> (Z.lxor i 1) `quot` 2 = i `quot` 2.
Proof.
  intros i Hi.
  assert (H1: 0 <= i) by lia.
  assert (H2: 0 <= Z.lxor i 1) by (apply lxor_1_nonneg; lia).
  (* Convert quot to div for non-negative numbers *)
  rewrite Z.quot_div_nonneg by lia.
  rewrite Z.quot_div_nonneg by lia.
  (* Convert div by 2 to shiftr by 1 *)
  rewrite <- shiftr_1_div_2 by lia.
  rewrite <- shiftr_1_div_2 by lia.
  (* Apply the key lemma *)
  apply shiftr_lxor_1. lia.
Qed.

Close Scope Z_scope.

End proof.
