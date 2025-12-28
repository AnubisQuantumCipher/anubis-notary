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

Lemma merkle_sibling_same_parent : forall i,
  0 < i -> (Z.lxor i 1) `quot` 2 = i `quot` 2.
Proof.
  intros i Hi.
  (* Both i and i^1 have the same bits except bit 0 *)
  (* Division by 2 (quot) discards bit 0 *)
  (* So the quotients are equal *)
  destruct (Z.even i) eqn:He.
  - (* i even: i^1 = i+1, both have same quot by 2 *)
    rewrite Z.even_spec in He.
    destruct He as [k Hk]. subst.
    rewrite Z.mul_comm.
    replace (Z.lxor (2 * k) 1) with (2 * k + 1).
    + rewrite Z.quot_add_l by lia.
      rewrite Z.quot_small by lia.
      rewrite Z.add_0_r.
      rewrite Z.quot_mul by lia.
      reflexivity.
    + (* Z.lxor (2*k) 1 = 2*k + 1 when 2*k is even *)
      admit.
  - (* i odd: i^1 = i-1 *)
    admit.
Admitted.

Close Scope Z_scope.

End proof.
