(** Proof for is_left_child: Check if index is a left child (even) *)
From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified.generated Require Import
  generated_code_anubis_verified
  generated_specs_anubis_verified.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(** The function is_left_child returns true iff the index is even.

    Implementation:
      pub fn is_left_child(index: usize) -> bool { index % 2 == 0 }

    Specification:
      #[rr::params("i" : "Z")]
      #[rr::args("i")]
      #[rr::returns("bool_decide (Z.even i)")]

    The proof shows that:
    1. index % 2 == 0 is equivalent to Z.even index
    2. The bool result matches bool_decide
*)

Lemma is_left_child_correct : forall i : Z,
  (Z.modulo i 2 =? 0)%Z = Z.even i.
Proof.
  intros i.
  rewrite Z.even_spec.
  destruct (Z.modulo i 2 =? 0)%Z eqn:Hmod.
  - apply Z.eqb_eq in Hmod.
    exists (i / 2)%Z.
    rewrite Z.mul_comm.
    apply Z.div_exact in Hmod; [|lia].
    lia.
  - apply Z.eqb_neq in Hmod.
    intros [k Hk]. subst.
    rewrite Z.mul_comm, Z.mod_mul in Hmod; lia.
Qed.

End proof.
