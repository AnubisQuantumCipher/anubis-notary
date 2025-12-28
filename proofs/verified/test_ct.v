From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

Definition ct_select_impl_xor (choice : Z) (a b : Z) : Z :=
  let mask := Z.land (0 - choice) 255 in
  Z.lxor (Z.land mask (Z.lxor a b)) b.

Lemma test_choice_0 : forall a b : Z, ct_select_impl_xor 0 a b = b.
Proof.
  intros a b.
  unfold ct_select_impl_xor.
  (* Let's see what simpl does *)
  simpl.
  (* Now the goal should be: Z.lxor (Z.land 0 (Z.lxor a b)) b = b *)
  reflexivity.
Qed.
