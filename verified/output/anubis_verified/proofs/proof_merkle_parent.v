From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified.generated Require Import generated_code_anubis_verified generated_specs_anubis_verified generated_template_merkle_parent.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma merkle_parent_proof (π : thread_id) :
  merkle_parent_lemma π.
Proof.
  merkle_parent_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
