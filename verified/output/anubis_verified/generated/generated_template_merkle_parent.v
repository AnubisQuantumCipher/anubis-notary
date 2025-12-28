From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified Require Import generated_code_anubis_verified generated_specs_anubis_verified.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition merkle_parent_lemma (π : thread_id) : Prop :=
  ⊢ typed_function π (merkle_parent_def ) [(IntSynType USize); (IntSynType USize); BoolSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_merkle_parent  <INST!>) (λ π, True ∗ ⌜trait_incl_of_merkle_parent <INST!>⌝)).
End proof.

Ltac merkle_parent_prelude :=
  unfold merkle_parent_lemma;
  set (FN_NAME := FUNCTION_NAME "merkle_parent");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let i := fresh "i" in
  start_function "merkle_parent" ϝ ( [] ) ( [] ) (  i ) (  i );
  intros arg_index local___0 local___2 local___3;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
