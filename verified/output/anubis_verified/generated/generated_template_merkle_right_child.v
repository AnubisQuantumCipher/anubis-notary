From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified Require Import generated_code_anubis_verified generated_specs_anubis_verified.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition merkle_right_child_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable (((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) →
  ⊢ typed_function π (merkle_right_child_def ) [(IntSynType USize); (IntSynType USize); (IntSynType USize); ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type); ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_merkle_right_child  <INST!>) (λ π, True ∗ ⌜trait_incl_of_merkle_right_child <INST!>⌝)).
End proof.

Ltac merkle_right_child_prelude :=
  unfold merkle_right_child_lemma;
  set (FN_NAME := FUNCTION_NAME "merkle_right_child");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let i := fresh "i" in
  start_function "merkle_right_child" ϝ ( [] ) ( [] ) (  i ) (  i );
  intros arg_index local___0 local___2 local___3 local___4 local___5;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
