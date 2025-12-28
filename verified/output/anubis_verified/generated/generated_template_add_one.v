From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified Require Import generated_code_anubis_verified generated_specs_anubis_verified.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition add_one_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable (((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) →
  ⊢ typed_function π (add_one_def ) [(IntSynType U64); (IntSynType U64); ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_add_one  <INST!>) (λ π, True ∗ ⌜trait_incl_of_add_one <INST!>⌝)).
End proof.

Ltac add_one_prelude :=
  unfold add_one_lemma;
  set (FN_NAME := FUNCTION_NAME "add_one");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let x := fresh "x" in
  start_function "add_one" ϝ ( [] ) ( [] ) (  x ) (  x );
  intros arg_n local___0 local___2 local___3;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts (named_lft_update "_flft" ϝ $ named_lft_update "static" static $ ∅ );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
