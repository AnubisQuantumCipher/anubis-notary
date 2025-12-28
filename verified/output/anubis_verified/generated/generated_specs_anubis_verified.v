From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified Require Export generated_code_anubis_verified.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_merkle_right_child  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_merkle_right_child  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (i) : (((Z))),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) i :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(0 ≤ i)%Z⌝)
        ∗ (⌜((2 * i + 1) ∈ usize)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : (unit), (2 * i + 1) @ (int USize);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_merkle_parent  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_merkle_parent  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (i) : (((Z))),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) i :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(0 ≤ i)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : (unit), (i `quot` 2) @ (int USize);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_add_one  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_add_one  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : (((Z))),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64);
      (* precondition. *) (λ π : thread_id, (⌜((x + 1) ∈ u64)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : (unit), (x + 1) @ (int U64);
      (* postcondition *) (λ π : thread_id, True).

Definition trait_incl_of_merkle_left_child  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_merkle_left_child  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (i) : (((Z))),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) i :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(0 ≤ i)%Z⌝)
        ∗ (⌜((2 * i) ∈ usize)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : (unit), (2 * i) @ (int USize);
      (* postcondition *) (λ π : thread_id, True).




End specs.
