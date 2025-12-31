(** * Val Conversions for RefinedRust Integration

    This module provides definitions for working with Caesium values.
    In Caesium, [val] is [list mbyte] - a sequence of memory bytes.

    To create a val from integers, we use [val_of_Z] which requires
    specifying an integer type (for byte layout) and returns Option val.

    For specification purposes, we also provide [place_rfn] conversions
    using the [#] notation (PlaceIn).
*)

From Stdlib Require Import ZArith List Bool.
From caesium Require Import lang notation val int_type.
From refinedrust Require Import type typing shims.
Import ListNotations.

Open Scope Z_scope.

(** ------------------------------------------------------------------ *)
(** ** Place Refinement Conversions (for specifications)               *)
(** ------------------------------------------------------------------ *)

(** Convert Z to place refinement using PlaceIn *)
Definition Z_to_rfn (n : Z) : place_rfn Z := #n.

(** Convert nat to place refinement *)
Definition nat_to_rfn (n : nat) : place_rfn Z := #(Z.of_nat n).

(** Convert bool to place refinement *)
Definition bool_to_rfn (b : bool) : place_rfn Z := #(if b then 1 else 0).

(** ------------------------------------------------------------------ *)
(** ** Val Conversions (for runtime values)                            *)
(** ------------------------------------------------------------------ *)

(** Create val from Z with specific integer type.
    Returns None if value is out of range for the type. *)
Definition Z_to_val_typed (n : Z) (it : int_type) : option val :=
  val_of_Z n it None.

(** Common integer type shortcuts *)
Definition Z_to_val_u8 (n : Z) : option val := val_of_Z n u8 None.
Definition Z_to_val_u32 (n : Z) : option val := val_of_Z n u32 None.
Definition Z_to_val_u64 (n : Z) : option val := val_of_Z n u64 None.
Definition Z_to_val_i32 (n : Z) : option val := val_of_Z n i32 None.
Definition Z_to_val_i64 (n : Z) : option val := val_of_Z n i64 None.
Definition Z_to_val_usize (n : Z) : option val := val_of_Z n USize None.
Definition Z_to_val_isize (n : Z) : option val := val_of_Z n ISize None.

(** Convert nat to val using usize (common for lengths) *)
Definition nat_to_val_usize (n : nat) : option val :=
  val_of_Z (Z.of_nat n) USize None.

(** ------------------------------------------------------------------ *)
(** ** Location Conversions                                             *)
(** ------------------------------------------------------------------ *)

(** Convert location to val (pointer representation) *)
Definition loc_to_val (l : loc) : val := val_of_loc l.

(** Location to place refinement *)
Definition loc_to_rfn (l : loc) : place_rfn loc := #l.

(** ------------------------------------------------------------------ *)
(** ** Byte Validity                                                    *)
(** ------------------------------------------------------------------ *)

(** Check that a Z value is a valid byte *)
Definition is_byte (b : Z) : bool :=
  (0 <=? b)%Z && (b <? 256)%Z.

(** Check that a list contains only valid bytes *)
Definition all_bytes (bs : list Z) : bool :=
  forallb is_byte bs.

(** ------------------------------------------------------------------ *)
(** ** Key/Handle Conversions                                           *)
(** ------------------------------------------------------------------ *)

(** Key type encoding *)
Inductive key_type_tag : Set :=
  | KT_MlDsa87_Tag
  | KT_MlKem1024_Tag.

Definition key_type_to_Z (kt : key_type_tag) : Z :=
  match kt with
  | KT_MlDsa87_Tag => 0
  | KT_MlKem1024_Tag => 1
  end.

(** ------------------------------------------------------------------ *)
(** ** Specification Helpers                                            *)
(** ------------------------------------------------------------------ *)

(** Place refinement injectivity *)
Lemma Z_to_rfn_inj : forall n m : Z,
  Z_to_rfn n = Z_to_rfn m -> n = m.
Proof.
  intros n m H.
  unfold Z_to_rfn in H.
  injection H. auto.
Qed.

Lemma nat_to_rfn_inj : forall n m : nat,
  nat_to_rfn n = nat_to_rfn m -> n = m.
Proof.
  intros n m H.
  unfold nat_to_rfn in H.
  injection H. intros.
  lia.
Qed.

(** ------------------------------------------------------------------ *)
(** ** Type Class for Generic Conversions                               *)
(** ------------------------------------------------------------------ *)

(** Type class for types that can be converted to place refinement *)
Class ToRfn (A : Type) (R : Type) := {
  to_rfn : A -> place_rfn R
}.

#[global] Instance ToRfn_Z : ToRfn Z Z := {
  to_rfn := Z_to_rfn
}.

#[global] Instance ToRfn_nat : ToRfn nat Z := {
  to_rfn := nat_to_rfn
}.

#[global] Instance ToRfn_loc : ToRfn loc loc := {
  to_rfn := loc_to_rfn
}.

Close Scope Z_scope.
