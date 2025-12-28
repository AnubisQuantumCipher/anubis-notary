From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
Section code.
Context `{RRGS : !refinedrustGS Σ}.
Open Scope printing_sugar.

Definition add_one_def  : function := 
  {|
   f_args := [
    ("n", (it_layout U64) : layout)
   ];
   f_local_vars := [
    ("__0", (it_layout U64) : layout);
   ("__2", (it_layout U64) : layout);
   ("__3", (use_layout_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) : layout)
   ];
   f_code :=
    <[
   "_bb0" :=
    "__2" <-{ IntOp U64 } use{ IntOp U64 } ("n");
    "__3" <-{ (use_op_alg' ((tuple2_sls ((IntSynType U64)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType U64)) BoolSynType) [("0", (use{ IntOp U64 } ("__2")) +{ IntOp U64 , IntOp U64 } (i2v (1) U64) : expr); ("1", (use{ IntOp U64 } ("__2")) +c{ IntOp U64 , IntOp U64 } (i2v (1) U64) : expr)];
    assert{ BoolOp }: (use{ BoolOp } (("__3") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
    Goto "_bb1"
   ]>%E $
   <[
   "_bb1" :=
    "__0" <-{ IntOp U64 } use{ IntOp U64 } (("__3") at{ (tuple2_sls ((IntSynType U64)) (BoolSynType)) } "0");
    return (use{ IntOp U64 } ("__0"))
   ]>%E $
    ∅;
   f_init := "_bb0";
  |}.

Definition merkle_left_child_def  : function := 
  {|
   f_args := [
    ("index", (it_layout USize) : layout)
   ];
   f_local_vars := [
    ("__0", (it_layout USize) : layout);
   ("__2", (it_layout USize) : layout);
   ("__3", (use_layout_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) : layout)
   ];
   f_code :=
    <[
   "_bb0" :=
    "__2" <-{ IntOp USize } use{ IntOp USize } ("index");
    "__3" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (use{ IntOp USize } ("__2")) ×{ IntOp USize , IntOp USize } (i2v (2) USize) : expr); ("1", (use{ IntOp USize } ("__2")) ×c{ IntOp USize , IntOp USize } (i2v (2) USize) : expr)];
    assert{ BoolOp }: (use{ BoolOp } (("__3") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
    Goto "_bb1"
   ]>%E $
   <[
   "_bb1" :=
    "__0" <-{ IntOp USize } use{ IntOp USize } (("__3") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
    return (use{ IntOp USize } ("__0"))
   ]>%E $
    ∅;
   f_init := "_bb0";
  |}.

Definition merkle_parent_def  : function := 
  {|
   f_args := [
    ("index", (it_layout USize) : layout)
   ];
   f_local_vars := [
    ("__0", (it_layout USize) : layout);
   ("__2", (it_layout USize) : layout);
   ("__3", bool_layout : layout)
   ];
   f_code :=
    <[
   "_bb0" :=
    "__2" <-{ IntOp USize } use{ IntOp USize } ("index");
    "__3" <-{ BoolOp } (i2v (2) USize) = { IntOp USize , IntOp USize , U8 } (i2v (0) USize);
    assert{ BoolOp }: (use{ BoolOp } ("__3")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
    Goto "_bb1"
   ]>%E $
   <[
   "_bb1" :=
    "__0" <-{ IntOp USize } (use{ IntOp USize } ("__2")) /{ IntOp USize , IntOp USize } (i2v (2) USize);
    return (use{ IntOp USize } ("__0"))
   ]>%E $
    ∅;
   f_init := "_bb0";
  |}.

Definition merkle_right_child_def  : function := 
  {|
   f_args := [
    ("index", (it_layout USize) : layout)
   ];
   f_local_vars := [
    ("__0", (it_layout USize) : layout);
   ("__2", (it_layout USize) : layout);
   ("__3", (it_layout USize) : layout);
   ("__4", (use_layout_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) : layout);
   ("__5", (use_layout_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) : layout)
   ];
   f_code :=
    <[
   "_bb0" :=
    "__3" <-{ IntOp USize } use{ IntOp USize } ("index");
    "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (use{ IntOp USize } ("__3")) ×{ IntOp USize , IntOp USize } (i2v (2) USize) : expr); ("1", (use{ IntOp USize } ("__3")) ×c{ IntOp USize , IntOp USize } (i2v (2) USize) : expr)];
    assert{ BoolOp }: (use{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
    Goto "_bb1"
   ]>%E $
   <[
   "_bb1" :=
    "__2" <-{ IntOp USize } use{ IntOp USize } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
    "__5" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (use{ IntOp USize } ("__2")) +{ IntOp USize , IntOp USize } (i2v (1) USize) : expr); ("1", (use{ IntOp USize } ("__2")) +c{ IntOp USize , IntOp USize } (i2v (1) USize) : expr)];
    assert{ BoolOp }: (use{ BoolOp } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false);
    Goto "_bb2"
   ]>%E $
   <[
   "_bb2" :=
    "__0" <-{ IntOp USize } use{ IntOp USize } (("__5") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
    return (use{ IntOp USize } ("__0"))
   ]>%E $
    ∅;
   f_init := "_bb0";
  |}.

(* closure shims *)
End code.