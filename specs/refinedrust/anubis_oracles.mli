
type comparison =
| Eq
| Lt
| Gt

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred_N : int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val div2 : int -> int

  val div2_up : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int
 end

module N :
 sig
  val succ_pos : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val pow_pos : int -> int -> int

  val pow : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val eqb : int -> int -> bool

  val of_N : int -> int

  val pos_div_eucl : int -> int -> int*int

  val div_eucl : int -> int -> int*int

  val div : int -> int -> int

  val div2 : int -> int

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val coq_lxor : int -> int -> int

  val pred : int -> int

  val lnot : int -> int
 end

module ExtractedModels :
 sig
  val merkle_parent : int -> int

  val merkle_left_child : int -> int

  val merkle_right_child : int -> int

  val merkle_sibling : int -> int

  val model_select : int -> int -> int -> int

  val nonce_index : int -> int -> int

  val nonce_key_id : int -> int

  val nonce_counter : int -> int

  val valid_threshold : int -> int -> bool
 end

module TestOracles :
 sig
  val oracle_parent_child : int -> bool

  val oracle_sibling_involutive : int -> bool

  val oracle_model_select : int -> int -> bool

  val oracle_ct_select : int -> int -> bool

  val oracle_nonce_roundtrip : int -> int -> bool

  val oracle_threshold_monotonic : int -> int -> int -> bool
 end
