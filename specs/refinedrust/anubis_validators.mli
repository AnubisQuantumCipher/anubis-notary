
type comparison =
| Eq
| Lt
| Gt

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison
 end

module Z :
 sig
  val mul : int -> int -> int

  val pow_pos : int -> int -> int

  val pow : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val ltb : int -> int -> bool
 end

module SpecValidators :
 sig
  val validate_index : int -> int -> bool

  val validate_threshold_params : int -> int -> bool

  val validate_nonce_params : int -> int -> bool

  val validate_byte : int -> bool

  val validate_u64 : int -> bool
 end
