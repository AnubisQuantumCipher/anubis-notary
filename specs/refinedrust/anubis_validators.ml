
type comparison =
| Eq
| Lt
| Gt

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p) (succ p))
      (fun p -> (fun p->1+2*p) p)
      (fun _ -> (fun p->2*p) 1)
      x

  (** val add : int -> int -> int **)

  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun q -> (fun p->2*p) (add p q))
        (fun _ -> (fun p->1+2*p) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (succ q))
        (fun q -> (fun p->1+2*p) q)
        (fun _ -> (fun p->2*p) 1)
        y)
      x

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val mul : int -> int -> int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> add y ((fun p->2*p) (mul p y)))
      (fun p -> (fun p->2*p) (mul p y))
      (fun _ -> y)
      x

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : int -> int -> comparison **)

  let compare =
    compare_cont Eq
 end

module Z =
 struct
  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val pow_pos : int -> int -> int **)

  let pow_pos z0 =
    Pos.iter (mul z0) ((fun x -> x) 1)

  (** val pow : int -> int -> int **)

  let pow x y =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> (fun x -> x) 1)
      (fun p -> pow_pos x p)
      (fun _ -> 0)
      y

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
 end

module SpecValidators =
 struct
  (** val validate_index : int -> int -> bool **)

  let validate_index i max_nodes =
    (&&) (Z.leb 0 i) (Z.ltb i max_nodes)

  (** val validate_threshold_params : int -> int -> bool **)

  let validate_threshold_params threshold n_signers =
    (&&) ((&&) (Z.ltb 0 threshold) (Z.ltb 0 n_signers))
      (Z.leb threshold n_signers)

  (** val validate_nonce_params : int -> int -> bool **)

  let validate_nonce_params key_id counter =
    (&&)
      ((&&)
        ((&&) (Z.leb 0 key_id)
          (Z.ltb key_id
            (Z.pow ((fun x -> x) ((fun p->2*p) 1)) ((fun x -> x)
              ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
              ((fun p->2*p) 1)))))))))
        (Z.leb 0 counter))
      (Z.ltb counter
        (Z.pow ((fun x -> x) ((fun p->2*p) 1)) ((fun x -> x) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))))

  (** val validate_byte : int -> bool **)

  let validate_byte v =
    (&&) (Z.leb 0 v)
      (Z.ltb v ((fun x -> x) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        1))))))))))

  (** val validate_u64 : int -> bool **)

  let validate_u64 v =
    (&&) (Z.leb 0 v)
      (Z.ltb v
        (Z.pow ((fun x -> x) ((fun p->2*p) 1)) ((fun x -> x) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) 1)))))))))
 end
