
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

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
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

  let rec iter f x n0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n0

  (** val div2 : int -> int **)

  let div2 p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val div2_up : int -> int **)

  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

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

  (** val coq_Nsucc_double : int -> int **)

  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val coq_Ndouble : int -> int **)

  let coq_Ndouble n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n0

  (** val coq_lor : int -> int -> int **)

  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun _ -> p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p) (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p) p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> q)
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> q)
        q)
      p

  (** val coq_land : int -> int -> int **)

  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 1)
        (fun _ -> 0)
        (fun _ -> 1)
        q)
      p

  (** val ldiff : int -> int -> int **)

  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun _ -> p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 0)
        (fun _ -> 1)
        (fun _ -> 0)
        q)
      p

  (** val coq_lxor : int -> int -> int **)

  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p) p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p) q0))
        (fun q0 -> ((fun p->1+2*p) q0))
        (fun _ -> 0)
        q)
      p
 end

module Coq_Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val size : int -> int **)

  let rec size p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ (size p0))
      (fun p0 -> succ (size p0))
      (fun _ -> 1)
      p
 end

module N =
 struct
  (** val succ_pos : int -> int **)

  let succ_pos n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> Pos.succ p)
      n0

  (** val coq_lor : int -> int -> int **)

  let coq_lor n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> (Pos.coq_lor p q))
        m)
      n0

  (** val coq_land : int -> int -> int **)

  let coq_land n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> 0)
        (fun q -> Pos.coq_land p q)
        m)
      n0

  (** val ldiff : int -> int -> int **)

  let ldiff n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> Pos.ldiff p q)
        m)
      n0

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> Pos.coq_lxor p q)
        m)
      n0
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> (fun x -> x) ((fun p->2*p) p))
      (fun p -> (fun x -> -x) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> (fun x -> x) 1)
      (fun p -> (fun x -> x) ((fun p->1+2*p) p))
      (fun p -> (fun x -> -x) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> (fun x -> -x) 1)
      (fun p -> (fun x -> x) (Pos.pred_double p))
      (fun p -> (fun x -> -x) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> (fun x -> x) ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (fun x -> x) (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun x -> -x) ((fun p->2*p) q))
        (fun q -> (fun x -> -x) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

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

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val of_N : int -> int **)

  let of_N = fun p -> p

  (** val pos_div_eucl : int -> int -> int*int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let q,r = pos_div_eucl a' b in
      let r' = add (mul ((fun x -> x) ((fun p->2*p) 1)) r) ((fun x -> x) 1) in
      if ltb r' b
      then (mul ((fun x -> x) ((fun p->2*p) 1)) q),r'
      else (add (mul ((fun x -> x) ((fun p->2*p) 1)) q) ((fun x -> x) 1)),
             (sub r' b))
      (fun a' ->
      let q,r = pos_div_eucl a' b in
      let r' = mul ((fun x -> x) ((fun p->2*p) 1)) r in
      if ltb r' b
      then (mul ((fun x -> x) ((fun p->2*p) 1)) q),r'
      else (add (mul ((fun x -> x) ((fun p->2*p) 1)) q) ((fun x -> x) 1)),
             (sub r' b))
      (fun _ ->
      if leb ((fun x -> x) ((fun p->2*p) 1)) b
      then 0,((fun x -> x) 1)
      else ((fun x -> x) 1),0)
      a

  (** val div_eucl : int -> int -> int*int **)

  let div_eucl a b =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> 0,0)
      (fun a' ->
      (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
        (fun _ -> 0,a)
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let q,r = pos_div_eucl a' ((fun x -> x) b') in
        ((fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
           (fun _ -> (opp q),0)
           (fun _ -> (opp (add q ((fun x -> x) 1))),(add b r))
           (fun _ -> (opp (add q ((fun x -> x) 1))),(add b r))
           r))
        b)
      (fun a' ->
      (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
        (fun _ -> 0,a)
        (fun _ ->
        let q,r = pos_div_eucl a' b in
        ((fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
           (fun _ -> (opp q),0)
           (fun _ -> (opp (add q ((fun x -> x) 1))),(sub b r))
           (fun _ -> (opp (add q ((fun x -> x) 1))),(sub b r))
           r))
        (fun b' -> let q,r = pos_div_eucl a' ((fun x -> x) b') in q,(opp r))
        b)
      a

  (** val div : int -> int -> int **)

  let div a b =
    let q,_ = div_eucl a b in q

  (** val even : int -> bool **)

  let even z0 =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> true)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> true)
        (fun _ -> false)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> true)
        (fun _ -> false)
        p)
      z0

  (** val div2 : int -> int **)

  let div2 z0 =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> (fun x -> x) (Pos.div2 p))
        (fun _ -> (fun x -> x) (Pos.div2 p))
        (fun _ -> 0)
        p)
      (fun p -> (fun x -> -x) (Pos.div2_up p))
      z0

  (** val shiftl : int -> int -> int **)

  let shiftl a n0 =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> a)
      (fun p -> Pos.iter (mul ((fun x -> x) ((fun p->2*p) 1))) a p)
      (fun p -> Pos.iter div2 a p)
      n0

  (** val shiftr : int -> int -> int **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : int -> int -> int **)

  let coq_lor a b =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> b)
      (fun a0 ->
      (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (fun x -> x) (Pos.coq_lor a0 b0))
        (fun b0 -> (fun x -> -x) (N.succ_pos (N.ldiff (Pos.pred_N b0) a0)))
        b)
      (fun a0 ->
      (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (fun x -> -x)
        (N.succ_pos (N.ldiff (Pos.pred_N a0) b0)))
        (fun b0 -> (fun x -> -x)
        (N.succ_pos (N.coq_land (Pos.pred_N a0) (Pos.pred_N b0))))
        b)
      a

  (** val coq_land : int -> int -> int **)

  let coq_land a b =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun a0 ->
      (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (Pos.coq_land a0 b0))
        (fun b0 -> of_N (N.ldiff a0 (Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (N.ldiff b0 (Pos.pred_N a0)))
        (fun b0 -> (fun x -> -x)
        (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))
        b)
      a

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor a b =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> b)
      (fun a0 ->
      (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> of_N (Pos.coq_lxor a0 b0))
        (fun b0 -> (fun x -> -x)
        (N.succ_pos (N.coq_lxor a0 (Pos.pred_N b0))))
        b)
      (fun a0 ->
      (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (fun x -> -x)
        (N.succ_pos (N.coq_lxor (Pos.pred_N a0) b0)))
        (fun b0 -> of_N (N.coq_lxor (Pos.pred_N a0) (Pos.pred_N b0)))
        b)
      a

  (** val succ : int -> int **)

  let succ = Stdlib.Int.succ

  (** val pred : int -> int **)

  let pred = Stdlib.Int.pred

  (** val odd : int -> bool **)

  let odd z0 =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> false)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> true)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> true)
        p)
      z0

  (** val log2 : int -> int **)

  let log2 z0 =
    (fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p -> (fun x -> x) (Coq_Pos.size p))
        (fun p -> (fun x -> x) (Coq_Pos.size p))
        (fun _ -> 0)
        p0)
      (fun _ -> 0)
      z0

  (** val log2_up : int -> int **)

  let log2_up a =
    match compare ((fun x -> x) 1) a with
    | Lt -> succ (log2 (pred a))
    | _ -> 0

  (** val lnot : int -> int **)

  let lnot a =
    pred (opp a)
 end

module ExtractedModels =
 struct
  (** val merkle_parent : int -> int **)

  let merkle_parent i =
    Z.div i ((fun x -> x) ((fun p->2*p) 1))

  (** val merkle_left_child : int -> int **)

  let merkle_left_child i =
    Z.mul ((fun x -> x) ((fun p->2*p) 1)) i

  (** val merkle_right_child : int -> int **)

  let merkle_right_child i =
    Z.add (Z.mul ((fun x -> x) ((fun p->2*p) 1)) i) ((fun x -> x) 1)

  (** val merkle_sibling : int -> int **)

  let merkle_sibling i =
    Z.coq_lxor i ((fun x -> x) 1)

  (** val is_left_child : int -> bool **)

  let is_left_child =
    Z.even

  (** val is_right_child : int -> bool **)

  let is_right_child =
    Z.odd

  (** val tree_height : int -> int **)

  let tree_height =
    Z.log2_up

  (** val model_select : int -> int -> int -> int **)

  let model_select a b choice =
    let mask = Z.opp choice in
    Z.coq_lor (Z.coq_land a mask) (Z.coq_land b (Z.lnot mask))

  (** val ct_select : int -> int -> int -> int **)

  let ct_select =
    model_select

  (** val model_eq : int -> int -> int **)

  let model_eq a b =
    let diff = Z.coq_lxor a b in
    let collapsed =
      Z.shiftr (Z.coq_lor diff (Z.opp diff)) ((fun x -> x) ((fun p->1+2*p)
        ((fun p->1+2*p) 1)))
    in
    Z.coq_lxor (Z.coq_land collapsed ((fun x -> x) 1)) ((fun x -> x) 1)

  (** val ct_eq : int -> int -> int **)

  let ct_eq =
    model_eq

  (** val model_lt : int -> int -> int **)

  let model_lt a b =
    let not_a = Z.lnot a in
    let xor_ab = Z.coq_lxor a b in
    let not_xor = Z.lnot xor_ab in
    let diff = Z.sub a b in
    let term1 = Z.coq_land not_a b in
    let term2 = Z.coq_land not_xor diff in
    Z.coq_land
      (Z.shiftr (Z.coq_lor term1 term2) ((fun x -> x) ((fun p->1+2*p)
        ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
        1)))))))
      ((fun x -> x) 1)

  (** val ct_lt : int -> int -> int **)

  let ct_lt =
    model_lt

  (** val nonce_index : int -> int -> int **)

  let nonce_index key_id counter =
    Z.coq_lor
      (Z.shiftl key_id ((fun x -> x) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
      counter

  (** val nonce_key_id : int -> int **)

  let nonce_key_id idx =
    Z.shiftr idx ((fun x -> x) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1))))))

  (** val nonce_counter : int -> int **)

  let nonce_counter idx =
    Z.coq_land idx
      (Z.sub
        (Z.pow ((fun x -> x) ((fun p->2*p) 1)) ((fun x -> x) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
        ((fun x -> x) 1))

  (** val valid_threshold : int -> int -> bool **)

  let valid_threshold =
    Z.leb

  (** val signatures_needed : int -> int -> int **)

  let signatures_needed current threshold =
    Z.max 0 (Z.sub threshold current)
 end
