type comparison = Eq | Lt | Gt

let id : 'a -> 'a = fun x -> x

module type Denum = sig
  type t

  val one : t
  val succ : t -> t
  val ( + ) : t -> t -> t
  val ( <= ) : t -> t -> bool
  val ( >= ) : t -> t -> bool
  val ( < ) : t -> t -> bool
  val ( > ) : t -> t -> bool
  val ( = ) : t -> t -> bool
  val sexp_of_t : t -> Sexplib0.Sexp.t
end

module Pos : Denum = struct
  (** val succ : positive -> positive **)
  type t = XI of t | XO of t | XH [@@deriving sexp_of]

  let one = XH
  let rec succ = function XI p -> XO (succ p) | XO p -> XI p | XH -> XO XH

  (** val add : positive -> positive -> positive **)
  let rec add x0 y =
    match x0 with
    | XI p -> (
        match y with
        | XI q -> XO (add_carry p q)
        | XO q -> XI (add p q)
        | XH -> XO (succ p))
    | XO p -> (
        match y with XI q -> XI (add p q) | XO q -> XO (add p q) | XH -> XI p)
    | XH -> ( match y with XI q -> XO (succ q) | XO q -> XI q | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x0 y =
    match x0 with
    | XI p -> (
        match y with
        | XI q -> XI (add_carry p q)
        | XO q -> XO (add_carry p q)
        | XH -> XI (succ p))
    | XO p -> (
        match y with
        | XI q -> XO (add_carry p q)
        | XO q -> XI (add p q)
        | XH -> XO (succ p))
    | XH -> (
        match y with XI q -> XI (succ q) | XO q -> XO (succ q) | XH -> XI XH)

  let ( + ) = add

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p -> (
        match y with
        | XI q -> compare_cont r p q
        | XO q -> compare_cont Gt p q
        | XH -> Gt)
    | XO p -> (
        match y with
        | XI q -> compare_cont Lt p q
        | XO q -> compare_cont r p q
        | XH -> Gt)
    | XH -> ( match y with XH -> r | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare = compare_cont Eq
  let ( < ) p p' = match compare p p' with Lt -> true | _ -> false
  let ( > ) p p' = match compare p p' with Gt -> true | _ -> false
  let ( <= ) p p' = match compare p p' with Lt | Eq -> true | _ -> false
  let ( >= ) p p' = match compare p p' with Gt | Eq -> true | _ -> false

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> ( match q with XI q0 -> eqb p0 q0 | _ -> false)
    | XO p0 -> ( match q with XO q0 -> eqb p0 q0 | _ -> false)
    | XH -> ( match q with XH -> true | _ -> false)

  let ( = ) = eqb
end

module Nat : Denum = struct
  type t = O | S of t [@@deriving sexp_of]

  let one = S O

  (** val succ : nat -> nat **)
  let succ x0 = S x0

  (** val add : nat -> nat -> nat **)

  let rec ( + ) n m = match n with O -> m | S p -> S (p + m)

  (** val eqb : nat -> nat -> bool **)

  let rec ( = ) n m =
    match n with
    | O -> ( match m with O -> true | S _ -> false)
    | S n' -> ( match m with O -> false | S m' -> n' = m')

  (** val leb : nat -> nat -> bool **)

  let rec ( <= ) n m =
    match n with
    | O -> true
    | S n' -> ( match m with O -> false | S m' -> n' <= m')

  let ( >= ) x y = y <= x

  (** val ltb : nat -> nat -> bool **)

  let ( < ) n m = S n <= m
  let ( > ) n m = S m <= n
end
