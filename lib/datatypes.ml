type comparison = Eq | Lt | Gt

let compOpp = function Eq -> Eq | Lt -> Gt | Gt -> Lt
let id : 'a -> 'a = fun x -> x

(** val compOpp : comparison -> comparison **)
module type Denum = sig
  type t

  val one : t
  val succ : t -> t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( <= ) : t -> t -> bool
  val ( >= ) : t -> t -> bool
  val ( < ) : t -> t -> bool
  val ( > ) : t -> t -> bool
  val ( = ) : t -> t -> bool
  val of_int : int -> t
  val sexp_of_t : t -> Sexplib0.Sexp.t
end

module Z : Denum = struct
  module Pos = struct
    type t = XI of t | XO of t | XH

    let sexp_of_t =
      let open Core.Int64 in
      let one = of_int 1 in
      let rec go = function
        | XI x -> (go x lsl 1) + one
        | XO x -> go x lsl 1
        | XH -> one
      in
      fun x -> sexp_of_t (go x)

    let of_int =
      let rec go (n : int) =
        if n <= 1 then XH
        else if n mod 2 = 1 then XI (go (n lsr 1))
        else XO (go (n lsr 1))
      in
      go

    (** val succ : positive -> positive **)
    let rec succ = function XI p -> XO (succ p) | XO p -> XI p | XH -> XO XH

    (** val add : positive -> positive -> positive **)

    let rec add x0 y0 =
      match x0 with
      | XI p -> (
          match y0 with
          | XI q -> XO (add_carry p q)
          | XO q -> XI (add p q)
          | XH -> XO (succ p))
      | XO p -> (
          match y0 with
          | XI q -> XI (add p q)
          | XO q -> XO (add p q)
          | XH -> XI p)
      | XH -> (
          match y0 with XI q -> XO (succ q) | XO q -> XI q | XH -> XO XH)

    (** val add_carry : positive -> positive -> positive **)

    and add_carry x0 y0 =
      match x0 with
      | XI p -> (
          match y0 with
          | XI q -> XI (add_carry p q)
          | XO q -> XO (add_carry p q)
          | XH -> XI (succ p))
      | XO p -> (
          match y0 with
          | XI q -> XO (add_carry p q)
          | XO q -> XI (add p q)
          | XH -> XO (succ p))
      | XH -> (
          match y0 with
          | XI q -> XI (succ q)
          | XO q -> XO (succ q)
          | XH -> XI XH)

    (** val pred_double : positive -> positive **)

    let rec pred_double = function
      | XI p -> XI (XO p)
      | XO p -> XI (pred_double p)
      | XH -> XH

    (** val compare_cont : comparison -> positive -> positive -> comparison **)

    let rec compare_cont r x0 y0 =
      match x0 with
      | XI p -> (
          match y0 with
          | XI q -> compare_cont r p q
          | XO q -> compare_cont Gt p q
          | XH -> Gt)
      | XO p -> (
          match y0 with
          | XI q -> compare_cont Lt p q
          | XO q -> compare_cont r p q
          | XH -> Gt)
      | XH -> ( match y0 with XH -> r | _ -> Lt)

    (** val compare : positive -> positive -> comparison **)

    let compare = compare_cont Eq
  end

  type t = Z0 | Zpos of Pos.t | Zneg of Pos.t [@@deriving sexp_of]

  let one = Zpos Pos.XH

  let of_int n =
    if n < 0 then Zneg (Pos.of_int (-n))
    else if n = 0 then Z0
    else Zpos (Pos.of_int n)

  (** val double : t -> t **)

  let double = function
    | Z0 -> Z0
    | Zpos p -> Zpos (XO p)
    | Zneg p -> Zneg (XO p)

  (** val succ_double : t -> t **)

  let succ_double = function
    | Z0 -> Zpos XH
    | Zpos p -> Zpos (XI p)
    | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : t -> t **)

  let pred_double = function
    | Z0 -> Zneg XH
    | Zpos p -> Zpos (Pos.pred_double p)
    | Zneg p -> Zneg (XI p)

  (** val pos_sub : Pos.t -> Pos.t -> t **)

  let rec pos_sub x0 y0 =
    match x0 with
    | Pos.XI p -> (
        match y0 with
        | Pos.XI q -> double (pos_sub p q)
        | Pos.XO q -> succ_double (pos_sub p q)
        | Pos.XH -> Zpos (XO p))
    | Pos.XO p -> (
        match y0 with
        | Pos.XI q -> pred_double (pos_sub p q)
        | Pos.XO q -> double (pos_sub p q)
        | Pos.XH -> Zpos (Pos.pred_double p))
    | Pos.XH -> (
        match y0 with
        | Pos.XI q -> Zneg (XO q)
        | Pos.XO q -> Zneg (Pos.pred_double q)
        | Pos.XH -> Z0)

  (** val add : t -> t -> t **)

  let ( + ) x0 y0 =
    match x0 with
    | Z0 -> y0
    | Zpos x' -> (
        match y0 with
        | Z0 -> x0
        | Zpos y' -> Zpos (Pos.add x' y')
        | Zneg y' -> pos_sub x' y')
    | Zneg x' -> (
        match y0 with
        | Z0 -> x0
        | Zpos y' -> pos_sub y' x'
        | Zneg y' -> Zneg (Pos.add x' y'))

  let succ x = x + one

  (** val opp : t -> t **)

  let opp = function Z0 -> Z0 | Zpos x1 -> Zneg x1 | Zneg x1 -> Zpos x1

  (** val sub : t -> t -> t **)

  let ( - ) m n = m + opp n

  (** val compare : t -> t -> comparison **)

  let compare x0 y0 =
    match x0 with
    | Z0 -> ( match y0 with Z0 -> Eq | Zpos _ -> Lt | Zneg _ -> Gt)
    | Zpos x' -> ( match y0 with Zpos y' -> Pos.compare x' y' | _ -> Gt)
    | Zneg x' -> (
        match y0 with Zneg y' -> compOpp (Pos.compare x' y') | _ -> Lt)

  let ( = ) x0 y0 = match compare x0 y0 with Eq -> true | _ -> false

  (** val ltb : t -> t -> bool **)

  let ( < ) x0 y0 = match compare x0 y0 with Lt -> true | _ -> false
  let ( <= ) x0 y0 = match compare x0 y0 with Lt | Eq -> true | _ -> false

  (** val gtb : t -> t -> bool **)

  let ( > ) x0 y0 = match compare x0 y0 with Gt -> true | _ -> false
  let ( >= ) x0 y0 = match compare x0 y0 with Gt | Eq -> true | _ -> false
end
