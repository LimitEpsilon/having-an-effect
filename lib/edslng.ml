(** Adapted from https://okmij.org/ftp/Computation/having-effect.html *)

open Debug
open Core
open Effect
open Effect.Deep

type (_, _) refl = Refl : ('a, 'a) refl
type pure = Pure_ty
type (_, _) dom = ..
type (_, _) dom += Pure : 'a -> ('a, pure) dom
type _ tag = ..
type _ tag += Pure_tag : pure tag

let eqb_tag : type a b. a tag -> b tag -> (a, b) refl option =
 fun x y ->
  match x with
  | Pure_tag -> ( match y with Pure_tag -> Some Refl | _ -> None)
  | _ -> None

(*
 * ------------------------------------------------------------------------
 * First language: integers
 *)

type _ Effect.t +=
  | Int : (int * 'repr tag) -> (int, 'repr) dom t
  | Add :
      ((int, 'repr) dom * (int, 'repr) dom * 'repr tag)
      -> (int, 'repr) dom t

let int i (tag : 'repr tag) = perform (Int (i, tag))

let ( + ) (type repr) (x : repr tag -> (int, repr) dom)
    (y : repr tag -> (int, repr) dom) (tag : repr tag) : (int, repr) dom =
  let x = x tag in
  let y = y tag in
  perform (Add (x, y, tag))

(* Examples: the first term in our simple language *)
module TInc = struct
  let res : type repr. repr tag -> (int, repr) dom =
   fun tag -> (int 2 + int 3 + int 4) tag
end

let int_h :
    type a repr.
    int ->
    repr tag ->
    (((int, repr) dom, (a, repr) dom) continuation -> (a, repr) dom) option =
 fun i ->
  if debug.get () then Printf.printf "Handle Int %d\n" i;

  function Pure_tag -> Some (fun k -> continue k (Pure i)) | _ -> None

let add_h :
    type a repr.
    (int, repr) dom ->
    (int, repr) dom ->
    repr tag ->
    (((int, repr) dom, (a, repr) dom) continuation -> (a, repr) dom) option =
 fun x y ->
  if debug.get () then Printf.printf "Handle Add\n";

  function
  | Pure_tag ->
      Some
        (fun k ->
          match (x, y) with
          | Pure x, Pure y -> continue k (Pure Int.(x + y))
          | _, _ -> raise @@ Invalid_argument "Not expected tag")
  | _ -> None

(*
 * ------------------------------------------------------------------------
 * First extension: if-then-else
 *)

type _ Effect.t +=
  | Eq :
      ((int, 'repr) dom * (int, 'repr) dom * 'repr tag)
      -> (bool, 'repr) dom Effect.t
  | Cond :
      ((bool, 'repr) dom
      * ('repr tag -> ('res, 'repr) dom)
      * ('repr tag -> ('res, 'repr) dom)
      * 'repr tag)
      -> ('repr tag -> ('res, 'repr) dom) Effect.t

let cond pred con alt (tag : 'repr tag) =
  perform (Cond (pred tag, con, alt, tag)) tag

let eq x y (tag : 'repr tag) =
  let x = x tag in
  let y = y tag in
  perform (Eq (x, y, tag))

module TIf = struct
  let tinc =
    let module M = TInc in
    M.res (* earlier term*)

  (* Example, reusing the earlier TInc *)
  let res : type res repr. repr tag -> (int, repr) dom =
   fun tag -> cond (eq (int 3) tinc) (int 10) (tinc + int 1) tag
end

let eq_h :
    type a repr.
    (int, repr) dom ->
    (int, repr) dom ->
    repr tag ->
    (((bool, repr) dom, (a, repr) dom) continuation -> (a, repr) dom) option =
 fun x y ->
  if debug.get () then Printf.printf "Handle Eq\n";

  function
  | Pure_tag ->
      Some
        (fun k ->
          match (x, y) with
          | Pure x, Pure y -> continue k (Pure Int.(x = y))
          | _, _ -> failwith "unexpected tag")
  | _ -> None

let cond_h :
    type a res repr.
    (bool, repr) dom ->
    (repr tag -> (res, repr) dom) ->
    (repr tag -> (res, repr) dom) ->
    repr tag ->
    ((repr tag -> (res, repr) dom, (a, repr) dom) continuation -> (a, repr) dom)
    option =
 fun pred con alt ->
  if debug.get () then Printf.printf "Handle Cond\n";

  function
  | Pure_tag ->
      Some
        (fun k ->
          match pred with
          | Pure true -> continue k con
          | Pure false -> continue k alt
          | _ -> failwith "cond type error")
  | _ -> None

(* * ------------------------------------------------------------------------ *
   Adding state *)

type _ Effect.t +=
  | Get : 'repr tag -> (int, 'repr) dom Effect.t
  | Put : ((int, 'repr) dom * 'repr tag) -> (int, 'repr) dom Effect.t

let get (tag : 'repr tag) = perform (Get tag)

let put x (tag : 'repr tag) =
  let x = x tag in
  perform (Put (x, tag))

module TSt = struct
  let tinc =
    let module M = TInc in
    M.res (* earlier term*)

  let res : type repr. repr tag -> (int, repr) dom =
   fun tag ->
    cond (eq (int 3) (put tinc)) (put (int 20)) (put (int 1 + get)) tag
end

(* We need to handle the State requests. *)

let get_h :
    type a repr.
    repr tag ->
    (( (int, repr) dom,
       state:(int, repr) dom -> (a * int, repr) dom )
     continuation ->
    state:(int, repr) dom ->
    (a * int, repr) dom)
    option = function
  | Pure_tag ->
      if debug.get () then Printf.printf "Handle Get\n";

      Some (fun k ~state -> continue k state ~state)
  | _ -> None

let put_h :
    type a repr.
    (int, repr) dom ->
    repr tag ->
    (( (int, repr) dom,
       state:(int, repr) dom -> (a * int, repr) dom )
     continuation ->
    state:(int, repr) dom ->
    (a * int, repr) dom)
    option =
 fun v ->
  if debug.get () then Printf.printf "Handle Put\n";

  function
  | Pure_tag -> Some (fun k ~state:_ -> continue k v ~state:v) | _ -> None

let dom_tuple (type repr a b) (r : repr tag) (x : (a, repr) dom)
    (y : (b, repr) dom) : (a * b, repr) dom =
  match r with
  | Pure_tag -> (
      match (x, y) with Pure x, Pure y -> Pure (x, y) | _, _ -> assert false)
  | _ -> assert false

let state_h :
    type a repr.
    repr tag ->
    ((a, repr) dom, state:(int, repr) dom -> (a * int, repr) dom) handler =
 fun tag ->
  {
    retc = (fun v ~state -> dom_tuple tag v state);
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        match eff with
        | Get tag' -> (
            match eqb_tag tag tag' with
            | Some Refl ->
                let res :
                    (( c,
                       state:(int, repr) dom -> (a * int, repr) dom )
                     continuation ->
                    state:(int, repr) dom ->
                    (a * int, repr) dom)
                    option =
                  get_h tag
                in
                res
            | None -> None)
        | Put (state, tag') -> (
            match eqb_tag tag tag' with
            | Some Refl -> put_h state tag
            | None -> None)
        | _ -> None);
  }

(*
 * ------------------------------------------------------------------------
 * Adding first-class functions
 *)

type _ ty =
  | Ity : int ty
  | Bty : bool ty
  | Fty : ('a ty * 'b ty) -> ('a -> 'b) ty

let rec eqb_ty : type a b. a ty -> b ty -> (a, b) refl option =
 fun x y ->
  match x with
  | Ity -> ( match y with Ity -> Some Refl | _ -> None)
  | Bty -> ( match y with Bty -> Some Refl | _ -> None)
  | Fty (a1, a2) -> (
      match y with
      | Fty (b1, b2) -> (
          match (eqb_ty a1 b1, eqb_ty a2 b2) with
          | Some Refl, Some Refl -> Some Refl
          | _, _ -> None)
      | _ -> None)

type _ var = TVar : (string * 'a ty) -> 'a var
type _ entry = Ent : ('a var * ('a, 'repr) dom) -> 'repr entry

type _ Effect.t +=
  | Var : ('a var * 'repr tag) -> ('a, 'repr) dom Effect.t
  | Lam :
      ('a var * ('repr tag -> ('b, 'repr) dom) * 'repr tag)
      -> ('a -> 'b, 'repr) dom Effect.t
  | App :
      (('a -> 'b, 'repr) dom * ('a, 'repr) dom * 'repr tag)
      -> ('repr tag -> ('b, 'repr) dom) Effect.t

let var x ty (tag : 'repr tag) = perform (Var (TVar (x, ty), tag))
let lam x ty body (tag : 'repr tag) = perform (Lam (TVar (x, ty), body, tag))

let ( $$ ) fn arg : 'repr tag -> ('b, 'repr) dom =
 fun tag ->
  let fn = fn tag in
  let arg = arg tag in
  perform (App (fn, arg, tag)) tag

module TLam = struct
  let tinc =
    let module M = TInc in
    M.res (* earlier term*)

  let res0 : type repr. repr tag -> (int -> int, repr) dom =
   fun tag -> lam "x" Ity (var "x" Ity + int 1) tag

  let res01 : type repr. repr tag -> (int, repr) dom =
   fun tag -> (res0 $$ tinc) tag

  let res1 : type repr. repr tag -> (int -> int -> int, repr) dom =
   fun tag ->
    lam "x" Ity
      (lam "y" Ity
      @@ cond
           (eq (var "x" Ity) (var "y" Ity))
           (var "x" Ity)
           (var "y" Ity + int 1))
      tag

  let res11 : type repr. repr tag -> (int, repr) dom =
   fun tag -> (res1 $$ int 1 $$ int 2) tag

  (* Higher-order functions *)
  let res2 : type repr. repr tag -> (int, repr) dom =
   fun tag ->
    (lam "z"
       (Fty (Ity, Ity))
       (lam "x" Ity (var "z" (Fty (Ity, Ity)) $$ var "x" Ity))
    $$ (res1 $$ int 1)
    $$ (* partial application of res1 *)
    int 2)
      tag
end

(* Implementation: lexical scope, call-by-value, left-to-right *)

let rec lookup : type a repr. a var -> repr entry list -> (a, repr) dom =
 fun (TVar (x, ty)) l ->
  match l with
  | [] -> failwith @@ "unbound variable " ^ x
  | Ent (TVar (h, ty'), v) :: t when String.(x = h) -> (
      match eqb_ty ty ty' with
      | Some Refl -> v
      | None -> lookup (TVar (x, ty)) t)
  | _ :: t -> lookup (TVar (x, ty)) t

type 'repr env = 'repr entry list

let var_h :
    type a b repr.
    b var ->
    repr tag ->
    (((b, repr) dom, env:repr env -> (a, repr) dom) continuation ->
    env:repr env ->
    (a, repr) dom)
    option =
 fun x ->
  let () =
    if debug.get () then
      let (TVar (x, _)) = x in
      Printf.printf "Handle Var %s\n" x
  in

  function
  | Pure_tag -> Some (fun k ~env -> continue k (lookup x env) ~env) | _ -> None

let lam_h :
    type a b c repr.
    ((c, repr) dom, env:repr env -> (c, repr) dom) handler ->
    b var ->
    (repr tag -> (c, repr) dom) ->
    repr tag ->
    (((b -> c, repr) dom, env:repr env -> (a, repr) dom) continuation ->
    env:repr env ->
    (a, repr) dom)
    option =
 fun env_h x body ->
  let () =
    if debug.get () then
      let (TVar (x, _)) = x in
      Printf.printf "Handle λ %s. _\n" x
  in

  function
  | Pure_tag ->
      Some
        (fun k ~env ->
          continue k
            (Pure
               (fun v ->
                 let env' = Ent (x, Pure v) :: env in
                 let (ret : (c, pure) dom) =
                   match_with body Pure_tag env_h ~env:env'
                 in
                 match ret with Pure ret -> ret | _ -> assert false))
            ~env)
  | _ -> None

let app_h :
    type a b c repr.
    (b -> c, repr) dom ->
    (b, repr) dom ->
    repr tag ->
    ((repr tag -> (c, repr) dom, env:repr env -> (a, repr) dom) continuation ->
    env:repr env ->
    (a, repr) dom)
    option =
 fun fn arg ->
  if debug.get () then Printf.printf "Handle App\n";

  function
  | Pure_tag ->
      Some
        (fun k ~env ->
          match fn with
          | Pure fn ->
              let arg = match arg with Pure arg -> arg | _ -> assert false in
              let v _tag : (c, repr) dom = Pure (fn arg) in
              continue k v ~env
          | _ -> failwith "type error in app")
  | _ -> None

let rec env_h :
    type a repr.
    repr tag -> ((a, repr) dom, env:repr env -> (a, repr) dom) handler =
 fun tag ->
  {
    retc = (fun v ~env:_ -> v);
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        match eff with
        | Var (x, tag') -> (
            match eqb_tag tag tag' with
            | Some Refl ->
                let res :
                    ((c, env:repr env -> (a, repr) dom) continuation ->
                    env:repr env ->
                    (a, repr) dom)
                    option =
                  var_h x tag
                in
                res
            | None -> None)
        | Lam (x, body, tag') -> (
            match eqb_tag tag tag' with
            | Some Refl -> lam_h (env_h tag) x body tag
            | None -> None)
        | App (fn, arg, tag') -> (
            match eqb_tag tag tag' with
            | Some Refl -> app_h fn arg tag
            | None -> None)
        | _ -> None);
  }

(* Other calling conventions (call-by-name, etc) and dynamic scope are left as
   an exercise to the reader *)

(*
 * ------------------------------------------------------------------------
 * Higher-order plus State: combining the existing features
 *)
module TLamSt = struct
  let incf : type repr. repr tag -> (int -> int, repr) dom =
    let module M = TLam in
    M.res0 (* increment function *)

  let incs : type repr. repr tag -> (int, repr) dom =
   fun tag -> put (incf $$ get) tag

  (* incf but counting the invocation in the state *)
  (* λx.(λ_.x + 10) incs *)
  let incf : type repr. repr tag -> (int -> int, repr) dom =
   fun tag -> lam "x" Ity (lam "_" Ity (var "x" Ity + int 10) $$ incs) tag

  (* λf.λz.f (f z) *)
  let c2 : type repr. repr tag -> ((int -> int) -> int -> int, repr) dom =
   fun tag ->
    lam "f"
      (Fty (Ity, Ity))
      (lam "z" Ity
         (var "f" (Fty (Ity, Ity)) $$ (var "f" (Fty (Ity, Ity)) $$ var "z" Ity)))
      tag

  let res : type repr. repr tag -> (int, repr) dom =
   fun tag -> ((c2 $$ incf $$ int 100) + get) tag
end

let eval_h : type a repr. repr tag -> ((a, repr) dom, (a, repr) dom) handler =
 fun tag ->
  {
    retc = (fun v -> v);
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        match eff with
        | Int (i, tag') -> (
            match eqb_tag tag tag' with
            | Some Refl ->
                let res :
                    ((c, (a, repr) dom) continuation -> (a, repr) dom) option =
                  int_h i tag
                in
                res
            | None -> None)
        | Add (x, y, tag') -> (
            match eqb_tag tag tag' with
            | Some Refl -> add_h x y tag
            | None -> None)
        | Eq (x, y, tag') -> (
            match eqb_tag tag tag' with
            | Some Refl -> eq_h x y tag
            | None -> None)
        | Cond (pred, con, alt, tag') -> (
            match eqb_tag tag tag' with
            | Some Refl -> cond_h pred con alt tag
            | None -> None)
        | _ -> None);
  }

let eval (type a repr) (tag : repr tag) (state : (int, repr) dom)
    (e : repr tag -> (a, repr) dom) =
  let env = [] in
  let comp = e in
  let comp x = match_with comp x (eval_h tag) in
  let comp x = match_with comp x (state_h tag) ~state in
  let comp x = match_with comp x (env_h tag) ~env in
  comp tag

let eval_v e =
  match eval Pure_tag (Pure 0) e with Pure (x, _) -> x | _ -> assert false
