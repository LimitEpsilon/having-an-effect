(** Adapted from https://okmij.org/ftp/Computation/having-effect.html *)

open Core
open Effect
open Effect.Deep

type 'a get_set = { get : unit -> 'a; set : 'a -> unit }

(*module X (Y : Tuple.Comparable_sexpable) = Core.Tuple.Comparable (Int) (Y)*)

let debug =
  let b = ref false in
  { get = (fun () -> !b); set = (fun debug' -> b := debug') }

type v = ..
type 'dom tag = ..
type 'dom tag += V : v tag

(*
 * ------------------------------------------------------------------------
 * First language: integers
 *)

type _ Effect.t +=
  | Int : (int * 'dom tag) -> 'dom t
  | Add : ('dom * 'dom * 'dom tag) -> 'dom t

let int i (tag : 'dom tag) = perform (Int (i, tag))

let ( + ) (type dom) (x : dom tag -> dom) (y : dom tag -> dom) (tag : dom tag) :
    dom =
  let x = x tag in
  let y = y tag in
  perform (Add (x, y, tag))

(* Examples: the first term in our simple language *)
module TInc = struct
  let res : type dom. dom tag -> dom = fun tag -> (int 2 + int 3 + int 4) tag
end

type v += VInt of int (* add integers to our value domain *)

let int_h : type a dom. int -> dom tag -> ((dom, a) continuation -> a) option =
 fun i ->
  if debug.get () then Printf.printf "Handle Int %d\n" i;

  function V -> Some (fun k -> continue k (VInt i)) | _ -> None

let add_h :
    type a dom. dom -> dom -> dom tag -> ((dom, a) continuation -> a) option =
 fun x y ->
  if debug.get () then Printf.printf "Handle Add\n";

  function
  | V ->
      Some
        (fun k ->
          match (x, y) with
          | VInt x, VInt y -> continue k (VInt Int.(x + y))
          | _, _ -> failwith "addition type error")
  | _ -> None

(*
 * ------------------------------------------------------------------------
 * First extension: if-then-else
 *)

type _ Effect.t +=
  | Eq : ('dom * 'dom * 'dom tag) -> 'dom Effect.t
  | Cond :
      ('dom * ('dom tag -> 'dom) * ('dom tag -> 'dom) * 'dom tag)
      -> ('dom tag -> 'dom) Effect.t

let cond pred con alt (tag : 'dom tag) =
  perform (Cond (pred tag, con, alt, tag)) tag

let eq x y (tag : 'dom tag) =
  let x = x tag in
  let y = y tag in
  perform (Eq (x, y, tag))

module TIf = struct
  let tinc =
    let module M = TInc in
    M.res (* earlier term*)

  (* Example, reusing the earlier TInc *)
  let res : type dom. dom tag -> dom =
   fun tag -> cond (eq (int 3) tinc) (int 10) (tinc + int 1) tag
end

(* Implementation, reusing the earlier RInt *)
type v += VBool of bool (* add booleans to our value domain *)

let eq_h :
    type a dom. dom -> dom -> dom tag -> ((dom, a) continuation -> a) option =
 fun x y ->
  if debug.get () then Printf.printf "Handle Eq\n";

  function
  | V ->
      Some
        (fun k ->
          match (x, y) with
          | VInt x, VInt y -> continue k (VBool Int.(x = y))
          | _, _ -> failwith "eq type error")
  | _ -> None

let cond_h :
    type a dom.
    dom ->
    (dom tag -> dom) ->
    (dom tag -> dom) ->
    dom tag ->
    ((dom tag -> dom, a) continuation -> a) option =
 fun pred con alt ->
  if debug.get () then Printf.printf "Handle Cond\n";

  function
  | V ->
      Some
        (fun k ->
          match pred with
          | VBool true -> continue k con
          | VBool false -> continue k alt
          | _ -> failwith "cond type error")
  | _ -> None

(* * ------------------------------------------------------------------------ *
   Adding state *)

type _ Effect.t +=
  | Get : 'dom tag -> 'dom Effect.t
  | Put : ('dom * 'dom tag) -> 'dom Effect.t

let get (tag : 'dom tag) = perform (Get tag)

let put x (tag : 'dom tag) =
  let x = x tag in
  perform (Put (x, tag))

module TSt = struct
  let tinc =
    let module M = TInc in
    M.res (* earlier term*)

  let res : type dom. dom tag -> dom =
   fun tag ->
    cond (eq (int 3) (put tinc)) (put (int 20)) (put (int 1 + get)) tag
end

(* We need to handle the State requests. *)

let get_h :
    type a dom.
    dom tag -> ((dom, state:v -> a * v) continuation -> state:v -> a * v) option
    = function
  | V ->
      if debug.get () then Printf.printf "Handle Get\n";

      Some (fun k ~state -> continue k state ~state)
  | _ -> None

let put_h :
    type a dom.
    dom ->
    dom tag ->
    ((dom, state:v -> a * v) continuation -> state:v -> a * v) option =
 fun v ->
  if debug.get () then Printf.printf "Handle Put\n";

  function V -> Some (fun k ~state:_ -> continue k v ~state:v) | _ -> None

(* fix the type of state to v *)
let state_h (type a) : (a, state:v -> a * v) handler =
  {
    retc = (fun v ~state -> (v, state));
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        match eff with
        | Get tag -> get_h tag
        | Put (state, tag) -> put_h state tag
        | _ -> None);
  }

(*
 * ------------------------------------------------------------------------
 * Adding first-class functions
 *)

type _ Effect.t +=
  | Var : (string * 'dom tag) -> 'dom Effect.t
  | Lam : (string * ('dom tag -> 'dom) * 'dom tag) -> 'dom Effect.t
  | App : ('dom * 'dom * 'dom tag) -> ('dom tag -> 'dom) Effect.t

let var x (tag : 'dom tag) = perform (Var (x, tag))
let lam x body (tag : 'dom tag) = perform (Lam (x, body, tag))

let ( $$ ) fn arg : 'dom tag -> 'dom =
 fun tag ->
  let fn = fn tag in
  let arg = arg tag in
  perform (App (fn, arg, tag)) tag

module TLam = struct
  let tinc =
    let module M = TInc in
    M.res (* earlier term*)

  let res0 : type dom. dom tag -> dom = fun tag -> lam "x" (var "x" + int 1) tag
  let res01 : type dom. dom tag -> dom = fun tag -> (res0 $$ tinc) tag

  let res1 : type dom. dom tag -> dom =
   fun tag ->
    lam "x"
      (lam "y" @@ cond (eq (var "x") (var "y")) (var "x") (var "y" + int 1))
      tag

  let res11 : type dom. dom tag -> dom = fun tag -> (res1 $$ int 1 $$ int 2) tag

  (* Higher-order functions *)
  let res2 : type dom. dom tag -> dom =
   fun tag ->
    (lam "z" (lam "x" (var "z" $$ var "x"))
    $$ (res1 $$ int 1)
    $$ (* partial application of res1 *)
    int 2)
      tag
end

(* Implementation: lexical scope, call-by-value, left-to-right *)

let rec lookup : string -> (string * 'b) list -> 'b =
 fun x l ->
  match l with
  | [] -> failwith @@ "unbound variable " ^ x
  | (h, v) :: _ when String.(x = h) -> v
  | _ :: t -> lookup x t

type env = (string * v) list
type v += VClos : (string * (v tag -> v) * env) -> v

let var_h :
    type a dom.
    string ->
    dom tag ->
    ((dom, env:env -> a) continuation -> env:env -> a) option =
 fun x ->
  if debug.get () then Printf.printf "Handle Var %s\n" x;

  function
  | V -> Some (fun k ~env -> continue k (lookup x env) ~env) | _ -> None

let lam_h :
    type a dom.
    string ->
    (dom tag -> dom) ->
    dom tag ->
    ((dom, env:env -> a) continuation -> env:env -> a) option =
 fun x body ->
  if debug.get () then Printf.printf "Handle λ %s. _\n" x;

  function
  | V -> Some (fun k ~env -> continue k (VClos (x, body, env)) ~env) | _ -> None

let app_h :
    type a dom.
    (dom, env:env -> dom) handler ->
    dom ->
    dom ->
    dom tag ->
    ((dom tag -> dom, env:env -> a) continuation -> env:env -> a) option =
 fun env_h fn arg ->
  if debug.get () then Printf.printf "Handle App\n";

  function
  | V ->
      Some
        (fun k ~env ->
          match fn with
          | VClos (x, body, local_env) ->
              let arg : v = arg in
              let env' = (x, arg) :: local_env in
              let v tag : v = match_with body tag env_h ~env:env' in
              continue k v ~env
          | _ -> failwith "type error in app")
  | _ -> None

let rec env_h : type a. (a, env:env -> a) handler =
  {
    retc = (fun v ~env:_ -> v);
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        match eff with
        | Var (x, tag) -> var_h x tag
        | Lam (x, body, tag) -> lam_h x body tag
        | App (fn, arg, tag) -> app_h env_h fn arg tag
        | _ -> None);
  }

(* Other calling conventions (call-by-name, etc) and dynamic scope are left as
   an exercise to the reader *)

(*
 * ------------------------------------------------------------------------
 * Higher-order plus State: combining the existing features
 *)
module TLamSt = struct
  let incf : type dom. dom tag -> dom =
    let module M = TLam in
    M.res0 (* increment function *)

  let incs : type dom. dom tag -> dom = fun tag -> put (incf $$ get) tag

  (* incf but counting the invocation in the state *)
  (* λx.(λ_.x + 10) incs *)
  let incf : type dom. dom tag -> dom =
   fun tag -> lam "x" (lam "_" (var "x" + int 10) $$ incs) tag

  (* λf.λz.f (f z) *)
  let c2 : type dom. dom tag -> dom =
   fun tag -> lam "f" (lam "z" (var "f" $$ (var "f" $$ var "z"))) tag

  let res : type dom. dom tag -> dom =
   fun tag -> ((c2 $$ incf $$ int 100) + get) tag
end

let eval_h : ('a, 'a) handler =
  {
    retc = (fun v -> v);
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        match eff with
        | Int (i, tag) -> int_h i tag
        | Add (x, y, tag) -> add_h x y tag
        | Eq (x, y, tag) -> eq_h x y tag
        | Cond (pred, con, alt, tag) -> cond_h pred con alt tag
        | _ -> None);
  }

let eval (type dom) (tag : dom tag) (e : dom tag -> dom) : dom =
  let env = [] in
  let state = VInt 0 in
  fst
  @@ match_with
       (fun x ->
         match_with (fun x -> match_with e x env_h ~env) x state_h ~state)
       tag eval_h

let eval_v = eval V
