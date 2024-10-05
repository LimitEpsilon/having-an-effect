open Core
open Effect
open Effect.Deep
open Datatypes

module Addr : Denum = struct
  include Pos
end

module Ticket : Denum = struct
  include Pos
end

exception Register_written_twice of { reg : string; value : string }

type inst =
  | Add : inst
  | Ld : Addr.t -> inst
  | St : Addr.t -> inst
  | Beq : Addr.t -> inst
  | Blt : Addr.t -> inst
  (*| Barrier : inst*)
  | Halt : inst
[@@deriving sexp_of]

type pc = Addr.t [@@deriving sexp_of]
type _ mem = Imem : inst mem | Dmem : int mem [@@deriving sexp_of]

type _ reg = PC : pc reg | RS1 : int reg | RS2 : int reg | RD : int reg
[@@deriving sexp_of]

type warp = Warp [@@deriving sexp_of]
type 'a promise = unit -> 'a option [@@deriving sexp]

type _ storage =
  | Mem_st : { mem_st : (Addr.t * 'a) list; mem_tag : 'a mem } -> 'a mem storage
  | Reg_st : { reg_st : 'a; reg_tag : 'a reg } -> 'a reg storage
  | Warp_st : {
      warp_pc : Addr.t;
      decode_req : inst promise option;
    }
      -> warp storage

type _ loc = Mem : (Addr.t * 'a mem) -> 'a loc | Reg : 'a reg -> 'a loc
[@@deriving sexp_of]

type _ update =
  | Mem_upd : {
      (* pending_r ≤ t < ticket ↔ t waiting *)
      pending_r : Ticket.t;
      (* TODO: Track program order *)
      (* pending writes in reverse order, latest request at head *)
      pending_w : (Addr.t * 'a) list;
      (* not yet given to anyone *)
      ticket : Ticket.t;
    }
      -> 'a mem update
  | Reg_upd : 'a option -> 'a reg update
  | Warp_upd : { voted : Addr.t list; nth_election : Ticket.t } -> warp update

type task =
  | Initial : (unit -> unit) -> task
  | Suspended : (('a, task list) continuation * 'a promise) -> task

(* memory hierarchy / architecture *)
type _ arch =
  | Mk_arch : {
      st : 's storage;
      upd : 's update;
      children : 'exec;
    }
      -> 'exec arch

type exec = Arch : exec arch list -> exec | Exec : task list -> exec

(* read-write events *)
type _ Effect.t +=
  | Read : 'a loc -> 'a promise t
  | Write : ('a loc * 'a) -> unit t

(* warp schedule *)
type _ Effect.t +=
  | Vote : Addr.t -> unit promise t
  | Decode : Addr.t -> inst promise option t

(* task schedule *)
type _ Effect.t +=
  | Schedule : (unit -> unit) -> unit t
  | Await : 'a promise -> 'a t
  | More : unit t (* unstable, do more *)

(* check promise *)
type _ Effect.t +=
  | Check_mem : (Ticket.t * Addr.t * 'a mem) -> 'a option t
  | Check_reg : 'a reg -> 'a option t
  | Check_ballot : Ticket.t -> unit option t

let read (type a) (s : a loc) : a promise = perform @@ Read s
let write (type a) (s : a loc) (x : a) : unit = perform @@ Write (s, x)
let schedule (task : unit -> unit) : unit = perform @@ Schedule task
let await (type a) (prm : a promise) : a = perform @@ Await prm

(******** sexp ********)
let sexp_of_mem_v (type m) (tag : m mem) : m -> Sexp.t =
  match tag with Imem -> sexp_of_inst | Dmem -> sexp_of_int

let sexp_of_reg_v (type r) (tag : r reg) : r -> Sexp.t =
  match tag with
  | PC -> sexp_of_pc
  | RS1 -> sexp_of_int
  | RS2 -> sexp_of_int
  | RD -> sexp_of_int

let sexp_of_mem_storage (type m) (st : m mem storage) : Sexp.t =
  let open Sexp in
  match st with
  | Mem_st { mem_st; mem_tag } ->
      let sexp_of_v : m -> Sexp.t = sexp_of_mem_v mem_tag in
      List
        [
          Atom "Mem_st";
          sexp_of_list (sexp_of_pair Addr.sexp_of_t sexp_of_v) mem_st;
          sexp_of_mem sexp_of_v mem_tag;
        ]

let sexp_of_reg_storage (type r) (st : r reg storage) : Sexp.t =
  let open Sexp in
  match st with
  | Reg_st { reg_st; reg_tag } ->
      let sexp_of_v : r -> Sexp.t = sexp_of_reg_v reg_tag in
      List [ Atom "Reg_st"; sexp_of_v reg_st; sexp_of_reg sexp_of_v reg_tag ]

let sexp_of_warp_storage (st : warp storage) : Sexp.t =
  let open Sexp in
  match st with
  | Warp_st { warp_pc; decode_req } ->
      List
        [
          Atom "Warp_st";
          Addr.sexp_of_t warp_pc;
          sexp_of_option (sexp_of_promise sexp_of_inst) decode_req;
        ]

let sexp_of_storage (type s) (st : s storage) : Sexp.t =
  match st with
  | Mem_st _ -> sexp_of_mem_storage st
  | Reg_st _ -> sexp_of_reg_storage st
  | Warp_st _ -> sexp_of_warp_storage st

let sexp_of_mem_update (type m) (tag : m mem) (upd : m mem update) =
  let open Sexp in
  match upd with
  | Mem_upd { pending_r; pending_w; ticket } ->
      let sexp_of_v : m -> Sexp.t = sexp_of_mem_v tag in
      List
        [
          Atom "Mem_upd";
          List [ Atom "pending_r"; Ticket.sexp_of_t pending_r ];
          List
            [
              Atom "pending_w";
              sexp_of_list (sexp_of_pair Addr.sexp_of_t sexp_of_v) pending_w;
            ];
          List [ Atom "ticket"; Ticket.sexp_of_t ticket ];
        ]

let sexp_of_reg_update (type r) (tag : r reg) (upd : r reg update) =
  let open Sexp in
  match upd with
  | Reg_upd o ->
      let sexp_of_v : r -> Sexp.t = sexp_of_reg_v tag in
      List [ Atom "Reg_upd"; sexp_of_option sexp_of_v o ]

let sexp_of_warp_update (upd : warp update) =
  let open Sexp in
  match upd with
  | Warp_upd { voted; nth_election } ->
      List
        [
          Atom "Warp_upd";
          List [ Atom "voted"; sexp_of_list Addr.sexp_of_t voted ];
          List [ Atom "nth_election"; Ticket.sexp_of_t nth_election ];
        ]

let sexp_of_update (type s) (tag : s) (upd : s update) =
  match upd with
  | Mem_upd _ -> sexp_of_mem_update tag upd
  | Reg_upd _ -> sexp_of_reg_update tag upd
  | Warp_upd _ -> sexp_of_warp_update upd

let sexp_of_task (t : task) : Sexp.t =
  match t with Initial _ -> Atom "Initial" | Suspended _ -> Atom "Suspended"

let sexp_of_arch (type exec) (sexp_of_exec : exec -> Sexp.t) (arch : exec arch)
    : Sexp.t =
  match arch with
  | Mk_arch { st; upd; children } -> (
      match st with
      | Mem_st { mem_tag; _ } ->
          List
            [
              Atom "Arch";
              List [ Atom "st"; sexp_of_storage st ];
              List [ Atom "upd"; sexp_of_update mem_tag upd ];
              List [ Atom "children"; sexp_of_exec children ];
            ]
      | Reg_st { reg_tag; _ } ->
          List
            [
              Atom "Arch";
              List [ Atom "st"; sexp_of_storage st ];
              List [ Atom "upd"; sexp_of_update reg_tag upd ];
              List [ Atom "children"; sexp_of_exec children ];
            ]
      | Warp_st _ ->
          List
            [
              Atom "Arch";
              List [ Atom "st"; sexp_of_storage st ];
              List [ Atom "upd"; sexp_of_update Warp upd ];
              List [ Atom "children"; sexp_of_exec children ];
            ])

let rec sexp_of_exec (exec : exec) : Sexp.t =
  match exec with
  | Arch l -> sexp_of_list (sexp_of_arch sexp_of_exec) l
  | Exec l -> sexp_of_list sexp_of_task l

let sexp_of_arch = sexp_of_arch sexp_of_exec
