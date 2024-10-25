open Core
open Effect
open Effect.Deep
open Datatypes

module Addr : Denum = struct
  include Z
end

module Ticket : Denum = struct
  include Z
end

type pc = Addr.t [@@deriving sexp_of]

type _ reg =
  | PC : Addr.t reg
  | R0 : int reg (* always zero *)
  | R1 : int reg
  | R2 : int reg
  | R3 : int reg
  | R4 : int reg
  | R5 : int reg
  | R6 : int reg
  | R7 : int reg
  | R8 : int reg
  | R9 : int reg
  | R10 : int reg
  | R11 : int reg
  | R12 : int reg
  | R13 : int reg
  | R14 : int reg
  | R15 : int reg
  | R16 : int reg
  | R17 : int reg
  | R18 : int reg
  | R19 : int reg
  | R20 : int reg
  | R21 : int reg
  | R22 : int reg
  | R23 : int reg
  | R24 : int reg
  | R25 : int reg
  | R26 : int reg
  | R27 : int reg
  | R28 : int reg
  | R29 : int reg
  | R30 : int reg
  | R31 : int reg
[@@deriving sexp_of]

type inst =
  | Add : (int reg * int reg * int reg) -> inst
  (* add rd rs1 rs2 *)
  (* rd ← (rs1) + (rs2) *)
  | Addi : (int reg * int reg * int) -> inst
  (* addi rd rs1 imm *)
  (* rd ← (rs1) + imm *)
  | Ld : (int reg * Addr.t * int reg) -> inst
  (* ld rd imm(rs1) *)
  (* rd ← M[(rs1) + imm] *)
  | St : (Addr.t * int reg * int reg) -> inst
  (* st imm(rs1) rs2 *)
  (* M[(rs1) + imm] ← (rs2) *)
  | Beq : (int reg * int reg * Addr.t) -> inst
  (* beq rs1 rs2 imm *)
  (* (pc') = if (rs1) = (rs2) then (pc) + imm else (pc) + 1 *)
  | Blt : (int reg * int reg * Addr.t) -> inst
  (* blt rs1 rs2 imm *)
  (* (pc') = if (rs1) < (rs2) then (pc) + imm else (pc) + 1 *)
  | Halt : inst
[@@deriving sexp_of]

type _ mem = Imem : inst mem | Dmem : int mem [@@deriving sexp_of]
type adder = Adder [@@deriving sexp_of]
type warp = Warp [@@deriving sexp_of]
type process = unit -> unit [@@deriving sexp_of]
type 'a promise = unit -> 'a option [@@deriving sexp]

type _ storage =
  | Mem_st : { mem_st : (Addr.t * 'a) list; mem_tag : 'a mem } -> 'a mem storage
  | Reg_st : { reg_st : 'a; reg_tag : 'a reg } -> 'a reg storage
  | Adder_st : adder storage
  | Warp_st : {
      warp_pc : Addr.t option;
      decode_req : inst promise;
    }
      -> warp storage

type _ loc = Mem : (Addr.t * 'a mem) -> 'a loc | Reg : 'a reg -> 'a loc
[@@deriving sexp_of]

(** Defunctionalize *)
type fn = Cycle [@@deriving sexp_of]

type _ ty =
  | Tyi : int ty
  | Regi : int reg ty
  | Tyb : bool ty
  | Tya : Addr.t ty
  | Rega : Addr.t reg ty
[@@deriving sexp_of]

type 'a var = string * 'a ty [@@deriving sexp_of]
type 'a value = 'a * 'a ty [@@deriving sexp_of]

type (_, _, _) bop =
  | Add : (int, int, int) bop
  | Eqb : (int, int, bool) bop
  | Ltb : (int, int, bool) bop
[@@deriving sexp_of]

type _ expr = Var : 'a var -> 'a expr | Val : 'a value -> 'a expr
[@@deriving sexp_of]

type _ que =
  | Read_mem : { src : Addr.t expr * 'a mem } -> 'a que
  | Read_reg : { src : 'a reg expr } -> 'a que
  | Write_mem : { dst : Addr.t expr * 'a mem; data : 'a expr } -> unit que
  | Write_reg : { dst : 'a reg expr; data : 'a expr } -> unit que
  | Bop : { op : ('a, 'b, 'c) bop; lop : 'a expr; rop : 'b expr } -> 'c que
  | Vote : { tgt : pc expr } -> unit que
  | Decode : { tgt : pc expr } -> inst option que
[@@deriving sexp_of]

type (_, _) branch =
  | Br_cont : { cont : 'a var * 'itree } -> ('a, 'itree) branch
  | Br_if : { con : 'itree; alt : 'itree } -> (bool, 'itree) branch
  | Br_dec : {
      none : 'itree;
      add : int reg var * int reg var * int reg var * 'itree;
      addi : int reg var * int reg var * int var * 'itree;
      ld : int reg var * Addr.t var * int reg var * 'itree;
      st : Addr.t var * int reg var * int reg var * 'itree;
      beq : int reg var * int reg var * Addr.t var * 'itree;
      blt : int reg var * int reg var * Addr.t var * 'itree;
      halt : 'itree;
    }
      -> (inst option, 'itree) branch
[@@deriving sexp_of]

type itree =
  | Ret : 'a expr -> itree
  | Call : fn -> itree
  | Unanswered : { ask : 'a que; cont : ('a, itree) branch } -> itree
  | Answered : { ask : 'a que; ans : 'a; cont : itree } -> itree
[@@deriving sexp_of]

type _ update =
  | Mem_upd : {
      (* pending_r ≤ t < ticket ↔ t waiting *)
      pending_r : Ticket.t;
      (* pending writes in reverse order, latest request at head *)
      pending_w : (Ticket.t * Addr.t * 'a option) list;
      (* not yet given to anyone *)
      ticket : Ticket.t;
    }
      -> 'a mem update
  | Reg_upd : {
      (* invariant : always the ticket of the earliest write *)
      (* if pending_w = [], pending_r = ticket *)
      pending_r : Ticket.t;
      (* pending writes in reverse order, latest request at head *)
      pending_w : (Ticket.t * 'a option) list;
      (* not yet given to anyone *)
      ticket : Ticket.t;
    }
      -> 'a reg update
  | Adder_upd : {
      pending_op : (Ticket.t * int option * int option) list;
      ticket : Ticket.t;
    }
      -> adder update
  | Warp_upd : {
      voted : (Addr.t * int * inst promise) list;
      nth_election : Ticket.t;
    }
      -> warp update

type task =
  | Initial : process -> task
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
  | Write : ('a loc * 'a promise) -> process t

type _ Effect.t +=
  | Add : (int promise * int promise) -> (process * int promise) t

(* warp schedule *)
type _ Effect.t +=
  | Vote : Addr.t -> unit promise t
  | Decode : Addr.t -> inst promise option t

(* task schedule *)
type _ Effect.t +=
  | Await : 'a promise -> 'a t
  | Schedule : process -> unit t
  | More : unit t (* unstable, do more *)

(* check/fulfill promise *)
type _ Effect.t +=
  | Check_mem : (Ticket.t * Addr.t * 'a mem) -> 'a option t
  | Fulfill_mem : (Ticket.t * 'a * 'a mem) -> unit t
  | Check_reg : (Ticket.t * 'a reg) -> 'a option t
  | Fulfill_reg : (Ticket.t * 'a * 'a reg) -> unit t
  | Check_add : Ticket.t -> int option t
  | Fulfill_add1 : (Ticket.t * int) -> unit t
  | Fulfill_add2 : (Ticket.t * int) -> unit t
  | Check_ballot : Ticket.t -> unit option t

let read (type a) (s : a loc) : a promise = perform @@ Read s

let write (type a) (s : a loc) (x : a promise) : process =
  perform @@ Write (s, x)

let add x y = perform @@ Add (x, y)
let await (type a) (prm : a promise) : a = perform @@ Await prm
let schedule (type a) (t : process) : unit = perform @@ Schedule t
let vote (pc : Addr.t) : unit promise = perform @@ Vote pc
let decode (pc : Addr.t) : inst promise option = perform @@ Decode pc

(******** sexp ********)
let sexp_of_mem_v (type m) (tag : m mem) : m -> Sexp.t =
  match tag with Imem -> sexp_of_inst | Dmem -> sexp_of_int

let sexp_of_reg_v (type r) (tag : r reg) : r -> Sexp.t =
  match tag with
  | PC -> sexp_of_pc
  | R0 -> sexp_of_int
  | R1 -> sexp_of_int
  | R2 -> sexp_of_int
  | R3 -> sexp_of_int
  | R4 -> sexp_of_int
  | R5 -> sexp_of_int
  | R6 -> sexp_of_int
  | R7 -> sexp_of_int
  | R8 -> sexp_of_int
  | R9 -> sexp_of_int
  | R10 -> sexp_of_int
  | R11 -> sexp_of_int
  | R12 -> sexp_of_int
  | R13 -> sexp_of_int
  | R14 -> sexp_of_int
  | R15 -> sexp_of_int
  | R16 -> sexp_of_int
  | R17 -> sexp_of_int
  | R18 -> sexp_of_int
  | R19 -> sexp_of_int
  | R20 -> sexp_of_int
  | R21 -> sexp_of_int
  | R22 -> sexp_of_int
  | R23 -> sexp_of_int
  | R24 -> sexp_of_int
  | R25 -> sexp_of_int
  | R26 -> sexp_of_int
  | R27 -> sexp_of_int
  | R28 -> sexp_of_int
  | R29 -> sexp_of_int
  | R30 -> sexp_of_int
  | R31 -> sexp_of_int

let sexp_of_mem_st (type m) (tag : m mem) =
  let open Sexp in
  let sexp_of_v : m -> t = sexp_of_mem_v tag in
  sexp_of_list (sexp_of_pair Addr.sexp_of_t sexp_of_v)

let sexp_of_mem_storage (type m) (st : m mem storage) : Sexp.t =
  let open Sexp in
  match st with
  | Mem_st { mem_st; mem_tag } ->
      let sexp_of_v : m -> Sexp.t = sexp_of_mem_v mem_tag in
      List
        [
          Atom "Mem_st";
          sexp_of_mem_st mem_tag mem_st;
          sexp_of_mem sexp_of_v mem_tag;
        ]

let sexp_of_reg_storage (type r) (st : r reg storage) : Sexp.t =
  let open Sexp in
  match st with
  | Reg_st { reg_st; reg_tag } ->
      let sexp_of_v : r -> Sexp.t = sexp_of_reg_v reg_tag in
      List [ Atom "Reg_st"; sexp_of_v reg_st; sexp_of_reg sexp_of_v reg_tag ]

let sexp_of_adder_storage (st : adder storage) : Sexp.t =
  let open Sexp in
  match st with Adder_st -> Atom "Adder_st"

let sexp_of_warp_storage (st : warp storage) : Sexp.t =
  let open Sexp in
  match st with
  | Warp_st { warp_pc; decode_req } ->
      List
        [
          Atom "Warp_st";
          sexp_of_option Addr.sexp_of_t warp_pc;
          sexp_of_promise sexp_of_inst decode_req;
        ]

let sexp_of_storage (type s) (st : s storage) : Sexp.t =
  match st with
  | Mem_st _ -> sexp_of_mem_storage st
  | Reg_st _ -> sexp_of_reg_storage st
  | Adder_st -> sexp_of_adder_storage st
  | Warp_st _ -> sexp_of_warp_storage st

let sexp_of_mem_pending_w (type m) (tag : m mem) =
  let open Sexp in
  let sexp_of_v : m -> t = sexp_of_mem_v tag in
  let sexp_of_entry (t, pc, ov) =
    List [ Ticket.sexp_of_t t; Addr.sexp_of_t pc; sexp_of_option sexp_of_v ov ]
  in
  sexp_of_list sexp_of_entry

let sexp_of_mem_update (type m) (tag : m mem) (upd : m mem update) =
  let open Sexp in
  match upd with
  | Mem_upd { pending_r; pending_w; ticket } ->
      List
        [
          Atom "Mem_upd";
          List [ Atom "pending_r"; Ticket.sexp_of_t pending_r ];
          List [ Atom "pending_w"; sexp_of_mem_pending_w tag pending_w ];
          List [ Atom "ticket"; Ticket.sexp_of_t ticket ];
        ]

let sexp_of_reg_pending_w (type r) (tag : r reg) =
  let open Sexp in
  let sexp_of_v : r -> t = sexp_of_reg_v tag in
  let sexp_of_entry (t, ov) =
    List [ Ticket.sexp_of_t t; sexp_of_option sexp_of_v ov ]
  in
  sexp_of_list sexp_of_entry

let sexp_of_reg_update (type r) (tag : r reg) (upd : r reg update) =
  let open Sexp in
  match upd with
  | Reg_upd { pending_r; pending_w; ticket } ->
      List
        [
          Atom "Reg_upd";
          List [ Atom "pending_r"; Ticket.sexp_of_t pending_r ];
          List [ Atom "pending_w"; sexp_of_reg_pending_w tag pending_w ];
          List [ Atom "ticket"; Ticket.sexp_of_t ticket ];
        ]

let sexp_of_warp_voted =
  let open Sexp in
  let sexp_of_entry (pc, n, prm) =
    List
      [ Addr.sexp_of_t pc; Int.sexp_of_t n; sexp_of_promise sexp_of_inst prm ]
  in
  sexp_of_list sexp_of_entry

let sexp_of_pending_op =
  let open Sexp in
  let sexp_of_entry (t, op1, op2) =
    List
      [
        Ticket.sexp_of_t t;
        sexp_of_option Int.sexp_of_t op1;
        sexp_of_option Int.sexp_of_t op2;
      ]
  in
  sexp_of_list sexp_of_entry

let sexp_of_adder_update (upd : adder update) =
  let open Sexp in
  match upd with
  | Adder_upd { pending_op; ticket } ->
      List
        [
          Atom "Adder_upd";
          List [ Atom "pending_op"; sexp_of_pending_op pending_op ];
          List [ Atom "ticket"; Ticket.sexp_of_t ticket ];
        ]

let sexp_of_warp_update (upd : warp update) =
  let open Sexp in
  match upd with
  | Warp_upd { voted; nth_election } ->
      List
        [
          Atom "Warp_upd";
          List [ Atom "voted"; sexp_of_warp_voted voted ];
          List [ Atom "nth_election"; Ticket.sexp_of_t nth_election ];
        ]

let sexp_of_update (type s) (tag : s) (upd : s update) =
  match upd with
  | Mem_upd _ -> sexp_of_mem_update tag upd
  | Reg_upd _ -> sexp_of_reg_update tag upd
  | Adder_upd _ -> sexp_of_adder_update upd
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
      | Adder_st ->
          List
            [
              Atom "Arch";
              List [ Atom "st"; sexp_of_storage st ];
              List [ Atom "upd"; sexp_of_update Adder upd ];
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
