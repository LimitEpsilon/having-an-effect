open Debug
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

type pc = { pc_tgt : Addr.t; pc_en : bool } [@@deriving sexp_of]

type inst =
  | Add : inst
  | Ld : Addr.t -> inst
  | St : Addr.t -> inst
  | Beq : Addr.t -> inst
  | Blt : Addr.t -> inst
  (*| Barrier : inst*)
  | Halt : inst
[@@deriving sexp_of]

type _ mem = Inst : inst mem | Data : int mem [@@deriving sexp_of]

type _ reg =
  | PC_warp : Addr.t reg
  | PC : pc reg
  | RS1 : int reg
  | RS2 : int reg
  | RD : int reg
[@@deriving sexp_of]

type _ req = Mem : (Addr.t * 'a mem) -> 'a req | Reg : 'a reg -> 'a req
[@@deriving sexp_of]

type _ state =
  | Mem_st : ((Addr.t * 'a) list * 'a mem) -> 'a mem state
  | Reg_st : ('a * 'a reg) -> 'a reg state

let sexp_of_mem_v (type m) (tag : m mem) : m -> Sexp.t =
  match tag with Inst -> sexp_of_inst | Data -> sexp_of_int

let sexp_of_reg_v (type r) (tag : r reg) : r -> Sexp.t =
  match tag with
  | PC_warp -> Addr.sexp_of_t
  | PC -> sexp_of_pc
  | RS1 -> sexp_of_int
  | RS2 -> sexp_of_int
  | RD -> sexp_of_int

let sexp_of_mem_state (type m) (st : m mem state) : Sexp.t =
  let open Sexp in
  match st with
  | Mem_st (m, tag) ->
      let sexp_of_v : m -> Sexp.t = sexp_of_mem_v tag in
      List
        [
          Atom "Mem_st";
          sexp_of_list (sexp_of_pair Addr.sexp_of_t sexp_of_v) m;
          sexp_of_mem sexp_of_v tag;
        ]

let sexp_of_reg_state (type r) (st : r reg state) : Sexp.t =
  let open Sexp in
  match st with
  | Reg_st (r, tag) ->
      let sexp_of_v : r -> Sexp.t = sexp_of_reg_v tag in
      List [ Atom "Reg_st"; sexp_of_v r; sexp_of_reg sexp_of_v tag ]

let sexp_of_state (type s) (st : s state) : Sexp.t =
  match st with
  | Mem_st _ -> sexp_of_mem_state st
  | Reg_st _ -> sexp_of_reg_state st

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
  | PC_upd : Addr.t list -> Addr.t reg update (* update the shared PC *)

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
  | PC_upd l -> List [ Atom "PC_upd"; sexp_of_list Addr.sexp_of_t l ]

let sexp_of_update (type s) (tag : s) (upd : s update) =
  match upd with
  | Mem_upd _ -> sexp_of_mem_update tag upd
  | Reg_upd _ -> sexp_of_reg_update tag upd
  | PC_upd _ -> sexp_of_reg_update tag upd

type 'a promise = unit -> 'a option [@@deriving sexp]

(* read-write events *)
type _ Effect.t +=
  | Read : 'a req -> 'a promise t
  | Write : ('a req * 'a) -> unit t

(* task schedule *)
type _ Effect.t +=
  | Schedule : (unit -> unit) -> unit t
  | Await : 'a promise -> 'a t
  | More : unit t (* unstable, do more *)

type task =
  | Initial : (unit -> unit) -> task
  | Suspended : (('a, task list) continuation * 'a promise) -> task

let sexp_of_task (t : task) : Sexp.t =
  match t with Initial _ -> Atom "Initial" | Suspended _ -> Atom "Suspended"

type _ Effect.t +=
  | Check_mem : (Ticket.t * Addr.t * 'a mem) -> 'a option t
  | Check_reg : 'a reg -> 'a option t

(* memory hierarchy / architecture *)
type _ arch =
  | Mk_arch : { st : 's state; upd : 's update; children : 'exec } -> 'exec arch

let sexp_of_arch (type exec) (sexp_of_exec : exec -> Sexp.t) (arch : exec arch)
    : Sexp.t =
  match arch with
  | Mk_arch { st; upd; children } -> (
      match st with
      | Mem_st (_, tag) ->
          List
            [
              Atom "Arch";
              List [ Atom "st"; sexp_of_state st ];
              List [ Atom "upd"; sexp_of_update tag upd ];
              List [ Atom "children"; sexp_of_exec children ];
            ]
      | Reg_st (_, tag) ->
          List
            [
              Atom "Arch";
              List [ Atom "st"; sexp_of_state st ];
              List [ Atom "upd"; sexp_of_update tag upd ];
              List [ Atom "children"; sexp_of_exec children ];
            ])

type exec = Arch : exec arch list -> exec | Exec : task list -> exec

let rec sexp_of_exec (exec : exec) : Sexp.t =
  match exec with
  | Arch l -> sexp_of_list (sexp_of_arch sexp_of_exec) l
  | Exec l -> sexp_of_list sexp_of_task l

let sexp_of_arch = sexp_of_arch sexp_of_exec
let read (type a) (s : a req) : a promise = perform (Read s)
let write (type a) (s : a req) (x : a) : unit = perform (Write (s, x))
let schedule (task : unit -> unit) : unit = perform (Schedule task)
let await (type a) (prm : a promise) : a = perform (Await prm)

(* differentiate btwn local/shared memory *)
(* differentiate btwn registers that have different latencies *)
let execute pc () =
  let inst = await (read (Mem (pc, Inst))) in
  match inst with
  | Add ->
      let x = read (Reg RS1) in
      let y = read (Reg RS2) in
      (* TODO: use effects to consider latency of addition *)
      let w1 () =
        let x = await x in
        let y = await y in
        write (Reg RD) (x + y)
      in
      let w2 () = write (Reg PC) { pc_tgt = Addr.(succ pc); pc_en = true } in
      schedule w1;
      schedule w2
  | Ld addr ->
      let x = read (Mem (addr, Data)) in
      let w1 () =
        let x = await x in
        write (Reg RD) x
      in
      let w2 () = write (Reg PC) { pc_tgt = Addr.(succ pc); pc_en = true } in
      schedule w1;
      schedule w2
  | St addr ->
      let x = read (Reg RS1) in
      let w1 () =
        let x = await x in
        write (Mem (addr, Data)) x
      in
      let w2 () = write (Reg PC) { pc_tgt = Addr.(succ pc); pc_en = true } in
      schedule w1;
      schedule w2
  | Beq addr ->
      let x = read (Reg RS1) in
      let y = read (Reg RS2) in
      (* TODO: use effects to consider latency of comparison *)
      let w () =
        let x = await x in
        let y = await y in
        if Int.(x = y) then write (Reg PC) { pc_tgt = addr; pc_en = true }
        else write (Reg PC) { pc_tgt = Addr.(succ pc); pc_en = true }
      in
      schedule w
  | Blt addr ->
      let x = read (Reg RS1) in
      let y = read (Reg RS2) in
      (* TODO: use effects to consider latency of comparison *)
      let w () =
        let x = await x in
        let y = await y in
        if Int.(x < y) then write (Reg PC) { pc_tgt = addr; pc_en = true }
        else write (Reg PC) { pc_tgt = Addr.(succ pc); pc_en = true }
      in
      schedule w
  | Halt ->
      let w () = write (Reg PC) { pc_tgt = Addr.(succ pc); pc_en = false } in
      schedule w

let cycle () =
  let pc_mine = read (Reg PC) in
  let pc_warp = read (Reg PC_warp) in
  schedule @@ fun () ->
  let { pc_tgt; pc_en } = await pc_mine in
  if pc_en then
    let pc_warp = await pc_warp in
    if Addr.(pc_tgt = pc_warp) then schedule @@ execute pc_warp
    else write (Reg PC) { pc_tgt; pc_en }
  else ()

type (_, _) refl = Refl : ('a, 'a) refl

let eqb_mem (type a b) (x : a mem) (y : b mem) : (a, b) refl option =
  match x with
  | Inst -> ( match y with Inst -> Some Refl | _ -> None)
  | Data -> ( match y with Data -> Some Refl | _ -> None)

let eqb_reg (type a b) (x : a reg) (y : b reg) : (a, b) refl option =
  match x with
  | PC -> ( match y with PC -> Some Refl | _ -> None)
  | RS1 -> ( match y with RS1 -> Some Refl | _ -> None)
  | RS2 -> ( match y with RS2 -> Some Refl | _ -> None)
  | RD -> ( match y with RD -> Some Refl | _ -> None)
  | PC_warp -> ( match y with PC_warp -> Some Refl | _ -> None)

let rec read_mem : type a. Addr.t -> (Addr.t * a) list -> a option =
 fun addr -> function
  | [] -> None
  | (x, v) :: tl -> if Addr.(x = addr) then Some v else read_mem addr tl

let task_h : (unit, task list) handler =
  {
    retc = (fun () -> []);
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        let () = if debug.hide () then printf "task_h\n" in
        match eff with
        | Schedule t ->
            perform More;
            Some (fun (k : (c, _) continuation) -> Initial t :: continue k ())
        | Await prm ->
            perform More;
            Some (fun k -> [ Suspended (k, prm) ])
        | _ -> None);
  }

let mem_h :
    type a m.
    m mem ->
    ( a,
      st:m mem state -> upd:m mem update -> a * m mem state * m mem update )
    handler =
 fun m ->
  {
    retc = (fun v ~st ~upd -> (v, st, upd));
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        let () =
          if debug.hide () then
            let m = Sexp.to_string_hum (sexp_of_mem (sexp_of_mem_v m) m) in
            print_string @@ "mem_h " ^ m ^ "\n"
        in
        match eff with
        | Read (Mem (addr, m')) -> (
            match eqb_mem m m' with
            | Some Refl ->
                let () =
                  if debug.hide () then
                    let m =
                      Sexp.to_string_hum
                        (sexp_of_pair Addr.sexp_of_t
                           (sexp_of_mem (sexp_of_mem_v m))
                           (addr, m))
                    in
                    print_string @@ "Handle: " ^ m ^ "\n"
                in

                Some
                  (fun (k : (c, _) continuation) ~st ~upd ->
                    match upd with
                    | Mem_upd { pending_r; pending_w; ticket } ->
                        let upd' =
                          Mem_upd
                            {
                              pending_r;
                              pending_w;
                              ticket = Ticket.(succ ticket);
                            }
                        in
                        continue k
                          (fun () -> perform @@ Check_mem (ticket, addr, m'))
                          ~st ~upd:upd')
            | None -> None)
        | Write (Mem (addr, m'), v) -> (
            match eqb_mem m m' with
            | Some Refl ->
                Some
                  (fun k ~st ~upd ->
                    let upd : m mem update = upd in
                    match upd with
                    | Mem_upd { pending_r; pending_w; ticket } ->
                        let upd' =
                          Mem_upd
                            {
                              pending_r;
                              pending_w = (addr, v) :: pending_w;
                              ticket;
                            }
                        in
                        continue k () ~st ~upd:upd')
            | None -> None)
        | Check_mem (ticket, addr, m') -> (
            match eqb_mem m m' with
            | Some Refl ->
                Some
                  (fun k ~st ~upd ->
                    match upd with
                    | Mem_upd { pending_r; _ } ->
                        if Ticket.(ticket < pending_r) then
                          match st with
                          | Mem_st (m, _) ->
                              let m : (Addr.t * m) list = m in
                              continue k (read_mem addr m) ~st ~upd
                        else continue k None ~st ~upd)
            | None -> None)
        | _ -> None);
  }

let reg_h :
    type a r.
    r reg ->
    ( a,
      st:r reg state -> upd:r reg update -> a * r reg state * r reg update )
    handler =
 fun r ->
  {
    retc = (fun v ~st ~upd -> (v, st, upd));
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        let () =
          if debug.hide () then
            let r = Sexp.to_string_hum (sexp_of_reg (sexp_of_reg_v r) r) in
            print_string @@ "reg_h " ^ r ^ "\n"
        in
        match eff with
        | Read (Reg r') -> (
            match eqb_reg r r' with
            | Some Refl ->
                let () =
                  if debug.hide () then
                    let r =
                      Sexp.to_string_hum (sexp_of_reg (sexp_of_reg_v r) r)
                    in
                    print_string @@ "Handle: " ^ r ^ "\n"
                in

                Some
                  (fun (k : (c, _) continuation) ~st ~upd ->
                    continue k (fun () -> perform @@ Check_reg r') ~st ~upd)
            | None -> None)
        | Write (Reg r', v) -> (
            match eqb_reg r r' with
            | Some Refl ->
                Some
                  (fun k ~st ~upd ->
                    let upd : r reg update = upd in
                    match upd with
                    | Reg_upd None ->
                        let () =
                          match r' with
                          | PC ->
                              let { pc_tgt; pc_en } = v in
                              if pc_en then write (Reg PC_warp) pc_tgt else ()
                          | _ -> ()
                        in
                        continue k () ~st ~upd:(Reg_upd (Some v))
                    | Reg_upd (Some _) ->
                        raise
                          (Register_written_twice
                             {
                               reg =
                                 Sexp.to_string
                                   (sexp_of_reg (sexp_of_reg_v r) r);
                               value = Sexp.to_string (sexp_of_reg_v r v);
                             })
                    | PC_upd u -> continue k () ~st ~upd:(PC_upd (v :: u)))
            | None -> None)
        | Check_reg r' -> (
            match eqb_reg r r' with
            | Some Refl ->
                Some
                  (fun k ~st ~upd ->
                    match st with
                    | Reg_st (v, _) ->
                        let v : r = v in
                        continue k (Some v) ~st ~upd)
            | None -> None)
        | _ -> None);
  }

let scheduler tasks =
  List.fold tasks ~init:[] ~f:(fun todo -> function
    | Initial task -> List.rev_append (match_with task () task_h) todo
    | Suspended (k, prm) -> (
        match prm () with
        | Some v -> List.rev_append (continue k v) todo
        | None -> Suspended (k, prm) :: todo))

let rec majority_aux (maj : Addr.t) (maj_count : int) (unseen : Addr.t list)
    (seen_count : Addr.t -> int) =
  match unseen with
  | [] -> maj
  | seen :: unseen' ->
      let count = seen_count seen + 1 in
      let seen_count' addr =
        if Addr.(seen = addr) then count else seen_count addr
      in
      let maj, maj_count =
        if maj_count < count then (seen, count) else (maj, maj_count)
      in
      majority_aux maj maj_count unseen' seen_count'

let majority (default : Addr.t) (l : Addr.t list) =
  majority_aux default 0 l (fun _ -> 0)

let update_state : type s. st:s state -> upd:s update -> s state * s update =
 fun ~st ~upd ->
  match st with
  | Mem_st (m, tag) -> (
      match upd with
      | Mem_upd { pending_r; pending_w; ticket } -> (
          (* serve read requests *)
          let pending_r =
            if Ticket.(pending_r < ticket) then (
              perform More;
              Ticket.(succ pending_r))
            else pending_r
          in
          (* serve write requests *)
          let open List in
          match rev pending_w with
          | (addr, v) :: rev_pending_w ->
              perform More;
              let pending_w = rev rev_pending_w in
              ( Mem_st ((addr, v) :: m, tag),
                Mem_upd { pending_r; pending_w; ticket } )
          | [] -> (st, Mem_upd { pending_r; pending_w; ticket })))
  | Reg_st (r, tag) -> (
      match upd with
      | Reg_upd o ->
          let st =
            match o with
            | None -> Reg_st (r, tag)
            | Some v ->
                perform More;
                Reg_st (v, tag)
          in
          (st, Reg_upd None)
      | PC_upd u ->
          let () = if not (List.is_empty u) then perform More in
          let st = Reg_st (majority r u, tag) in
          (st, PC_upd []))

let fix_h : type a. (a, more:bool -> a * bool) handler =
  {
    retc = (fun v ~more -> (v, more));
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        let () = if debug.hide () then printf "fix_h\n" in

        match eff with
        | More ->
            Some
              (fun (k : (c, _) continuation) ~more:_ ->
                continue k () ~more:true)
        | _ -> None);
  }

let rec step_arch (arch : exec arch) =
  match arch with
  | Mk_arch { st; upd; children } -> (
      let exec () =
        match children with
        | Arch l -> Arch (List.map ~f:step_arch l)
        | Exec l -> Exec (scheduler l)
      in
      match st with
      | Mem_st (_, tag) ->
          let children, st, upd = match_with exec () (mem_h tag) ~st ~upd in
          Mk_arch { st; upd; children }
      | Reg_st (_, tag) ->
          let children, st, upd = match_with exec () (reg_h tag) ~st ~upd in
          Mk_arch { st; upd; children })

let fix_step : ?threshold:int -> exec arch -> exec arch =
 fun ?threshold ->
  let num = ref 0 in
  let rec go arch =
    let do_more =
      match threshold with
      | None -> true
      | Some t ->
          let more = !num < t in
          incr num;
          more
    in
    if do_more then
      let arch, more = match_with step_arch arch fix_h ~more:false in
      if more then
        let () =
          if debug.get () then (
            printf "-------- After step --------\n";
            Sexp.pp_hum Stdlib.Format.std_formatter (sexp_of_arch arch);
            Out_channel.newline stdout)
        in
        go arch
      else arch
    else arch
  in
  go

let rec update_arch (arch : exec arch) =
  match arch with
  | Mk_arch { st; upd; children } -> (
      let st, upd = update_state ~st ~upd in
      match children with
      | Arch l ->
          Mk_arch { st; upd; children = Arch (List.map ~f:update_arch l) }
      | Exec l -> Mk_arch { st; upd; children = Exec (Initial cycle :: l) })

let run : ?threshold:int -> exec arch -> exec arch =
 fun ?threshold ->
  let num = ref 0 in
  let rec go arch =
    let do_more =
      match threshold with
      | None -> true
      | Some t ->
          let more = !num < t in
          incr num;
          more
    in
    if do_more then
      let arch = fix_step ?threshold arch in
      let arch, more = match_with update_arch arch fix_h ~more:false in
      if more then
        let () =
          if debug.get () then (
            printf "-------- After run --------\n";
            Sexp.pp_hum Stdlib.Format.std_formatter (sexp_of_arch arch);
            Out_channel.newline stdout)
        in
        go arch
      else arch
    else arch
  in
  go
