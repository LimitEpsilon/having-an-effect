open Debug
open Core
open Effect
open Effect.Deep
open Domains

exception Write_to_R0

type (_, _) refl = Refl : ('a, 'a) refl

let eqb_mem (type a b) (x : a mem) (y : b mem) : (a, b) refl option =
  match x with
  | Imem -> ( match y with Imem -> Some Refl | _ -> None)
  | Dmem -> ( match y with Dmem -> Some Refl | _ -> None)

let eqb_reg (type a b) (x : a reg) (y : b reg) : (a, b) refl option =
  match x with
  | PC -> ( match y with PC -> Some Refl | _ -> None)
  | R0 -> ( match y with R0 -> Some Refl | _ -> None)
  | R1 -> ( match y with R1 -> Some Refl | _ -> None)
  | R2 -> ( match y with R2 -> Some Refl | _ -> None)
  | R3 -> ( match y with R3 -> Some Refl | _ -> None)
  | R4 -> ( match y with R4 -> Some Refl | _ -> None)
  | R5 -> ( match y with R5 -> Some Refl | _ -> None)
  | R6 -> ( match y with R6 -> Some Refl | _ -> None)
  | R7 -> ( match y with R7 -> Some Refl | _ -> None)
  | R8 -> ( match y with R8 -> Some Refl | _ -> None)
  | R9 -> ( match y with R9 -> Some Refl | _ -> None)
  | R10 -> ( match y with R10 -> Some Refl | _ -> None)
  | R11 -> ( match y with R11 -> Some Refl | _ -> None)
  | R12 -> ( match y with R12 -> Some Refl | _ -> None)
  | R13 -> ( match y with R13 -> Some Refl | _ -> None)
  | R14 -> ( match y with R14 -> Some Refl | _ -> None)
  | R15 -> ( match y with R15 -> Some Refl | _ -> None)
  | R16 -> ( match y with R16 -> Some Refl | _ -> None)
  | R17 -> ( match y with R17 -> Some Refl | _ -> None)
  | R18 -> ( match y with R18 -> Some Refl | _ -> None)
  | R19 -> ( match y with R19 -> Some Refl | _ -> None)
  | R20 -> ( match y with R20 -> Some Refl | _ -> None)
  | R21 -> ( match y with R21 -> Some Refl | _ -> None)
  | R22 -> ( match y with R22 -> Some Refl | _ -> None)
  | R23 -> ( match y with R23 -> Some Refl | _ -> None)
  | R24 -> ( match y with R24 -> Some Refl | _ -> None)
  | R25 -> ( match y with R25 -> Some Refl | _ -> None)
  | R26 -> ( match y with R26 -> Some Refl | _ -> None)
  | R27 -> ( match y with R27 -> Some Refl | _ -> None)
  | R28 -> ( match y with R28 -> Some Refl | _ -> None)
  | R29 -> ( match y with R29 -> Some Refl | _ -> None)
  | R30 -> ( match y with R30 -> Some Refl | _ -> None)
  | R31 -> ( match y with R31 -> Some Refl | _ -> None)

let rec read_mem : type a. Addr.t -> (Addr.t * a) list -> a option =
 fun addr -> function
  | [] -> None
  | (x, v) :: tl -> if Addr.(x = addr) then Some v else read_mem addr tl

let sexp_of_mem m = sexp_of_mem (sexp_of_mem_v m) m
let sexp_of_reg r = sexp_of_reg (sexp_of_reg_v r) r

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
            Some (fun (k : (c, _) continuation) -> [ Suspended (k, prm) ])
        | _ -> None);
  }

let fulfill_mem (type a) (m : (Ticket.t * Addr.t * a option) list)
    (t : Ticket.t) (v : a) =
  let rec go seen = function
    | [] -> List.rev seen
    | (ticket, addr, ov) :: unseen ->
        if Ticket.(t = ticket) then
          List.rev_append seen ((ticket, addr, Some v) :: unseen)
        else go ((ticket, addr, ov) :: seen) unseen
  in
  go [] m

let mem_h :
    type a m.
    m mem ->
    ( a,
      st:m mem storage -> upd:m mem update -> a * m mem storage * m mem update
    )
    handler =
 fun m ->
  {
    retc = (fun v ~st ~upd -> (v, st, upd));
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        let () =
          if debug.hide () then
            let m = sexp_of_mem m in
            print_string @@ "mem_h " ^ Sexp.to_string_hum m ^ "\n"
        in
        match eff with
        | Read (Mem (addr, m')) -> (
            match eqb_mem m m' with
            | Some Refl ->
                Some
                  (fun (k : (c, _) continuation) ~st ~upd ->
                    let upd : m mem update = upd in
                    match upd with
                    | Mem_upd { pending_r; pending_w; ticket } ->
                        let () =
                          if debug.hide () then
                            let t =
                              Sexp.to_string_hum (Ticket.sexp_of_t ticket)
                            in
                            print_endline @@ "Read with ticket " ^ t
                        in
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
                        let () =
                          if debug.hide () then
                            let t =
                              Sexp.to_string_hum (Ticket.sexp_of_t ticket)
                            in
                            print_endline @@ "Write with ticket " ^ t
                        in
                        let upd' =
                          Mem_upd
                            {
                              pending_r;
                              pending_w = (ticket, addr, None) :: pending_w;
                              ticket = Ticket.(succ ticket);
                            }
                        in
                        continue k
                          (fun () ->
                            perform @@ Fulfill_mem (ticket, await v, m))
                          ~st ~upd:upd')
            | None -> None)
        | Check_mem (ticket, addr, m') -> (
            match eqb_mem m m' with
            | Some Refl ->
                Some
                  (fun k ~st ~upd ->
                    let upd : m mem update = upd in
                    match upd with
                    | Mem_upd { pending_r; _ } ->
                        let () =
                          if debug.hide () then
                            let t =
                              Sexp.to_string_hum (Ticket.sexp_of_t ticket)
                            in
                            print_endline @@ "Check with ticket " ^ t
                        in
                        if Ticket.(ticket + one = pending_r) then
                          match st with
                          | Mem_st { mem_st; _ } ->
                              let m : (Addr.t * m) list = mem_st in
                              continue k (read_mem addr m) ~st ~upd
                        else continue k None ~st ~upd)
            | None -> None)
        | Fulfill_mem (t, v, m') -> (
            match eqb_mem m m' with
            | Some Refl ->
                Some
                  (fun k ~st ~upd ->
                    let upd : m mem update = upd in
                    match upd with
                    | Mem_upd { pending_r; pending_w; ticket } ->
                        let () =
                          if debug.hide () then (
                            let pending_w =
                              Sexp.to_string_hum
                              @@ sexp_of_mem_pending_w m pending_w
                            in
                            print_endline pending_w;

                            let t = Sexp.to_string_hum (Ticket.sexp_of_t t) in
                            print_endline @@ "Fulfill with ticket " ^ t)
                        in
                        let pending_w = fulfill_mem pending_w t v in
                        let upd' = Mem_upd { pending_r; pending_w; ticket } in
                        continue k () ~st ~upd:upd')
            | None -> None)
        | _ -> None);
  }

let fulfill_reg (type a) (r : (Ticket.t * a option) list) (t : Ticket.t) (v : a)
    =
  let rec go seen = function
    | [] -> List.rev seen
    | (ticket, ov) :: unseen ->
        if Ticket.(t = ticket) then
          List.rev_append seen ((ticket, Some v) :: unseen)
        else go ((ticket, ov) :: seen) unseen
  in
  go [] r

let reg_h :
    type a r.
    r reg ->
    ( a,
      st:r reg storage -> upd:r reg update -> a * r reg storage * r reg update
    )
    handler =
 fun r ->
  {
    retc = (fun v ~st ~upd -> (v, st, upd));
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        let () =
          if debug.hide () then
            let r = sexp_of_reg r in
            print_string @@ "reg_h " ^ Sexp.to_string_hum r ^ "\n"
        in
        match eff with
        | Read (Reg r') -> (
            match eqb_reg r r' with
            | Some Refl ->
                Some
                  (fun (k : (c, _) continuation) ~st ~upd ->
                    let upd : r reg update = upd in
                    match upd with
                    | Reg_upd { ticket; _ } ->
                        let () =
                          if debug.hide () then
                            let t =
                              Sexp.to_string_hum (Ticket.sexp_of_t ticket)
                            in
                            print_endline @@ "Read with ticket " ^ t
                        in
                        continue k
                          (fun () -> perform @@ Check_reg (ticket, r))
                          ~st ~upd)
            | None -> None)
        | Write (Reg r', v) -> (
            match eqb_reg r r' with
            | Some Refl ->
                Some
                  (fun k ~st ~upd ->
                    let upd : r reg update = upd in
                    match upd with
                    | Reg_upd { pending_r; pending_w; ticket } ->
                        let () =
                          if debug.hide () then
                            let t =
                              Sexp.to_string_hum (Ticket.sexp_of_t ticket)
                            in
                            print_endline @@ "Write with ticket " ^ t
                        in
                        let upd' =
                          Reg_upd
                            {
                              pending_r;
                              pending_w = (ticket, None) :: pending_w;
                              ticket = Ticket.(succ ticket);
                            }
                        in
                        continue k
                          (fun () ->
                            perform @@ Fulfill_reg (ticket, await v, r))
                          ~st ~upd:upd')
            | None -> None)
        | Check_reg (t, r') -> (
            match eqb_reg r r' with
            | Some Refl ->
                Some
                  (fun k ~st ~upd ->
                    let upd : r reg update = upd in
                    match upd with
                    | Reg_upd { pending_r; ticket; _ } ->
                        let () =
                          if debug.hide () then
                            let t =
                              Sexp.to_string_hum (Ticket.sexp_of_t ticket)
                            in
                            print_endline @@ "Check with ticket " ^ t
                        in
                        if Ticket.(t = pending_r) then
                          match st with
                          | Reg_st { reg_st; _ } ->
                              let r : r = reg_st in
                              continue k (Some r) ~st ~upd
                        else continue k None ~st ~upd)
            | None -> None)
        | Fulfill_reg (t, v, r') -> (
            match eqb_reg r r' with
            | Some Refl ->
                Some
                  (fun k ~st ~upd ->
                    let upd : r reg update = upd in
                    match upd with
                    | Reg_upd { pending_r; pending_w; ticket } ->
                        let () =
                          if debug.hide () then
                            let t = Sexp.to_string_hum (Ticket.sexp_of_t t) in
                            print_endline @@ "Fulfill with ticket " ^ t
                        in
                        let pending_w = fulfill_reg pending_w t v in
                        let upd' = Reg_upd { pending_r; pending_w; ticket } in
                        continue k () ~st ~upd:upd')
            | None -> None)
        | _ -> None);
  }

let fulfill_add1 (a : (Ticket.t * int option * int option) list) (t : Ticket.t)
    (v : int) =
  let rec go seen = function
    | [] -> List.rev seen
    | (ticket, _, o2) :: unseen when Ticket.(t = ticket) ->
        perform More;
        List.rev_append seen ((ticket, Some v, o2) :: unseen)
    | hd :: unseen -> go (hd :: seen) unseen
  in
  go [] a

let fulfill_add2 (a : (Ticket.t * int option * int option) list) (t : Ticket.t)
    (v : int) =
  let rec go seen = function
    | [] -> List.rev seen
    | (ticket, o1, _) :: unseen when Ticket.(t = ticket) ->
        perform More;
        List.rev_append seen ((ticket, o1, Some v) :: unseen)
    | hd :: unseen -> go (hd :: seen) unseen
  in
  go [] a

let check_add (a : (Ticket.t * int option * int option) list) (t : Ticket.t) =
  let rec go seen = function
    | [] -> (List.rev seen, None)
    | (ticket, Some v1, Some v2) :: unseen when Ticket.(t = ticket) ->
        perform More;
        (List.rev_append seen unseen, Some Int.(v1 + v2))
    | hd :: unseen -> go (hd :: seen) unseen
  in
  go [] a

let add_h :
    type a.
    ( a,
      st:adder storage -> upd:adder update -> a * adder storage * adder update
    )
    handler =
  {
    retc = (fun v ~st ~upd -> (v, st, upd));
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        match eff with
        | Add (x, y) ->
            Some
              (fun (k : (c, _) continuation) ~st ~upd ->
                let (Adder_upd { pending_op; ticket }) = upd in
                let upd =
                  Adder_upd
                    {
                      pending_op = (ticket, None, None) :: pending_op;
                      ticket = Ticket.(succ ticket);
                    }
                in
                let worker () =
                  let op1 () = perform @@ Fulfill_add1 (ticket, await x) in
                  let op2 () = perform @@ Fulfill_add2 (ticket, await y) in
                  schedule op1;
                  schedule op2
                in
                let checker () = perform @@ Check_add ticket in
                continue k (worker, checker) ~st ~upd)
        | Fulfill_add1 (t, x) ->
            Some
              (fun (k : (c, _) continuation) ~st ~upd ->
                let (Adder_upd { pending_op; ticket }) = upd in
                let upd =
                  Adder_upd { pending_op = fulfill_add1 pending_op t x; ticket }
                in
                continue k () ~st ~upd)
        | Fulfill_add2 (t, y) ->
            Some
              (fun (k : (c, _) continuation) ~st ~upd ->
                let (Adder_upd { pending_op; ticket }) = upd in
                let upd =
                  Adder_upd { pending_op = fulfill_add2 pending_op t y; ticket }
                in
                continue k () ~st ~upd)
        | Check_add t ->
            Some
              (fun (k : (c, _) continuation) ~st ~upd ->
                let (Adder_upd { pending_op; ticket }) = upd in
                let pending_op, found = check_add pending_op t in
                let upd = Adder_upd { pending_op; ticket } in
                continue k found ~st ~upd)
        | _ -> None);
  }

let vote pc voted =
  let rec go seen = function
    | [] -> (List.rev seen, false)
    | (addr, n, prm) :: unseen ->
        if Addr.(addr = pc) then
          (List.rev_append seen ((addr, n + 1, prm) :: unseen), true)
        else go ((addr, n, prm) :: seen) unseen
  in
  let voted, found = go [] voted in
  if found then voted else (pc, 1, read (Mem (pc, Imem))) :: voted

let elect default voted =
  let rec go (addr, n, prm) seen = function
    | [] -> ((addr, n, prm), List.rev seen)
    | (addr', n', prm') :: unseen ->
        if Int.(n' < n) then
          go (addr, n, prm) ((addr', n', prm') :: seen) unseen
        else go (addr', n', prm') ((addr, n, prm) :: seen) unseen
  in
  go default [] voted

let warp_h :
    type a.
    ( a,
      st:warp storage -> upd:warp update -> a * warp storage * warp update )
    handler =
  {
    retc = (fun v ~st ~upd -> (v, st, upd));
    exnc = raise;
    effc =
      (fun (type c) (eff : c t) ->
        match eff with
        | Vote pc ->
            Some
              (fun (k : (c, _) continuation) ~st ~upd ->
                let upd, ballot =
                  match upd with
                  | Warp_upd { voted; nth_election } ->
                      ( Warp_upd { voted = vote pc voted; nth_election },
                        fun () -> perform @@ Check_ballot nth_election )
                in
                continue k ballot ~st ~upd)
        | Decode pc ->
            Some
              (fun (k : (c, _) continuation) ~st ~upd ->
                let decode_res =
                  match st with
                  | Warp_st { warp_pc; decode_req } -> (
                      match warp_pc with
                      | None -> None
                      | Some warp_pc ->
                          if Addr.(pc = warp_pc) then Some decode_req else None)
                in
                continue k decode_res ~st ~upd)
        | Check_ballot ballot ->
            Some
              (fun (k : (c, _) continuation) ~st ~upd ->
                let ans =
                  match upd with
                  | Warp_upd { nth_election; _ } ->
                      if Ticket.(ballot < nth_election) then Some () else None
                in
                continue k ans ~st ~upd)
        | _ -> None);
  }

let scheduler tasks =
  List.fold tasks ~init:[] ~f:(fun todo -> function
    | Initial task -> List.rev_append (match_with task () task_h) todo
    | Suspended (k, prm) -> (
        match prm () with
        | Some v -> List.rev_append (continue k v) todo
        | None -> Suspended (k, prm) :: todo))

let update_storage :
    type s. st:s storage -> upd:s update -> s storage * s update =
 fun ~st ~upd ->
  match st with
  | Mem_st { mem_st; mem_tag } -> (
      match upd with
      | Mem_upd { pending_r; pending_w; ticket } -> (
          let fst_w, rev_pending_w =
            let rev_pending_w = List.rev pending_w in
            let fst_w =
              match rev_pending_w with
              | [] -> ticket
              | (fst_w, _, _) :: _ -> fst_w
            in
            (fst_w, rev_pending_w)
          in
          if Ticket.(pending_r < fst_w) then (
            (* turn to read *)
            perform More;
            let pending_r = Ticket.(succ pending_r) in
            (st, Mem_upd { pending_r; pending_w; ticket }))
          else
            (* turn to write *)
            match rev_pending_w with
            | (_, addr, Some v) :: rev_pending_w ->
                perform More;
                let pending_r = Ticket.(succ pending_r) in
                let snd_w =
                  match rev_pending_w with
                  | [] -> ticket
                  | (snd_w, _, _) :: _ -> snd_w
                in
                let pending_r =
                  if Ticket.(pending_r < snd_w) then
                    (* allow reading *)
                    Ticket.(succ pending_r)
                  else pending_r
                in
                let pending_w = List.rev rev_pending_w in
                ( Mem_st { mem_st = (addr, v) :: mem_st; mem_tag },
                  Mem_upd { pending_r; pending_w; ticket } )
            | _ -> (st, upd)))
  | Reg_st { reg_tag; _ } -> (
      match upd with
      | Reg_upd { pending_r; pending_w; ticket } -> (
          match List.rev pending_w with
          | (_, Some v) :: rev_pending_w ->
              perform More;
              let pending_r = Ticket.(succ pending_r) in
              let pending_w = List.rev rev_pending_w in
              ( Reg_st { reg_st = v; reg_tag },
                Reg_upd { pending_r; pending_w; ticket } )
          | _ -> (st, upd)))
  | Adder_st -> (st, upd)
  | Warp_st _ -> (
      match upd with
      | Warp_upd { voted; nth_election } -> (
          match voted with
          | [] -> (st, upd)
          | default :: voted ->
              perform More;
              let (pc, _, prm), voted = elect default voted in
              ( Warp_st { warp_pc = Some pc; decode_req = prm },
                Warp_upd { voted; nth_election = Ticket.succ nth_election } )))

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
      | Mem_st { mem_tag; _ } ->
          let children, st, upd = match_with exec () (mem_h mem_tag) ~st ~upd in
          Mk_arch { st; upd; children }
      | Reg_st { reg_tag; _ } ->
          let children, st, upd = match_with exec () (reg_h reg_tag) ~st ~upd in
          Mk_arch { st; upd; children }
      | Adder_st ->
          let children, st, upd = match_with exec () add_h ~st ~upd in
          Mk_arch { st; upd; children }
      | Warp_st _ ->
          let children, st, upd = match_with exec () warp_h ~st ~upd in
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
            Out_channel.flush stdout;
            print_endline "-------- After step --------";
            print_endline (Sexp.to_string_hum @@ sexp_of_arch arch))
        in
        go arch
      else arch
    else arch
  in
  go

let rec update_arch (arch : exec arch) =
  match arch with
  | Mk_arch { st; upd; children } -> (
      let st, upd = update_storage ~st ~upd in
      match children with
      | Arch l ->
          Mk_arch { st; upd; children = Arch (List.map ~f:update_arch l) }
      | Exec _ -> Mk_arch { st; upd; children })

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
            Out_channel.flush stdout;
            print_endline "-------- After run --------";
            print_endline (Sexp.to_string_hum @@ sexp_of_arch arch))
        in
        go arch
      else arch
    else arch
  in
  go
