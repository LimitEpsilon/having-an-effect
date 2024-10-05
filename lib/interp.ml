open Debug
open Core
open Effect
open Effect.Deep
open Domains

type (_, _) refl = Refl : ('a, 'a) refl

let eqb_mem (type a b) (x : a mem) (y : b mem) : (a, b) refl option =
  match x with
  | Imem -> ( match y with Imem -> Some Refl | _ -> None)
  | Dmem -> ( match y with Dmem -> Some Refl | _ -> None)

let eqb_reg (type a b) (x : a reg) (y : b reg) : (a, b) refl option =
  match x with
  | PC -> ( match y with PC -> Some Refl | _ -> None)
  | RS1 -> ( match y with RS1 -> Some Refl | _ -> None)
  | RS2 -> ( match y with RS2 -> Some Refl | _ -> None)
  | RD -> ( match y with RD -> Some Refl | _ -> None)

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
            Some (fun k -> [ Suspended (k, prm) ])
        | _ -> None);
  }

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
                let () =
                  if debug.hide () then
                    let m = sexp_of_pair Addr.sexp_of_t sexp_of_mem (addr, m) in
                    print_string @@ "Handle: " ^ Sexp.to_string_hum m ^ "\n"
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
                          | Mem_st { mem_st; _ } ->
                              let m : (Addr.t * m) list = mem_st in
                              continue k (read_mem addr m) ~st ~upd
                        else continue k None ~st ~upd)
            | None -> None)
        | _ -> None);
  }

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
                let () =
                  if debug.hide () then
                    let r = sexp_of_reg r in
                    print_string @@ "Handle: " ^ Sexp.to_string_hum r ^ "\n"
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
                    | Reg_upd None -> continue k () ~st ~upd:(Reg_upd (Some v))
                    | Reg_upd (Some _) ->
                        raise
                          (Register_written_twice
                             {
                               reg = Sexp.to_string (sexp_of_reg r);
                               value = Sexp.to_string (sexp_of_reg_v r v);
                             }))
            | None -> None)
        | Check_reg r' -> (
            match eqb_reg r r' with
            | Some Refl ->
                Some
                  (fun k ~st ~upd ->
                    match st with
                    | Reg_st { reg_st; _ } ->
                        let v : r = reg_st in
                        continue k (Some v) ~st ~upd)
            | None -> None)
        | _ -> None);
  }

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
                      ( Warp_upd { voted = pc :: voted; nth_election },
                        fun () -> perform @@ Check_ballot nth_election )
                in
                continue k ballot ~st ~upd)
        | Decode pc ->
            Some
              (fun (k : (c, _) continuation) ~st ~upd ->
                let st, decode_res =
                  match st with
                  | Warp_st { warp_pc; decode_req } ->
                      if Addr.(pc = warp_pc) then
                        match decode_req with
                        | None ->
                            let req = read (Mem (pc, Imem)) in
                            ( Warp_st { warp_pc; decode_req = Some req },
                              Some req )
                        | Some req -> (st, Some req)
                      else (st, None)
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

let update_storage :
    type s. st:s storage -> upd:s update -> s storage * s update =
 fun ~st ~upd ->
  match st with
  | Mem_st { mem_st; mem_tag } -> (
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
              ( Mem_st { mem_st = (addr, v) :: mem_st; mem_tag },
                Mem_upd { pending_r; pending_w; ticket } )
          | [] -> (st, Mem_upd { pending_r; pending_w; ticket })))
  | Reg_st { reg_st; reg_tag } -> (
      match upd with
      | Reg_upd o ->
          let st =
            match o with
            | None -> Reg_st { reg_st; reg_tag }
            | Some v ->
                perform More;
                Reg_st { reg_st = v; reg_tag }
          in
          (st, Reg_upd None))
  | Warp_st { warp_pc; _ } -> (
      match upd with
      | Warp_upd { voted; nth_election } -> (
          match voted with
          | [] -> (st, upd)
          | _ ->
              ( Warp_st { warp_pc = majority warp_pc voted; decode_req = None },
                Warp_upd { voted = []; nth_election = Ticket.succ nth_election }
              )))

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