open EDSLNG
open Debug
open Core

let () = debug.set false

let reg_upd_init =
  let open Domains in
  Reg_upd { pending_r = Ticket.one; pending_w = []; ticket = Ticket.one }

let mem_upd_init =
  let open Domains in
  Mem_upd { pending_r = Ticket.one; pending_w = []; ticket = Ticket.one }

let add_reg =
  let open Domains in
  fun (type r e) (r : r reg) init (l : e) ->
    Mk_arch
      {
        st = Reg_st { reg_st = init; reg_tag = r };
        upd = reg_upd_init;
        children = l;
      }

let add_mem =
  let open Domains in
  fun (type m e) (m : m mem) init (l : e) ->
    Mk_arch
      {
        st = Mem_st { mem_st = init; mem_tag = m };
        upd = mem_upd_init;
        children = l;
      }

let add_warp =
  let open Domains in
  fun (type e) (l : e) ->
    Mk_arch
      {
        st = Warp_st { warp_pc = None; decode_req = (fun () -> None) };
        upd = Warp_upd { voted = []; nth_election = Ticket.one };
        children = l;
      }

let () =
  debug.set true;
  let open Domains in
  let a_base = 0 in
  let b_base = 200 in
  let mem iter_num : (Addr.t * int) list =
    let rec go acc n =
      if n <= 0 then acc
      else
        let acc =
          Addr.(
            (of_int Int.(a_base + n - 1), n)
            :: (of_int Int.(b_base + n - 1), Int.(iter_num + n))
            :: acc)
        in
        go acc (n - 1)
    in
    go [] iter_num
  in
  let imem_base = 0 in
  (* PRE : (R2) = loop iter *)
  let loop : (Addr.t * inst) list =
    Addr.
      [
        (of_int Int.(imem_base + 0), Ld (R3, of_int 0, R1));
        (* R3 ← M[(R1)] *)
        (of_int Int.(imem_base + 1), Add (R3, R3, R3));
        (* R3 ← (R3) + (R3) *)
        (of_int Int.(imem_base + 2), St (of_int 100, R1, R3));
        (* M[(R1) + 100] ← (R3) *)
        (of_int Int.(imem_base + 3), Addi (R1, R1, 1));
        (* R1 ← (R1) + 1 *)
        (of_int Int.(imem_base + 4), Addi (R2, R2, -1));
        (* R2 ← (R2) - 1 *)
        (of_int Int.(imem_base + 5), Blt (R0, R2, of_int (-5)));
        (* if 0 < (R2) then goto loop head else halt *)
        (of_int Int.(imem_base + 6), Halt);
      ]
  in
  let prog = loop in
  let thread base iter_num =
    let arch = Exec [ Initial Gpu.cycle ] in
    let arch = Arch [ add_reg PC Addr.(of_int imem_base) arch ] in
    let arch = Arch [ add_reg R3 0 arch ] in
    let arch = Arch [ add_reg R2 iter_num arch ] in
    let arch = Arch [ add_reg R1 base arch ] in
    let arch = add_reg R0 0 arch in
    arch
  in
  let arch iter_num =
    let arch = Arch [ thread a_base iter_num; thread b_base iter_num ] in
    let arch = Arch [ add_warp arch ] in
    let arch = Arch [ add_mem Imem prog arch ] in
    let arch = add_mem Dmem (mem iter_num) arch in
    arch
  in
  let final = Sexp.to_string_hum (sexp_of_arch (Interp.run (arch 3))) in
  print_endline "-------- Final state --------";
  print_endline final
