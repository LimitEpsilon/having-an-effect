open EDSLNG
open Debug
open Core
open Edslng

let () = debug.set false

let (VInt 9) =
  let module M = TInc in
  eval_v M.res

let (VInt 10) =
  let module M = TIf in
  eval_v M.res

(* Demonstrating that our if_ works correctly, even in the presence of errors *)
let (VInt 11) =
  let res =
    int 1
    + cond (eq (int 1 + int 2) (int 3)) (int 10) (fun _ -> failwith "Bang!")
  in
  eval_v res

let "Bang!" =
  let res =
    int 1
    + cond (eq (int 1 + int 2) (int 4)) (int 10) (fun _ -> failwith "Bang!")
  in
  try
    eval_v res |> ignore;
    "No"
  with
  | Failure s -> s
  | _ -> "No"

let (VInt 10) =
  let module M = TSt in
  eval_v M.res

(* Test cases *)
let (VClos _) =
  let module M = TLam in
  eval_v M.res0

let (VInt 10) =
  let module M = TLam in
  eval_v M.res01

let (VClos _) =
  let module M = TLam in
  eval_v M.res1

let (VInt 3) =
  let module M = TLam in
  eval_v M.res11

let (VInt 3) =
  let module M = TLam in
  eval_v M.res2

(* But we do not need any functors! *)

let (VInt 122) =
  let module M = TLamSt in
  eval_v M.res

(*let _ = print_endline "All Done"*)

let _ =
  debug.set true;
  let open Gpu in
  let add_addr = Addr.one in
  let halt_addr = Addr.succ add_addr in
  let prog : (Addr.t * inst) list = [ (add_addr, Add); (halt_addr, Halt) ] in
  let thread =
    Mk_arch
      {
        st = Reg_st (1, RS1);
        upd = Reg_upd None;
        children =
          Arch
            [
              Mk_arch
                {
                  st = Reg_st (1, RS2);
                  upd = Reg_upd None;
                  children =
                    Arch
                      [
                        Mk_arch
                          {
                            st = Reg_st (0, RD);
                            upd = Reg_upd None;
                            children =
                              Arch
                                [
                                  Mk_arch
                                    {
                                      st =
                                        Reg_st
                                          ( { pc_tgt = add_addr; pc_en = true },
                                            PC );
                                      upd = Reg_upd None;
                                      children = Exec [ Initial cycle ];
                                    };
                                ];
                          };
                      ];
                };
            ];
      }
  in
  let arch =
    Mk_arch
      {
        st = Mem_st (prog, Inst);
        upd =
          Mem_upd
            { pending_r = Ticket.one; pending_w = []; ticket = Ticket.one };
        children =
          Arch
            [
              Mk_arch
                {
                  st = Reg_st (Addr.one, PC_warp);
                  upd = PC_upd [];
                  children = Arch [ thread; thread ];
                };
            ];
      }
  in
  Sexp.pp_hum Stdlib.Format.std_formatter (sexp_of_arch (run arch));
  Out_channel.newline stdout
