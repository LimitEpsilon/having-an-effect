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

let _ =
  debug.set true;
  let open Domains in
  let a_base = 0 in
  let b_base = 200 in
  let mem : (Addr.t * int) list =
    Addr.
      [
        (of_int Int.(a_base + 0), 1);
        (of_int Int.(a_base + 1), 2);
        (of_int Int.(a_base + 2), 3);
        (of_int Int.(b_base + 0), 4);
        (of_int Int.(b_base + 1), 5);
        (of_int Int.(b_base + 2), 6);
      ]
  in
  let imem_base = 0 in
  let prog : (Addr.t * inst) list =
    Addr.
      [
        (of_int Int.(imem_base + 0), Ld (RS2, of_int 0, RS1));
        (of_int Int.(imem_base + 1), Add (RD, RS2, RS2));
        (of_int Int.(imem_base + 2), St (of_int 100, RS1, RD));
        (of_int Int.(imem_base + 3), Ld (RS2, of_int 1, RS1));
        (of_int Int.(imem_base + 4), Add (RD, RS2, RS2));
        (of_int Int.(imem_base + 5), St (of_int 101, RS1, RD));
        (of_int Int.(imem_base + 6), Ld (RS2, of_int 2, RS1));
        (of_int Int.(imem_base + 7), Add (RD, RS2, RS2));
        (of_int Int.(imem_base + 8), St (of_int 102, RS1, RD));
        (of_int Int.(imem_base + 9), Halt);
      ]
  in
  let thread rs1 rs2 =
    Mk_arch
      {
        st = Reg_st { reg_st = rs1; reg_tag = RS1 };
        upd = reg_upd_init;
        children =
          Arch
            [
              Mk_arch
                {
                  st = Reg_st { reg_st = rs2; reg_tag = RS2 };
                  upd = reg_upd_init;
                  children =
                    Arch
                      [
                        Mk_arch
                          {
                            st = Reg_st { reg_st = 0; reg_tag = RD };
                            upd = reg_upd_init;
                            children =
                              Arch
                                [
                                  Mk_arch
                                    {
                                      st =
                                        Reg_st
                                          {
                                            reg_st = Addr.(of_int imem_base);
                                            reg_tag = PC;
                                          };
                                      upd = reg_upd_init;
                                      children = Exec [ Initial Gpu.cycle ];
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
        st = Mem_st { mem_st = mem; mem_tag = Dmem };
        upd =
          Mem_upd
            { pending_r = Ticket.one; pending_w = []; ticket = Ticket.one };
        children =
          Arch
            [
              Mk_arch
                {
                  st = Mem_st { mem_st = prog; mem_tag = Imem };
                  upd = mem_upd_init;
                  children =
                    Arch
                      [
                        Mk_arch
                          {
                            st =
                              Warp_st
                                {
                                  warp_pc = Addr.of_int imem_base;
                                  decode_req = None;
                                };
                            upd =
                              Warp_upd { voted = []; nth_election = Ticket.one };
                            children =
                              Arch
                                [
                                  Mk_arch
                                    {
                                      st = Reg_st { reg_st = 0; reg_tag = R0 };
                                      upd = reg_upd_init;
                                      children =
                                        Arch
                                          [ thread a_base 0; thread b_base 0 ];
                                    };
                                ];
                          };
                      ];
                };
            ];
      }
  in
  let final = Sexp.to_string_hum (sexp_of_arch (Interp.run arch)) in
  print_endline "-------- Final state --------";
  print_endline final
