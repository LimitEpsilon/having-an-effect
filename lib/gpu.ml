open Core
open Domains

let rec cycle () =
  let pc_tgt = await (read (Reg PC)) in
  let pc_warp = decode pc_tgt in
  match pc_warp with
  | None -> next_cycle pc_tgt
  | Some inst -> execute pc_tgt (await inst)

and next_cycle pc =
  let w = write (Reg PC) (fun () -> pc) in
  let () = schedule w in
  let ballot = vote pc in
  let () = await ballot in
  cycle ()

(* differentiate btwn local/shared memory *)
(* differentiate btwn registers that have different latencies *)
and execute pc inst =
  match inst with
  | Add (rd, rs1, rs2) ->
      let x = read (Reg rs1) in
      let y = read (Reg rs2) in
      (* TODO: use effects to consider latency of addition *)
      let added () = await x + await y in
      let w = write (Reg rd) added in
      let () = schedule w in
      let pc_tgt = Addr.(succ pc) in
      next_cycle pc_tgt
  | Addi (rd, rs1, imm) ->
      let x = read (Reg rs1) in
      (* TODO: use effects to consider latency of addition *)
      let added () = await x + imm in
      let w = write (Reg rd) added in
      let () = schedule w in
      let pc_tgt = Addr.(succ pc) in
      next_cycle pc_tgt
  | Ld (rd, imm, rs1) ->
      let base = read (Reg rs1) in
      let addr = Addr.(of_int (await base) + imm) in
      let x = read (Mem (addr, Dmem)) in
      let x () = await x in
      let w = write (Reg rd) x in
      let () = schedule w in
      let pc_tgt = Addr.(succ pc) in
      next_cycle pc_tgt
  | St (imm, rs1, rs2) ->
      let base = read (Reg rs1) in
      let x = read (Reg rs2) in
      let x () = await x in
      let addr = Addr.(of_int (await base) + imm) in
      let w = write (Mem (addr, Dmem)) x in
      let () = schedule w in
      let pc_tgt = Addr.(succ pc) in
      next_cycle pc_tgt
  | Beq (rs1, rs2, imm) ->
      let x = read (Reg rs1) in
      let y = read (Reg rs2) in
      (* TODO: use effects to consider latency of comparison *)
      let taken = Int.(await x = await y) in
      let pc_tgt = Addr.(if taken then pc + imm else succ pc) in
      next_cycle pc_tgt
  | Blt (rs1, rs2, imm) ->
      let x = read (Reg rs1) in
      let y = read (Reg rs2) in
      (* TODO: use effects to consider latency of comparison *)
      let taken = Int.(await x < await y) in
      let pc_tgt = Addr.(if taken then pc + imm else succ pc) in
      next_cycle pc_tgt
  | Halt -> ()
