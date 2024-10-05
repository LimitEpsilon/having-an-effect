open Core
open Effect
open Domains

let rec cycle () =
  let pc_tgt = await (read (Reg PC)) in
  let pc_warp = perform @@ Decode pc_tgt in
  match pc_warp with
  | None -> next_cycle pc_tgt
  | Some inst -> execute pc_tgt (await inst)

and next_cycle pc =
  write (Reg PC) pc;
  let ballot = perform @@ Vote pc in
  await ballot;
  cycle ()

(* differentiate btwn local/shared memory *)
(* differentiate btwn registers that have different latencies *)
and execute pc inst =
  match inst with
  | Add ->
      let x = read (Reg RS1) in
      let y = read (Reg RS2) in
      (* TODO: use effects to consider latency of addition *)
      let w () =
        let x = await x in
        let y = await y in
        write (Reg RD) (x + y)
      in
      let pc_tgt = Addr.(succ pc) in
      schedule w;
      next_cycle pc_tgt
  | Ld addr ->
      let x = read (Mem (addr, Dmem)) in
      let w () =
        let x = await x in
        write (Reg RD) x
      in
      let pc_tgt = Addr.(succ pc) in
      schedule w;
      next_cycle pc_tgt
  | St addr ->
      let x = read (Reg RS1) in
      let w () =
        let x = await x in
        write (Mem (addr, Dmem)) x
      in
      let pc_tgt = Addr.(succ pc) in
      schedule w;
      next_cycle pc_tgt
  | Beq addr ->
      let x = read (Reg RS1) in
      let y = read (Reg RS2) in
      (* TODO: use effects to consider latency of comparison *)
      let w () =
        let x = await x in
        let y = await y in
        let pc_tgt = if Int.(x = y) then addr else Addr.(succ pc) in
        next_cycle pc_tgt
      in
      schedule w
  | Blt addr ->
      let x = read (Reg RS1) in
      let y = read (Reg RS2) in
      (* TODO: use effects to consider latency of comparison *)
      let w () =
        let x = await x in
        let y = await y in
        let pc_tgt = if Int.(x < y) then addr else Addr.(succ pc) in
        next_cycle pc_tgt
      in
      schedule w
  | Halt -> ()
