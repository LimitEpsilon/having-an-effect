open EDSLNG
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

let _ = print_endline "All Done"
