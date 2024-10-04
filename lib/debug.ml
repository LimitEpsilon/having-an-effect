type 'a get_set = { get : unit -> 'a; set : 'a -> unit; hide : unit -> 'a }

(*module X (Y : Tuple.Comparable_sexpable) = Core.Tuple.Comparable (Int) (Y)*)

let debug =
  let b = ref false in
  {
    get = (fun () -> !b);
    set = (fun debug' -> b := debug');
    hide = (fun () -> false);
  }
