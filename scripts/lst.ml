(**
   Some handy list operations
*)

(* Build a list that is a range of values between min and max. *)
let rec range ?(accum=[]) ?(step=pred) ?(min=1) max =
  if max < min then accum
  else range ~accum:(max :: accum) ~step:step ~min:min (step max)



(* Associate all elements of [alst] with all elements of [blst] (the cartesian product). *)
let cart_prod alst blst =
  List.flatten (List.map (fun a -> List.map (fun b -> (a, b)) blst) alst)
