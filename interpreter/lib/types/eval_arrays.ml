(* The natives of [std.array] (generics.arrays). An array is held as a list of
   exactly its size, whose value semantics are an array's (generics.array-elements). *)

open Value
open Eval_state
open Eval_targets
module T = Types

(* The size that an array type's arguments give, the second of [targs]: the
   impl's for a method, and the function's own for [fill] and [from_list]. *)
let size targs =
  match List.map T.resolve targs with
  | _ :: T.Value text :: _ -> Int64.of_string text
  | _ -> invalid_arg "Eval_arrays.size"

(* [n] copies of [x]; a negative size panics with [bounds]. *)
let fill n x =
  if n < 0L then
    Fault.panic "bounds"
      "an array's size is never negative, and this one is %Ld" n
  else (
    reserve (Int64.to_int n * 8);
    List (Vec.of_list (List.init (Int64.to_int n) (fun _ -> x))))

let native t fr loc name targs args =
  match (name, args) with
  | "fill", [| x |] -> fill (size targs) x
  | "from_list", [| List xs |] ->
      if Int64.of_int (Vec.length xs) = size targs then some (List xs) else none
  (* [f] of each element, called in order. *)
  | "map", [| List xs; Fn f |] ->
      let target = target_of_fn t f in
      List
        (Vec.of_list
           (List.map
              (fun x -> t.apply t fr loc target [| x |])
              (Vec.to_list xs)))
  | _ -> invalid_arg ("Eval_arrays.native: " ^ name)
