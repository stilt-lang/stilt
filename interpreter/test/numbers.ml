(* What the tests of numeric operations share. *)

open Stilt

let kind name = Option.get (Ints.of_name name)
let option show = function Some x -> show x | None -> print_endline "None"
