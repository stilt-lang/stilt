(* Tests the length limit of facts.greatest-length: no list holds more than 2^48
   elements, and a run that would make a longer one ends as running out of
   memory does, with status 134. *)

open Stilt

let run text =
  match Driver.analyse (Diagnostics.sources [ ("main.lt", text) ]) with
  | [], Some (env, hir, program) -> (
      match Eval.run env hir program ~args:[] with
      | Some status -> Printf.printf "exit %d\n" status
      | None -> print_endline "no main")
  | _ -> print_endline "the program has errors"

let%expect_test "a list past 2^48 elements" =
  run
    "fn main() {\n\
    \  let xs = List.repeat(0, 281474976710657)\n\
    \  let _ = xs.len()\n\
     }";
  [%expect {|
    fatal: out of memory
    exit 134
    |}]
