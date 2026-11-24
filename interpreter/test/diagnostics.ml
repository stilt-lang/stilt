(* Checks a test's program and prints its diagnostics as conformance.diagnostic-lines compares them:
   a file, a line and a code each. *)

open Stilt

let sources files =
  List.map
    (fun (file, text) ->
      {
        Program.module_path = Program.module_path file;
        file;
        text;
        package = 0;
      })
    files

let print = function
  | [] -> print_endline "ok"
  | diagnostics ->
      List.iter
        (fun (d : Diagnostic.t) ->
          Printf.printf "%s:%d: %s\n" d.file d.line (d.code :> string))
        diagnostics

let check files = print (Driver.check (sources files))
let main text = check [ ("main.lt", text) ]

module Errors = struct
  let check files =
    print (List.filter Diagnostic.is_error (Driver.check (sources files)))

  let main text = check [ ("main.lt", text) ]
end
