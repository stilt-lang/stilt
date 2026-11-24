(* The playground's runs: the reference interpreter's [run] of a program of one
   file, compiled to JavaScript. The page calls [stiltRun] with the text of
   [main.lt], and gets back what the program wrote, each piece with its stream,
   and its exit status, as [stilt-ref run main.lt] would end. *)

open Js_of_ocaml

(* What the program wrote, latest first, each piece with its stream. *)
let written = ref []

let collect stream text =
  match !written with
  | (s, before) :: rest when s = stream -> written := (s, before ^ text) :: rest
  | pieces -> written := (stream, text) :: pieces

(* The status of a program with errors, or without [main]
   (conformance.run-statuses). *)
let erroneous = 2

(* An exception that escapes the interpreter, as cmdliner reports one for
   stilt-ref: a call of the system that a browser doesn't have, among them. *)
let internal_error = 125

(* The program [main.lt] of [text], as [Program.load] reads it from a file of
   the current directory. *)
let program text : Stilt.Program.t =
  {
    sources =
      [ { module_path = [ "main" ]; file = "main.lt"; text; package = 0 } ];
    packages = Stilt.Program.single;
  }

(* Runs the program as stilt-ref's [run] does, with no arguments: a program
   with errors runs too, after its diagnostics, and ends with status 2
   (program.programs-with-errors). *)
let status text =
  let { Stilt.Program.sources; packages } = program text in
  let diagnostics, (env, hir, tast) = Stilt.Driver.for_run ~packages sources in
  let errors = List.exists Stilt.Diagnostic.is_error diagnostics in
  if errors then
    List.iter
      (fun d -> prerr_endline (Stilt.Diagnostic.to_string d))
      diagnostics;
  match Stilt.Eval.run env hir tast ~args:[] with
  | Some status -> if errors then erroneous else status
  | None ->
      (* program.missing-main *)
      prerr_endline "stilt-ref: module `main` has no function `main`";
      erroneous

let run text =
  written := [];
  let status =
    try status (Js.to_string text)
    with e ->
      flush stdout;
      prerr_endline ("stilt-ref: internal error: " ^ Printexc.to_string e);
      internal_error
  in
  flush stdout;
  flush stderr;
  let piece (stream, text) = Js.array [| Js.string stream; Js.string text |] in
  Js.Unsafe.obj
    [|
      ("status", Js.Unsafe.inject status);
      ( "output",
        Js.Unsafe.inject
          (Js.array (Array.of_list (List.rev_map piece !written))) );
    |]

let () =
  Stilt.Driver.use_std_snapshot Std_snapshot.data;
  Sys_js.set_channel_flusher stdout (collect "stdout");
  Sys_js.set_channel_flusher stderr (collect "stderr");
  Js.export "stiltRun" (Js.wrap_callback run)
