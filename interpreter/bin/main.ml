(* stilt-ref, the reference interpreter. Its commands follow the protocol of
   conformance.commands as the stages behind them are written; [lex] is a debugging aid. *)

open Cmdliner

(* A path that isn't a program is an error in the command line. *)
let not_a_program = Cmd.Exit.cli_error

let lex path =
  let text = In_channel.with_open_bin path In_channel.input_all in
  let output = Stilt.Lexer.tokenize ~file:path text in
  List.iter
    (fun ({ token; line; col } : Stilt.Lexer.token) ->
      Printf.printf "%d:%d %s\n" line col (Stilt.Token.to_string token))
    output.tokens;
  match output.error with
  | None -> 0
  | Some diagnostic ->
      prerr_endline (Stilt.Diagnostic.to_string diagnostic);
      1

(* Runs [f] on the program at [path]. *)
let with_program path f =
  match Stilt.Program.load path with
  | Ok program -> f program
  | Error message ->
      prerr_endline ("stilt-ref: " ^ message);
      not_a_program

(* Prints the tree of every file, or, if any file has a syntax error, the
   first syntax error of each such file and nothing on stdout. *)
let parse path =
  with_program path @@ fun { sources; _ } ->
  match Stilt.Driver.parse sources with
  | Ok modules ->
      List.iter
        (fun ((src : Stilt.Program.source), m) ->
          Printf.printf "(file %s %s)\n"
            (Stilt.Sexp.quote src.file)
            (Stilt.Sexp.of_module m))
        modules;
      0
  | Error errors ->
      List.iter (fun d -> prerr_endline (Stilt.Diagnostic.to_string d)) errors;
      1

(* Reports the program's diagnostics: as JSON on stdout for [--json]
   (conformance.diagnostic-objects), and otherwise as lines on stderr. *)
let check json path =
  with_program path @@ fun { sources; packages } ->
  let diagnostics = Stilt.Driver.check ~packages sources in
  if json then
    Printf.printf "{\"diagnostics\": [%s]}\n"
      (String.concat ", " (List.map Stilt.Diagnostic.to_json diagnostics))
  else
    List.iter
      (fun d -> prerr_endline (Stilt.Diagnostic.to_string d))
      diagnostics;
  if List.exists Stilt.Diagnostic.is_error diagnostics then 1 else 0

(* The exit status of [run] for a program with errors, or without [main]
   (conformance.run-statuses). *)
let erroneous = 2

(* Runs the program with its arguments. A program with errors runs too, after
   its diagnostics, and ends with status 2 (program.programs-with-errors). *)
let run path args =
  with_program path @@ fun { sources; packages } ->
  let diagnostics, (env, hir, program) =
    Stilt.Driver.for_run ~packages sources
  in
  let errors = List.exists Stilt.Diagnostic.is_error diagnostics in
  if errors then
    List.iter
      (fun d -> prerr_endline (Stilt.Diagnostic.to_string d))
      diagnostics;
  Stilt.Program.load_libraries packages;
  match Stilt.Eval.run env hir program ~args with
  | Some status -> if errors then erroneous else status
  | None ->
      (* program.missing-main *)
      prerr_endline "stilt-ref: module `main` has no function `main`";
      erroneous

(* The status of [model] for a program that the Lean model's calculus can't
   write, which its runs skip. *)
let outside_model = 77

(* Writes a program as the Lean model's calculus writes it, for the model's
   executable semantics (formal/Stilt/Run), one with errors as [run] runs it. *)
let model path =
  with_program path @@ fun { sources; packages } ->
  let diagnostics, (env, _, program) = Stilt.Driver.for_run ~packages sources in
  let erroneous = List.exists Stilt.Diagnostic.is_error diagnostics in
  match Stilt.Model.export ~erroneous env program with
  | Ok json ->
      print_endline json;
      0
  | Error why ->
      prerr_endline ("stilt-ref: outside the model: " ^ why);
      outside_model

(* Runs every test, doc example and property of a program that has no errors, and
   reports them with the program's diagnostics: as JSON on stdout for
   [--json] (conformance.diagnostic-objects), and otherwise as lines. With [--std], the
   standard library's own tests and examples run instead (std.examples). *)
let test json std path =
  if std then Stilt.Program.read_std_examples ();
  with_program path @@ fun { sources; packages } ->
  let diagnostics, checked = Stilt.Driver.analyse ~packages sources in
  let errors = List.exists Stilt.Diagnostic.is_error diagnostics in
  let verdicts =
    match checked with
    | Some (env, hir, program) when not errors ->
        let tests =
          if std then Stilt.Driver.std_tests program
          else Stilt.Driver.root_tests sources program
        in
        Stilt.Program.load_libraries packages;
        Stilt.Eval.test env hir tests
    | _ -> Ok []
  in
  match verdicts with
  | Error reason ->
      (* program.exit-statuses *)
      prerr_endline ("fatal: " ^ reason);
      134
  | Ok verdicts ->
      let line (v : Stilt.Eval.verdict) =
        if json then
          let property =
            match v.property with
            | Some p -> ", \"property\": " ^ Stilt.Eval_props.json p
            | None -> ""
          in
          Printf.sprintf {|{"file": %s, "line": %d, "passed": %b%s}|}
            (Stilt.Json.string v.file) v.line v.passed property
        else
          Printf.sprintf "%s:%d: %s" v.file v.line
            (if v.passed then "passed" else "failed")
      in
      if json then
        Printf.printf "{\"diagnostics\": [%s], \"tests\": [%s]}\n"
          (String.concat ", " (List.map Stilt.Diagnostic.to_json diagnostics))
          (String.concat ", " (List.map line verdicts))
      else (
        List.iter
          (fun d -> prerr_endline (Stilt.Diagnostic.to_string d))
          diagnostics;
        List.iter (fun v -> print_endline (line v)) verdicts);
      let passed (v : Stilt.Eval.verdict) = v.passed in
      if errors || not (List.for_all passed verdicts) then 1 else 0

let file =
  let doc = "The source file to read." in
  Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE" ~doc)

let program =
  let doc =
    "A source file, a directory holding a program's main.lt, or a package."
  in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"PATH" ~doc)

let sexp =
  let doc = "Print each file's syntax tree as an S-expression." in
  Arg.(required & vflag None [ (Some (), info [ "sexp" ] ~doc) ])

let json =
  let doc = "Print the diagnostics as one JSON object." in
  Arg.(value & flag & info [ "json" ] ~doc)

let std =
  let doc =
    "Run the standard library's own tests and doc examples instead of the \
     program's."
  in
  Arg.(value & flag & info [ "std" ] ~doc)

let program_args =
  let doc = "The arguments that the program receives." in
  Arg.(value & pos_right 0 string [] & info [] ~docv:"ARGS" ~doc)

let lex_command =
  let doc = "Print the tokens of a source file, one per line." in
  Cmd.make (Cmd.info "lex" ~doc) Term.(const lex $ file)

let parse_command =
  let doc =
    "Print the syntax tree of a program, as reference/03-syntax.md defines it."
  in
  Cmd.make (Cmd.info "parse" ~doc)
    Term.(const (fun () -> parse) $ sexp $ program)

let check_command =
  let doc = "Report the errors of a program." in
  Cmd.make (Cmd.info "check" ~doc) Term.(const check $ json $ program)

let run_command =
  let doc =
    "Run a program, whose code with errors panics where it is reached."
  in
  Cmd.make (Cmd.info "run" ~doc) Term.(const run $ program $ program_args)

let model_command =
  let doc =
    "Write a program as the Lean model's calculus writes it, as JSON, or end \
     with status 77 when it uses something the calculus lacks."
  in
  Cmd.make (Cmd.info "model" ~doc) Term.(const model $ program)

let test_command =
  let doc =
    "Run the tests, doc examples and properties of a program that has no \
     errors."
  in
  Cmd.make (Cmd.info "test" ~doc) Term.(const test $ json $ std $ program)

(* The arguments after [run PATH] belong to the program, even those that look
   like options, so they follow a [--]. *)
let argv =
  match Array.to_list Sys.argv with
  | exe :: "run" :: path :: args when not (String.starts_with ~prefix:"-" path)
    ->
      Array.of_list (exe :: "run" :: path :: "--" :: args)
  | _ -> Sys.argv

let () =
  Stilt.Driver.use_std_snapshot Std_snapshot.data;
  let doc = "The reference interpreter for Stilt" in
  let info = Cmd.info "stilt-ref" ~version:"0.0.0" ~doc in
  exit
    (Cmd.eval' ~argv
       (Cmd.group info
          [
            lex_command;
            parse_command;
            check_command;
            run_command;
            test_command;
            model_command;
          ]))
