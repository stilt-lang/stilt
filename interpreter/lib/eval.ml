(* The evaluator: a tree walker over the elaborated program, whose types decide
   dispatch, literals and integer widths. This module runs a
   program's [main], or its tests, doc examples and properties, and
   {!Eval_exprs} walks their code. *)

open Tast
open Value
open Eval_state
open Eval_operators
open Eval_traits
open Eval_exprs

(* A constant is evaluated where it is first used, once. One with an error
   panics wherever it is read (program.bodies-with-errors). *)
let add_constants t (hir : Hir.program) (program : Tast.program) =
  let value home at = function
    | Code e -> lazy (expr t (frame t ~home ~tenv:[] ~entry:None) e)
    | Broken -> (
        match at () with
        | Some (_, loc) -> lazy (check_error t ~home loc)
        | None -> invalid_arg "Eval.create")
    | Native -> invalid_arg "Eval.create"
  in
  List.iter
    (fun ((item : Hir.item), def) ->
      if not (Hashtbl.mem t.constants item) then
        Hashtbl.add t.constants item
          (value item.home (fun () -> Check_broken.constant_loc hir item) def))
    program.constants;
  List.iter
    (fun (((owner : Hir.item), name), def) ->
      let v =
        match (def, name) with
        | Native, "NAN" -> lazy (Float Float.nan)
        | Native, "INFINITY" -> lazy (Float Float.infinity)
        | _ ->
            value owner.home
              (fun () -> Check_broken.member_constant_loc hir owner name)
              def
      in
      if not (Hashtbl.mem t.member_constants (owner, name)) then
        Hashtbl.add t.member_constants (owner, name) v)
    program.member_constants;
  List.iter
    (fun (((trait, owner, name) as key), def) ->
      let at () = Check_broken.impl_constant_loc hir trait owner name in
      if not (Hashtbl.mem t.impl_constants key) then
        Hashtbl.add t.impl_constants key (value owner.Hir.home at def))
    program.impl_constants

let create env (hir : Hir.program) (program : Tast.program) ~args ~out =
  (* Of two definitions with the same name, the first is the one that names
     refer to. *)
  let table pairs =
    let h = Hashtbl.create 64 in
    List.iter
      (fun (k, v) -> if not (Hashtbl.mem h k) then Hashtbl.add h k v)
      pairs;
    h
  in
  let t =
    {
      env;
      modules = table (List.map (fun (m : Hir.module_) -> (m.name, m)) hir);
      functions = table program.functions;
      members = table program.members;
      impl_methods = table program.impl_methods;
      default_methods = table program.default_methods;
      constants = Hashtbl.create 64;
      member_constants = Hashtbl.create 64;
      impl_constants = Hashtbl.create 64;
      default_constants = table program.default_constants;
      args;
      out;
      apply;
      eval = expr;
    }
  in
  add_constants t hir program;
  t

(* macros.running: calls of a procedural macro of a checked program, which
   performs nothing, so that what it would print goes nowhere visible. *)
let caller env hir (program : Tast.program) =
  limit_resources ();
  let t = create env hir program ~args:[] ~out:stderr in
  fun (item : Hir.item) values loc ->
    match List.assoc_opt item program.functions with
    | Some f ->
        let fr = frame t ~home:item.home ~tenv:[] ~entry:None in
        apply t fr loc (Body (f, [])) values
    | None -> invalid_arg "Eval.caller"

let main : Hir.item = { home = "main"; name = "main" }

(* Where [main] is declared. *)
let main_loc (hir : Hir.program) =
  let declared (d : Hir.decl Hir.node) =
    match d.desc.kind with
    | Fn f when f.name.desc = main.name -> Some f.name.loc
    | _ -> None
  in
  List.find_map
    (fun (m : Hir.module_) ->
      if m.name = main.home then List.find_map declared m.decls else None)
    hir
  |> Option.get

let fatal reason =
  flush stdout;
  Printf.eprintf "fatal: %s\n%!" reason;
  134

(* program.exit-statuses: a write to a closed standard output fails rather than ending the
   process, and ends the program with the status a shell reports for a process that the signal of
   a broken pipe ends. *)
let closed_status = 141
let broken_pipe message = String.ends_with ~suffix:"Broken pipe" message

let run env hir (program : Tast.program) ~args =
  match List.assoc_opt main program.functions with
  | None -> None
  | Some f -> (
      limit_resources ();
      Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
      let t = create env hir program ~args ~out:stdout in
      let fr = frame t ~home:main.home ~tenv:[] ~entry:None in
      let loc = main_loc hir in
      (* program.exit-statuses *)
      let ended () =
        match apply t fr loc (Body (f, [])) [||] with
        | _ -> 0
        | exception Raised e ->
            let error = Option.get (Env.function_sig env main) in
            let shown = show t fr loc "show" (Option.get error.row.raise) e in
            flush stdout;
            prerr_string ("error: " ^ shown ^ "\n");
            1
      in
      match ended () with
      | status -> Some status
      | exception Panicked { kind; detail; file; loc } ->
          (* program.output-flushing and program.panic-report: the report comes after everything the
             program printed. *)
          flush stdout;
          Printf.eprintf "panic: %s: %s\n  at %s:%d:%d\n%!" kind detail file
            loc.line loc.col;
          Some 101
      | exception Exited status -> Some status
      | exception Sys_error message when broken_pipe message ->
          Some closed_status
      | exception Fatal reason -> Some (fatal reason)
      | exception Stack_overflow -> Some (fatal "stack overflow"))

type verdict = {
  file : string;
  line : int;
  passed : bool;
  property : Eval_props.verdict option;
}

let test ?(out = stderr) env hir (program : Tast.program) =
  limit_resources ();
  let t = create env hir program ~args:[] ~out in
  let module_of file = List.find (fun (m : Hir.module_) -> m.file = file) hir in
  let frame_of file =
    frame t ~home:(module_of file).name ~tenv:[] ~entry:None
  in
  (* A raise, a panic or an exit ends only the test that does it. *)
  let passes file run () =
    match run (frame_of file) with
    | passed -> (passed, None)
    | exception (Raised _ | Panicked _ | Exited _) -> (false, None)
  in
  let definition = function
    | Code x -> x
    | Native | Broken -> invalid_arg "Eval.test"
  in
  let test (test : Tast.test) =
    let body = definition test.block in
    let run fr =
      match block t fr body with _ -> true | exception Return _ -> true
    in
    (test.file, test.loc.line, passes test.file run)
  in
  let example (example : Tast.example) =
    let claim = definition example.claim in
    let run fr = truth (expr t fr claim) in
    (example.file, example.loc.line, passes example.file run)
  in
  (* A property reports its seed and cases, and its counterexample when it
     fails (tests.property-verdict). *)
  let property (p : Tast.property) =
    let run () =
      let v = Eval_props.run t (frame_of p.file) p (definition p.closure) in
      (v.failed = None, Some v)
    in
    (p.file, p.loc.line, run)
  in
  (* In order of position: the files in the order of their paths, and source
     order within a file (program.test-order). *)
  let cases =
    List.sort
      (fun (f, l, _) (g, m, _) -> compare (f, l) (g, m))
      (List.map test program.tests
      @ List.map example program.examples
      @ List.map property program.properties)
  in
  let verdict (file, line, run) =
    let passed, property = run () in
    { file; line; passed; property }
  in
  match List.map verdict cases with
  | verdicts -> Ok verdicts
  | exception Fatal reason -> Error reason
  | exception Stack_overflow -> Error "stack overflow"
