(* A source file read whole, or a part at a time if it has a syntax error
   (errors.syntax-errors and errors.parts), with the warnings about its comments, the syntax errors
   that its parts report and the text in which each holds back the others, the
   extents of its items, and the names of what its parts that break declare
   with an error. *)
type read = {
  source : Program.source;
  tree : Ast.module_;
  comments : Diagnostic.t list;
  reports : Syntax_recovery.report list;
  extents : Syntax_parts.extent list Lazy.t;
  broken : Ast.loc list;
  unreadable : bool;
}

let read ?native (src : Program.source) =
  let file = src.file in
  match Syntax.parse ?native ~file src.text with
  | Ok (tree, comments) ->
      {
        source = src;
        tree;
        comments;
        reports = [];
        extents = lazy (Syntax_parts.extents (Syntax.placed ~file src.text));
        broken = [];
        unreadable = false;
      }
  | Error _ ->
      let r = Syntax_recovery.read ~file src.text in
      {
        source = src;
        tree = r.module_;
        comments = Syntax.comment_warnings ~file r.comments;
        reports = r.reports;
        extents = Lazy.from_val r.extents;
        broken = r.broken;
        unreadable = r.unreadable;
      }

let syntax_errors reads =
  List.concat_map
    (fun r -> List.map (fun (p : Syntax_recovery.report) -> p.error) r.reports)
    reads

let parse ?native sources =
  let reads = List.map (read ?native) sources in
  match syntax_errors reads with
  | [] -> Ok (List.map (fun r -> (r.source, r.tree)) reads)
  | errors -> Error errors

let parse_std () =
  match parse ~native:true (Program.std ()) with
  | Ok modules -> modules
  | Error errors ->
      failwith
        ("the standard library has syntax errors: "
        ^ String.concat "; " (List.map Diagnostic.to_string errors))

(* The standard library's trees, and whether its bodies were checked when they
   were parsed. *)
type std = { modules : Resolve.parsed list; checked : bool }

(* The standard library's trees, without its doc examples, as an executable
   was built with them, if it was. *)
let snapshot = ref None
let use_std_snapshot data = snapshot := Some data

(* Parsing the library is most of the work of a command on a small program,
   so a command reads the trees it was built with, whose bodies were checked
   then, but for [test --std], which checks the doc examples that the trees
   leave out. [Marshal] reads only what [std_snapshot] wrote: the build links
   the snapshot into this executable, from a run of the same code, so the
   bytes have the type they are read at, and nothing reads them from outside. *)
let std =
  lazy
    (match !snapshot with
    | Some data when not (Program.reads_std_examples ()) ->
        {
          modules = (Marshal.from_string data 0 : Resolve.parsed list);
          checked = true;
        }
    | _ -> { modules = parse_std (); checked = false })

let by_position (a : Diagnostic.t) (b : Diagnostic.t) =
  compare (a.file, a.line, a.col, a.code) (b.file, b.line, b.col, b.code)

(* Resolves and checks the modules that were read, giving their diagnostics
   and the program that the evaluator runs. *)
let pipeline ?(std = Lazy.force std) ?(host = Procs.none) packages reads =
  let unreadable =
    List.filter_map
      (fun r -> if r.unreadable then Some r.source.file else None)
      reads
  in
  let program, resolution =
    Resolve.resolve ~packages ~unreadable ~host ~std:std.modules
      (List.map (fun r -> (r.source, r.tree)) reads)
  in
  (* views.viewable-types and views.view-types: the views that declarations write, whose types
     then have the error type. *)
  let views = Views_types.declarations program in
  let program = Views_types.erase program in
  let env, declarations = Env.build program in
  let declarations = declarations @ views in
  let elaborated, bodies = Check.check env program in
  let texts = List.map (fun r -> (r.source.file, r.source.text)) reads in
  let text file = Option.value (List.assoc_opt file texts) ~default:"" in
  let later =
    Phases.check ~std:(not std.checked) ~text env program elaborated
  in
  let trees = List.map (fun r -> (r.source, r.tree)) reads in
  let exports =
    Check_exports.check packages trees @ Check_foreign_decls.check trees program
  in
  ( resolution @ declarations @ bodies @ exports @ later,
    (env, program, elaborated) )

(* The library's trees, once a program of no module of its own has checked
   all their bodies without an error. *)
let std_snapshot () =
  let std = { modules = parse_std (); checked = false } in
  match
    List.filter Diagnostic.is_error (fst (pipeline ~std Program.single []))
  with
  | [] -> Marshal.to_string std.modules []
  | errors ->
      failwith
        ("the standard library has errors: "
        ^ String.concat "; " (List.map Diagnostic.to_string errors))

(* Whether a part with a syntax error holds back [d]: one whose text holds its
   primary span, but for E0200, which is about the file's name. *)
let held_back reads (d : Diagnostic.t) =
  let within (p : Syntax_recovery.report) =
    let at = (d.line, d.col) in
    (p.from.line, p.from.col) <= at
    && Option.fold ~none:true
         ~some:(fun (u : Ast.loc) -> at < (u.line, u.col))
         p.until
  in
  d.code <> Code.e0200
  && List.exists
       (fun r -> r.source.file = d.file && List.exists within r.reports)
       reads

(* The package of each module of the program, by its name. *)
let package_of_module sources (hir : Hir.program) =
  let by_file = Hashtbl.create 16 in
  List.iter
    (fun (src : Program.source) -> Hashtbl.replace by_file src.file src.package)
    sources;
  let by_name = Hashtbl.create 16 in
  List.iter
    (fun (m : Hir.module_) ->
      if not m.std then
        Option.iter
          (Hashtbl.replace by_name m.name)
          (Hashtbl.find_opt by_file m.file))
    hir;
  Hashtbl.find_opt by_name

(* The program with every body that has an error [Broken], as program.bodies-with-errors decides it. [errors] are all of the program's errors, reported or held
   back. *)
let marked reads errors (env, hir, elaborated) =
  Check_broken.mark env hir elaborated ~errors
    ~extents:(List.map (fun r -> (r.source.file, Lazy.force r.extents)) reads)
    ~recovered:
      (List.concat_map
         (fun r -> List.map (fun l -> (r.source.file, l)) r.broken)
         reads)

(* What the program's packages do: the program [marked], and which of its
   functions perform [io] (packages.own-effects). *)
let grants reads errors (env, hir, elaborated) =
  let program = marked reads errors (env, hir, elaborated) in
  let sources = List.map (fun r -> r.source) reads in
  (program, Grants.find env hir program (package_of_module sources hir))

(* macros.expansion-order and macros.running: a procedural macro's module, checked with the
   modules it imports as a program of its own, which calls its macros. Its
   macros are usable unless the module has an error. *)
type proc_module = { hir : Hir.program; call : Macro_run.call; usable : bool }

let module_of r = String.concat "." r.source.module_path

(* The modules that [home] imports, with [use] and [meta use], and theirs,
   which [find] gives by the package of the module that names them. *)
let closure ~find reads home =
  let imports r =
    List.filter_map
      (fun (i : Ast.item) ->
        match i.desc with
        | Use p | Meta_use p ->
            find r.source.package
              (String.concat "." (List.map (fun (n : Ast.name) -> n.desc) p))
        | _ -> None)
      r.tree.items
  in
  let rec go seen = function
    | [] -> seen
    | m :: rest when List.mem m seen -> go seen rest
    | m :: rest -> (
        match List.find_opt (fun r -> module_of r = m) reads with
        | Some r -> go (m :: seen) (imports r @ rest)
        | None -> go seen rest)
  in
  go [] [ home ]

let checked_module host packages reads home =
  let found, checked = pipeline ~host packages reads in
  let errors = List.filter Diagnostic.is_error found in
  let ill r =
    module_of r = home
    && (r.reports <> []
       || List.exists (fun (d : Diagnostic.t) -> d.file = r.source.file) errors
       )
  in
  let env, hir, _ = checked in
  let program = marked reads errors checked in
  {
    hir;
    call = Eval.caller env hir program;
    usable = not (List.exists ill reads);
  }

let host packages reads =
  let table = Hashtbl.create 4 and self = ref Procs.none in
  let proc_module ~find home =
    match Hashtbl.find_opt table home with
    | Some m -> m
    | None ->
        (* A module whose check reaches itself through a cycle, which E0206
           reports, makes no macro usable there. *)
        Hashtbl.replace table home None;
        let names = closure ~find reads home in
        let sub = List.filter (fun r -> List.mem (module_of r) names) reads in
        let m =
          if List.mem home names then
            Some (checked_module !self packages sub home)
          else None
        in
        Hashtbl.replace table home m;
        m
  in
  let source file =
    Option.map
      (fun r -> r.source.text)
      (List.find_opt (fun r -> r.source.file = file) reads)
  in
  let state ~find home name =
    match proc_module ~find home with
    | Some m when m.usable -> Macro_host.state m.hir home name
    | _ -> Procs.Unusable
  in
  let run (use : Procs.use) =
    match Hashtbl.find_opt table use.home with
    | Some (Some m) ->
        Macro_run.run m.call
          ~named:(Macro_host.named m.hir use.home)
          ~source:(source use.file) use
    | _ -> Procs.Stopped "its module isn't checked"
  in
  let read ~file path =
    match List.find_opt (fun r -> r.source.file = file) reads with
    | Some r -> Macro_files.read ~dir:(Macro_files.dir packages r.source) path
    | None -> Error "the file of this use isn't the program's"
  in
  self := { state; run; read; source };
  !self

(* The diagnostics of a program, and all its errors, reported or held back,
   with what was read and checked. *)
let analysed packages sources =
  let reads = List.map read sources in
  let found, checked = pipeline ~host:(host packages reads) packages reads in
  let errors = List.filter Diagnostic.is_error found in
  let _, granted = grants reads errors checked in
  let manifests = packages.problems @ Grants.diagnostics granted packages in
  let kept =
    List.filter
      (fun d -> not (held_back reads d))
      (found @ List.concat_map (fun r -> r.comments) reads)
  in
  ( List.sort by_position (syntax_errors reads @ kept @ manifests),
    errors,
    (reads, checked) )

let analyse ?(packages = Program.single) sources =
  let diagnostics, _, (_, checked) = analysed packages sources in
  (diagnostics, Some checked)

let check ?packages sources = fst (analyse ?packages sources)

let for_run ?(packages = Program.single) sources =
  let diagnostics, errors, (reads, checked) = analysed packages sources in
  let env, hir, _ = checked in
  if not (List.exists Diagnostic.is_error diagnostics) then
    (* No body of a program without errors meets the error type. *)
    (diagnostics, checked)
  else
    let program, found = grants reads errors checked in
    (diagnostics, (env, hir, Grants.break found packages program))

(* The program, with only the tests, doc examples and properties of the root
   package's own modules, which [test] runs (program.running-tests). *)
let root_tests sources (program : Tast.program) =
  let root file =
    List.exists
      (fun (src : Program.source) -> src.file = file && src.package = 0)
      sources
  in
  {
    program with
    tests = List.filter (fun (t : Tast.test) -> root t.file) program.tests;
    examples =
      List.filter (fun (e : Tast.example) -> root e.file) program.examples;
    properties =
      List.filter (fun (p : Tast.property) -> root p.file) program.properties;
  }

(* The standard library's files are those under [std/] (Program.std). *)
let std_tests (program : Tast.program) =
  let std file = String.starts_with ~prefix:"std/" file in
  {
    program with
    tests = List.filter (fun (t : Tast.test) -> std t.file) program.tests;
    examples =
      List.filter (fun (e : Tast.example) -> std e.file) program.examples;
    properties =
      List.filter (fun (p : Tast.property) -> std p.file) program.properties;
  }
