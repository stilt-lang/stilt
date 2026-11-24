(** The stages that turn a program's source files into what [stilt-ref] reports.
*)

val parse :
  ?native:bool ->
  Program.source list ->
  (Resolve.parsed list, Diagnostic.t list) result
(** Parses every file. If any file has a syntax error, the result is the syntax
    errors that its parts report, in order of file (errors.syntax-errors and
    errors.part-reports). The files may declare native types only if [native],
    as the standard library's do (views.std-view). *)

val std_snapshot : unit -> string
(** The standard library's trees, parsed without its doc examples, as bytes that
    {!use_std_snapshot} takes. An executable is built with them, so that a
    command doesn't parse the library again, which is most of the work of a
    command on a small program. The bytes hold the trees of the library that
    this executable embeds, and only one built from the same sources reads them.

    @raise Failure
      if the standard library has errors, which a command reading the bytes then
      doesn't check for again. *)

val use_std_snapshot : string -> unit
(** Makes every later command read the standard library's trees from bytes of
    {!std_snapshot}, rather than parse it, but for one that reads the library's
    doc examples (Program.read_std_examples), which parses it. *)

val check :
  ?packages:Program.packages -> Program.source list -> Diagnostic.t list
(** The diagnostics of a program, whose manifests give [packages], sorted by
    file and position: the first syntax error of each part of a file that has
    one, the diagnostics of its manifests (packages.manifest-diagnostics and
    packages.manifest), the errors of name resolution and of its declarations,
    the diagnostics of the three phases of checking its bodies, and the warnings
    about its comments, but for those that a part with a syntax error holds back
    (errors.part-reports).

    @raise Failure if the standard library has errors, which is a bug in it. *)

val analyse :
  ?packages:Program.packages ->
  Program.source list ->
  Diagnostic.t list * (Env.t * Hir.program * Tast.program) option
(** The diagnostics of {!check}, with the program that the evaluator runs: its
    environment, its modules and its elaborated bodies, with each file that has
    a syntax error read a part at a time. [test] runs it only if it has no
    errors. *)

val for_run :
  ?packages:Program.packages ->
  Program.source list ->
  Diagnostic.t list * (Env.t * Hir.program * Tast.program)
(** The diagnostics of {!check}, with the program that [run] runs, errors and
    all (program.programs-with-errors and program.bodies-with-errors): every
    body that has an error replaced by [Broken], which panics with the kind
    [check-error] where it is reached, as is every function that performs an
    effect that a manifest doesn't grant its package
    (packages.running-with-ungranted-effect).

    @raise Failure if the standard library has errors, which is a bug in it. *)

val root_tests : Program.source list -> Tast.program -> Tast.program
(** The program with only the tests, doc examples and properties of the root
    package's own modules, which [test] runs (program.running-tests). *)

val std_tests : Tast.program -> Tast.program
(** The program with only the tests, doc examples and properties of the standard
    library's modules, which are the library's own tests and which [test --std]
    runs (std.examples). *)
