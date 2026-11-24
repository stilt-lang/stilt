(** Name resolution: what every name in a program refers to (program.namespaces,
    declarations.name-lookup). *)

type parsed = Program.source * Ast.module_
(** A module's source file, and its syntax tree. *)

val resolve :
  ?packages:Program.packages ->
  ?unreadable:string list ->
  ?host:Procs.host ->
  std:parsed list ->
  parsed list ->
  Hir.program * Diagnostic.t list
(** [resolve ~packages ~unreadable ~std modules] resolves the program made of
    [modules], whose [packages] decide what each module's [use] declarations can
    name (packages.modules-of-dependencies and packages.imports), against the
    standard library [std], whose modules are part of the result. The files
    [unreadable] break lexical.source-text: every path into their modules has
    the error type (errors.root-causes). [host] runs the procedural macros that
    the program's uses name (macros.running), none by default.

    The diagnostics are the errors that name resolution finds, sorted by file
    and position, each where [reference/errors.toml] places it: module names and
    headers, imports and their cycles, names declared twice or that may not be
    used, names that don't resolve or name the wrong kind of thing, visibility,
    [self] and [Self] outside methods and impls, [break] and [continue] outside
    loops, the names of or-patterns, the number of type arguments, and the
    elements of effect rows. No diagnostic is caused by another
    (errors.root-causes).

    @raise Failure if the standard library has errors, which is a bug in it. *)
