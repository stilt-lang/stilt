(** The module of procedural macros (macros.procedural-declarations and
    macros.procedural-bodies) of a csmith program, from a stream of its own: its
    helpers, which quotes and macros call (macros.linking), and its macros, of
    the kinds of {!Macro_kinds}. *)

val name : int -> string
(** The name of the module of the program made from [seed], [macros_N]. *)

val make : int -> Macro_kinds.t
(** The module of macros of the program made from [seed]. It declares a [Mix], a
    [Listed], a [Twice], a pattern macro and a [Shape], in which
    {!Macro_mistakes} plants mistakes, and some macros of the other kinds, at
    most one of each kind that has no code of its own, and marks each fixed
    function and macro with a number of its own, so that the ten programs that
    [just differential] runs as one declare no equal bodies, which W0302 would
    report (docs.duplicate-bodies). *)

val render :
  ?planted:Code.line list ->
  ?retyped:int * string ->
  Macro_kinds.decl ->
  Code.line list
(** The lines of a macro's declaration, its doc comment, then its signature on
    one line and its body: with [planted] at the top of its body, and the type
    of its parameter [i] written [t] when [retyped] is [(i, t)]. *)

val text :
  ?edit:(Macro_kinds.decl -> Code.line list option) -> Macro_kinds.t -> string
(** The module's text: [use std.meta], its helpers, then its macros, each
    rendered by {!render} or as [edit] gives its lines. *)
