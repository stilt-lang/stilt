(** The checks of a macro's patterns and templates where it is declared
    (macros.patterns, macros.pattern-checks and macros.templates). *)

type error = { code : Code.t; loc : Ast.loc; message : string }

val kinds : string list
(** The kinds of fragments: [expr], [block], [pattern], [type], [name] and
    [Name] (macros.patterns). *)

val fragments : Ast.tree -> (string * string) list
(** The fragments of a pattern, with their kinds, in order, a repetition's among
    them. *)

val names : Ast.tree list -> string list
(** The fragments that trees of a template or a pattern name, without repeating
    any. *)

val check_arm : Ast.macro_arm -> error list
(** The E0220s of an arm's pattern: a fragment named twice or of no kind, an
    [expr], [pattern] or [type] fragment followed by what it could read on into,
    and a repetition without a fragment (macros.pattern-checks). Then, if there
    are none, the E0221s of its template: a fragment the pattern doesn't bind,
    or binds inside another number of repetitions, and a repetition whose
    fragments come from two repetitions of the pattern, or that names none
    (macros.templates). *)
