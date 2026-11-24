(** Csmith-style programs: well-typed, terminating [core] programs that print
    what they compute, and have tests, for differential testing.

    Generation is type-directed, so a program checks by construction. It
    terminates by construction too: every loop runs a bounded number of times, a
    function calls only the functions declared before it, and the work of each
    body is kept under a budget. Operands that could make an operator panic are
    masked so that they can't. *)

val type_decl : Context.program -> pub:bool -> Code.line list
(** A record or variant type, whose fields and payloads use only the types
    declared before it, so that no type contains itself. The program declares
    it. *)

val function_ :
  Context.program -> budget:int -> pub:bool -> Context.fn_sig * Code.line list
(** A function, which calls only the functions declared before it and whose
    body's work stays within [budget]. The program declares it. *)

val main : ?pub:bool -> ?par:int -> Context.program -> Code.line list
(** [main], which computes some values of its own, drawn once as the scale
    mode's port to Stilt draws them, then calls every function and prints what
    each returns, raises, or leaves in its [inout] arguments, then, given the
    seed [par], makes that seed's calls of [std.par] ({!Csmith_par.calls});
    [pub] when [pub] is. It uses no array. *)

val items : ?macros:Macro_kinds.t -> int -> Code.line list list
(** The items of a program made from [seed]: its types, then its functions, then
    [main], which calls nothing of [std.par]. Given the seed's module of macros,
    [main] and the functions after it use its macros, as in {!files}, without
    the [meta use] that imports them. *)

val program : ?macros:bool -> int -> string
(** The text of the program made from [seed], as {!files} makes it, without its
    module of macros; with [~macros:false], as it would be if it used none, its
    lines then those of the program with macros but for the [meta use] that
    imports them and the lines and functions that use them. *)

val files : int -> (string * string) list
(** The files of the program made from [seed], each with its path: its items,
    then one to three tests, which doc examples and a property may document,
    generated from a stream of their own so that the items are those of
    [items seed]. A test, an example or a property may fail. Three in ten
    programs also name [std.array] and use arrays at the end of their [main]
    ({!Csmith_arrays}), three in ten name [std.meta] and reflect on values after
    them ({!Csmith_reflect}), three in ten import a module of procedural macros
    with [meta use] and use them after that ({!Csmith_macros}), three in ten
    declare effects and handle them after that ({!Csmith_effects}), and half the
    programs name [std.par] and end their [main] with calls of it
    ({!Csmith_par}); one in five name [std.view] and view the fields of records
    ({!Csmith_views}), one in five name [std.text] and use text beyond ASCII
    ({!Csmith_text}), and three in a hundred recurse tens of thousands of calls
    deep and build lists of 10^5 or 10^6 elements ({!Csmith_deep}), at the end
    of [main]; each from a stream of its own, so that the rest of the program is
    the same; such a [main] may, rarely, end with a panic. A program without
    macros is the one file [seed_N.lt]; one with macros, since a macro is used
    only from another module (macros.meta-use), is the directory program
    [seed_N], whose [main.lt] is the program and [macros_N.lt] its module of
    macros. *)

val module_files : int -> (string * string) list
(** The program made from [seed], as {!files} makes it, but with its [main]
    public, as the module [seed_N.lt] of a bundle whose own [main] calls it,
    followed by its module of macros, [macros_N.lt], if it has one. *)

val bundle : int list -> string
(** The [main.lt] of a bundle of the modules [seed_N] that {!module_files} makes
    from [seeds]: it prints each module's name, then calls its [main], in turn.
    A generated program panics only in its last call of [std.par], and rarely,
    so each module's [main] runs unless one before it panics, and a bundle is
    checked, run and tested as its programs would be one at a time, with the
    work that every program costs alike, such as starting a process, done once
    for all of them. *)
