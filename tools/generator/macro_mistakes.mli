(** Mistakes in the procedural macros (macros.failed-uses and
    macros.errors-in-expansions) of a csmith program, each annotated with the
    one diagnostic the Reference requires for it, on the line where it starts.
*)

(** Where a mistake goes. *)
type place =
  | Use of string list
      (** Lines at the top of a function of the program, which name nothing but
          what they declare and the module's macros; the last is annotated. *)
  | Module of (Macro_kinds.decl -> Code.line list option)
      (** The lines of each macro of the module that changes, its mistake
          annotated: a module of macros with an error expands no use and reports
          nothing where its macros are used (macros.expansion-order). *)

val plant : Macro_kinds.t -> int -> place
(** The mistake of [kind] in a program whose module of macros is [m]: a part too
    many or too few (E0227, macros.parts), an expression macro where a pattern
    stands or a type macro where an expression does (E0223,
    macros.procedural-uses), a cursor raising at a part's token (E0225,
    macros.cursor and macros.raised-errors), a parameter whose type isn't one of
    [std.meta]'s input types (E0228, macros.procedural-declarations), a quote
    naming a local of the macro's code without [$] (E0211,
    macros.quote-hygiene), or a macro used in its own module (E0212,
    macros.meta-use). The kinds take turns as [kind] grows, and [kind] varies
    the macro and the type where a mistake has a choice. *)
