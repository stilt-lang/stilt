(** The parts of a procedural macro's use, given to its parameters
    (macros.parts). *)

type given =
  | Code of Hir.code * Lexer.token list
      (** A part that parses whole as the form a parameter takes. *)
  | Literal of Procs.literal * bool
      (** A string literal without interpolation, and whether it names a file.
      *)
  | Tokens of Ast.tree list * Ast.loc
      (** Tokens, and the closing bracket after them. *)

val args :
  file:string ->
  Procs.input list ->
  Ast.tree list ->
  (given list, Ast.loc * string) result
(** [args ~file inputs groups] splits the first of [groups], a use's group, into
    parts at its commas outside nested groups, and gives them, with the contents
    of its trailing block if [groups] holds one, to parameters that take
    [inputs]: [Error] at the place of E0227 when an empty part, a part that
    doesn't fit its parameter, a part too many or a part too few breaks
    macros.parts. *)
