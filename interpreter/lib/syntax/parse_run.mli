(** Running the parser over tokens: the driver of the grammar's automaton, which
    reads contextual keywords (lexical.contextual-keywords) and the tokens of
    macros (macros.uses) where the grammar accepts them. *)

type 'a start = Lexing.position -> 'a Parser.MenhirInterpreter.checkpoint
(** An entry point of the grammar, such as [Parser.Incremental.file]. *)

val syntax_error : file:string -> Ast.loc -> string -> Diagnostic.t
(** An E0100 at a position. *)

val run :
  ?macros:bool ->
  file:string ->
  'a start ->
  Lexer.token list ->
  ('a, Diagnostic.t option) result
(** Runs an entry point over tokens, giving its result or its first syntax
    error. [Error None] means the tokens ran out before the parser was done,
    which happens only after a lexical error. A token is read as a [MACRO_TOKEN]
    where the grammar accepts one only if [macros], which is by default whether
    the tokens declare or use a macro. *)

val longest : file:string -> 'a start -> Lexer.token list -> (int * 'a) option
(** The longest prefix of the tokens, given without [EOF], that the entry point
    parses whole, as the number of its tokens and its tree, if any prefix does
    (macros.matching). *)
