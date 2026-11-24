(** Matching a use's tokens against a macro's arms (macros.matching). *)

(** What a fragment matched: one form of its kind, as its tokens, or, for a
    fragment inside a repetition, what it matched in each round. *)
type binding = One of string * Lexer.token list | Many of binding list

type bindings = (string * binding) list

val parse_entry : string -> Lexer.token list -> int option
(** [parse_entry kind tokens] is the number of tokens of the longest prefix of
    [tokens] that is a form of the kind [expr], [pattern], [type] or [block]. *)

val first :
  Ast.macro_arm list ->
  Lexer.token array ->
  (Ast.macro_arm * bindings, Lexer.token * string) result
(** [first arms tokens] is the first arm that matches all of [tokens], a use's
    group between its brackets and then its trailing block, if any, between its
    braces, with what its fragments match. A fragment matches the longest form
    of its kind, and a repetition as many times as it can. When no arm matches,
    it is the furthest token any arm reached and what that arm expected there.
*)
