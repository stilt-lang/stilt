(** The tokens that the parser reads, so that a quote keeps its contents as
    tokens beside its tree (macros.quote and macros.outside-run). *)

val reading : Lexer.token list -> unit
(** Makes [between] read these tokens, which the driver of the grammar is about
    to offer, the [n]th at a position whose [pos_bol] is [n]. *)

val between : Lexing.position -> Lexing.position -> Ast.tree list
(** The tokens strictly between the tokens at two positions, as trees. *)

val trees : Lexer.token list -> Ast.tree list
(** Tokens as trees, each bracket and its match a group. *)
