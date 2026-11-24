(** The parts of a file with a syntax error, each read alone, and what a part
    that breaks declares (errors.broken-parts), and the extent of each item,
    which tells which body an error lies in (program.errors-in-bodies). *)

(** What an item is. *)
type kind =
  | Fn
  | Const
  | Type
  | Test
  | Impl
  | Trait
  | Syntax
  | Effect
  | Macro
  | Other

type extent = {
  kind : kind;
  first : Ast.loc;  (** Its first token after its doc comments. *)
  last : Ast.loc;  (** Its last token. *)
  name : Ast.loc;
      (** The name of a function, constant, type or trait, and the keyword of a
          test or an impl. *)
  block : Ast.loc option;  (** The [{] that opens an impl's or trait's block. *)
  members : extent list;  (** The members of that block. *)
}
(** The tokens of an item: one part of the file's tokens, cut before each token
    that begins an item and follows a separator outside brackets. *)

val extents : Lexer.output -> extent list
(** The items of a file, from its tokens with doc comments in place
    ({!Syntax.placed}), in order. *)

val item_start : Token.t -> Token.t option -> bool
(** Whether a token, given the token after it, begins a part: [use], [impl],
    [pub], [fn], [type], [trait], [const], [test], [syntax], [effect], [macro],
    a [meta] that [use] follows, or a doc comment. *)

val cut :
  starts:(Token.t -> Token.t option -> bool) ->
  Lexer.token array ->
  int ->
  int ->
  (int * int) list
(** [cut ~starts ts lo hi] cuts the tokens from [lo] to [hi] into parts, as
    ranges: before each token that [starts] accepts, given the token after it,
    and that follows a separator outside brackets, which is in neither part. *)

val extent : Lexer.token array -> int * int -> extent
(** The extent of the item that the tokens of a range make. *)

val code : Lexer.output -> Lexer.token array * int
(** The tokens of a lexer's output, and where its code ends: before its [EOF],
    or at its end after a lexical error. *)

type reader
(** The tokens of a text read a part at a time, and the functions, constants and
    tests that its parts that break declare with an error. *)

val reader : file:string -> Lexer.output -> reader
(** A reader of a text, from its tokens with doc comments in place. *)

val tokens : reader -> Lexer.token array

val broken : reader -> Ast.loc list
(** The names of the functions and constants, and the [test] keywords of the
    tests, that the parts that broke so far declare with an error. *)

(** A part parsed alone: what it declares, or where it breaks, and whether that
    is at the lexical error that ends it. *)
type parsed = Parsed of Ast.module_ | Breaks of Diagnostic.t * bool

val parse_alone : reader -> int * int -> parsed
(** Parses the part of a range alone, as a file (errors.parts). *)

val declare_broken : reader -> int * int -> Diagnostic.t -> Ast.item list
(** The items that the part of a range declares when it breaks at the error, by
    the table of errors.declarations-with-errors. *)

val declared_at : reader -> int -> int -> Lexer.token
(** The first token of the part of a range after its doc comments, or its first
    token when it holds nothing else. *)
