(* The values that macros read and write (macros.tokens-and-code): the native types
   of [std.meta] that only a macro's run makes, but for a quote's code and a
   fresh name (macros.outside-run). *)

(* A place in the use's file, from [start] to [stop], or in a file that a
   use names, whose literal is at [named] (macros.named-files). *)
type span = { start : Ast.loc; stop : Ast.loc; named : Ast.loc option }

(* Where a text's value is written: a string literal at [at], whose source
   from its opening quote is [raw] when it is known, in the use's file or in
   the file that the literal at [named] names, or a file that the literal at
   [at] names. *)
type origin =
  | Literal of { at : Ast.loc; raw : string option; named : Ast.loc option }
  | File_text of Ast.loc

type text = { value : string; origin : origin }

type token = {
  lexed : Lexer.token list;
      (* The token as lexed, where it is written, or all the tokens of a group
         or of an interpolated string. *)
  span : span;
  kind : kind;
}

and kind =
  | Word of string
  | Number of string
  | String_lit of text
  | Interpolated
  | Punct of string
  | Group of Ast.delim * token list * span
(* Its brackets, its tokens and its closing bracket's span. *)

(* An identifier: the user's, as written, with the marks of an expansion it
   came through, or a fresh one, numbered as an expansion is (macros.quote-hygiene). *)
type name = { written : string; at : span; fresh : int option }

(* Code, its tokens as the expansion holds them (macros.splices and macros.raised-errors). *)
type code = { tokens : Lexer.token list; at : span; form : Hir.code }
type error = { at : span; message : string; notes : (span * string) list }

type t =
  | Span of span
  | Token of token
  | Text of text
  | Name of name
  | Code of code
  | Error of error

let point loc = { start = loc; stop = loc; named = None }

(* The place a diagnostic is reported at for a span: a span in a named file
   is placed at the literal that names it (macros.raised-errors). *)
let placed s = match s.named with Some literal -> literal | None -> s.start

(* A name's text, without the marks of an expansion. *)
let text (n : name) = Macro_marks.base n.written
