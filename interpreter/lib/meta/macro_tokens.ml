(* The tokens of macros: atoms and token trees as tokens. *)

open Ast

let stands_for_itself : Token.t -> bool = function
  | LPAREN | RPAREN | LBRACKET | RBRACKET | LBRACE | RBRACE | DOLLAR | SEP | EOF
  | DOC _ | MISPLACED_DOC | MACRO_TOKEN _ ->
      false
  | _ -> true

let atom : Token.t -> atom = function
  | LIDENT s -> A_lower s
  | UIDENT s -> A_upper s
  | INT s -> A_int s
  | FLOAT s -> A_float s
  | STRING s -> A_string s
  | STRING_HEAD s -> A_string_head s
  | STRING_MID s -> A_string_mid s
  | STRING_TAIL s -> A_string_tail s
  | FORMAT s -> A_format s
  | SEP -> A_sep
  | t ->
      let text = Token.to_string t in
      if List.mem_assoc text Token.punctuation then A_punct text
      else A_word text

let token : atom -> Token.t = function
  | A_lower s -> LIDENT s
  | A_upper s -> UIDENT s
  | A_word "_" -> UNDERSCORE
  | A_word w -> ( match Token.word w with Some t -> t | None -> LIDENT w)
  | A_int s -> INT s
  | A_float s -> FLOAT s
  | A_string s -> STRING s
  | A_string_head s -> STRING_HEAD s
  | A_string_mid s -> STRING_MID s
  | A_string_tail s -> STRING_TAIL s
  | A_format s -> FORMAT s
  | A_punct p -> List.assoc p Token.punctuation
  | A_sep -> SEP

let opener : delim -> Token.t = function
  | Paren -> LPAREN
  | Bracket -> LBRACKET
  | Brace -> LBRACE

let closer : delim -> Token.t = function
  | Paren -> RPAREN
  | Bracket -> RBRACKET
  | Brace -> RBRACE

let at (loc : loc) token = { Lexer.token; line = loc.line; col = loc.col }
let loc (t : Lexer.token) = { line = t.line; col = t.col }

let rec flatten trees = List.concat_map flatten_tree trees

and flatten_tree (t : tree) =
  match t.desc with
  | Token a -> [ at t.loc (token a) ]
  | Group (d, ts, close) ->
      (at t.loc (opener d) :: flatten ts) @ [ at close (closer d) ]
  | Fragment _ | Repeat _ -> invalid_arg "Macro_tokens.flatten"

let describe : Token.t -> string = function
  | SEP -> "`;`"
  | EOF -> "the end of the group"
  | LIDENT s | UIDENT s -> Printf.sprintf "`%s`" (Macro_marks.base s)
  | INT s | FLOAT s -> Printf.sprintf "the number `%s`" s
  | STRING _ | STRING_HEAD _ -> "a string"
  | STRING_MID _ | STRING_TAIL _ | FORMAT _ -> "the rest of a string"
  | t -> Printf.sprintf "`%s`" (Token.to_string t)
