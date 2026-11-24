(* Tokens as a macro reads them (macros.tokens-and-code): the tokens of lexical.tokens, as
   written, each group one token holding its own, each interpolated string
   one token, without the separators that newlines insert, and without doc
   comments. *)

module M = Macro_values

(* Where the tokens are written: a token's span, a string literal's text, and
   the text where they are written, when it is known, from which a number's
   text comes as written. *)
type source = {
  span : Lexer.token -> M.span;
  text : Lexer.token -> M.text;
  written : string option;
}

(* A number as written, its [_] kept, as the lexer gives it without them:
   the source from the token's place on, its characters those of [digits]
   with each [_] between them kept (macros.tokens-and-code). *)
let number src (t : Lexer.token) digits =
  match src.written with
  | None -> digits
  | Some text ->
      let start = Macro_texts.offset text { line = t.line; col = t.col } in
      let n = String.length text and len = String.length digits in
      let rec go i j =
        if j >= len then i
        else if i < n && text.[i] = '_' then go (i + 1) j
        else if i < n && text.[i] = digits.[j] then go (i + 1) (j + 1)
        else -1
      in
      let stop = go start 0 in
      if stop < 0 then digits else String.sub text start (stop - start)

(* A separator that a newline inserted, at the token before it, rather than
   a written [;]. An inserted one always follows a token (lexical.terminator-positions), so
   a separator that comes first, as in [(; x)], is written. *)
let inserted (prev : Lexer.token option) (t : Lexer.token) =
  t.token = SEP
  &&
  match prev with
  | Some p -> p.line = t.line && p.col = t.col
  | None -> false

let is_word text =
  text <> "" && match text.[0] with 'a' .. 'z' -> true | _ -> false

let kind src (t : Lexer.token) : M.kind =
  match t.token with
  | LIDENT s | UIDENT s -> Word (Macro_marks.base s)
  | UNDERSCORE -> Word "_"
  | INT s | FLOAT s -> Number (number src t s)
  | STRING _ -> String_lit (src.text t)
  | SEP -> Punct ";"
  | token ->
      let text = Token.to_string token in
      if is_word text then Word text else Punct text

let delim : Token.t -> Ast.delim = function
  | LPAREN -> Paren
  | LBRACKET -> Bracket
  | _ -> Brace

(* The tokens from an opening bracket, or the head of an interpolated
   string, to what closes it, and the tokens after. *)
let slice (tokens : Lexer.token list) =
  let step (t : Lexer.token) =
    match t.token with
    | LPAREN | LBRACKET | LBRACE | STRING_HEAD _ -> 1
    | RPAREN | RBRACKET | RBRACE | STRING_TAIL _ -> -1
    | _ -> 0
  in
  let rec go depth acc = function
    | [] -> (List.rev acc, [])
    | t :: rest ->
        let depth = depth + step t in
        if depth = 0 then (List.rev (t :: acc), rest)
        else go depth (t :: acc) rest
  in
  go 0 [] tokens

let rec last = function
  | [ x ] -> x
  | _ :: xs -> last xs
  | [] -> invalid_arg "Macro_lexed.last"

let rec tokens src (lexed : Lexer.token list) : M.token list =
  let rec go prev acc = function
    | [] -> List.rev acc
    | (t : Lexer.token) :: _ when t.token = EOF -> List.rev acc
    | t :: rest when inserted prev t -> go (Some t) acc rest
    | t :: rest -> (
        match t.token with
        | LPAREN | LBRACKET | LBRACE | STRING_HEAD _ ->
            let part, rest = slice (t :: rest) in
            go (Some (last part)) (compound src part :: acc) rest
        | _ ->
            let one =
              { M.lexed = [ t ]; span = src.span t; kind = kind src t }
            in
            go (Some t) (one :: acc) rest)
  in
  go None [] lexed

(* A group, which holds its tokens, or an interpolated string. *)
and compound src (part : Lexer.token list) : M.token =
  let first = List.hd part and close = last part in
  let span : M.span = { (src.span first) with stop = (src.span close).start } in
  let kind : M.kind =
    match first.token with
    | STRING_HEAD _ -> Interpolated
    | opener ->
        let inner =
          List.filteri (fun i _ -> i > 0 && i < List.length part - 1) part
        in
        Group (delim opener, tokens src inner, src.span close)
  in
  { lexed = part; span; kind }

(* The tokens of a token as code: where they are written, at the literal
   that names the file they are in (macros.errors-in-expansions), or, lexed from a
   literal's value, at the token's place in the literal. *)
let placed (t : M.token) =
  let at (l : Ast.loc) =
    List.map
      (fun (x : Lexer.token) -> { x with line = l.line; col = l.col })
      t.lexed
  in
  match (t.span.named, t.lexed) with
  | Some l, _ -> at l
  | None, x :: _ when (x.line, x.col) <> (t.span.start.line, t.span.start.col)
    ->
      at t.span.start
  | None, _ -> t.lexed

(* The tokens as code, with no terminator at their top level, as inside
   [( … )] (macros.part-forms; lexical.inside-brackets): a group keeps its own, which
   lexical.terminator-insertion inserts inside a [{ … }]. *)
let code (items : M.token list) = List.concat_map placed items
