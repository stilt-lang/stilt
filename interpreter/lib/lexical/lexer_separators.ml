(* The separators that the lexer inserts at the newlines that end statements,
   and drops where they separate nothing. *)

type token = { token : Token.t; line : int; col : int }

(* lexical.terminator-insertion: the tokens after which a newline can end a statement. *)
let ends_statement : Token.t -> bool = function
  | LIDENT _ | UIDENT _ | INT _ | FLOAT _ | STRING _ | STRING_TAIL _ | TRUE
  | FALSE | SELF | SELF_TYPE | RETURN | BREAK | CONTINUE | UNSAFE | RPAREN
  | RBRACKET | RBRACE | QUESTION | GT | GT_GT ->
      true
  | _ -> false

(* lexical.continuation-lines: the tokens that continue the previous line. *)
let continues_line : Token.t -> bool = function
  | DOT | ELSE | CATCH | PIPE -> true
  | _ -> false

(* lexical.contextual-keywords: the limits that a [without] clause takes, the
   contextual keywords among them read from identifiers, and [unsafe]
   (c.without-unsafe). *)
let is_limit (token : Token.t) =
  let token =
    match token with
    | LIDENT text -> Option.value (Token.contextual_keyword text) ~default:token
    | _ -> token
  in
  List.exists (fun (_, limit) -> limit = token) Lexicon.limits

(* lexical.continuation-lines: whether the line that starts at token [i] continues the line
   before it: it begins with one of the tokens above, or with [without]
   followed on its line by a limit, which starts a [without] clause. *)
let continues (tokens : token array) i =
  continues_line tokens.(i).token
  ||
  match tokens.(i).token with
  | LIDENT "without" ->
      i + 1 < Array.length tokens
      && tokens.(i + 1).line = tokens.(i).line
      && is_limit tokens.(i + 1).token
  | _ -> false

(* lexical.terminator-insertion and lexical.inside-brackets: inserts a separator at each newline that ends a statement.
   [tokens] ends with [EOF]. *)
let insert_separators (tokens : token list) =
  let tokens = Array.of_list tokens in
  let out = ref [] in
  let brackets = ref [] in
  let line_first = ref Token.EOF in
  Array.iteri
    (fun i (t : token) ->
      if i = 0 || tokens.(i - 1).line < t.line then line_first := t.token;
      out := t :: !out;
      (match t.token with
      | LPAREN | LBRACKET | LBRACE -> brackets := t.token :: !brackets
      | RPAREN | RBRACKET | RBRACE -> brackets := List.drop 1 !brackets
      | _ -> ());
      if i + 1 < Array.length tokens then
        let next : token = tokens.(i + 1) in
        let inside_parens =
          match !brackets with (LPAREN | LBRACKET) :: _ -> true | _ -> false
        in
        if
          next.line > t.line && ends_statement t.token && (not inside_parens)
          && (not (continues tokens (i + 1)))
          && !line_first <> AT
        then out := { t with token = SEP } :: !out)
    tokens;
  List.rev !out

(* lexical.separators: drops the separators that separate nothing. *)
let drop_empty_separators tokens =
  let rec go kept = function
    | [] -> List.rev kept
    | ({ token = SEP; _ } as separator : token) :: rest ->
        let after_opener =
          match kept with
          | [] | { token = LBRACE | SEP; _ } :: _ -> true
          | _ -> false
        in
        let before_closer =
          match rest with
          | { token = RBRACE | EOF | SEP; _ } :: _ -> true
          | _ -> false
        in
        if after_opener || before_closer then go kept rest
        else go (separator :: kept) rest
    | t :: rest -> go (t :: kept) rest
  in
  go [] tokens
