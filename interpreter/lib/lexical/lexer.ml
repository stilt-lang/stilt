open Lexer_source

type token = Lexer_separators.token = { token : Token.t; line : int; col : int }
type comment = { text : string; doc : bool; line : int; col : int }

type output = {
  tokens : token list;
  written : int;
  comments : comment list;
  error : Diagnostic.t option;
}

(* An interpolation being lexed, with the position of its string's opening
   quote. *)
type interpolation = {
  mutable depth : int;  (** Brackets opened inside it and not yet closed. *)
  quote_line : int;
  quote_col : int;
}

type state = {
  c : cursor;
  mutable raw : token list;  (** Tokens so far, latest first. *)
  mutable comments : comment list;  (** Comments so far, latest first. *)
  mutable interpolations : interpolation list;  (** Innermost first. *)
  mutable dot_end : int;  (** The byte offset just after the latest [.]. *)
  mutable last_end : int * int;
      (** The line and column just after the latest token. *)
}

(* Every token is emitted once the cursor has moved past it, so the cursor
   marks where the token ends. *)
let emit st token ~offset =
  st.raw <- { token; line = st.c.line; col = column st.c offset } :: st.raw;
  st.last_end <- (st.c.line, column st.c st.c.pos)

let unterminated ~quote_line ~quote_col =
  raise
    (Error
       {
         code = Code.e0005;
         line = quote_line;
         col = quote_col;
         message = "unterminated string literal";
       })

(* lexical.identifiers and lexical.case: an identifier, a keyword or the wildcard. *)
let lex_word st =
  let c = st.c in
  let start = c.pos in
  while is_ident_char (peek c 0) do
    advance c 1
  done;
  let text = String.sub c.src start (c.pos - start) in
  let token : Token.t =
    if text = "_" then UNDERSCORE
    else
      match Token.word text with
      | Some keyword -> keyword
      | None -> (
          match Seq.find is_letter (String.to_seq text) with
          | None ->
              fail c ~offset:start Code.e0003
                (Printf.sprintf "`%s` has no letter" text)
          | Some 'A' .. 'Z' -> UIDENT text
          | Some _ -> LIDENT text)
  in
  emit st token ~offset:start

(* lexical.integer-literals: a run of digits in [base], with [_] only between two digits. The
   cursor is on a digit. *)
let digits c base =
  let rec loop () =
    if is_digit base (peek c 0) then (
      advance c 1;
      loop ())
    else if peek c 0 = '_' then
      if is_digit base (peek c 1) then (
        advance c 1;
        loop ())
      else fail c Code.e0004 "`_` must sit between two digits"
  in
  loop ()

(* lexical.integer-literals, lexical.float-literals and lexical.digits-after-dot. [after_dot] tells whether the literal directly follows a
   [.] token, in which case it is a decimal integer. *)
let lex_number st ~after_dot =
  let c = st.c in
  let start = c.pos in
  let no_leading_zero () =
    if peek c 0 = '0' && (is_digit 10 (peek c 1) || peek c 1 = '_') then
      fail c Code.e0004 "a decimal literal can't have a leading zero"
  in
  let is_float =
    if after_dot then (
      no_leading_zero ();
      digits c 10;
      false)
    else
      match (peek c 0, peek c 1) with
      | '0', (('x' | 'o' | 'b') as prefix) ->
          let base = match prefix with 'x' -> 16 | 'o' -> 8 | _ -> 2 in
          advance c 2;
          if not (is_digit base (peek c 0)) then
            fail c Code.e0004 "a base prefix must be followed by a digit";
          digits c base;
          false
      | _ ->
          no_leading_zero ();
          digits c 10;
          let fraction = peek c 0 = '.' && is_digit 10 (peek c 1) in
          if fraction then (
            advance c 1;
            digits c 10);
          let sign = match peek c 1 with '+' | '-' -> 1 | _ -> 0 in
          let exponent =
            (peek c 0 = 'e' || peek c 0 = 'E')
            && is_digit 10 (peek c (1 + sign))
          in
          if exponent then (
            advance c (1 + sign);
            while is_digit 10 (peek c 0) do
              advance c 1
            done);
          fraction || exponent
  in
  if is_ident_char (peek c 0) then
    fail c Code.e0004
      "a number literal can't be followed directly by a letter, a digit or `_`";
  let text =
    String.sub c.src start (c.pos - start)
    |> String.split_on_char '_' |> String.concat ""
  in
  emit st (if is_float then FLOAT text else INT text) ~offset:start

(* lexical.escapes: one escape. The cursor is on the backslash. *)
let lex_escape c buffer =
  let start = c.pos in
  let simple ch =
    Buffer.add_char buffer ch;
    advance c 2
  in
  match peek c 1 with
  | 'n' -> simple '\n'
  | 't' -> simple '\t'
  | 'r' -> simple '\r'
  | '0' -> simple '\000'
  | '\\' -> simple '\\'
  | '"' -> simple '"'
  | '{' -> simple '{'
  | 'u' when peek c 2 = '{' ->
      advance c 3;
      let hex_start = c.pos in
      while is_digit 16 (peek c 0) do
        advance c 1
      done;
      let count = c.pos - hex_start in
      if peek c 0 <> '}' || count < 1 || count > 6 then
        fail c ~offset:start Code.e0006
          "`\\u{…}` takes 1 to 6 hexadecimal digits";
      let value = int_of_string ("0x" ^ String.sub c.src hex_start count) in
      if not (Uchar.is_valid value) then
        fail c ~offset:start Code.e0006
          "`\\u{…}` must name a Unicode scalar value";
      Buffer.add_utf_8_uchar buffer (Uchar.of_int value);
      advance c 1
  | _ -> fail c ~offset:start Code.e0006 "invalid escape"

(* lexical.string-literals: the text of a string literal up to its closing quote or its next
   interpolation. [first] tells whether the text starts the literal. The token
   is placed at [offset]. *)
let lex_string_text st ~first ~offset ~quote_line ~quote_col =
  let c = st.c in
  let buffer = Buffer.create 16 in
  let rec loop () =
    if at_end c || peek c 0 = '\n' then unterminated ~quote_line ~quote_col
    else
      match peek c 0 with
      | '"' ->
          advance c 1;
          let text = Buffer.contents buffer in
          emit st (if first then STRING text else STRING_TAIL text) ~offset
      | '{' when peek c 1 = '{' ->
          (* lexical.escapes *)
          fail c Code.e0006 "a brace is written `\\{`, not `{{`"
      | '{' ->
          advance c 1;
          let text = Buffer.contents buffer in
          emit st (if first then STRING_HEAD text else STRING_MID text) ~offset;
          st.interpolations <-
            { depth = 0; quote_line; quote_col } :: st.interpolations
      | '\\' ->
          lex_escape c buffer;
          loop ()
      | ch ->
          Buffer.add_char buffer ch;
          advance c 1;
          loop ()
  in
  loop ()

let lex_string st =
  let c = st.c in
  let offset = c.pos in
  let quote_line = c.line and quote_col = column c offset in
  advance c 1;
  lex_string_text st ~first:true ~offset ~quote_line ~quote_col

(* Ends the innermost interpolation at the [}] under the cursor, and goes on
   with the rest of its string. *)
let close_interpolation st interpolation =
  let c = st.c in
  let offset = c.pos in
  advance c 1;
  st.interpolations <- List.tl st.interpolations;
  lex_string_text st ~first:false ~offset ~quote_line:interpolation.quote_line
    ~quote_col:interpolation.quote_col

(* lexical.format-specs: the format spec of the innermost interpolation, from the [:] under
   the cursor to the [}] that ends the interpolation. *)
let lex_format st interpolation =
  let c = st.c in
  let offset = c.pos in
  advance c 1;
  let spec_start = c.pos in
  while (not (at_end c)) && peek c 0 <> '}' && peek c 0 <> '\n' do
    advance c 1
  done;
  if peek c 0 <> '}' then
    unterminated ~quote_line:interpolation.quote_line
      ~quote_col:interpolation.quote_col;
  let spec = String.sub c.src spec_start (c.pos - spec_start) in
  if Option.is_none (Format_spec.parse spec) then
    fail c ~offset Code.e0007 (Printf.sprintf "`%s` is not a format spec" spec);
  emit st (FORMAT spec) ~offset;
  close_interpolation st interpolation

(* lexical.line-comments, lexical.doc-comments and lexical.commented-out-code: a comment, recorded for doc examples and for the
   commented-out-code warning. *)
let lex_comment st =
  let c = st.c in
  let offset = c.pos in
  let doc = peek c 2 = '/' in
  let text_start = offset + if doc then 3 else 2 in
  let stop =
    Option.value
      (String.index_from_opt c.src offset '\n')
      ~default:(String.length c.src)
  in
  let text = String.sub c.src text_start (stop - text_start) in
  st.comments <-
    { text; doc; line = c.line; col = column c offset } :: st.comments;
  c.pos <- stop

let starts_with_at c text =
  let length = String.length text in
  c.pos + length <= String.length c.src && String.sub c.src c.pos length = text

(* lexical.tokens: an operator or punctuation token, by maximal munch. *)
let lex_punctuation st =
  let c = st.c in
  match
    List.find_opt (fun (text, _) -> starts_with_at c text) Token.punctuation
  with
  | None ->
      let message =
        match peek c 0 with
        | '`' -> "unexpected backtick"
        | ' ' .. '~' as ch -> Printf.sprintf "unexpected character `%c`" ch
        | _ ->
            let decoded = String.get_utf_8_uchar c.src c.pos in
            Printf.sprintf "unexpected character U+%04X"
              (Uchar.to_int (Uchar.utf_decode_uchar decoded))
      in
      fail c Code.e0002 message
  | Some (text, token) ->
      let offset = c.pos in
      advance c (String.length text);
      (match (st.interpolations, token) with
      | inner :: _, (LPAREN | LBRACKET | LBRACE) ->
          inner.depth <- inner.depth + 1
      | inner :: _, (RPAREN | RBRACKET | RBRACE) when inner.depth > 0 ->
          inner.depth <- inner.depth - 1
      | _ -> ());
      if token = DOT then st.dot_end <- c.pos;
      emit st token ~offset

let rec lex_code st =
  let c = st.c in
  let innermost = List.nth_opt st.interpolations 0 in
  let at_interpolation_level =
    match innermost with Some inner -> inner.depth = 0 | None -> false
  in
  if at_end c then
    match innermost with
    | Some inner ->
        unterminated ~quote_line:inner.quote_line ~quote_col:inner.quote_col
    | None ->
        (* The end of the file sits just after its last token (lexical.terminator-positions). *)
        let line, col = st.last_end in
        st.raw <- { token = EOF; line; col } :: st.raw
  else (
    (match (peek c 0, innermost) with
    | (' ' | '\t'), _ -> advance c 1
    | '\n', Some inner ->
        unterminated ~quote_line:inner.quote_line ~quote_col:inner.quote_col
    | '\n', None -> newline c
    | '/', _ when peek c 1 = '/' -> lex_comment st
    | ('a' .. 'z' | 'A' .. 'Z' | '_'), _ -> lex_word st
    | '0' .. '9', _ -> lex_number st ~after_dot:(st.dot_end = c.pos)
    | '"', _ -> lex_string st
    | ':', Some inner when at_interpolation_level -> lex_format st inner
    | '}', Some inner when at_interpolation_level ->
        close_interpolation st inner
    | _ -> lex_punctuation st);
    lex_code st)

(* The tokens before a lexical error: those the file would have if it ended
   just before the error, so with no separator after the last of them (lexical.separators). Tokens lexed inside an interpolation that the error leaves open
   come after the error's position, and are dropped too. *)
let prefix_before (raw : token list) ~line ~col =
  let before (t : token) = compare (t.line, t.col) (line, col) < 0 in
  let sentinel = { token = Token.EOF; line; col } in
  List.rev (sentinel :: List.filter before raw)
  |> Lexer_separators.insert_separators
  |> Lexer_separators.drop_empty_separators
  |> List.filter (fun (t : token) -> t.token <> EOF)

let written raw =
  List.length (List.filter (fun (t : token) -> t.token <> EOF) raw)

let tokenize ?(line = 1) ?(col = 1) ~file text =
  let diagnostic code line col message =
    Some { Diagnostic.code; file; line; col; message }
  in
  match normalize ~line ~col text with
  | exception Error { code; line; col; message } ->
      {
        tokens = [];
        written = 0;
        comments = [];
        error = diagnostic code line col message;
      }
  | text -> (
      let st =
        {
          c = cursor ~line ~col text;
          raw = [];
          comments = [];
          interpolations = [];
          dot_end = -1;
          last_end = (line, col);
        }
      in
      let comments () = List.rev st.comments in
      match lex_code st with
      | () ->
          let tokens =
            List.rev st.raw |> Lexer_separators.insert_separators
            |> Lexer_separators.drop_empty_separators
          in
          {
            tokens;
            written = written st.raw;
            comments = comments ();
            error = None;
          }
      | exception Error { code; line; col; message } ->
          {
            tokens = prefix_before st.raw ~line ~col;
            written = written st.raw;
            comments = comments ();
            error = diagnostic code line col message;
          })
