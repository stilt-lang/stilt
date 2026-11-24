(* The texts that macros read (macros.named-files): the places of a text's
   bytes, in a string literal of the use's file or in a file a use names. *)

module M = Macro_values

(* A piece of a literal's value, an escape or one character, with the
   columns of its source, from [first] to before [stop]. *)
type piece = { at : int; bytes : int; first : int; stop : int }

let utf8_length c =
  let n = Char.code c in
  if n < 0x80 then 1 else if n < 0xE0 then 2 else if n < 0xF0 then 3 else 4

(* One piece of [raw] at [i], [col], and its decoded bytes (lexical.string-literals and lexical.escapes), or [None] at the closing quote. *)
let piece raw i =
  let len = String.length raw in
  if i >= len || raw.[i] = '"' then None
  else if raw.[i] <> '\\' then
    let n = min (utf8_length raw.[i]) (len - i) in
    Some (String.sub raw i n, n, 1)
  else
    let simple c = Some (String.make 1 c, 2, 2) in
    match if i + 1 < len then raw.[i + 1] else ' ' with
    | 'n' -> simple '\n'
    | 't' -> simple '\t'
    | 'r' -> simple '\r'
    | '0' -> simple '\000'
    | ('\\' | '"' | '{') as c -> simple c
    | 'u' -> (
        match String.index_from_opt raw i '}' with
        | Some close -> (
            let hex = String.sub raw (i + 3) (max 0 (close - i - 3)) in
            match int_of_string_opt ("0x" ^ hex) with
            | Some v when Uchar.is_valid v ->
                let b = Buffer.create 4 in
                Buffer.add_utf_8_uchar b (Uchar.of_int v);
                let cols = close - i + 1 in
                Some (Buffer.contents b, cols, cols)
            | _ -> None)
        | None -> None)
    | _ -> None

(* The pieces of the literal whose source, from its opening quote at column
   [col], is [raw], if they decode to [value]. *)
let pieces ~col ~value raw =
  let rec go i c at acc =
    match piece raw i with
    | None -> List.rev acc
    | Some (decoded, chars, cols) ->
        let p =
          { at; bytes = String.length decoded; first = c; stop = c + cols }
        in
        go (i + chars) (c + cols) (at + p.bytes) ((decoded, p) :: acc)
  in
  if String.length raw = 0 || raw.[0] <> '"' then None
  else
    let found = go 1 (col + 1) 0 [] in
    if String.concat "" (List.map fst found) = value then
      Some (List.map snd found)
    else None

(* The source of a string literal at [loc], from its opening quote, in the
   text of its file. *)
let raw_literal text (loc : Ast.loc) =
  let lines = String.split_on_char '\n' text in
  match List.nth_opt lines (loc.line - 1) with
  | None -> None
  | Some line ->
      let rec byte i col =
        if col = loc.col || i >= String.length line then i
        else byte (i + utf8_length line.[i]) (col + 1)
      in
      let i = byte 0 1 in
      if i < String.length line then
        Some (String.sub line i (String.length line - i))
      else None

(* macros.tokens-and-code: where the value's bytes from [start] to [stop] are written,
   widened to whole escapes. *)
let literal_span (loc : Ast.loc) named pieces ~start ~stop : M.span =
  let containing b =
    List.find_opt (fun p -> p.at <= b && b < p.at + p.bytes) pieces
  in
  let col_of default b f =
    match containing b with Some p -> f p | None -> default
  in
  let first = col_of (loc.col + 1) start (fun p -> p.first) in
  let last = col_of first (max start (stop - 1)) (fun p -> p.stop) in
  { start = { loc with col = first }; stop = { loc with col = last }; named }

(* The line and column of the byte [b] of [text]. *)
let position text b : Ast.loc =
  let b = min b (String.length text) in
  let line = ref 1 and col = ref 1 and i = ref 0 in
  while !i < b do
    if text.[!i] = '\n' then (
      incr line;
      col := 1;
      incr i)
    else (
      incr col;
      i := !i + utf8_length text.[!i])
  done;
  { line = !line; col = !col }

(* The byte of [text] at a line and a column. *)
let offset text (loc : Ast.loc) =
  let len = String.length text in
  let rec go i line col =
    if i >= len || (line = loc.line && col = loc.col) then i
    else if text.[i] = '\n' then go (i + 1) (line + 1) 1
    else go (i + utf8_length text.[i]) line (col + 1)
  in
  go 0 1 1

let span (t : M.text) ~start ~stop : M.span =
  match t.origin with
  | Literal { at; raw = Some raw; named } -> (
      match pieces ~col:at.col ~value:t.value raw with
      | Some ps -> literal_span at named ps ~start ~stop
      | None -> { (M.point at) with named })
  | Literal { at; raw = None; named } -> { (M.point at) with named }
  | File_text literal ->
      {
        start = position t.value start;
        stop = position t.value stop;
        named = Some literal;
      }

(* Where a position of the text's own lines is written. *)
let place (t : M.text) (loc : Ast.loc) : M.span =
  let b = offset t.value loc in
  match t.origin with
  | File_text literal -> { start = loc; stop = loc; named = Some literal }
  | Literal _ ->
      let s = span t ~start:b ~stop:(b + 1) in
      { s with stop = s.start }
