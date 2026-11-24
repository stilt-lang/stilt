(* The source text, as the lexer reads it: a cursor over its bytes, the errors
   at its positions, the classes of its characters, and the check of its
   encoding. *)

exception Error of { code : Code.t; line : int; col : int; message : string }

(* A position in the source text: a byte offset, and the line it falls on. *)
type cursor = {
  src : string;
  mutable pos : int;
  mutable line : int;
  mutable line_start : int;  (** Byte offset of the current line's start. *)
  first_line : int;
  first_col : int;  (** The column of the text's first character. *)
  mutable counted : int * int;
      (** The column of a byte of the current line that [column] counted to, so
          that the next count on the line starts there. *)
}

let cursor ~line ~col src =
  {
    src;
    pos = 0;
    line;
    line_start = 0;
    first_line = line;
    first_col = col;
    counted = (0, col);
  }

let at_end c = c.pos >= String.length c.src

(* The byte [k] places ahead, or NUL past the end. Callers that must tell a NUL
   in the text from the end check [at_end]. *)
let peek c k =
  let i = c.pos + k in
  if i < String.length c.src then c.src.[i] else '\000'

let advance c n = c.pos <- c.pos + n

(* Moves past a newline. *)
let newline c =
  advance c 1;
  c.line <- c.line + 1;
  c.line_start <- c.pos

(* The column of byte [offset] on the current line, in Unicode scalar values.
   Tokens are measured in order, so each count goes on from the last one on the
   line, and a long line costs its length rather than its length for each of
   its tokens. *)
let column c offset =
  let from, col =
    match c.counted with
    | at, col when at >= c.line_start && at <= offset -> (at, col)
    | _ -> (c.line_start, if c.line = c.first_line then c.first_col else 1)
  in
  let col = ref col in
  for i = from to offset - 1 do
    if Char.code c.src.[i] land 0xC0 <> 0x80 then incr col
  done;
  c.counted <- (offset, !col);
  !col

let fail ?offset c code message =
  let offset = Option.value offset ~default:c.pos in
  raise (Error { code; line = c.line; col = column c offset; message })

let is_letter = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false
let is_ident_char ch = is_letter ch || ch = '_' || ('0' <= ch && ch <= '9')

let is_digit base ch =
  match (base, ch) with
  | 2, ('0' | '1') | 8, '0' .. '7' | 10, '0' .. '9' -> true
  | 16, ('0' .. '9' | 'a' .. 'f' | 'A' .. 'F') -> true
  | _ -> false

(* lexical.source-text: the text must be UTF-8 with no byte-order mark, and a carriage
   return may only precede a newline. Returns the text with each "\r\n"
   replaced by "\n". *)
let normalize ~line ~col text =
  let c = cursor ~line ~col text in
  if String.starts_with ~prefix:"\xEF\xBB\xBF" text then
    fail c Code.e0001 "a source file can't begin with a byte-order mark";
  let out = Buffer.create (String.length text) in
  while not (at_end c) do
    let decoded = String.get_utf_8_uchar text c.pos in
    if not (Uchar.utf_decode_is_valid decoded) then
      fail c Code.e0001 "the file isn't valid UTF-8";
    match text.[c.pos] with
    | '\r' when peek c 1 = '\n' -> advance c 1
    | '\r' ->
        fail c Code.e0001 "a carriage return must be followed by a newline"
    | '\n' ->
        Buffer.add_char out '\n';
        newline c
    | _ ->
        let length = Uchar.utf_decode_length decoded in
        Buffer.add_string out (String.sub text c.pos length);
        advance c length
  done;
  Buffer.contents out
