(* The four kinds of string of TOML 1.0: basic and literal, on one line or on
   several. *)

open Toml_scan

let utf8 b code =
  if code < 0x80 then Buffer.add_char b (Char.chr code)
  else Buffer.add_utf_8_uchar b (Uchar.of_int code)

let hex_digit ch = digit_of 16 ch

(* An escape, after its backslash. *)
let escape c b =
  match peek c with
  | None -> fail c "the string isn't closed"
  | Some ch -> (
      let simple =
        match ch with
        | 'b' -> Some '\b'
        | 't' -> Some '\t'
        | 'n' -> Some '\n'
        | 'f' -> Some '\012'
        | 'r' -> Some '\r'
        | '"' -> Some '"'
        | '\\' -> Some '\\'
        | 'u' | 'U' -> None
        | _ -> fail c "no such escape"
      in
      bump c;
      match simple with
      | Some s -> Buffer.add_char b s
      | None ->
          let n = if ch = 'u' then 4 else 8 in
          let v = ref 0 in
          for i = 1 to n do
            match Option.bind (peek c) hex_digit with
            | None -> fail c "expected a hexadecimal digit"
            | Some d ->
                v := (!v * 16) + d;
                if i = n && not (Uchar.is_valid !v) then
                  fail c "the escape names no Unicode scalar value";
                bump c
          done;
          utf8 b !v)

let single_line c quote =
  let b = Buffer.create 16 in
  let rec go () =
    match peek c with
    | Some ch when ch = quote ->
        bump c;
        Buffer.contents b
    | Some '\\' when quote = '"' ->
        bump c;
        escape c b;
        go ()
    | Some ch when is_control ch && ch <> '\t' ->
        fail c "the string isn't closed on its line"
    | Some ch ->
        Buffer.add_char b ch;
        bump c;
        go ()
    | None -> fail c "the string isn't closed"
  in
  go ()

(* After a backslash in a multi-line basic string: spaces up to a newline, and
   every space and newline after it, which the string doesn't hold. *)
let line_ending_backslash c =
  let start = c.pos in
  ws c;
  if newline c then (
    let rec skip () =
      ws c;
      if newline c then skip ()
    in
    skip ();
    true)
  else if c.pos > start then fail c "a `\\` before spaces ends its line"
  else false

let multi_line c quote =
  let b = Buffer.create 16 in
  let rec run n = if peek_at c n = Some quote then run (n + 1) else n in
  let rec go () =
    match peek c with
    | Some ch when ch = quote ->
        let n = run 0 in
        if n < 3 then (
          Buffer.add_string b (String.make n quote);
          c.pos <- c.pos + n;
          go ())
        else if n > 5 then (
          c.pos <- c.pos + 5;
          fail c "a string ends with at most five quotes")
        else (
          Buffer.add_string b (String.make (n - 3) quote);
          c.pos <- c.pos + n;
          Buffer.contents b)
    | Some '\\' when quote = '"' ->
        bump c;
        if not (line_ending_backslash c) then escape c b;
        go ()
    | Some ('\n' | '\r') ->
        if newline c then Buffer.add_char b '\n';
        go ()
    | Some ch when is_control ch && ch <> '\t' ->
        fail c "a string holds no control character"
    | Some ch ->
        Buffer.add_char b ch;
        bump c;
        go ()
    | None -> fail c "the string isn't closed"
  in
  go ()

(* A string of any kind, at its opening quote. *)
let string c =
  let quote = Option.get (peek c) in
  if peek_at c 1 = Some quote && peek_at c 2 = Some quote then (
    c.pos <- c.pos + 3;
    ignore (newline c);
    multi_line c quote)
  else (
    bump c;
    single_line c quote)
