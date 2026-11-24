(* The kinds of number that [number] reads. *)
type number = Int_number | Float_number | Date_number

(* The lexical layer of TOML 1.0: a cursor over the text, and its scalar
   values, read so that an error is at the first character from which no TOML
   document can continue (packages.manifest-diagnostics, "Diagnostics"). *)

exception Syntax of int * string

type cursor = { text : string; mutable pos : int }

let peek c = if c.pos < String.length c.text then Some c.text.[c.pos] else None

let peek_at c n =
  if c.pos + n < String.length c.text then Some c.text.[c.pos + n] else None

let fail c message = raise (Syntax (c.pos, message))
let bump c = c.pos <- c.pos + 1

let eat c ch =
  if peek c = Some ch then (
    bump c;
    true)
  else false

let expect c ch what = if not (eat c ch) then fail c ("expected " ^ what)

let ws c =
  while peek c = Some ' ' || peek c = Some '\t' do
    bump c
  done

(* A control character that TOML allows only as a tab or in a newline. *)
let is_control ch =
  (ch >= '\000' && ch <= '\008') || (ch >= '\n' && ch <= '\031') || ch = '\127'

(* A newline, if one is here. A carriage return alone is an error. *)
let newline c =
  match peek c with
  | Some '\n' ->
      bump c;
      true
  | Some '\r' when peek_at c 1 = Some '\n' ->
      c.pos <- c.pos + 2;
      true
  | Some '\r' -> fail c "a carriage return only goes before a newline"
  | _ -> false

let comment c =
  if eat c '#' then
    let rec go () =
      match peek c with
      | None | Some '\n' -> ()
      | Some '\r' when peek_at c 1 = Some '\n' -> ()
      | Some ch when is_control ch && ch <> '\t' ->
          fail c "a comment holds no control character"
      | Some _ ->
          bump c;
          go ()
    in
    go ()

let word c w = String.iter (fun ch -> expect c ch ("`" ^ w ^ "`")) w

let digit_of radix ch =
  let v =
    match ch with
    | '0' .. '9' -> Char.code ch - 48
    | 'a' .. 'f' -> Char.code ch - 87
    | 'A' .. 'F' -> Char.code ch - 55
    | _ -> 99
  in
  if v < radix then Some v else None

(* One or more digits of [radix], with single underscores between them. *)
let digits c radix =
  let b = Buffer.create 8 in
  let rec group () =
    (match Option.bind (peek c) (digit_of radix) with
    | Some _ -> ()
    | None -> fail c "expected a digit");
    let rec run () =
      match peek c with
      | Some ch when Option.is_some (digit_of radix ch) ->
          Buffer.add_char b ch;
          bump c;
          run ()
      | _ -> ()
    in
    run ();
    if eat c '_' then group ()
  in
  group ();
  Buffer.contents b

let fixed c n =
  let v = ref 0 in
  for _ = 1 to n do
    match peek c with
    | Some ('0' .. '9' as ch) ->
        v := (!v * 10) + Char.code ch - 48;
        bump c
    | _ -> fail c "expected a digit"
  done;
  !v

let digits_then c n ch =
  let rec all i =
    i >= n
    || (match peek_at c i with Some '0' .. '9' -> true | _ -> false)
       && all (i + 1)
  in
  all 0 && peek_at c n = Some ch

let field c n max =
  let at = c.pos in
  if fixed c n > max then raise (Syntax (at, "this field is out of range"))

let days_in year month =
  match month with
  | 2 when year mod 4 = 0 && (year mod 100 <> 0 || year mod 400 = 0) -> 29
  | 2 -> 28
  | 4 | 6 | 9 | 11 -> 30
  | _ -> 31

let time c ~after_date =
  field c 2 23;
  expect c ':' "`:`";
  field c 2 59;
  expect c ':' "`:`";
  field c 2 60;
  if eat c '.' then (
    ignore (fixed c 1);
    while match peek c with Some '0' .. '9' -> true | _ -> false do
      bump c
    done);
  if after_date then
    match peek c with
    | Some ('Z' | 'z') -> bump c
    | Some ('+' | '-') ->
        bump c;
        field c 2 23;
        expect c ':' "`:`";
        field c 2 59
    | _ -> ()

let date_time c =
  let year = fixed c 4 in
  expect c '-' "`-`";
  let month_at = c.pos in
  let month = fixed c 2 in
  expect c '-' "`-`";
  let day_at = c.pos in
  let day = fixed c 2 in
  if month < 1 || month > 12 then raise (Syntax (month_at, "no such month"));
  if day = 0 || day > days_in year month then
    raise (Syntax (day_at, "that month has no such day"));
  let timed =
    match peek c with
    | Some ('T' | 't') -> true
    | Some ' ' -> (
        match peek_at c 1 with Some '0' .. '9' -> true | _ -> false)
    | _ -> false
  in
  if timed then (
    bump c;
    time c ~after_date:true)

let integer start digits radix =
  let prefix =
    match radix with 16 -> "0x" | 8 -> "0o" | 2 -> "0b" | _ -> ""
  in
  match Int64.of_string_opt (prefix ^ digits) with
  | Some v when radix = 10 || Int64.compare v 0L >= 0 -> Int_number
  | _ -> raise (Syntax (start, "the integer is out of the range of 64 bits"))

let decimal c start =
  let whole =
    if peek c = Some '0' then (
      bump c;
      "0")
    else digits c 10
  in
  let float = ref false in
  if eat c '.' then (
    ignore (digits c 10);
    float := true);
  if eat c 'e' || eat c 'E' then (
    ignore (eat c '+' || eat c '-');
    ignore (digits c 10);
    float := true);
  if !float then Float_number
  else
    let negative = c.text.[start] = '-' in
    integer start ((if negative then "-" else "") ^ whole) 10

(* A number, a date or a time. *)
let number c =
  let start = c.pos in
  let signed = eat c '+' || eat c '-' in
  match peek c with
  | Some 'i' ->
      word c "inf";
      Float_number
  | Some 'n' ->
      word c "nan";
      Float_number
  | _ when (not signed) && digits_then c 4 '-' ->
      date_time c;
      Date_number
  | _ when (not signed) && digits_then c 2 ':' ->
      time c ~after_date:false;
      Date_number
  | Some '0'
    when (not signed) && List.mem (peek_at c 1) [ Some 'x'; Some 'o'; Some 'b' ]
    ->
      let radix =
        match peek_at c 1 with Some 'x' -> 16 | Some 'o' -> 8 | _ -> 2
      in
      c.pos <- c.pos + 2;
      integer start (digits c radix) radix
  | _ -> decimal c start
