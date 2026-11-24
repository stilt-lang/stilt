(* The native methods of [str] that std.str, std.bytes-and-scalars and std.code-points adds. Offsets count bytes,
   and every string is valid UTF-8. *)

let rfind s sub =
  let rec go i =
    if i < 0 then None
    else if Strings.occurs_at s sub i then Some i
    else go (i - 1)
  in
  go (String.length s - String.length sub)

let drop_while_start s =
  let rec first i =
    if i < String.length s && Strings.is_space s.[i] then first (i + 1) else i
  in
  let start = first 0 in
  String.sub s start (String.length s - start)

let drop_while_end s =
  let rec last j =
    if j > 0 && Strings.is_space s.[j - 1] then last (j - 1) else j
  in
  String.sub s 0 (last (String.length s))

let strip_prefix s prefix =
  if String.starts_with ~prefix s then
    Some
      (String.sub s (String.length prefix)
         (String.length s - String.length prefix))
  else None

let strip_suffix s suffix =
  if String.ends_with ~suffix s then
    Some (String.sub s 0 (String.length s - String.length suffix))
  else None

(* The text before and after an occurrence of [sep] at offset [i]. *)
let around s sep i =
  let after = i + String.length sep in
  (String.sub s 0 i, String.sub s after (String.length s - after))

let split_once s sep = Option.map (around s sep) (Strings.find s sep)
let rsplit_once s sep = Option.map (around s sep) (rfind s sep)
let char_count s = List.length (Strings.chars s)

(* Empty [sub] occurs at every boundary between scalar values, and at both
   ends, as [replace] finds it. *)
let count s sub =
  if sub = "" then char_count s + 1 else List.length (Strings.split s sub) - 1

let replace_first s from into =
  match split_once s from with
  | Some (before, after) -> before ^ into ^ after
  | None -> s

let split_whitespace s =
  let pieces = ref [] and start = ref 0 in
  for i = 0 to String.length s do
    if i = String.length s || Strings.is_space s.[i] then (
      if i > !start then pieces := String.sub s !start (i - !start) :: !pieces;
      start := i + 1)
  done;
  List.rev !pieces

(* Copies of [fill], the last cut short, that bring [s] to [width] scalar
   values. *)
let padding s width fill =
  let fill = Array.of_list (Strings.chars fill) in
  let missing = width - char_count s in
  if missing <= 0 || Array.length fill = 0 then ""
  else
    String.concat ""
      (List.init missing (fun i -> fill.(i mod Array.length fill)))

let pad_start s width fill = padding s width fill ^ s
let pad_end s width fill = s ^ padding s width fill
let reverse s = String.concat "" (List.rev (Strings.chars s))
let is_ascii s = String.for_all (fun c -> Char.code c < 0x80) s
let classified test s = s <> "" && String.for_all test s
let is_digit = function '0' .. '9' -> true | _ -> false
let is_upper = function 'A' .. 'Z' -> true | _ -> false
let is_lower = function 'a' .. 'z' -> true | _ -> false
let is_alpha c = is_upper c || is_lower c

let classify = function
  | "is_ascii_digit" -> Some is_digit
  | "is_ascii_alpha" -> Some is_alpha
  | "is_ascii_alphanumeric" -> Some (fun c -> is_alpha c || is_digit c)
  | "is_ascii_whitespace" -> Some Strings.is_space
  | "is_ascii_upper" -> Some is_upper
  | "is_ascii_lower" -> Some is_lower
  | _ -> None

let code_points s =
  let rec go i acc =
    if i >= String.length s then List.rev acc
    else
      let d = String.get_utf_8_uchar s i in
      go
        (i + Uchar.utf_decode_length d)
        (Uchar.to_int (Uchar.utf_decode_uchar d) :: acc)
  in
  go 0 []

let from_code_point c =
  if Uchar.is_valid c then (
    let b = Buffer.create 4 in
    Buffer.add_utf_8_uchar b (Uchar.of_int c);
    Some (Buffer.contents b))
  else None

let from_utf8 bytes =
  let s = String.of_seq (List.to_seq (List.map Char.chr bytes)) in
  if String.is_valid_utf_8 s then Some s else None

let from_utf8_lossy bytes =
  Strings.repair (String.of_seq (List.to_seq (List.map Char.chr bytes)))
