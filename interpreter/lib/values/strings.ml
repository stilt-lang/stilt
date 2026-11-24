let occurs_at s sub i =
  let n = String.length sub in
  let rec same j = j = n || (s.[i + j] = sub.[j] && same (j + 1)) in
  i + n <= String.length s && same 0

let rec find_from s sub i =
  if i + String.length sub > String.length s then None
  else if occurs_at s sub i then Some i
  else find_from s sub (i + 1)

let find s sub = find_from s sub 0

let is_boundary s i =
  i = 0 || i = String.length s || Char.code s.[i] land 0xc0 <> 0x80

let scalar_length s i = Uchar.utf_decode_length (String.get_utf_8_uchar s i)

let chars s =
  let rec go i acc =
    if i >= String.length s then List.rev acc
    else
      let n = scalar_length s i in
      go (i + n) (String.sub s i n :: acc)
  in
  go 0 []

let split s sep =
  if sep = "" then chars s
  else
    let rec go start acc =
      match find_from s sep start with
      | Some i ->
          go (i + String.length sep) (String.sub s start (i - start) :: acc)
      | None -> List.rev (String.sub s start (String.length s - start) :: acc)
    in
    go 0 []

let lines s =
  let strip line =
    if String.ends_with ~suffix:"\r" line then
      String.sub line 0 (String.length line - 1)
    else line
  in
  let pieces = String.split_on_char '\n' s in
  (* A final newline ends the last line rather than starting another, so
     [""] has no lines at all. *)
  let pieces =
    match List.rev pieces with "" :: rest -> List.rev rest | _ -> pieces
  in
  List.map strip pieces

let is_space c = c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\012'

let trim s =
  let rec first i =
    if i < String.length s && is_space s.[i] then first (i + 1) else i
  in
  let start = first 0 in
  let rec last j =
    if j > start && is_space s.[j - 1] then last (j - 1) else j
  in
  String.sub s start (last (String.length s) - start)

let replace s from into =
  (* An empty [from] occurs at every boundary between scalar values, and at
     both ends. *)
  if from = "" then String.concat into (("" :: chars s) @ [ "" ])
  else String.concat into (split s from)

let repair s =
  if String.is_valid_utf_8 s then s
  else
    let b = Buffer.create (String.length s) in
    let rec go i =
      if i < String.length s then (
        let d = String.get_utf_8_uchar s i in
        Buffer.add_utf_8_uchar b (Uchar.utf_decode_uchar d);
        go (i + Uchar.utf_decode_length d))
    in
    go 0;
    Buffer.contents b

let quote s =
  let b = Buffer.create (String.length s + 2) in
  let escape i =
    let n = scalar_length s i in
    (match Char.code s.[i] with
    | 0x22 -> Buffer.add_string b "\\\""
    | 0x5c -> Buffer.add_string b "\\\\"
    | 0x0a -> Buffer.add_string b "\\n"
    | 0x09 -> Buffer.add_string b "\\t"
    | 0x0d -> Buffer.add_string b "\\r"
    | 0x00 -> Buffer.add_string b "\\0"
    | c when c < 0x20 || c = 0x7f -> Printf.bprintf b "\\u{%x}" c
    | _ -> Buffer.add_string b (String.sub s i n));
    i + n
  in
  let rec go i = if i < String.length s then go (escape i) in
  Buffer.add_char b '"';
  go 0;
  Buffer.add_char b '"';
  Buffer.contents b
