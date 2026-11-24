type t =
  | Str of string
  | Arr of t list
  | Bool of bool
  | Null
  | Obj of (string * t) list

let tag name fields = Arr (Str name :: fields)

let rec write b = function
  | Str s -> Buffer.add_string b (Json.string s)
  | Bool v -> Buffer.add_string b (string_of_bool v)
  | Null -> Buffer.add_string b "null"
  | Arr xs ->
      Buffer.add_char b '[';
      List.iteri
        (fun i x ->
          if i > 0 then Buffer.add_char b ',';
          write b x)
        xs;
      Buffer.add_char b ']'
  | Obj kvs ->
      Buffer.add_char b '{';
      List.iteri
        (fun i (k, v) ->
          if i > 0 then Buffer.add_char b ',';
          Buffer.add_string b (Json.string k);
          Buffer.add_char b ':';
          write b v)
        kvs;
      Buffer.add_char b '}'

let to_string j =
  let b = Buffer.create 4096 in
  write b j;
  Buffer.contents b
