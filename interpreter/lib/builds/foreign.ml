(* What the reference interpreter does with C (c.both-implementations), through
   foreign_stubs.c. A value crosses as its bits in an int64: an integer as Ints
   holds it, a float's binary32 or binary64 bits, [bool] as 0 or 1, and an
   address as itself. *)

open Value
module T = Types

external load : string -> bool = "stilt_c_load"
external symbol : string -> int64 = "stilt_c_symbol"

external call_c : int64 -> int array -> int64 array -> int -> int64
  = "stilt_c_call"

external alloc : int -> int64 = "stilt_c_alloc"
external free : int64 -> unit = "stilt_c_free"
external peek : int64 -> int -> bool -> int64 = "stilt_c_peek"
external poke : int64 -> int -> int64 -> unit = "stilt_c_poke"
external c_bytes : int64 -> string = "stilt_c_string"
external write_bytes : int64 -> string -> unit = "stilt_c_write_bytes"

(* The kinds of foreign_stubs.c, in its order. *)
let kinds =
  [ "i8"; "u8"; "i16"; "u16"; "i32"; "u32"; "i64"; "u64"; "f32"; "f64" ]

let kind t =
  match T.numeric_name t with
  | Some name ->
      let rec index i = function
        | n :: rest -> if n = name then i else index (i + 1) rest
        | [] -> 0
      in
      index 1 kinds
  | None -> (
      match T.resolve t with
      | t when t = T.bool -> 11
      | t when t = T.unit -> 0
      | _ -> 12)

let size t =
  match T.numeric_name t with
  | Some ("i8" | "u8") -> 1
  | Some ("i16" | "u16") -> 2
  | Some ("i32" | "u32" | "f32") -> 4
  | Some _ -> 8
  | None -> if T.resolve t = T.bool then 1 else 8

let bits t v =
  match (v, T.numeric_name t) with
  | Int i, _ -> i
  | Float f, Some "f32" -> Int64.of_int32 (Int32.bits_of_float f)
  | Float f, _ -> Int64.bits_of_float f
  | Bool b, _ -> if b then 1L else 0L
  | _ -> 0L

let of_bits t b =
  match T.numeric_name t with
  | Some "f32" -> Float (Int32.float_of_bits (Int64.to_int32 b))
  | Some "f64" -> Float (Int64.float_of_bits b)
  | Some name -> Int (Ints.wrap (Option.get (Ints.of_name name)) b)
  | None -> (
      match T.resolve t with
      | t when t = T.bool -> Bool (b <> 0L)
      | t when t = T.unit -> Tuple []
      | _ -> Int b)

let call name params ret args =
  let address = symbol name in
  if address = 0L then raise (Eval_state.Fatal ("no C function " ^ name));
  let result =
    call_c address
      (Array.of_list (List.map kind params))
      (Array.of_list (List.map2 bits params args))
      (kind ret)
  in
  of_bits ret result

let signed t =
  match Option.bind (T.numeric_name t) Ints.of_name with
  | Some k -> k.signed
  | None -> false

let read t address =
  match T.numeric_name t with
  | Some "f32" -> of_bits t (peek address 4 false)
  | _ -> of_bits t (peek address (size t) (signed t))

let write t address v = poke address (size t) (bits t v)

let lend t xs =
  let n = size t in
  let buffer = alloc (n * List.length xs) in
  List.iteri (fun i x -> write t (Int64.add buffer (Int64.of_int (i * n))) x) xs;
  buffer

let read_list t address count =
  List.init (max count 0) (fun i ->
      read t (Int64.add address (Int64.of_int (i * size t))))

let c_string s =
  let buffer = alloc (String.length s + 1) in
  write_bytes buffer s;
  buffer

let to_str address = Strings.repair (c_bytes address)
