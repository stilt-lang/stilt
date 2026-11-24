(* The types of generated programs, and what the Reference says each one can
   do. *)

type int_kind = I8 | I16 | I32 | I64 | U8 | U16 | U32 | U64
type float_kind = F32 | F64

type t =
  | Int of int_kind
  | Float of float_kind
  | Bool
  | Str
  | Unit
  | Tuple of t list
  | List of t
  | Map of t * t
  | Option of t
  | Named of string  (** A record or variant type that the program declares. *)

(* A declared type: a record's fields, or a variant type's variants with their
   payloads. *)
type decl = Record of (string * t) list | Variants of (string * t list) list

let int_kinds = [ I8; I16; I32; I64; U8; U16; U32; U64 ]
let float_kinds = [ F32; F64 ]

let int_name = function
  | I8 -> "i8"
  | I16 -> "i16"
  | I32 -> "i32"
  | I64 -> "i64"
  | U8 -> "u8"
  | U16 -> "u16"
  | U32 -> "u32"
  | U64 -> "u64"

let float_name = function F32 -> "f32" | F64 -> "f64"

let bits = function
  | I8 | U8 -> 8
  | I16 | U16 -> 16
  | I32 | U32 -> 32
  | I64 | U64 -> 64

let signed = function
  | I8 | I16 | I32 | I64 -> true
  | U8 | U16 | U32 | U64 -> false

let rec to_string = function
  | Int k -> int_name k
  | Float k -> float_name k
  | Bool -> "bool"
  | Str -> "str"
  | Unit -> "()"
  | Tuple ts -> "(" ^ String.concat ", " (List.map to_string ts) ^ ")"
  | List t -> "List<" ^ to_string t ^ ">"
  | Map (k, v) -> "Map<" ^ to_string k ^ ", " ^ to_string v ^ ">"
  | Option t -> "Option<" ^ to_string t ^ ">"
  | Named name -> name

(* [t] with [f] applied to the name of every declared type in it. *)
let rec map_named f = function
  | Named name -> Named (f name)
  | Tuple ts -> Tuple (List.map (map_named f) ts)
  | List t -> List (map_named f t)
  | Option t -> Option (map_named f t)
  | Map (k, v) -> Map (map_named f k, map_named f v)
  | (Int _ | Float _ | Bool | Str | Unit) as t -> t

(* The names of the declared types in [t]. *)
let rec named = function
  | Named name -> [ name ]
  | Tuple ts -> List.concat_map named ts
  | List t | Option t -> named t
  | Map (k, v) -> named k @ named v
  | Int _ | Float _ | Bool | Str | Unit -> []

(* numbers.conversions: [.to_T()] returns [T] when every value of the source type
   fits in [T], and [Option<T>] otherwise. *)
let widens ~from ~into =
  match (signed from, signed into) with
  | true, false -> false
  | false, true -> bits from < bits into
  | _ -> bits from <= bits into

(* Whether [t] has [Ord] structurally (traits.structural-impls). Floats do, through
   their total order, and maps don't. *)
let rec ordered ~decls t =
  let ordered = ordered ~decls in
  match t with
  | Int _ | Float _ | Bool | Str | Unit -> true
  | Map _ -> false
  | Tuple ts -> List.for_all ordered ts
  | List t | Option t -> ordered t
  | Named name -> (
      match List.assoc name decls with
      | Record fields -> List.for_all (fun (_, t) -> ordered t) fields
      | Variants cases ->
          List.for_all (fun (_, payload) -> List.for_all ordered payload) cases)

(* Whether a map appears anywhere in [t]. *)
let rec has_map decls = function
  | Map _ -> true
  | Tuple ts -> List.exists (has_map decls) ts
  | List t | Option t -> has_map decls t
  | Named name -> (
      match List.assoc name decls with
      | Record fields -> List.exists (fun (_, t) -> has_map decls t) fields
      | Variants cases ->
          List.exists (fun (_, ts) -> List.exists (has_map decls) ts) cases)
  | Int _ | Float _ | Bool | Str | Unit -> false
