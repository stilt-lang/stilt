(* tests.generated-scalars, tests.composite-values and tests.minimal-values. *)

open Value
module P = Prop_types
module R = Prop_rand

type insert = Types.ty -> dict -> value -> value -> dict

let rec minimal (g : P.graph) i =
  match g.nodes.(i) with
  | Bool -> Bool false
  | Int _ -> Int 0L
  | Float _ -> Float 0.0
  | Str -> Str ""
  | Unit -> unit
  | List _ -> List Vec.empty
  | Map _ -> Map (Dict.empty None)
  | Tuple slots -> Tuple (List.map (minimal g) slots)
  | Record (item, fields) ->
      Record (item, List.map (fun (f, s) -> (f, minimal g s)) fields)
  | Variants vs -> (
      match P.nearest g vs with
      | (v, payload) :: _ -> Variant (v, List.map (minimal g) payload)
      | [] -> invalid_arg "Prop_gen.minimal")

(* The boundary values of tests.boundary-values. *)
let int_bounds (k : Ints.kind) =
  let lo = Ints.min_value k and hi = Ints.max_value k in
  if k.signed then [| 0L; 1L; -1L; lo; hi; Int64.add lo 1L; Int64.sub hi 1L |]
  else [| 0L; 1L; hi; Int64.sub hi 1L |]

let float_bounds f32 =
  let largest, normal, subnormal =
    if f32 then
      ( Int32.float_of_bits 0x7f7fffffl,
        Int32.float_of_bits 0x00800000l,
        Int32.float_of_bits 1l )
    else (Float.max_float, Float.min_float, Int64.float_of_bits 1L)
  in
  [|
    0.0;
    -0.0;
    1.0;
    -1.0;
    largest;
    -.largest;
    normal;
    subnormal;
    Float.infinity;
    Float.neg_infinity;
    Float.nan;
  |]

(* The low [bits] bits of [x], read as two's complement when [signed]. *)
let low (k : Ints.kind) x =
  if k.bits = 64 then x
  else
    let shift = 64 - k.bits in
    let up = Int64.shift_left x shift in
    if k.signed then Int64.shift_right up shift
    else Int64.shift_right_logical up shift

let int r ~size (k : Ints.kind) =
  match R.below_int r 4 with
  | 0 ->
      let b = int_bounds k in
      Int b.(R.below_int r (Array.length b))
  | 1 | 2 ->
      if k.signed then
        Int (Int64.of_int (R.below_int r ((2 * size) + 1) - size))
      else Int (Int64.of_int (R.below_int r (size + 1)))
  | _ -> Int (low k (R.next r))

let float r ~size f32 =
  match R.below_int r 4 with
  | 0 ->
      let b = float_bounds f32 in
      Float b.(R.below_int r (Array.length b))
  | 1 | 2 ->
      let n = R.below_int r ((512 * size) + 1) - (256 * size) in
      Float (Float.of_int n /. 256.0)
  | _ ->
      let bits = R.next r in
      Float
        (if f32 then Int32.float_of_bits (Int64.to_int32 bits)
         else Int64.float_of_bits bits)

let char r =
  match R.below_int r 4 with
  | 0 | 1 -> 0x20 + R.below_int r 95
  | 2 -> R.below_int r 128
  | _ ->
      let v = R.below_int r 0x10F800 in
      if v >= 0xD800 then v + 0x800 else v

let string r ~size =
  let n = R.below_int r (size + 1) in
  let b = Buffer.create n in
  for _ = 1 to n do
    Buffer.add_utf_8_uchar b (Uchar.of_int (char r))
  done;
  Str (Buffer.contents b)

let scalar r ~size : P.node -> value = function
  | Bool -> Bool (R.below_int r 2 = 1)
  | Int k -> int r ~size k
  | Float f32 -> float r ~size f32
  | Str -> string r ~size
  | Unit -> unit
  | _ -> invalid_arg "Prop_gen.scalar"

let key_type ty =
  match Types.resolve ty with
  | Con (_, [ k; _ ]) -> k
  | _ -> invalid_arg "Prop_gen.key_type"

let build_map insert kty entries =
  Map
    (List.fold_left
       (fun d (k, v) -> insert kty d k v)
       (Dict.empty None) entries)

(* [f] applied to each element, from the first, as the draws must be made in
   order (tests.draws). *)
let in_order f xs = List.rev (List.fold_left (fun acc x -> f x :: acc) [] xs)
let times n f = in_order (fun _ -> f ()) (List.init n Fun.id)

(* tests.composite-values: each of [k] components' budget. *)
let share budget k = if budget >= 1 && k > 0 then (budget - 1) / k else 0

let rec generate insert (g : P.graph) r ~budget ~size i =
  let gen budget = generate insert g r ~budget ~size in
  match g.nodes.(i) with
  | (Bool | Int _ | Float _ | Str | Unit) as node -> scalar r ~size node
  | Tuple slots ->
      let b = share budget (List.length slots) in
      Tuple (in_order (gen b) slots)
  | Record (item, fields) ->
      let b = share budget (List.length fields) in
      Record (item, in_order (fun (f, s) -> (f, gen b s)) fields)
  | List elem ->
      let n = R.below_int r (budget + 1) in
      let b = share budget n in
      List (Vec.of_list (times n (fun () -> gen b elem)))
  | Map (k, v) ->
      let n = R.below_int r (budget + 1) in
      let b = share budget (2 * n) in
      let entries =
        times n (fun () ->
            let key = gen b k in
            (key, gen b v))
      in
      build_map insert (key_type g.tys.(i)) entries
  | Variants vs ->
      let among = if budget >= 1 then P.live g vs else P.nearest g vs in
      let v, payload = List.nth among (R.below_int r (List.length among)) in
      let b = share budget (List.length payload) in
      Variant (v, in_order (gen b) payload)

let case insert g ~seed params i =
  if i = 0 then List.map (minimal g) params
  else
    let r = R.create seed i in
    in_order (generate insert g r ~budget:i ~size:i) params
