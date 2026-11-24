type kind = { bits : int; signed : bool }

let of_name = function
  | "i8" -> Some { bits = 8; signed = true }
  | "i16" -> Some { bits = 16; signed = true }
  | "i32" -> Some { bits = 32; signed = true }
  | "i64" -> Some { bits = 64; signed = true }
  | "u8" -> Some { bits = 8; signed = false }
  | "u16" -> Some { bits = 16; signed = false }
  | "u32" -> Some { bits = 32; signed = false }
  | "u64" -> Some { bits = 64; signed = false }
  | _ -> None

let name k = Printf.sprintf "%c%d" (if k.signed then 'i' else 'u') k.bits

let wrap k x =
  if k.bits = 64 then x
  else
    let shift = 64 - k.bits in
    if k.signed then Int64.shift_right (Int64.shift_left x shift) shift
    else Int64.shift_right_logical (Int64.shift_left x shift) shift

let min_value k =
  if k.signed then Int64.neg (Int64.shift_left 1L (k.bits - 1)) else 0L

let max_value k =
  if k.signed then Int64.pred (Int64.shift_left 1L (k.bits - 1))
  else if k.bits = 64 then -1L
  else Int64.pred (Int64.shift_left 1L k.bits)

let compare k a b =
  if k.signed then Int64.compare a b else Int64.unsigned_compare a b

let to_string k x =
  if k.signed then Int64.to_string x else Printf.sprintf "%Lu" x

(* numbers.integer-panics *)

let overflow k =
  Fault.panic "overflow" "the result doesn't fit in `%s`" (name k)

(* A result computed exactly in an [int64], checked against a narrow type. *)
let narrow k r = if wrap k r <> r then overflow k else r

let add k a b =
  let r = Int64.add a b in
  if k.bits < 64 then narrow k r
  else if k.signed then
    if Int64.logand (Int64.logxor a r) (Int64.logxor b r) < 0L then overflow k
    else r
  else if Int64.unsigned_compare r a < 0 then overflow k
  else r

let sub k a b =
  let r = Int64.sub a b in
  if k.bits < 64 then narrow k r
  else if k.signed then
    if Int64.logand (Int64.logxor a b) (Int64.logxor a r) < 0L then overflow k
    else r
  else if Int64.unsigned_compare a b < 0 then overflow k
  else r

let mul k a b =
  let r = Int64.mul a b in
  if k.bits <= 16 || (k.signed && k.bits = 32) then narrow k r
  else if k.bits = 32 then
    (* Two [u32] values multiply to less than 2^64. *)
    if Int64.unsigned_compare r (max_value k) > 0 then overflow k else r
  else if a = 0L || b = 0L then 0L
  else if k.signed then
    if
      (a = -1L && b = Int64.min_int)
      || (b = -1L && a = Int64.min_int)
      || Int64.div r b <> a
    then overflow k
    else r
  else if Int64.unsigned_div r b <> a then overflow k
  else r

(* numbers.integer-panics and numbers.division-and-remainder *)
let divide k a b ~signed ~unsigned =
  if b = 0L then Fault.panic "divide-by-zero" "division by zero"
  else if k.signed then
    if a = min_value k && b = -1L then overflow k else signed a b
  else unsigned a b

let div k a b = divide k a b ~signed:Int64.div ~unsigned:Int64.unsigned_div
let rem k a b = divide k a b ~signed:Int64.rem ~unsigned:Int64.unsigned_rem

let neg k a =
  if k.signed then if a = min_value k then overflow k else Int64.neg a
  else if a = 0L then 0L
  else overflow k

(* numbers.wrapping *)
let add_wrap k a b = wrap k (Int64.add a b)
let sub_wrap k a b = wrap k (Int64.sub a b)
let mul_wrap k a b = wrap k (Int64.mul a b)

(* numbers.bitwise-operators *)
let logand = Int64.logand
let logor = Int64.logor
let logxor = Int64.logxor
let lognot k a = wrap k (Int64.lognot a)

(* numbers.shift-amounts: the amount [n] has its own kind [by], in which it is negative
   only when [by] is signed. *)
let amount k ~by n =
  if
    (by.signed && n < 0L) || Int64.unsigned_compare n (Int64.of_int k.bits) >= 0
  then
    Fault.panic "overflow" "the shift amount %s is out of range for `%s`"
      (to_string by n) (name k)
  else Int64.to_int n

let shift_left k ~by a n = wrap k (Int64.shift_left a (amount k ~by n))

let shift_right k ~by a n =
  let n = amount k ~by n in
  if k.signed then Int64.shift_right a n else Int64.shift_right_logical a n

(* numbers.conversions and numbers.wrapping-conversions *)

let fits ~from into a =
  if (not from.signed) && from.bits = 64 && a < 0L then
    (not into.signed) && into.bits = 64
  else if into.signed then
    Int64.compare a (min_value into) >= 0
    && Int64.compare a (max_value into) <= 0
  else a >= 0L && (into.bits = 64 || Int64.compare a (max_value into) <= 0)

let lossless ~from into =
  (from.signed = into.signed && into.bits >= from.bits)
  || ((not from.signed) && into.signed && into.bits > from.bits)

let to_float k a =
  if (not k.signed) && k.bits = 64 && a < 0L then
    (* Halving with the lost bit kept as a sticky bit rounds once. *)
    let half =
      Int64.logor (Int64.shift_right_logical a 1) (Int64.logand a 1L)
    in
    2.0 *. Int64.to_float half
  else Int64.to_float a

let to_f32 k a =
  let negative = k.signed && a < 0L in
  let m = if negative then Int64.neg a else a in
  (* The magnitude [m], read as unsigned, rounded to 24 significant bits,
     to nearest with ties to even. *)
  let rec high_bit i =
    if i < 0 || Int64.shift_right_logical m i = 1L then i else high_bit (i - 1)
  in
  let h = high_bit 63 in
  let magnitude =
    if h < 24 then Int64.to_float m
    else
      let shift = h - 23 in
      let kept = Int64.shift_right_logical m shift in
      let rest = Int64.logand m (Int64.pred (Int64.shift_left 1L shift)) in
      let half = Int64.shift_left 1L (shift - 1) in
      let up =
        Int64.unsigned_compare rest half > 0
        || (rest = half && Int64.logand kept 1L = 1L)
      in
      Float.ldexp (Int64.to_float (if up then Int64.succ kept else kept)) shift
  in
  if negative then -.magnitude else magnitude

(* Literals and parsing *)

let digit c =
  match c with
  | '0' .. '9' -> Char.code c - Char.code '0'
  | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
  | 'A' .. 'F' -> Char.code c - Char.code 'A' + 10
  | _ -> invalid_arg "Ints.digit"

let radix text =
  if String.length text > 2 && text.[0] = '0' then
    match text.[1] with
    | 'x' -> (16, 2)
    | 'o' -> (8, 2)
    | 'b' -> (2, 2)
    | _ -> (10, 0)
  else (10, 0)

let of_literal text =
  let base, start = radix text in
  let v = ref 0L in
  for i = start to String.length text - 1 do
    v :=
      Int64.add
        (Int64.mul !v (Int64.of_int base))
        (Int64.of_int (digit text.[i]))
  done;
  !v

(* numbers.parsing *)
let parse k s =
  let n = String.length s in
  let negative = n > 0 && s.[0] = '-' in
  let start = if negative then 1 else 0 in
  let digits =
    n > start
    && String.for_all
         (fun c -> c >= '0' && c <= '9')
         (String.sub s start (n - start))
  in
  if (not digits) || (negative && not k.signed) then None
  else
    (* The magnitude, as an unsigned 64-bit value, unless it exceeds one. *)
    let limit = Int64.unsigned_div (-1L) 10L in
    let rec go i m =
      if i = n then Some m
      else
        let d = Int64.of_int (digit s.[i]) in
        if Int64.unsigned_compare m limit > 0 then None
        else
          let m' = Int64.add (Int64.mul m 10L) d in
          if Int64.unsigned_compare m' (Int64.mul m 10L) < 0 then None
          else go (i + 1) m'
    in
    match go start 0L with
    | None -> None
    | Some m when negative ->
        if Int64.unsigned_compare m (Int64.neg (min_value k)) > 0 then None
        else Some (Int64.neg m)
    | Some m ->
        if Int64.unsigned_compare m (max_value k) > 0 then None else Some m

(* std.integer-kinds: a negative value shows as its two's complement at the
   type's width. *)
let to_base k ~base ~upper a =
  let digits = if upper then "0123456789ABCDEF" else "0123456789abcdef" in
  let m =
    if k.bits = 64 then a
    else Int64.logand a (Int64.pred (Int64.shift_left 1L k.bits))
  in
  let b = Int64.of_int base in
  let rec go m acc =
    let acc =
      String.make 1 digits.[Int64.to_int (Int64.unsigned_rem m b)] ^ acc
    in
    let m = Int64.unsigned_div m b in
    if m = 0L then acc else go m acc
  in
  go m ""
