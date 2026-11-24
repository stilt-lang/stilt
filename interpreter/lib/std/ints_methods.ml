(* The methods of the integer types that std.integers adds. A value is held
   as {!Ints} holds it. *)

open Ints

let overflows = function Fault.Panic ("overflow", _) -> true | _ -> false

let checked op k a b =
  match op k a b with r -> Some r | exception e when overflows e -> None

let checked_add = checked add
let checked_sub = checked sub
let checked_mul = checked mul

(* An overflowing sum goes past the end that [b]'s sign points to. *)
let saturating_add k a b =
  match checked_add k a b with
  | Some r -> r
  | None -> if k.signed && b < 0L then min_value k else max_value k

let saturating_sub k a b =
  match checked_sub k a b with
  | Some r -> r
  | None -> if k.signed && b < 0L then max_value k else min_value k

(* With [|a| >= 2], each power's magnitude grows, so the powers before one that
   fits fit too, and repeated multiplication overflows within 64 steps. *)
let pow k a exp =
  if exp = 0L then 1L
  else if a = 0L || a = 1L then a
  else if k.signed && a = -1L then if Int64.rem exp 2L = 0L then 1L else -1L
  else
    let rec go r n = if n = 0L then r else go (mul k r a) (Int64.pred n) in
    go a (Int64.pred exp)

(* Euclidean division: the remainder is never negative. *)
let div_euclid k a b =
  let q = div k a b in
  if k.signed && rem k a b < 0L then
    if b > 0L then Int64.pred q else Int64.succ q
  else q

let rem_euclid k a b =
  let r = rem k a b in
  if k.signed && r < 0L then if b > 0L then Int64.add r b else Int64.sub r b
  else r

(* The value's bits at its width, read as unsigned. *)
let bits k a =
  if k.bits = 64 then a
  else Int64.logand a (Int64.pred (Int64.shift_left 1L k.bits))

let count_ones k a =
  let rec go x n =
    if x = 0L then n else go (Int64.logand x (Int64.pred x)) (Int64.succ n)
  in
  go (bits k a) 0L

let leading_zeros k a =
  let x = bits k a in
  let rec go i =
    if i < 0 || Int64.logand (Int64.shift_right_logical x i) 1L = 1L then i
    else go (i - 1)
  in
  Int64.of_int (k.bits - 1 - go (k.bits - 1))

let trailing_zeros k a =
  let x = bits k a in
  let rec go i =
    if i = k.bits || Int64.logand (Int64.shift_right_logical x i) 1L = 1L then i
    else go (i + 1)
  in
  Int64.of_int (go 0)

(* The magnitude of a value as an unsigned 64-bit pattern, which holds even
   that of [i64.MIN]. *)
let magnitude k a = if k.signed && a < 0L then Int64.neg a else a
let rec gcd_u64 a b = if b = 0L then a else gcd_u64 b (Int64.unsigned_rem a b)
let u64 = { bits = 64; signed = false }

(* A magnitude as a value of [k], or an overflow. *)
let of_magnitude k m =
  if fits ~from:u64 k m then m
  else Fault.panic "overflow" "the result doesn't fit in `%s`" (name k)

let gcd k a b = of_magnitude k (gcd_u64 (magnitude k a) (magnitude k b))

let lcm k a b =
  if a = 0L || b = 0L then 0L
  else
    let a = magnitude k a and b = magnitude k b in
    let q = Int64.unsigned_div a (gcd_u64 a b) in
    match checked_mul u64 q b with
    | Some m -> of_magnitude k m
    | None -> Fault.panic "overflow" "the result doesn't fit in `%s`" (name k)
