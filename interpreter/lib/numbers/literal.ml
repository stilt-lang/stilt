(* Natural numbers, as little-endian lists of base-2^16 limbs with no
   trailing zero limb. *)

let base = 1 lsl 16

let rec normalize = function
  | [] -> []
  | l -> (
      match List.rev l with 0 :: rest -> normalize (List.rev rest) | _ -> l)

(* [n * m + a] for small [m] and [a]. *)
let mul_add n m a =
  let rec go carry = function
    | [] -> if carry = 0 then [] else [ carry mod base ] @ go (carry / base) []
    | limb :: rest ->
        let x = (limb * m) + carry in
        (x mod base) :: go (x / base) rest
  in
  normalize (go a n)

let of_digits radix digits =
  String.fold_left
    (fun n c ->
      let d =
        match c with
        | '0' .. '9' -> Char.code c - Char.code '0'
        | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
        | 'A' .. 'F' -> Char.code c - Char.code 'A' + 10
        | _ -> invalid_arg "Literal.of_digits"
      in
      mul_add n radix d)
    [] digits

let strip_zeros digits =
  let rec first i =
    if i < String.length digits && digits.[i] = '0' then first (i + 1) else i
  in
  let i = first 0 in
  String.sub digits i (String.length digits - i)

(* An integer literal's radix and digits, without its prefix and leading
   zeros. *)
let int_digits text =
  let radix, digits =
    if String.length text > 2 && text.[0] = '0' then
      match text.[1] with
      | 'x' -> (16, String.sub text 2 (String.length text - 2))
      | 'o' -> (8, String.sub text 2 (String.length text - 2))
      | 'b' -> (2, String.sub text 2 (String.length text - 2))
      | _ -> (10, text)
    else (10, text)
  in
  (radix, strip_zeros digits)

(* The value of an integer literal, or [None] when it is surely at least
   [2^bits]. Every numeric type's values are below 2^1025, so no test needs
   arithmetic on larger numbers, however long the literal. *)
let int_value text ~bits =
  let radix, digits = int_digits text in
  let bits_per_digit = match radix with 16 -> 4 | 8 -> 3 | 2 -> 1 | _ -> 3 in
  (* A decimal digit adds more than 3 bits, and the first digit at least
     one. *)
  if (String.length digits - 1) * bits_per_digit >= bits then None
  else Some (of_digits radix digits)

let compare_nat a b =
  let la = List.length a and lb = List.length b in
  if la <> lb then compare la lb else compare (List.rev a) (List.rev b)

let pow2 k = normalize (List.init (k / 16) (fun _ -> 0) @ [ 1 lsl (k mod 16) ])

let rec mul a b =
  match a with
  | [] -> []
  | limb :: rest ->
      let partial = mul_add b limb 0 in
      let shifted = normalize (0 :: mul rest b) in
      add partial shifted

and add a b =
  let rec go carry a b =
    match (a, b) with
    | [], [] -> if carry = 0 then [] else [ carry ]
    | x :: a, [] | [], x :: a ->
        let s = x + carry in
        (s mod base) :: go (s / base) a []
    | x :: a, y :: b ->
        let s = x + y + carry in
        (s mod base) :: go (s / base) a b
  in
  normalize (go 0 a b)

let sub a b =
  let rec go borrow a b =
    match (a, b) with
    | [], _ -> []
    | x :: a, [] ->
        let d = x - borrow in
        if d < 0 then (d + base) :: go 1 a [] else d :: go 0 a []
    | x :: a, y :: b ->
        let d = x - y - borrow in
        if d < 0 then (d + base) :: go 1 a b else d :: go 0 a b
  in
  normalize (go 0 a b)

let rec pow10 k = if k = 0 then [ 1 ] else mul_add (pow10 (k - 1)) 10 0

let bit_length n =
  match List.rev n with
  | [] -> 0
  | top :: _ ->
      let rec bits x = if x = 0 then 0 else 1 + bits (x lsr 1) in
      ((List.length n - 1) * 16) + bits top

let trailing_zeros n =
  let rec limbs i = function
    | [] -> 0
    | 0 :: rest -> limbs (i + 16) rest
    | x :: _ ->
        let rec bits x = if x land 1 = 1 then 0 else 1 + bits (x lsr 1) in
        i + bits x
  in
  limbs 0 n

let width = function
  | "i8" | "u8" -> 8
  | "i16" | "u16" -> 16
  | "i32" | "u32" -> 32
  | "i64" | "u64" -> 64
  | ty -> invalid_arg ("Literal.width: " ^ ty)

let int_fits text ~negative ty =
  let bits = width ty in
  match int_value text ~bits:(bits + 1) with
  | None -> false
  | Some n ->
      if ty.[0] = 'u' then
        n = [] || ((not negative) && compare_nat n (pow2 bits) < 0)
      else
        let limit = pow2 (bits - 1) in
        if negative then compare_nat n limit <= 0 else compare_nat n limit < 0

(* The significand's bits and the largest power of two below the overflow
   threshold of each float type. *)
let float_format = function
  | "f32" -> (24, 128)
  | "f64" -> (53, 1024)
  | ty -> invalid_arg ("Literal.float_format: " ^ ty)

let int_exact_in text ty =
  let significand, max_exponent = float_format ty in
  match int_value text ~bits:(max_exponent + 1) with
  | None -> false
  | Some n ->
      n = []
      || bit_length n - trailing_zeros n <= significand
         && bit_length n <= max_exponent

(* A float literal [D.D], [DeE] or [D.DeE] is [m * 10^e] for a natural [m].
   It rounds to infinity when it is at least halfway between the largest
   finite value and the next power of two, [2^max - 2^(max - significand -
   1)]. *)
let float_fits text ty =
  let significand, max_exponent = float_format ty in
  let split text c =
    match String.index_from_opt text 0 c with
    | Some i ->
        ( String.sub text 0 i,
          String.sub text (i + 1) (String.length text - i - 1) )
    | None -> (text, "")
  in
  let mantissa, exponent = split (String.lowercase_ascii text) 'e' in
  let whole, fraction = split mantissa '.' in
  let digits = strip_zeros (whole ^ fraction) in
  let n = String.length digits in
  let threshold =
    sub (pow2 max_exponent) (pow2 (max_exponent - significand - 1))
  in
  (* The value [digits * 10^e] lies between [10^(n + e - 1)] and
     [10^(n + e)]. The largest finite value of every float type is below
     10^309, so only an [n + e] from 1 to 309 needs a closer look. Then the
     value is below the threshold, an integer, exactly when its integer part,
     the first [n + e] digits, is. An exponent too large for an [int] decides
     by its sign. *)
  match int_of_string_opt (if exponent = "" then "0" else exponent) with
  | _ when n = 0 -> true
  | Some e when abs e <= 1_000_000_000 ->
      let e = e - String.length fraction in
      if n + e <= 0 then true
      else if n + e > 309 then false
      else if e >= 0 then
        compare_nat (mul (of_digits 10 digits) (pow10 e)) threshold < 0
      else
        compare_nat (of_digits 10 (String.sub digits 0 (n + e))) threshold < 0
  | _ -> exponent.[0] = '-'

let int_canonical text =
  let negative = String.length text > 0 && text.[0] = '-' in
  let text =
    if negative then String.sub text 1 (String.length text - 1) else text
  in
  let radix, digits = int_digits text in
  let limbs = of_digits radix digits in
  let magnitude = String.concat "." (List.map string_of_int limbs) in
  if negative && limbs <> [] then "-" ^ magnitude else magnitude
