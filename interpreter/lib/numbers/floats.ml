let round32 x = Int32.float_of_bits (Int32.bits_of_float x)

(* numbers.ieee-754: every [f32] operation rounds its result to binary32. Rounding the
   exact [f64] result of [+], [-], [*], [/] or [sqrt] once more gives the
   correctly rounded binary32 result, since binary64 has more than twice the
   precision. *)
let result ~f32 x = if f32 then round32 x else x

(* Decimal numbers *)

(* A decimal number: its sign, its significant digits without leading or
   trailing zeros, and the exponent of 10 of its first digit's place. The
   digits are empty for zero. *)
type decimal = { negative : bool; digits : string; point : int }

(* Reads text in the form [-?d+(.d+)?([eE][+-]?d+)?], as [%e] writes it. *)
let decimal text =
  let negative = String.length text > 0 && text.[0] = '-' in
  let body =
    if negative then String.sub text 1 (String.length text - 1) else text
  in
  let mantissa, exponent =
    match String.index_opt (String.lowercase_ascii body) 'e' with
    | Some i ->
        ( String.sub body 0 i,
          int_of_string (String.sub body (i + 1) (String.length body - i - 1))
        )
    | None -> (body, 0)
  in
  let whole, fraction =
    match String.index_opt mantissa '.' with
    | Some i ->
        ( String.sub mantissa 0 i,
          String.sub mantissa (i + 1) (String.length mantissa - i - 1) )
    | None -> (mantissa, "")
  in
  let all = whole ^ fraction in
  let rec first i =
    if i < String.length all && all.[i] = '0' then first (i + 1) else i
  in
  let rec last i = if i > 0 && all.[i - 1] = '0' then last (i - 1) else i in
  let a = first 0 and b = last (String.length all) in
  if a >= b then { negative; digits = ""; point = 0 }
  else
    {
      negative;
      digits = String.sub all a (b - a);
      point = exponent + String.length whole - a - 1;
    }

(* Compares the magnitudes of two decimals. *)
let compare_magnitude x y =
  match (x.digits, y.digits) with
  | "", "" -> 0
  | "", _ -> -1
  | _, "" -> 1
  | _ when x.point <> y.point -> compare x.point y.point
  | a, b ->
      let n = max (String.length a) (String.length b) in
      let pad s = s ^ String.make (n - String.length s) '0' in
      compare (pad a) (pad b)

(* The exact decimal expansion of a float: binary64 values have at most 767
   significant digits. *)
let exact x = decimal (Printf.sprintf "%.767e" x)

(* The binary32 neighbour of [f], a binary32 value, in the direction of
   [toward]. A binary32 value's magnitude grows with its bits. *)
let next32 f ~toward =
  if f = 0.0 then Float.copy_sign (Int32.float_of_bits 1l) toward
  else
    let bits = Int32.bits_of_float f in
    Int32.float_of_bits
      (if toward > f = (f > 0.0) then Int32.succ bits else Int32.pred bits)

(* numbers.float-literals and numbers.parsing: the decimal [text] rounded to binary32 in one step.
   The nearest binary64 value, rounded again, is right unless it lies
   exactly halfway between two binary32 values; the decimal then decides by
   which side of that midpoint it lies on. *)
let f32_of_decimal text =
  let d = float_of_string text in
  let f = round32 d in
  if f = d || Float.is_nan d then f
  else
    let max32 = Int32.float_of_bits 0x7f7fffffl in
    let other, midpoint =
      if Float.abs f = Float.infinity then
        let g = Float.copy_sign max32 f in
        (g, Float.copy_sign (max32 +. Float.ldexp 1.0 103) f)
      else
        let g = next32 f ~toward:d in
        (g, (f +. g) /. 2.0)
    in
    if d <> midpoint then f
    else
      let c = compare_magnitude (decimal text) (exact d) in
      let away = Float.abs other > Float.abs f in
      if c = 0 then f else if c > 0 = away then other else f

(* numbers.printing-floats and numbers.float-digits *)

(* The shortest digits that read back as [x], a finite nonzero magnitude,
   with the exponent [k] of the form 0.d₁…dₙ × 10^k. Of two candidates of
   that length, the one nearer [x] wins. *)
let shortest ~f32 x =
  let reads_back s =
    (if f32 then f32_of_decimal s else float_of_string s) = x
  in
  let at p = Printf.sprintf "%.*e" (p - 1) x in
  (* The candidate [s] of [p] digits, moved by [step] in its last digit: an
     [Int64], since an [int] holds only 32 bits where the interpreter runs as
     JavaScript, as the playground runs it. *)
  let neighbour p s step =
    let d = decimal s in
    let n = String.length d.digits in
    let m =
      Int64.add
        (Int64.of_string (d.digits ^ String.make (p - n) '0'))
        (Int64.of_int step)
    in
    if m <= 0L then None else Some (Printf.sprintf "%Lde%d" m (d.point - p + 1))
  in
  let rec go p =
    let s = at p in
    if reads_back s then decimal s
    else
      let toward = if float_of_string s < x then 1 else -1 in
      match
        List.find_opt reads_back
          (List.filter_map (neighbour p s) [ toward; -toward ])
      with
      | Some s -> decimal s
      | None -> go (p + 1)
  in
  let d = go 1 in
  (d.digits, d.point + 1)

let special x =
  if Float.is_nan x then Some "nan"
  else if x = Float.infinity then Some "inf"
  else if x = Float.neg_infinity then Some "-inf"
  else None

let sign x = if Float.sign_bit x then "-" else ""

let to_string ~f32 x =
  match special x with
  | Some s -> s
  | None when x = 0.0 -> sign x ^ "0.0"
  | None ->
      let digits, k = shortest ~f32 (Float.abs x) in
      let n = String.length digits in
      sign x
      ^
      if k > -4 && k <= 16 then
        if k <= 0 then "0." ^ String.make (-k) '0' ^ digits
        else if n <= k then digits ^ String.make (k - n) '0' ^ ".0"
        else String.sub digits 0 k ^ "." ^ String.sub digits k (n - k)
      else
        let first = String.sub digits 0 1
        and rest = String.sub digits 1 (n - 1) in
        first
        ^ (if rest = "" then "" else "." ^ rest)
        ^ "e"
        ^ string_of_int (k - 1)

(* std.precision and std.scientific-notation *)

let fixed ~precision x =
  match special x with Some s -> s | None -> Printf.sprintf "%.*f" precision x

let scientific ~f32 ?precision x =
  match special x with
  | Some s -> s
  | None -> (
      match precision with
      | None when x = 0.0 -> sign x ^ "0e0"
      | None ->
          let digits, k = shortest ~f32 (Float.abs x) in
          let first = String.sub digits 0 1 in
          let rest = String.sub digits 1 (String.length digits - 1) in
          sign x ^ first
          ^ (if rest = "" then "" else "." ^ rest)
          ^ "e"
          ^ string_of_int (k - 1)
      | Some p ->
          let s = Printf.sprintf "%.*e" p x in
          let i = String.index s 'e' in
          String.sub s 0 i ^ "e"
          ^ string_of_int
              (int_of_string (String.sub s (i + 1) (String.length s - i - 1))))

(* numbers.conversions *)
let to_int (k : Ints.kind) x =
  if not (Float.is_finite x) then None
  else
    let t = Float.trunc x in
    let top = Float.ldexp 1.0 (if k.signed then k.bits - 1 else k.bits) in
    let bottom = if k.signed then -.top else 0.0 in
    if t < bottom || t >= top then None
    else if t >= Float.ldexp 1.0 63 then
      Some (Int64.add (Int64.of_float (t -. Float.ldexp 1.0 63)) Int64.min_int)
    else Some (Int64.of_float t)

(* std.floats: IEEE 754-2019 minimum and maximum. *)
let minimum a b =
  if Float.is_nan a || Float.is_nan b then Float.nan
  else if a = 0.0 && b = 0.0 then if Float.sign_bit a then a else b
  else Float.min a b

let maximum a b =
  if Float.is_nan a || Float.is_nan b then Float.nan
  else if a = 0.0 && b = 0.0 then if Float.sign_bit a then b else a
  else Float.max a b

(* traits.floats: every NaN equals every other and exceeds every other
   value, and -0.0 is less than 0.0. *)
let total_compare a b =
  match (Float.is_nan a, Float.is_nan b) with
  | true, true -> 0
  | true, false -> 1
  | false, true -> -1
  | false, false ->
      if a < b then -1
      else if a > b then 1
      else compare (Float.sign_bit b) (Float.sign_bit a)

(* numbers.parsing *)
let parse ~f32 s =
  let n = String.length s in
  let i = ref (if n > 0 && s.[0] = '-' then 1 else 0) in
  let digits () =
    let start = !i in
    while !i < n && s.[!i] >= '0' && s.[!i] <= '9' do
      incr i
    done;
    !i > start
  in
  let ok =
    digits ()
    && (if !i < n && s.[!i] = '.' then (
          incr i;
          digits ())
        else true)
    && (if !i < n && (s.[!i] = 'e' || s.[!i] = 'E') then (
          incr i;
          if !i < n && (s.[!i] = '+' || s.[!i] = '-') then incr i;
          digits ())
        else true)
    && !i = n
  in
  if not ok then None
  else
    let x = if f32 then f32_of_decimal s else float_of_string s in
    if Float.abs x = Float.infinity then None else Some x
