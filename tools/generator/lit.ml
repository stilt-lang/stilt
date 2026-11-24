(* Literals, as lexical.integer-literals, lexical.float-literals and lexical.string-literals writes them. Values near the ends of each range are
   more likely than the rest, since that is where implementations disagree. *)

open Ty

(* The bounds of an integer type, as decimal text. *)
let bounds k =
  match k with
  | I8 -> ("-128", "127")
  | I16 -> ("-32768", "32767")
  | I32 -> ("-2147483648", "2147483647")
  | I64 -> ("-9223372036854775808", "9223372036854775807")
  | U8 -> ("0", "255")
  | U16 -> ("0", "65535")
  | U32 -> ("0", "4294967295")
  | U64 -> ("0", "18446744073709551615")

(* A value of [k] from all of its range, as decimal text. *)
let anywhere r k =
  let n = Pick.bits64 r in
  let width = bits k in
  if width = 64 then
    if signed k then Printf.sprintf "%Ld" n else Printf.sprintf "%Lu" n
  else
    let low = Int64.(logand n (sub (shift_left 1L width) 1L)) in
    let value =
      if signed k && Int64.(compare low (shift_left 1L (width - 1))) >= 0 then
        Int64.(sub low (shift_left 1L width))
      else low
    in
    Int64.to_string value

let int r k =
  let small = if signed k then Pick.between r (-9) 9 else Pick.between r 0 9 in
  let lo, hi = bounds k in
  Pick.weighted r
    [ (6, string_of_int small); (1, lo); (1, hi); (2, anywhere r k) ]

(* A finite float that every float type can hold. *)
let float r =
  let digits () = string_of_int (Pick.between r 0 999) in
  let mantissa = digits () ^ "." ^ digits () in
  let text =
    Pick.weighted r
      [
        (5, mantissa);
        (2, mantissa ^ "e" ^ string_of_int (Pick.between r (-20) 20));
        (1, "0.0");
        (1, "1.0");
      ]
  in
  if Pick.chance r 0.3 then "-" ^ text else text

(* The text inside a string literal, ASCII only, with the escapes of lexical.escapes. *)
let string_body r =
  let piece () =
    Pick.weighted r
      [
        (12, String.make 1 (Char.chr (Pick.between r 97 122)));
        (2, " ");
        (2, ",");
        (2, string_of_int (Pick.below r 10));
        (1, "\\n");
        (1, "\\t");
        (1, "\\\"");
        (1, "\\\\");
        (1, "\\{");
        (1, "}");
      ]
  in
  String.concat "" (Pick.times (Pick.between r 0 6) piece)

let string r = "\"" ^ string_body r ^ "\""
