(* Tests format specs: their grammar, and how they lay out the values that a
   string interpolates (std.width-fill-and-alignment, std.precision, std.integer-kinds, std.scientific-notation and std.format-special-values; lexical.format-specs). *)

open Stilt
open Numbers

(* std.width-fill-and-alignment, std.precision, std.integer-kinds, std.scientific-notation and std.format-special-values *)
let%expect_test "format specs" =
  let spec s number shown =
    let spec = Option.get (Format_spec.parse s) in
    print_endline ("[" ^ Format_spec.apply spec number shown ^ "]")
  in
  let i8 v = Format_spec.Int (kind "i8", v)
  and f x = Format_spec.Float (false, x) in
  spec ">6" (i8 127L) "127";
  spec "6" (i8 127L) "127";
  spec "6" Not_a_number "ana";
  spec "^5" Not_a_number "ab";
  spec "*^4" (i8 7L) "7";
  spec "é>4" Not_a_number "ü";
  spec "x" (i8 (-1L)) "-1";
  spec "0>8b" (i8 5L) "5";
  spec "X" (i8 (-128L)) "-128";
  spec "X" (i8 (-1L)) "-1";
  spec "o" (i8 8L) "8";
  spec ".2" (f 3.14159) "3.14159";
  spec ".2e" (f 12345.0) "12345.0";
  spec "e" (f 12345.0) "12345.0";
  spec "8.2" (f Float.nan) "nan";
  spec "<6e" (f Float.neg_infinity) "-inf";
  spec "2" Not_a_number "long";
  spec "4" Not_a_number "ana";
  [%expect
    {|
    [   127]
    [   127]
    [ana   ]
    [ ab  ]
    [*7**]
    [éééü]
    [ff]
    [00000101]
    [80]
    [FF]
    [10]
    [3.14]
    [1.23e4]
    [1.2345e4]
    [     nan]
    [-inf  ]
    [long]
    [ana ]
    |}]

(* lexical.format-specs *)
let%expect_test "the grammar of specs" =
  List.iter
    (fun s -> Printf.printf "%b " (Option.is_some (Format_spec.parse s)))
    [
      "";
      "{<5";
      "{";
      "<<5";
      "é^9.3e";
      "65535";
      "65536";
      ".65535";
      ".65536";
      "99999999999999999999";
      "5.";
      "x5";
      "5xx";
      "d";
      "0";
      "05";
      "00";
      ".0";
      ".05";
      "0>5";
      "09";
      "0.5";
      "0x";
      "<";
    ];
  [%expect
    {| true false false true true true false true false false false false false false true false false true false true false true true true |}]
