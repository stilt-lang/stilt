(* Tests the float operations the evaluator builds on: printing, parsing,
   conversions and ordering (numbers.printing-floats and numbers.ieee-754, std.floats). Rule numbers refer to numbers.printing-floats and numbers.ieee-754
   unless a comment names another record. *)

open Stilt
open Numbers

let f64 x = print_endline (Floats.to_string ~f32:false x)
let f32 x = print_endline (Floats.to_string ~f32:true x)

(* numbers.printing-floats, with its examples first. *)
let%expect_test "shortest float output" =
  List.iter f64
    [
      1.0;
      0.1;
      123456.789;
      0.0001;
      0.00001;
      1.5e-7;
      1e16;
      1e15;
      0.1 +. 0.2;
      -2.5;
      Float.nan;
      Float.neg_infinity;
      -0.0;
    ];
  [%expect
    {|
    1.0
    0.1
    123456.789
    0.0001
    1e-5
    1.5e-7
    1e16
    1000000000000000.0
    0.30000000000000004
    -2.5
    nan
    -inf
    -0.0
    |}]

(* At a power of two the next value down is closer than the next one up, so
   fewer digits may not read back. *)
let%expect_test "float output at the edges of the range" =
  List.iter f64
    [
      5e-324;
      Float.max_float;
      2.2250738585072014e-308;
      9007199254740992.0;
      18014398509481984.0;
    ];
  [%expect
    {|
    5e-324
    1.7976931348623157e308
    2.2250738585072014e-308
    9007199254740992.0
    1.8014398509481984e16
    |}]

(* numbers.float-digits: an [f32] prints the shortest digits that read back as binary32. *)
let%expect_test "f32 output" =
  List.iter
    (fun x -> f32 (Floats.round32 x))
    [
      0.1; 16777216.0; 3.4028234663852886e38; 1.401298464324817e-45; 1.0 /. 3.0;
    ];
  [%expect
    {|
    0.1
    16777216.0
    3.4028235e38
    1e-45
    0.33333334
    |}]

(* numbers.float-literals and numbers.ieee-754: a decimal rounds to binary32 in one step. *)
let%expect_test "f32 literals" =
  List.iter
    (fun s -> f32 (Floats.f32_of_decimal s))
    [
      "16777217";
      "16777219";
      "1.000000059604644775390625";
      "1.00000005960464477539062500000001";
    ];
  [%expect {|
    16777216.0
    16777220.0
    1.0
    1.0000001
    |}]

(* numbers.parsing *)
let%expect_test "parsing floats" =
  List.iter
    (fun s -> option f64 (Floats.parse ~f32:false s))
    [
      "1.";
      ".5";
      "1e5";
      "1E+5";
      "-0";
      "inf";
      "nan";
      "1_0";
      " 1";
      "+1";
      "1e400";
      "1e-400";
    ];
  (* The midpoint between the largest [f32] and 2^128, then just below it. *)
  List.iter
    (fun s -> option f32 (Floats.parse ~f32:true s))
    [
      "340282356779733661637539395458142568448";
      "340282356779733661637539395458142568447";
    ];
  [%expect
    {|
    None
    None
    100000.0
    100000.0
    -0.0
    None
    None
    None
    None
    None
    None
    0.0
    None
    3.4028235e38
    |}]

(* numbers.conversions *)
let%expect_test "floats to integers" =
  let to_int k x =
    option
      (fun v -> print_endline (Ints.to_string (kind k) v))
      (Floats.to_int (kind k) x)
  in
  List.iter (to_int "i64")
    [
      7.9;
      -7.9;
      Float.nan;
      Float.infinity;
      9223372036854775808.0;
      -9223372036854775808.0;
    ];
  List.iter (to_int "u64") [ 18446744073709549568.0; 18446744073709551616.0 ];
  List.iter (to_int "u8") [ -0.5; 255.9; 256.0; -1.0 ];
  [%expect
    {|
    7
    -7
    None
    None
    None
    -9223372036854775808
    18446744073709549568
    None
    0
    255
    None
    None
    |}]

(* std.floats; traits.floats *)
let%expect_test "minimum, maximum and the total order" =
  List.iter f64
    [
      Floats.minimum 0.0 (-0.0);
      Floats.maximum (-0.0) 0.0;
      Floats.minimum Float.nan 1.0;
      Floats.maximum 1.0 Float.nan;
    ];
  List.iter
    (fun (a, b) -> Printf.printf "%d " (Floats.total_compare a b))
    [
      (-0.0, 0.0);
      (Float.nan, Float.infinity);
      (-.Float.nan, Float.nan);
      (-.Float.nan, 1.0);
    ];
  [%expect {|
    -0.0
    0.0
    nan
    nan
    -1 1 0 1
    |}]

(* std.precision and std.scientific-notation: digits round from the exact binary value. *)
let%expect_test "fixed and scientific notation" =
  List.iter
    (fun (p, x) -> print_endline (Floats.fixed ~precision:p x))
    [
      (2, 0.125);
      (2, 0.375);
      (2, 1.005);
      (0, 2.5);
      (0, 3.5);
      (1, -0.0);
      (1, 1e21);
      (0, 0.0);
    ];
  List.iter
    (fun (p, x) -> print_endline (Floats.scientific ~f32:false ?precision:p x))
    [
      (Some 2, 12345.0);
      (None, 12345.0);
      (None, 0.0);
      (Some 1, -0.0);
      (None, 1e-7);
      (Some 1, 125.0);
      (Some 1, 135.0);
      (Some 1, 9.99);
    ];
  print_endline (Floats.scientific ~f32:true (Floats.round32 0.1));
  [%expect
    {|
    0.12
    0.38
    1.00
    2
    4
    -0.0
    1000000000000000000000.0
    0
    1.23e4
    1.2345e4
    0e0
    -0.0e0
    1e-7
    1.2e2
    1.4e2
    1.0e1
    1e-1
    |}]

(* numbers.float-literals: an f32 literal rounds its exact decimal value to the
   nearest f32, ties to even. 2^24 + 1 lies halfway between 2^24 and 2^24 + 2,
   whose f64 is that midpoint too, so the decimal digits decide. *)
let%expect_test "f32 literals at a midpoint" =
  List.iter
    (fun s ->
      Printf.printf "%lx\n" (Int32.bits_of_float (Floats.f32_of_decimal s)))
    [
      "16777217";
      "16777217.000000001";
      "16777216.999999999";
      "-16777217.000000001";
      "-16777216.999999999";
    ];
  [%expect
    {|
    4b800000
    4b800001
    4b800000
    cb800001
    cb800000
    |}]

(* std.floats and traits.floats: the other orders of the operands, and values
   that aren't NaN or zero. *)
let%expect_test "minimum, maximum and the order of other values" =
  List.iter f64
    [
      Floats.minimum (-0.0) 0.0;
      Floats.maximum 0.0 (-0.0);
      Floats.minimum 1.0 2.0;
      Floats.maximum 1.0 2.0;
    ];
  List.iter
    (fun (a, b) -> Printf.printf "%d " (Floats.total_compare a b))
    [ (1.0, 2.0); (2.0, 1.0); (1.0, Float.nan); (0.0, -0.0); (1.5, 1.5) ];
  [%expect {|
    -0.0
    0.0
    1.0
    2.0
    -1 1 -1 1 0
    |}]

(* numbers.ieee-754: an f32 operation's result is rounded to f32, and an f64
   one's isn't. *)
let%expect_test "results rounded to their type" =
  f64 (Floats.result ~f32:true 0.1);
  f64 (Floats.result ~f32:false 0.1);
  [%expect {|
    0.10000000149011612
    0.1
    |}]

(* numbers.parsing: digits on both sides of the point. *)
let%expect_test "parsing fractions" =
  List.iter
    (fun s -> option f64 (Floats.parse ~f32:false s))
    [ "1.5"; "-2.25"; "0.125e1" ];
  [%expect {|
    1.5
    -2.25
    1.25
    |}]
