(* Tests the integer operations the evaluator builds on: arithmetic at every
   width, conversions, parsing and printing (numbers.numeric-types and numbers.conversions, std.integers). Rule numbers
   refer to the Reference unless a comment names another record. *)

open Stilt
open Numbers

(* Prints the result of an integer operation of kind [k], or its panic. *)
let int k f =
  match f () with
  | v -> print_endline (Ints.to_string (kind k) v)
  | exception Fault.Panic (panic, _) -> print_endline ("panic: " ^ panic)

let ints k f cases =
  List.iter (fun (a, b) -> int k (fun () -> f (kind k) a b)) cases

(* numbers.integer-panics *)
let%expect_test "overflow at every width" =
  ints "i8" Ints.add [ (127L, 1L); (-128L, -1L); (100L, 27L) ];
  ints "u8" Ints.sub [ (0L, 1L); (255L, 255L) ];
  ints "i64" Ints.mul
    [
      (Int64.min_int, -1L);
      (Int64.max_int, 2L);
      (4294967296L, 2147483648L);
      (-4294967296L, 2147483648L);
    ];
  (* [u64] values from 2^63 on are held by their bit pattern. *)
  ints "u64" Ints.mul [ (4294967296L, 4294967296L); (4294967295L, 4294967297L) ];
  ints "u32" Ints.mul [ (65536L, 65536L); (65535L, 65537L) ];
  [%expect
    {|
    panic: overflow
    panic: overflow
    127
    panic: overflow
    0
    panic: overflow
    panic: overflow
    panic: overflow
    -9223372036854775808
    panic: overflow
    18446744073709551615
    panic: overflow
    4294967295
    |}]

(* numbers.integer-panics and numbers.division-and-remainder *)
let%expect_test "division and remainder" =
  ints "i64" Ints.div [ (Int64.min_int, -1L); (7L, 0L); (-7L, 2L); (7L, -2L) ];
  ints "i64" Ints.rem [ (Int64.min_int, -1L); (7L, 0L); (-7L, 2L); (7L, -2L) ];
  ints "u64" Ints.div [ (-1L, 2L) ];
  ints "u64" Ints.rem [ (-1L, 10L) ];
  int "i8" (fun () -> Ints.neg (kind "i8") (-128L));
  int "i64" (fun () -> Ints.neg (kind "i64") Int64.min_int);
  [%expect
    {|
    panic: overflow
    panic: divide-by-zero
    -3
    -3
    panic: overflow
    panic: divide-by-zero
    -1
    1
    9223372036854775807
    5
    panic: overflow
    panic: overflow
    |}]

(* numbers.wrapping and numbers.shifts *)
let%expect_test "wrapping and shifts" =
  ints "u8" Ints.add_wrap [ (200L, 100L) ];
  ints "i8" Ints.sub_wrap [ (-128L, 1L) ];
  ints "i64" Ints.mul_wrap [ (Int64.max_int, 2L) ];
  let by = kind "i64" in
  ints "i8" (Ints.shift_left ~by) [ (1L, 7L); (1L, 8L); (1L, -1L) ];
  ints "u8" (Ints.shift_left ~by) [ (255L, 1L) ];
  ints "u64" (Ints.shift_left ~by:(kind "u64")) [ (1L, -1L) ];
  ints "u8" (Ints.shift_right ~by:(kind "u8")) [ (128L, 7L) ];
  ints "i8" (Ints.shift_right ~by:(kind "i8")) [ (-128L, 7L) ];
  (* An amount of an unsigned type is never negative, and is too large from
     2^63 on, which its bit pattern holds. *)
  ints "i64" (Ints.shift_left ~by:(kind "u8")) [ (1L, 63L); (1L, 200L) ];
  ints "u8" (Ints.shift_right ~by:(kind "u64")) [ (128L, Int64.min_int) ];
  [%expect
    {|
    44
    127
    -2
    -128
    panic: overflow
    panic: overflow
    254
    panic: overflow
    1
    -1
    -9223372036854775808
    panic: overflow
    panic: overflow
    |}]

(* numbers.conversions and numbers.wrapping-conversions *)
let%expect_test "integer conversions" =
  let lossless (a, b) =
    Printf.printf "%b " (Ints.lossless ~from:(kind a) (kind b))
  in
  List.iter lossless
    [
      ("i8", "i16"); ("u8", "i8"); ("i64", "u64"); ("u32", "i64"); ("u64", "i64");
    ];
  print_newline ();
  let fits (a, b, v) =
    Printf.printf "%b " (Ints.fits ~from:(kind a) (kind b) v)
  in
  List.iter fits
    [
      ("u64", "i64", -1L);
      ("i64", "u64", -1L);
      ("i64", "u8", 255L);
      ("i64", "u8", 256L);
      ("u64", "u64", -1L);
    ];
  print_newline ();
  int "i8" (fun () -> Ints.wrap (kind "i8") 255L);
  int "u64" (fun () -> Ints.wrap (kind "u64") (-1L));
  [%expect
    {|
    true false false true false
    false false true false true
    -1
    18446744073709551615
    |}]

(* numbers.conversions: integers round to nearest, ties to even, in one step. *)
let%expect_test "integers to floats" =
  let exact x = Printf.printf "%.0f\n" x in
  exact (Ints.to_float (kind "u64") (-1L));
  exact (Ints.to_float (kind "i64") Int64.max_int);
  (* 2^63 + 1025 rounds up, and 2^63 + 1024 is a tie, which rounds to 2^63. *)
  exact (Ints.to_float (kind "u64") (Int64.add Int64.min_int 1025L));
  exact (Ints.to_float (kind "u64") (Int64.add Int64.min_int 1024L));
  exact (Ints.to_f32 (kind "i64") 16777217L);
  exact (Ints.to_f32 (kind "i64") 16777219L);
  (* 2^62 + 2^38 + 1 is just above the midpoint between two binary32 values,
     which rounding through binary64 would lose. *)
  exact (Ints.to_f32 (kind "i64") 4611686293305294849L);
  [%expect
    {|
    18446744073709551616
    9223372036854775808
    9223372036854777856
    9223372036854775808
    16777216
    16777220
    4611686568183201792
    |}]

(* numbers.parsing *)
let%expect_test "parsing integers" =
  let parse k s =
    option
      (fun v -> print_endline (Ints.to_string (kind k) v))
      (Ints.parse (kind k) s)
  in
  List.iter (parse "i64")
    [ "007"; "-0"; "+5"; ""; "-"; "99999999999999999999999"; " 1" ];
  List.iter (parse "i8") [ "-128"; "128" ];
  List.iter (parse "u8") [ "-0"; "255" ];
  List.iter (parse "u64") [ "18446744073709551615"; "18446744073709551616" ];
  [%expect
    {|
    7
    0
    None
    None
    None
    None
    None
    -128
    None
    None
    255
    18446744073709551615
    None
    |}]

let%expect_test "integer literals" =
  List.iter
    (fun s -> print_endline (Ints.to_string (kind "u64") (Ints.of_literal s)))
    [ "0xFF"; "0b1010"; "0o777"; "18446744073709551615"; "0xffffffffffffffff" ];
  [%expect
    {|
    255
    10
    511
    18446744073709551615
    18446744073709551615
    |}]

(* std.integer-kinds *)
let%expect_test "integers in other bases" =
  let base k b upper v =
    print_endline (Ints.to_base (kind k) ~base:b ~upper v)
  in
  base "i8" 16 false (-1L);
  base "i8" 2 false (-128L);
  base "u64" 8 false (-1L);
  base "i64" 16 true 255L;
  base "i64" 2 false 0L;
  base "i16" 8 false (-2L);
  [%expect
    {|
    ff
    10000000
    1777777777777777777777
    FF
    0
    177776
    |}]

(* numbers.numeric-types: each type's name, sign and width, so its least and
   greatest values. *)
let%expect_test "every type's bounds" =
  List.iter
    (fun name ->
      let k = kind name in
      Printf.printf "%s %s %s\n" (Ints.name k)
        (Ints.to_string k (Ints.min_value k))
        (Ints.to_string k (Ints.max_value k)))
    Types.integer_types;
  [%expect
    {|
    i8 -128 127
    i16 -32768 32767
    i32 -2147483648 2147483647
    i64 -9223372036854775808 9223372036854775807
    u8 0 255
    u16 0 65535
    u32 0 4294967295
    u64 0 18446744073709551615
    |}]

(* numbers.integer-panics: the 64-bit sums and differences, whose overflow no
   wider type holds, and an unsigned `-`, which overflows but on 0
   (numbers.unsigned-negation). *)
let%expect_test "64-bit sums and differences" =
  ints "i64" Ints.add
    [ (Int64.max_int, 1L); (Int64.min_int, -1L); (Int64.max_int, -1L) ];
  ints "i64" Ints.sub
    [ (Int64.min_int, 1L); (Int64.max_int, -1L); (Int64.min_int, -1L) ];
  ints "u64" Ints.add [ (-1L, 1L); (Int64.max_int, 1L) ];
  ints "u64" Ints.sub [ (0L, 1L); (Int64.min_int, 1L) ];
  ints "i32" Ints.add [ (2147483647L, 1L); (2147483646L, 1L) ];
  ints "u16" Ints.add [ (65535L, 1L); (65534L, 1L) ];
  int "u8" (fun () -> Ints.neg (kind "u8") 0L);
  int "u8" (fun () -> Ints.neg (kind "u8") 1L);
  int "i32" (fun () -> Ints.neg (kind "i32") 5L);
  [%expect
    {|
    panic: overflow
    panic: overflow
    9223372036854775806
    panic: overflow
    panic: overflow
    -9223372036854775807
    panic: overflow
    9223372036854775808
    panic: overflow
    9223372036854775807
    panic: overflow
    2147483647
    panic: overflow
    65535
    0
    panic: overflow
    -5
    |}]

(* numbers.comparisons: an unsigned type compares the values its bit patterns
   hold, so 2^63 is above 1. *)
let%expect_test "unsigned comparison" =
  Printf.printf "%d %d\n"
    (Ints.compare (kind "u64") Int64.min_int 1L)
    (Ints.compare (kind "i64") Int64.min_int 1L);
  [%expect {| 1 -1 |}]

(* numbers.conversions: a value fits a type within its bounds, at both ends. *)
let%expect_test "conversions at their edges" =
  List.iter
    (fun (a, b, v) -> Printf.printf "%b " (Ints.fits ~from:(kind a) (kind b) v))
    [
      ("i64", "i8", -128L);
      ("i64", "i8", -129L);
      ("i64", "i8", 127L);
      ("i64", "i8", 128L);
      ("i64", "u64", 0L);
      ("i8", "u64", -1L);
      ("u64", "i64", Int64.max_int);
    ];
  print_newline ();
  [%expect {| true false true false true false true |}]

(* numbers.integer-panics: an unsigned sum with 0 and a difference of equal
   values don't overflow. *)
let%expect_test "unsigned sums and differences at their bounds" =
  ints "u64" Ints.add [ (5L, 0L); (-1L, 0L) ];
  ints "u64" Ints.sub [ (5L, 5L); (-1L, -1L) ];
  [%expect {|
    5
    18446744073709551615
    0
    0
    |}]

(* lexical.integer-literals: a literal's digits in its base. *)
let%expect_test "literals in every base" =
  List.iter
    (fun s -> print_endline (Int64.to_string (Ints.of_literal s)))
    [ "19"; "0x5"; "0x1f"; "0o17"; "0b101"; "7" ];
  [%expect {|
    19
    5
    31
    15
    5
    7
    |}]

(* numbers.parsing: a signed type's least value parses, one below it doesn't. *)
let%expect_test "parsing at a signed type's least value" =
  List.iter
    (fun s ->
      print_endline
        (match Ints.parse (kind "i64") s with
        | Some v -> Int64.to_string v
        | None -> "None"))
    [ "-9223372036854775808"; "-9223372036854775809"; "-9223372036854775810" ];
  [%expect {|
    -9223372036854775808
    None
    None
    |}]
