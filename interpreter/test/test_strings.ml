(* Tests the native operations on strings (std.str-search and std.str-splitting). *)

open Stilt

(* Each string in angle brackets, with carriage returns shown as [\r], or
   [none] for no strings. *)
let strings = function
  | [] -> print_endline "none"
  | xs ->
      let show x =
        "<" ^ String.concat "\\r" (String.split_on_char '\r' x) ^ ">"
      in
      print_endline (String.concat "|" (List.map show xs))

(* std.str-splitting *)
let%expect_test "splitting" =
  strings (Strings.split "a,,b" ",");
  strings (Strings.split "" ",");
  strings (Strings.split "a--b--" "--");
  strings (Strings.split "héj" "");
  strings (Strings.split "" "");
  [%expect
    {|
    <a>|<>|<b>
    <>
    <a>|<b>|<>
    <h>|<é>|<j>
    none
    |}];
  strings (Strings.lines "a\r\nb\n");
  strings (Strings.lines "");
  strings (Strings.lines "x\n\n");
  strings (Strings.lines "\n");
  strings (Strings.lines "a\r\r\nb");
  [%expect {|
    <a>|<b>
    none
    <x>|<>
    <>
    <a\r>|<b>
    |}]

let%expect_test "searching and trimming" =
  let find s sub =
    print_endline
      (Option.fold ~none:"None" ~some:string_of_int (Strings.find s sub))
  in
  find "hello" "l";
  find "hello" "";
  find "" "";
  find "hello" "lo!";
  find "aab" "ab";
  [%expect {|
    2
    0
    0
    None
    1
    |}];
  (* A substring that would run past the end doesn't occur there. *)
  Printf.printf "%b %b %b\n"
    (Strings.occurs_at "abc" "bc" 1)
    (Strings.occurs_at "abc" "cd" 2)
    (Strings.occurs_at "abc" "" 3);
  [%expect {| true false true |}];
  print_endline ("<" ^ Strings.trim " \t a b\n\012" ^ ">");
  print_endline ("<" ^ String.escaped (Strings.trim "\011x\011") ^ ">");
  print_endline ("<" ^ Strings.trim "   " ^ ">");
  [%expect {|
    <a b>
    <\011x\011>
    <>
    |}]

let%expect_test "replacing" =
  List.iter
    (fun (s, from, into) ->
      print_endline ("<" ^ Strings.replace s from into ^ ">"))
    [
      ("aaa", "a", "b");
      ("aaaa", "aa", "x");
      ("aaa", "aa", "x");
      ("ab", "", "-");
      ("", "", "-");
      ("é", "", ".");
      ("abc", "z", "y");
    ];
  [%expect
    {|
    <bbb>
    <xx>
    <xa>
    <-a-b->
    <->
    <.é.>
    <abc>
    |}]

let%expect_test "scalar values and boundaries" =
  strings (Strings.chars "aé€😀");
  List.iter
    (fun i -> Printf.printf "%b " (Strings.is_boundary "aé" i))
    [ 0; 1; 2; 3 ];
  [%expect {|
    <a>|<é>|<€>|<😀>
    true true false true
    |}]

(* std.code-points: each maximal subpart of an invalid sequence becomes one
   U+FFFD, written here as [?]. *)
let%expect_test "repairing UTF-8" =
  let repair s =
    print_endline
      (String.concat "?" (Strings.split (Strings.repair s) "\u{FFFD}"))
  in
  (* A truncated sequence, an overlong form, a surrogate, a value past
     U+10FFFF, a lone continuation byte, and a truncated four-byte sequence at
     the end. *)
  List.iter repair
    [
      "a\xe2\x82Ab";
      "\xc0\x80";
      "\xed\xa0\x80";
      "\xf4\x90\x80\x80";
      "x\x80y";
      "\xf0\x9f\x98";
    ];
  print_endline (Strings.repair "ok é");
  [%expect {|
    a?Ab
    ??
    ???
    ????
    x?y
    ?
    ok é
    |}]

(* std.show-names-and-escapes *)
let%expect_test "nested strings" =
  print_endline (Strings.quote "a\"b\\c\nd\te\rf\000g\027h\127i é");
  print_endline (Strings.quote "");
  [%expect {|
    "a\"b\\c\nd\te\rf\0g\u{1b}h\u{7f}i é"
    ""
    |}]
