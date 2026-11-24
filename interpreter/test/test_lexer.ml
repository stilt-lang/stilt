(* Tests of the lexer against lexical.tokens. Each test prints the tokens of a source
   text on one line, or the diagnostic it produces. *)

open Stilt

let show text =
  match Lexer.tokenize ~file:"t.lt" text with
  | { error = Some diagnostic; _ } ->
      print_endline (Diagnostic.to_string diagnostic)
  | { tokens; _ } ->
      tokens
      |> List.map (fun ({ token; _ } : Lexer.token) -> Token.to_string token)
      |> String.concat " " |> print_endline

let%expect_test "integer literals" =
  show "0 7 1_000 0xFf 0o17 0b1010 0x_1";
  [%expect {| t.lt:1:30: E0004: a base prefix must be followed by a digit |}];
  show "0 7 1_000 0xFf 0o17 0b1010";
  [%expect {| INT 0 INT 7 INT 1000 INT 0xFf INT 0o17 INT 0b1010 EOF |}];
  show "1__0";
  [%expect {| t.lt:1:2: E0004: `_` must sit between two digits |}];
  show "1_";
  [%expect {| t.lt:1:2: E0004: `_` must sit between two digits |}];
  show "007";
  [%expect {| t.lt:1:1: E0004: a decimal literal can't have a leading zero |}];
  show "0X1";
  [%expect
    {| t.lt:1:2: E0004: a number literal can't be followed directly by a letter, a digit or `_` |}];
  show "0x";
  [%expect {| t.lt:1:3: E0004: a base prefix must be followed by a digit |}];
  show "10u8";
  [%expect
    {| t.lt:1:3: E0004: a number literal can't be followed directly by a letter, a digit or `_` |}];
  show "0b102";
  [%expect
    {| t.lt:1:5: E0004: a number literal can't be followed directly by a letter, a digit or `_` |}]

let%expect_test "float literals" =
  show "0.5 1.25 1e9 1E9 2.5e-3 1e+05 1_0.0_1";
  [%expect
    {| FLOAT 0.5 FLOAT 1.25 FLOAT 1e9 FLOAT 1E9 FLOAT 2.5e-3 FLOAT 1e+05 FLOAT 10.01 EOF |}];
  show "00.5";
  [%expect {| t.lt:1:1: E0004: a decimal literal can't have a leading zero |}];
  show "1e";
  [%expect
    {| t.lt:1:2: E0004: a number literal can't be followed directly by a letter, a digit or `_` |}];
  show "1e1_0";
  [%expect
    {| t.lt:1:4: E0004: a number literal can't be followed directly by a letter, a digit or `_` |}];
  show "1. .5 1.e5";
  [%expect {| INT 1 . . INT 5 INT 1 . LIDENT e5 EOF |}]

let%expect_test "digits after a dot" =
  show "t.0.1 0..n 1..=5 x.1.5";
  [%expect
    {| LIDENT t . INT 0 . INT 1 INT 0 .. LIDENT n INT 1 ..= INT 5 LIDENT x . INT 1 . INT 5 EOF |}];
  show "t.1e3";
  [%expect
    {| t.lt:1:4: E0004: a number literal can't be followed directly by a letter, a digit or `_` |}];
  show "t. 0.5";
  [%expect {| LIDENT t . FLOAT 0.5 EOF |}];
  show "t?.0.1";
  [%expect {| LIDENT t ? . INT 0 . INT 1 EOF |}]

(* types.hole-before-dot: [?.] is a hole, then a [.]. *)
let%expect_test "a hole before a dot" =
  show "a?.b ?..3 ?..=3";
  [%expect {| LIDENT a ? . LIDENT b ? .. INT 3 ? ..= INT 3 EOF |}]

let%expect_test "strings and escapes" =
  show {|"" "a b" "\n\t\r\0\\\"\{" "\u{41}\u{1F600}" "}"|};
  [%expect
    {| STRING "" STRING "a b" STRING "\n\t\r\000\\\"{" STRING "A\240\159\152\128" STRING "}" EOF |}];
  show {|"\q"|};
  [%expect {| t.lt:1:2: E0006: invalid escape |}];
  show {|"\u{}"|};
  [%expect {| t.lt:1:2: E0006: `\u{…}` takes 1 to 6 hexadecimal digits |}];
  show {|"\u{1234567}"|};
  [%expect {| t.lt:1:2: E0006: `\u{…}` takes 1 to 6 hexadecimal digits |}];
  show {|"\u{D800}"|};
  [%expect {| t.lt:1:2: E0006: `\u{…}` must name a Unicode scalar value |}];
  show "x = \"abc\ndef\"";
  [%expect {| t.lt:1:5: E0005: unterminated string literal |}]

let%expect_test "interpolation" =
  show {|"a{x}b{y:>5}c"|};
  [%expect
    {| STRING_HEAD "a" LIDENT x STRING_MID "b" LIDENT y FORMAT ">5" STRING_TAIL "c" EOF |}];
  show {|"{m["k"]:.2} {f({a})}"|};
  [%expect
    {| STRING_HEAD "" LIDENT m [ STRING "k" ] FORMAT ".2" STRING_MID " " LIDENT f ( { LIDENT a } ) STRING_TAIL "" EOF |}];
  show {|"{"{1}"}"|};
  [%expect
    {| STRING_HEAD "" STRING_HEAD "" INT 1 STRING_TAIL "" STRING_TAIL "" EOF |}];
  show {|"{x"|};
  [%expect {| t.lt:1:4: E0005: unterminated string literal |}];
  show "\"{x\n}\"";
  [%expect {| t.lt:1:1: E0005: unterminated string literal |}]

let%expect_test "format specs" =
  let spec s = show (Printf.sprintf {|"{x:%s}"|} s) in
  List.iter spec
    [
      "";
      "<";
      "*^";
      "<<";
      "é>8";
      "8";
      ".2";
      "0>8.3";
      "x";
      "X";
      "o";
      "b";
      "e";
      ">10.4e";
    ];
  [%expect
    {|
    STRING_HEAD "" LIDENT x FORMAT "" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "<" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "*^" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "<<" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "\195\169>8" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "8" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT ".2" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "0>8.3" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "x" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "X" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "o" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "b" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT "e" STRING_TAIL "" EOF
    STRING_HEAD "" LIDENT x FORMAT ">10.4e" STRING_TAIL "" EOF
    |}];
  List.iter spec [ "{<5"; "."; "5x2"; "xx"; "<<<"; "d"; "08" ];
  [%expect
    {|
    t.lt:1:4: E0007: `{<5` is not a format spec
    t.lt:1:4: E0007: `.` is not a format spec
    t.lt:1:4: E0007: `5x2` is not a format spec
    t.lt:1:4: E0007: `xx` is not a format spec
    t.lt:1:4: E0007: `<<<` is not a format spec
    t.lt:1:4: E0007: `d` is not a format spec
    t.lt:1:4: E0007: `08` is not a format spec
    |}]

let%expect_test "identifiers, keywords and case" =
  show "main Order _ _x _X x_1 str fn Self self with because io";
  [%expect
    {| LIDENT main UIDENT Order _ LIDENT _x UIDENT _X LIDENT x_1 LIDENT str fn Self self with LIDENT because LIDENT io EOF |}];
  (* meta.staging-annotations: [comptime] is a keyword, which a staging annotation
     writes, and c.unsafe-because and c.without-unsafe: so is [unsafe], which a block and a
     limit write. *)
  show "comptime when unsafe as dyn move mut ref static";
  [%expect
    {| comptime when unsafe LIDENT as LIDENT dyn LIDENT move LIDENT mut LIDENT ref LIDENT static EOF |}];
  show "__";
  [%expect {| t.lt:1:1: E0003: `__` has no letter |}];
  show "_1";
  [%expect {| t.lt:1:1: E0003: `_1` has no letter |}]

let%expect_test "operators, by maximal munch" =
  show "+%= -% *%= <<= >>= ..= == != <= >= && || << >> -> => | ? @ $ ' #";
  [%expect
    {| +%= -% *%= <<= >>= ..= == != <= >= && || << >> -> => | ? @ $ ' # EOF |}];
  show "a;b;;c";
  [%expect {| LIDENT a SEP LIDENT b SEP LIDENT c EOF |}];
  show "x ~ y";
  [%expect {| t.lt:1:3: E0002: unexpected character `~` |}];
  show "let é = 1";
  [%expect {| t.lt:1:5: E0002: unexpected character U+00E9 |}]

let%expect_test "comments" =
  let comments text =
    match Lexer.tokenize ~file:"t.lt" text with
    | { error = Some diagnostic; _ } ->
        print_endline (Diagnostic.to_string diagnostic)
    | { comments; _ } ->
        List.iter
          (fun ({ text; doc; line; col } : Lexer.comment) ->
            Printf.printf "%d:%d doc=%b %S\n" line col doc text)
          comments
  in
  comments "// a\nx /// b\n//~ ERROR E0001\n////c";
  [%expect
    {|
    1:1 doc=false " a"
    2:3 doc=true " b"
    3:1 doc=false "~ ERROR E0001"
    4:1 doc=true "/c"
    |}]

let%expect_test "source text" =
  show "\xEF\xBB\xBFx";
  [%expect
    {| t.lt:1:1: E0001: a source file can't begin with a byte-order mark |}];
  show "a\r\nb";
  [%expect {| LIDENT a SEP LIDENT b EOF |}];
  show "a\rb";
  [%expect
    {| t.lt:1:2: E0001: a carriage return must be followed by a newline |}];
  show "a\n\xFFb";
  [%expect {| t.lt:2:1: E0001: the file isn't valid UTF-8 |}]

let%expect_test "positions count Unicode scalar values" =
  match Lexer.tokenize ~file:"t.lt" "\"héllo\" x\n\ty" with
  | { error = Some diagnostic; _ } ->
      print_endline (Diagnostic.to_string diagnostic)
  | { tokens; _ } ->
      List.iter
        (fun ({ token; line; col } : Lexer.token) ->
          Printf.printf "%d:%d %s\n" line col (Token.to_string token))
        tokens;
      [%expect
        {|
        1:1 STRING "h\195\169llo"
        1:9 LIDENT x
        1:9 SEP
        2:2 LIDENT y
        2:3 EOF
        |}]

let%expect_test "terminators after each listed token" =
  List.iter show
    [
      "a\nb";
      "1\nb";
      "1.5\nb";
      "\"s\"\nb";
      "\"{x}\"\nb";
      "true\nb";
      "false\nb";
      "self\nb";
      "Self\nb";
      "return\nb";
      "break\nb";
      "continue\nb";
      "f()\nb";
      "xs[0]\nb";
      "{}\nb";
      "?\nb";
      "List<str>\nb";
      "List<List<str>>\nb";
      "-> str\nb";
    ];
  [%expect
    {|
    LIDENT a SEP LIDENT b EOF
    INT 1 SEP LIDENT b EOF
    FLOAT 1.5 SEP LIDENT b EOF
    STRING "s" SEP LIDENT b EOF
    STRING_HEAD "" LIDENT x STRING_TAIL "" SEP LIDENT b EOF
    true SEP LIDENT b EOF
    false SEP LIDENT b EOF
    self SEP LIDENT b EOF
    Self SEP LIDENT b EOF
    return SEP LIDENT b EOF
    break SEP LIDENT b EOF
    continue SEP LIDENT b EOF
    LIDENT f ( ) SEP LIDENT b EOF
    LIDENT xs [ INT 0 ] SEP LIDENT b EOF
    { } SEP LIDENT b EOF
    ? SEP LIDENT b EOF
    UIDENT List < LIDENT str > SEP LIDENT b EOF
    UIDENT List < UIDENT List < LIDENT str >> SEP LIDENT b EOF
    -> LIDENT str SEP LIDENT b EOF
    |}]

let%expect_test "no terminator after other tokens" =
  List.iter show
    [ "a +\nb"; "a =\nb"; "a,\nb"; "f(\nb)"; "a ==\nb"; "x =>\ny"; "fn\nf" ];
  [%expect
    {|
    LIDENT a + LIDENT b EOF
    LIDENT a = LIDENT b EOF
    LIDENT a , LIDENT b EOF
    LIDENT f ( LIDENT b ) EOF
    LIDENT a == LIDENT b EOF
    LIDENT x => LIDENT y EOF
    fn LIDENT f EOF
    |}]

let%expect_test "continuation lines" =
  List.iter show
    [
      "xs\n.len()";
      "xs\n// note\n\n.len()";
      "if c { a }\nelse { b }";
      "try f()\ncatch _ => 0";
      "type T =\n  | A\n  | B";
      "a\n..b";
      "a\n|| b";
      "o\n?.len()";
    ];
  [%expect
    {|
    LIDENT xs . LIDENT len ( ) EOF
    LIDENT xs . LIDENT len ( ) EOF
    if LIDENT c { LIDENT a } else { LIDENT b } EOF
    try LIDENT f ( ) catch _ => INT 0 EOF
    type UIDENT T = | UIDENT A | UIDENT B EOF
    LIDENT a SEP .. LIDENT b EOF
    LIDENT a SEP || LIDENT b EOF
    LIDENT o SEP ? . LIDENT len ( ) EOF
    |}]

let%expect_test "brackets" =
  List.iter show
    [
      "f(a\nb)";
      "[a\nb]";
      "xs.map(|l| {\n  let a = f(l)\n  g(a)\n})";
      "{\n  (a\n  b)\n}";
      "type R = {\n  a: i64,\n  b: str\n}";
      "R {\n  a: 1\n  b: 2\n}";
    ];
  [%expect
    {|
    LIDENT f ( LIDENT a LIDENT b ) EOF
    [ LIDENT a LIDENT b ] EOF
    LIDENT xs . LIDENT map ( | LIDENT l | { let LIDENT a = LIDENT f ( LIDENT l ) SEP LIDENT g ( LIDENT a ) } ) EOF
    { ( LIDENT a LIDENT b ) } EOF
    type UIDENT R = { LIDENT a : LIDENT i64 , LIDENT b : LIDENT str } EOF
    UIDENT R { LIDENT a : INT 1 SEP LIDENT b : INT 2 } EOF
    |}]

let%expect_test "attributes and separators" =
  List.iter show
    [
      "@derive_json\ntype User = {}";
      "@sql(x)\nfn f()";
      "{ ; a ;; b ; }";
      "; a\n\n\nb ;";
      "use std.cli; use std.fs";
    ];
  [%expect
    {|
    @ LIDENT derive_json type UIDENT User = { } EOF
    @ LIDENT sql ( LIDENT x ) fn LIDENT f ( ) EOF
    { LIDENT a SEP LIDENT b } EOF
    LIDENT a SEP LIDENT b EOF
    use LIDENT std . LIDENT cli SEP use LIDENT std . LIDENT fs EOF
    |}]

let%expect_test "the tokens before an error" =
  let prefix text =
    let { Lexer.tokens; error; _ } = Lexer.tokenize ~file:"t.lt" text in
    tokens
    |> List.map (fun ({ token; _ } : Lexer.token) -> Token.to_string token)
    |> String.concat " " |> print_endline;
    Option.iter (fun d -> print_endline (Diagnostic.to_string d)) error
  in
  prefix "let x = a\n007";
  [%expect
    {|
    let LIDENT x = LIDENT a
    t.lt:2:1: E0004: a decimal literal can't have a leading zero
    |}];
  prefix "f(a, \"{b\" c";
  [%expect
    {|
    LIDENT f ( LIDENT a , STRING_HEAD "" LIDENT b
    t.lt:1:9: E0005: unterminated string literal
    |}];
  prefix "a\n\xFFb";
  [%expect {| t.lt:2:1: E0001: the file isn't valid UTF-8 |}]

let%expect_test "a start position for text inside a file" =
  match Lexer.tokenize ~line:7 ~col:12 ~file:"t.lt" "f(x) == 1 // c" with
  | { error = Some diagnostic; _ } ->
      print_endline (Diagnostic.to_string diagnostic)
  | { tokens; comments; _ } ->
      List.iter
        (fun ({ token; line; col } : Lexer.token) ->
          Printf.printf "%d:%d %s\n" line col (Token.to_string token))
        tokens;
      List.iter
        (fun ({ line; col; _ } : Lexer.comment) ->
          Printf.printf "comment %d:%d\n" line col)
        comments;
      [%expect
        {|
        7:12 LIDENT f
        7:13 (
        7:14 LIDENT x
        7:15 )
        7:17 ==
        7:20 INT 1
        7:21 EOF
        comment 7:22
        |}]
