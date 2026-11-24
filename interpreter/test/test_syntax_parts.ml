(* Tests of reading a file a part at a time, as every command reads a file
   with a syntax error (errors.parts). Each test prints the items that the
   file's parts declare, those that declare only their name marked unknown,
   then the names of what the parts that break declare with an error, and the
   syntax error that each part reports, with the text it holds back. *)

open Stilt

let rec decl indent (d : Ast.decl Ast.node) =
  let unknown = if d.desc.unknown then ", unknown" else "" in
  match d.desc.kind with
  | Fn f ->
      Printf.printf "%sfn %s, %d parameters%s\n" indent f.name.desc
        (List.length f.params) unknown
  | Const c -> Printf.printf "%sconst %s%s\n" indent c.name.desc unknown
  | Type t -> Printf.printf "%stype %s%s\n" indent t.name.desc unknown
  | Trait t ->
      Printf.printf "%strait %s%s\n" indent t.name.desc unknown;
      List.iter (decl (indent ^ "  ")) t.members
  | Test (name, _) -> Printf.printf "%stest %S\n" indent name
  | Syntax s -> Printf.printf "%ssyntax %s%s\n" indent s.name.desc unknown
  | Effect e ->
      Printf.printf "%seffect %s, %d operations%s\n" indent e.name.desc
        (List.length e.ops) unknown
  | Macro f -> Printf.printf "%smacro %s%s\n" indent f.name.desc unknown

let read text =
  let r = Syntax_recovery.read ~file:"main.lt" text in
  if Option.is_some r.module_.header then print_endline "header";
  List.iter
    (fun (item : Ast.item) ->
      match item.desc with
      | Use _ -> print_endline "use"
      | Meta_use _ -> print_endline "meta use"
      | Decl d -> decl "" { desc = d; loc = item.loc }
      | Impl i ->
          print_endline "impl";
          List.iter (decl "  ") i.members)
    r.module_.items;
  List.iter
    (fun (l : Ast.loc) -> Printf.printf "with an error: %d:%d\n" l.line l.col)
    r.broken;
  List.iter
    (fun (p : Syntax_recovery.report) ->
      Printf.printf "%s at %d:%d, from %d:%d to %s\n"
        (p.error.code :> string)
        p.error.line p.error.col p.from.line p.from.col
        (match p.until with
        | Some u -> Printf.sprintf "%d:%d" u.line u.col
        | None -> "the end"))
    r.reports

let%expect_test "an error in a body keeps the function's signature" =
  read "fn half(x: i64) -> i64 { x / }\nfn twice(x: i64) -> i64 { x * 2 }\n";
  [%expect
    {|
    fn half, 1 parameters
    fn twice, 1 parameters
    with an error: 1:4
    E0100 at 1:30, from 1:1 to 2:1
    |}]

let%expect_test "an error in a signature leaves it unknown" =
  read "fn half(x i64) -> i64 { x }\n\nfn main() {}\n";
  [%expect
    {|
    fn half, 0 parameters, unknown
    fn main, 0 parameters
    with an error: 1:4
    E0100 at 1:11, from 1:1 to 3:1
    |}]

let%expect_test
    "a bracket left open ends at the next declaration that starts a line" =
  read "fn a() {\n  if true {\n}\n\nfn b() {}\n";
  [%expect
    {|
    fn a, 0 parameters
    fn b, 0 parameters
    with an error: 1:4
    E0100 at 5:1, from 1:1 to 5:1
    |}]

let%expect_test "a closing bracket that nothing opened ends nothing" =
  read "fn a() -> i64 { 1 } }\nfn main() {}\n";
  [%expect
    {|
    fn a, 0 parameters
    fn main, 0 parameters
    with an error: 1:4
    E0100 at 1:21, from 1:1 to 2:1
    |}]

let%expect_test "a block's members are read one at a time" =
  read
    "module main\n\
     impl T {\n\
    \  fn a(self) -> i64 { 1 }\n\
    \  fn b(self) -> i64 { 1 + }\n\
    \  const C: i64 = 2\n\
     }\n";
  [%expect
    {|
    header
    impl
      fn a, 1 parameters
      fn b, 1 parameters
      const C
    with an error: 4:6
    E0100 at 4:27, from 2:1 to the end
    |}]

let%expect_test "an error before an impl's block declares no impl" =
  read "impl Show fro T {\n  fn show(self) -> str { \"t\" }\n}\nfn f() {}\n";
  [%expect {|
    fn f, 0 parameters
    E0100 at 1:11, from 1:1 to 4:1
    |}]

let%expect_test "types, traits, constants and tests with errors" =
  read
    "use std.io\n\
     type P = { x: }\n\
     trait Q { fn q(self) -> }\n\
     const N: i64 = 1 1\n\
     test \"t\" { assert }\n\
     ) stray\n\
     fn f(p: P) {}\n";
  [%expect
    {|
    use
    type P, unknown
    trait Q
      fn q, 0 parameters, unknown
    const N
    test "t"
    fn f, 1 parameters
    with an error: 3:14
    with an error: 4:7
    with an error: 5:1
    E0100 at 2:15, from 2:1 to 3:1
    E0100 at 3:25, from 3:1 to 4:1
    E0100 at 4:18, from 4:1 to 5:1
    E0100 at 5:19, from 5:1 to 7:1
    |}]

let%expect_test "the part that a lexical error ends has that error" =
  read "fn a() -> i64 { 1 }\nfn main() {}\n`";
  [%expect
    {|
    fn a, 0 parameters
    fn main, 0 parameters
    with an error: 2:4
    E0002 at 3:1, from 2:1 to the end
    |}]

let%expect_test "a block holds only functions and constants" =
  read "impl T {\n  fn a(self) -> i64 { 1 + }\n  pub type U = { }\n}\n";
  [%expect
    {|
    impl
      fn a, 1 parameters
    with an error: 2:6
    E0100 at 2:27, from 1:1 to the end
    |}]

let%expect_test "a part of doc comments alone, which a lexical error ends" =
  read "/// ex: 1 +\n\"\\q\"\n";
  [%expect {| E0100 at 1:1, from 1:1 to the end |}]
