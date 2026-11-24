(* Tests of pattern macros (macros.syntax-declarations and macros.hygiene) beyond the conformance suite's: the trees
   that the parser makes of declarations and uses, how a use's tokens match
   an arm, and the hygiene of expansions. *)

open Stilt

let show text =
  match Syntax.parse ~file:"t.lt" text with
  | Ok (m, _) -> print_endline (Sexp.of_module m)
  | Error diagnostic -> print_endline (Diagnostic.to_string diagnostic)

(* macros.syntax-declarations, macros.patterns and macros.templates *)
let%expect_test "declarations" =
  show "pub syntax m {\n($x: expr, $($y: Name);+) $b: block => [$($y),*]\n}";
  [%expect
    {| (module (pub (syntax m (arm (paren (frag x expr) , (rep ; + (frag y Name))) (frag b block) (template (bracket (rep , * (frag y)))))))) |}];
  (* A template runs to the separator that ends its arm. *)
  show "syntax m { [$t: type] => 1 + 2; () => { a; b } }";
  [%expect
    {| (module (syntax m (arm (bracket (frag t type)) (template "1" + "2")) (arm (paren) (template (brace a ; b))))) |}]

(* macros.uses: a use's groups are tokens, and its trailing block starts on the
   line where its group ends, outside a head. *)
let%expect_test "uses" =
  show "fn f() { m!(a b, \"x{y}\") { c }\nn.m![1]\n{ d } }";
  [%expect
    {| (module (fn f () () (tuple) (row) (block (macro m (paren a b , "x" y "") (brace c)) (macro n.m (bracket "1")) (block d)))) |}];
  show "fn f() { if m!(x) { 1 } }";
  [%expect
    {| (module (fn f () () (tuple) (row) (block (if (macro m (paren x)) (block 1))))) |}];
  show "fn f() { match x { m!(1, _) => 0 } }";
  [%expect
    {| (module (fn f () () (tuple) (row) (block (match x (arm (macro m (paren "1" , _)) 0))))) |}]

(* macros.templates: [$] stands nowhere else, and a fragment's name is a [lower]. *)
let%expect_test "dollars" =
  show "fn f() { m!($x) }";
  [%expect {| t.lt:1:13: E0100: unexpected `$` |}];
  show "syntax m { ($X: expr) => 1 }";
  [%expect {| t.lt:1:14: E0100: unexpected `X` |}]

(* The arms of the first macro of [decl], matched against the tokens of
   [use], a group and perhaps a trailing block. *)
let matches decl use =
  let arms =
    match Syntax.parse ~file:"t.lt" decl with
    | Ok ({ items = { desc = Decl { kind = Syntax s; _ }; _ } :: _; _ }, _) ->
        s.arms
    | _ -> invalid_arg "matches"
  in
  let tokens =
    List.filter
      (fun (t : Lexer.token) -> t.token <> EOF)
      (Lexer.tokenize ~file:"u.lt" use).tokens
  in
  let rec binding = function
    | Macro_match.One (_, ts) ->
        String.concat " "
          (List.map (fun (t : Lexer.token) -> Token.to_string t.token) ts)
    | Many bs -> "[" ^ String.concat " | " (List.map binding bs) ^ "]"
  in
  match Macro_match.first arms (Array.of_list tokens) with
  | Ok (arm, env) ->
      Printf.printf "arm at %d:%d\n" arm.pattern.loc.line arm.pattern.loc.col;
      List.iter
        (fun (name, b) -> Printf.printf "  $%s = %s\n" name (binding b))
        (List.rev env)
  | Error (t, expected) ->
      Printf.printf "no arm: at %d:%d %s, expected %s\n" t.line t.col
        (Token.to_string t.token) expected

(* macros.matching: a fragment matches the longest form of its kind, and the first
   arm that matches is used. *)
let%expect_test "matching" =
  let decl =
    "syntax m {\n\
     ($a: expr, $b: pattern) => 0\n\
     ($($k: expr => $v: expr),*) => 0\n\
     }"
  in
  matches decl "(1 + 2 * 3, Some(x) | None)";
  [%expect
    {|
    arm at 2:1
      $a = INT 1 + INT 2 * INT 3
      $b = UIDENT Some ( LIDENT x ) | UIDENT None
    |}];
  matches decl "(1 => f(2), x => y)";
  [%expect
    {|
    arm at 3:1
      $k = [INT 1 | LIDENT x]
      $v = [LIDENT f ( INT 2 ) | LIDENT y]
    |}];
  (* The furthest token that any arm reached. *)
  matches decl "(1 => 2, 3 4)";
  [%expect {| no arm: at 1:12 INT 4, expected `=>` |}]

(* macros.matching: a repetition matches as many rounds as it can, and a trailing
   block only a use's trailing block. *)
let%expect_test "repetitions and blocks" =
  let decl = "syntax m {\n($($n: name)* ; $e: expr) $b: block => 0\n}" in
  matches decl "(a b c; 1) { 2 }";
  [%expect
    {|
    arm at 2:1
      $n = [LIDENT a | LIDENT b | LIDENT c]
      $e = INT 1
      $b = { INT 2 }
    |}];
  matches decl "(; 1)";
  [%expect {| no arm: at 1:5 ), expected a trailing block after the group |}]

let errors = Diagnostics.Errors.main

(* macros.hygiene: what the names of an expansion refer to. *)
let%expect_test "hygiene" =
  (* A template's name resolves where the macro is declared, whatever the
     use's scope binds. *)
  Resolved.refers
    "fn helper() -> i64 { 1 }\n\
     syntax h { () => helper }\n\
     fn t() -> i64 { let helper = 2\n\
     h!() }";
  [%expect {| fn main.helper |}];
  (* A fragment's name resolves where the use is. *)
  Resolved.refers
    "syntax id { ($x: expr) => $x }\nfn t() -> i64 { let v = 2\nid!(v) }";
  [%expect {| local v |}];
  (* A template's binding is fresh: it captures none of the user's names,
     and the user's names can't name it. *)
  errors
    "syntax wrap { ($e: expr) => { let tmp = 1; $e } }\n\
     fn t() -> i64 { wrap!(tmp) }\n\
     fn u() -> i64 { let tmp = 2\n\
     wrap!(tmp) }";
  [%expect {| main.lt:2: E0211 |}]

(* macros.checked-templates and macros.hygiene: a template names its module's private items from another
   module, and a name that resolves nowhere is an error where it is
   declared, not where it is used. *)
let%expect_test "names across modules" =
  Diagnostics.Errors.check
    [
      ( "tools.lt",
        "pub syntax twice { ($x: expr) => double($x) }\n\
         fn double(x: i64) -> i64 { x * 2 }\n\
         pub syntax broken { () => nowhere() }" );
      ( "main.lt",
        "use tools\n\
         fn double(x: str) -> str { x }\n\
         fn main() { let a: i64 = tools.twice!(1)\n\
         tools.broken!() }" );
    ];
  [%expect {| tools.lt:3: E0211 |}]

(* syntax.parts: [syntax] starts a part, so a part that breaks
   before it leaves the macro declared, and a macro that breaks declares its
   name, whose uses report nothing more (errors.broken-parts). *)
let%expect_test "parts" =
  errors
    "fn f() -> i64 { 1 +\n\
     syntax twice { ($x: expr) => $x * 2 }\n\
     fn g() -> i64 { twice!(2) }";
  [%expect {| main.lt:2: E0100 |}];
  errors
    "syntax bad { ($x expr) => 1 }\n\
     fn g() -> i64 { bad!(2) }\n\
     syntax good { () => 1 }\n\
     fn h() -> i64 { good!() + nothing }";
  [%expect {|
    main.lt:1: E0100
    main.lt:4: E0211
    |}]
