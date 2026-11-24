(* Tests of the parser against reference/03-syntax.md and the records it cites. Each
   test prints the tree of a source text, or its first syntax error. *)

open Stilt

let show text =
  match Syntax.parse ~file:"t.lt" text with
  | Ok (m, _) -> print_endline (Sexp.of_module m)
  | Error diagnostic -> print_endline (Diagnostic.to_string diagnostic)

(* Prints the statements of [text], parsed as the body of a function. *)
let body text =
  let prefix = "(module (fn t () () (tuple) (row) (block" in
  match Syntax.parse ~file:"t.lt" ("fn t() {\n" ^ text ^ "\n}") with
  | Error diagnostic -> print_endline (Diagnostic.to_string diagnostic)
  | Ok (m, _) ->
      let tree = Sexp.of_module m in
      let inner =
        String.sub tree (String.length prefix)
          (String.length tree - String.length prefix - 3)
      in
      print_endline (String.trim inner)

let%expect_test "precedence, from tightest to loosest" =
  body "-a.b * c + d << e & f ^ g | h == i && j || k else l";
  [%expect
    {| (else (|| (&& (== (| (^ (& (<< (+ (* (neg (field a b)) c) d) e) f) g) h) i) j) k) l) |}];
  body "a - b - c";
  [%expect {| (- (- a b) c) |}];
  body "a else b else c";
  [%expect {| (else a (else b c)) |}];
  body "!a == b";
  [%expect {| (== (not a) b) |}]

let%expect_test "comparisons don't chain" =
  body "a < b < c";
  [%expect {| t.lt:2:7: E0100: unexpected `<` |}];
  body "a == b != c";
  [%expect {| t.lt:2:8: E0100: unexpected `!=` |}]

let%expect_test "level 14 extends as far right as possible" =
  body "x else raise e + 1";
  [%expect {| (else x (raise (+ e 1))) |}];
  body "a + try b() * c";
  [%expect {| (+ a (try (* (call b) c))) |}];
  body "-raise e";
  [%expect {| (neg (raise e)) |}];
  body "f(|x| x + 1, 2)";
  [%expect {| (call f (closure (x) (+ x 1)) 2) |}];
  body "return -1";
  [%expect {| (return (neg 1)) |}];
  body "if c { return }";
  [%expect {| (if c (block (return))) |}];
  body "|| 0";
  [%expect {| (closure () 0) |}];
  body "a || b";
  [%expect {| (|| a b) |}]

let%expect_test "catch belongs to the nearest try without one" =
  body "try a(try b()) catch _ => 0";
  [%expect {| (try (call a (try (call b))) (catch (arm _ 0))) |}];
  body "try a + try b() catch _ => 0";
  [%expect {| (try (+ a (try (call b) (catch (arm _ 0))))) |}];
  body "let x = try a() catch _ because \"old configs\" => 0 + 1";
  [%expect
    {| (let x (try (call a) (catch (arm _ (because "old configs") (+ 0 1))))) |}];
  body
    "try f() catch {\n\
    \  NotFound(p) => 1\n\
    \  e if bad(e) => 2,\n\
    \  _ => raise e\n\
     }";
  [%expect
    {| (try (call f) (catch (arm (NotFound p) 1) (arm e (if (call bad e)) 2) (arm _ (raise e)))) |}]

let%expect_test "catch arms" =
  body "try f() catch e if c because \"r\" => 0";
  [%expect {| t.lt:2:22: E0100: unexpected `because` |}];
  body "try f() catch e since \"r\" => 0";
  [%expect {| t.lt:2:17: E0100: unexpected `since` |}];
  body "match x { _ because \"r\" => 0 }";
  [%expect {| t.lt:2:13: E0100: unexpected `because` |}]

let%expect_test "else after if" =
  body "if a { 1 } else if b { 2 } else { 3 }";
  [%expect {| (if a (block 1) (if b (block 2) (block 3))) |}];
  body "if a { 1 }\nelse { 2 }";
  [%expect {| (if a (block 1) (block 2)) |}];
  body "if a { 1 } else 2";
  [%expect {| t.lt:2:17: E0100: unexpected the number `2` |}];
  body "(if a { b }) else c";
  [%expect {| (else (if a (block b)) c) |}]

let%expect_test "heads" =
  body "if x == None { 1 }";
  [%expect {| (if (== x None) (block 1)) |}];
  body "while n < MAX { n += 1 }";
  [%expect {| (while (< n MAX) (block (+= n 1))) |}];
  body "if p == (Point { x: 0 }) { 1 }";
  [%expect {| (if (== p (struct Point (x 0))) (block 1)) |}];
  body "match xs.any(|x| x > 0) { true => 1, false => 0 }";
  [%expect
    {| (match (call (field xs any) (closure (x) (> x 0))) (arm true 1) (arm false 0)) |}];
  body "if p == Point { x: 0 } { 1 }";
  [%expect {| t.lt:2:18: E0100: unexpected `:` |}];
  body "while if a { b } else { c } { d }";
  [%expect {| t.lt:2:7: E0100: unexpected `if` |}];
  body "for x in { xs } { f(x) }";
  [%expect {| t.lt:2:10: E0100: unexpected `{` |}];
  (* The block form of [catch] can't stand in a head, where a [{] after
     [catch] begins an anonymous record's pattern (records.anonymous-patterns), which no
     [_] begins. *)
  body "if try f() catch { _ => true } { 1 }";
  [%expect {| t.lt:2:20: E0100: unexpected `_` |}]

let%expect_test "struct literals" =
  body "Order { customer, qty: 3, }";
  [%expect {| (struct Order (customer customer) (qty 3)) |}];
  body "orders.Order {}";
  [%expect {| (struct orders.Order) |}];
  body "Self { x }";
  [%expect {| (struct Self (x x)) |}];
  body "f() { x: 1 }";
  [%expect {| t.lt:2:5: E0100: unexpected `{` |}];
  body "order { x: 1 }";
  [%expect {| t.lt:2:7: E0100: unexpected `{` |}];
  body "Order {\n  customer: c\n  qty: 3\n}";
  [%expect {| t.lt:3:13: E0100: unexpected end of the statement |}]

let%expect_test "commas and tuples" =
  body "(a)";
  [%expect {| a |}];
  body "(a,)";
  [%expect {| (tuple a) |}];
  body "(a, b,)";
  [%expect {| (tuple a b) |}];
  body "()";
  [%expect {| (tuple) |}];
  body "f(a, b,)";
  [%expect {| (call f a b) |}];
  body "[1, 2,]";
  [%expect {| (list 1 2) |}];
  body "f(a,, b)";
  [%expect {| t.lt:2:5: E0100: unexpected `,` |}]

let%expect_test "postfix forms and key paths" =
  body "xs.sorted_by(.name.len()).items[0].1";
  [%expect
    {| (field (index (field (call (field xs sorted_by) (call (field (field . name) len))) items) 0) 1) |}];
  body "xs.map(.items[0])";
  [%expect {| (call (field xs map) (index (field . items) 0)) |}];
  body "f64.PI";
  [%expect {| (field f64 PI) |}];
  body "normalize(inout v, w)";
  [%expect {| (call normalize (inout v) w) |}];
  body "t.0.1";
  [%expect {| (field (field t 0) 1) |}];
  body "xs\n  .len()";
  [%expect {| (call (field xs len)) |}]

(* types.fields-through-option and types.hole-before-dot: a field read through an [Option] is a field like
   any other, and [?.] is a hole before a field. *)
let%expect_test "fields through options" =
  body "p.address.city.len()";
  [%expect {| (call (field (field (field p address) city) len)) |}];
  body "(a.b).c";
  [%expect {| (field (field a b) c) |}];
  body "?.len()";
  [%expect {| (call (field ? len)) |}]

let%expect_test "literals and interpolation" =
  body "\"a{x}b{y:>5}\"";
  [%expect {| (interp "a" (splice x) "b" (splice y ">5")) |}];
  body "\"{\"{1}\"}\"";
  [%expect {| (interp (splice (interp (splice 1)))) |}];
  body "\"tab\\there\\u{1b}\"";
  [%expect {| "tab\there\u{1b}" |}];
  body "1_000 + 2.5e-3 + 0xFf";
  [%expect {| (+ (+ 1000 2.5e-3) 0xFf) |}];
  body "?";
  [%expect {| ? |}]

let%expect_test "loops and ranges" =
  body "for i in 0..n + 1 { f(i) }";
  [%expect {| (for i (.. 0 (+ n 1)) (block (call f i))) |}];
  body "for (c, t) in m { break }";
  [%expect {| (for (tuple c t) m (block break)) |}];
  body "for i in 1..=3 { continue }";
  [%expect {| (for i (..= 1 3) (block continue)) |}];
  body "loop { break }";
  [%expect {| (loop (block break)) |}];
  body "let r = 0..n";
  [%expect {| t.lt:2:10: E0100: unexpected `..` |}]

let%expect_test "statements" =
  body
    "let x: i64 = 1\nvar (a, b) = p\nxs[i] = v\nm[k] += 1\nassert a == b\nf()";
  [%expect
    {| (let (: x i64) 1) (var (tuple a b) p) (= (index xs i) v) (+= (index m k) 1) (assert (== a b)) (call f) |}];
  body "let [a, b] = xs else raise e";
  [%expect {| (let (list a b) (else xs (raise e))) |}];
  body "a; b;; c";
  [%expect {| a b c |}];
  body "a = b = c";
  [%expect {| t.lt:2:7: E0100: unexpected `=` |}];
  body "let x = 1 let y = 2";
  [%expect {| t.lt:2:11: E0100: unexpected `let` |}]

let%expect_test "patterns" =
  body
    "match v {\n\
    \  0 | -1 => a\n\
    \  \"s\" | true => b\n\
    \  shapes.Circle(r) | Rect(r, _) => c\n\
    \  Point { x, y: 0, .. } => d\n\
    \  [first, ..rest] | [] | [_, ..] => e\n\
    \  (a, (b,)) => f\n\
    \  f64.PI | Color.RED | None => g\n\
     }";
  [%expect
    {| (match v (arm (or 0 -1) a) (arm (or "s" true) b) (arm (or (shapes.Circle r) (Rect r _)) c) (arm (record Point (x x) (y 0) ..) d) (arm (or (list first (.. rest)) (list) (list _ ..)) e) (arm (tuple a (tuple b)) f) (arm (or f64.PI Color.RED None) g)) |}];
  body "match v { 1.5 => a }";
  [%expect {| t.lt:2:11: E0100: unexpected the number `1.5` |}];
  body "match v { \"{x}\" => a }";
  [%expect {| t.lt:2:11: E0100: unexpected a string |}];
  body "match v { [.., last] => a }";
  [%expect {| t.lt:2:16: E0100: unexpected `last` |}];
  body "let |x| = 1";
  [%expect {| t.lt:2:5: E0100: unexpected `|` |}]

let%expect_test "closures" =
  body "xs.map(|(n, l): (i64, str)| parse(n, l))";
  [%expect
    {| (call (field xs map) (closure ((: (tuple n l) (tuple i64 str))) (call parse n l))) |}];
  body "|x| -> i64 { x }";
  [%expect {| t.lt:2:5: E0100: unexpected `->` |}];
  body "xs.map(|l| {\n  let a = f(l)\n  g(a)\n})";
  [%expect
    {| (call (field xs map) (closure (l) (block (let a (call f l)) (call g a)))) |}]

let%expect_test "types" =
  show "fn f(m: Map<str, List<i64>>, n: List<List<List<i64>>>) {}";
  [%expect
    {| (module (fn f () ((m (Map str (List i64))) (n (List (List (List i64))))) (tuple) (row) (block))) |}];
  show "fn f(g: List<fn(i64) -> List<i64>>, h: Map<str, (i64,)>) {}";
  [%expect
    {| (module (fn f () ((g (List (fn (i64) (List i64) (row)))) (h (Map str (tuple i64)))) (tuple) (row) (block))) |}];
  show "fn f(g: fn(inout Vec3, str) / {io, raise<List<str>>, e}) {}";
  [%expect
    {| (module (fn f () ((g (fn ((inout Vec3) str) (tuple) (row io (raise (List str)) e)))) (tuple) (row) (block))) |}];
  show "fn make() -> fn(i64) -> i64 / io {}";
  [%expect {| (module (fn make () () (fn (i64) i64 (row io)) (row) (block))) |}];
  show "fn make() -> (fn(i64) -> i64) / io {}";
  [%expect {| (module (fn make () () (fn (i64) i64 (row)) (row io) (block))) |}];
  show "fn f(x: Self, y: m.T<A,>, z: ()) {}";
  [%expect
    {| (module (fn f () ((x Self) (y (m.T A)) (z (tuple))) (tuple) (row) (block))) |}]

let%expect_test "functions" =
  show
    "pub fn map<A, B: Ord + m.Show, e>(xs: List<A>, escaping f: fn(A) -> B / \
     e) -> List<B> / e = ?";
  [%expect
    {| (module (pub (fn map (A (B Ord m.Show) e) ((xs (List A)) (escaping f (fn (A) B (row e)))) (List B) (row e) ?))) |}];
  show "fn f(inout self, x: str) {}";
  [%expect
    {| (module (fn f () ((inout self) (x str)) (tuple) (row) (block))) |}];
  show "fn f(x: i64, self) {}";
  [%expect {| t.lt:1:14: E0100: unexpected `self` |}];
  show "fn f(let x: i64) {}";
  [%expect {| t.lt:1:6: E0100: unexpected `let` |}];
  show "fn Main() {}";
  [%expect {| t.lt:1:4: E0100: unexpected `Main` |}];
  show "fn with() {}";
  [%expect {| t.lt:1:4: E0100: unexpected `with` |}];
  show "fn f() {} fn g() {}";
  [%expect {| t.lt:1:11: E0100: unexpected `fn` |}]

let%expect_test "types, traits, impls, constants and tests" =
  show
    "type Shape =\n\
    \  | Circle(radius: f64)\n\
    \  | Rect(w: f64, h: f64)\n\
     type UserId = | UserId(i64)\n\
     type Empty = {}\n\
     pub type Pair<A, B> = { first: A, second: B, }";
  [%expect
    {| (module (type Shape () (variants (Circle (radius f64)) (Rect (w f64) (h f64)))) (type UserId () (variants (UserId i64))) (type Empty () (record)) (pub (type Pair (A B) (record (first A) (second B))))) |}];
  show "type Id = UserId";
  [%expect {| t.lt:1:17: E0100: unexpected end of the file |}];
  show "type Ids = List<i64>";
  [%expect {| t.lt:1:16: E0100: unexpected `<` |}];
  show
    "trait Show {\n\
    \  fn show(self) -> str\n\
    \  fn show_nested(self) -> str { self.show() }\n\
     }\n\
     impl<T: Ord> List<T> {\n\
    \  pub fn sorted(self) -> List<T> { self.sorted_by(|x| x) }\n\
    \  const EMPTY: i64 = 0\n\
     }\n\
     impl Show for Order { fn show(self) -> str = ? }\n\
     const MAX: i64 = -1\n\
     test \"sorting\" { assert MAX < 0 }";
  [%expect
    {| (module (trait Show (fn show () (self) str (row)) (fn show_nested () (self) str (row) (block (call (field self show))))) (impl ((T Ord)) (List T) (pub (fn sorted () (self) (List T) (row) (block (call (field self sorted_by) (closure (x) x))))) (const EMPTY i64 0)) (impl-trait () Show Order (fn show () (self) str (row) ?)) (const MAX i64 (neg 1)) (test "sorting" (block (assert (< MAX 0))))) |}];
  show "impl Show for Order { pub fn show(self) -> str = ? }";
  [%expect {| t.lt:1:23: E0100: unexpected `pub` |}];
  show "pub test \"t\" {}";
  [%expect {| t.lt:1:5: E0100: unexpected `test` |}]

let%expect_test "doc comments" =
  show
    "/// Adds.\n\
     /// ex: add(1, 2) == 3\n\
     ///\n\
     pub fn add(a: i64, b: i64) -> i64 { a + b }";
  [%expect
    {| (module (doc "Adds." (ex (== (call add 1 2) 3)) "" (pub (fn add () ((a i64) (b i64)) i64 (row) (block (+ a b)))))) |}];
  show "impl T {\n  /// Makes one.\n  fn new() -> T = ?\n}";
  [%expect
    {| (module (impl () T (doc "Makes one." (fn new () () T (row) ?)))) |}];
  show "/// ex: true //~ PASS\ntest \"t\" {}";
  [%expect {| (module (doc (ex true) (test "t" (block)))) |}];
  show "/// Orphan.\n\nfn f() {}";
  [%expect
    {| t.lt:1:1: E0100: a doc comment must come directly before a declaration |}];
  show "/// Orphan.\n// note\nfn f() {}";
  [%expect
    {| t.lt:1:1: E0100: a doc comment must come directly before a declaration |}];
  show "/// Imports.\nuse std.fs";
  [%expect
    {| t.lt:1:1: E0100: a doc comment must come directly before a declaration |}];
  show "fn f() {} /// trailing";
  [%expect
    {| t.lt:1:11: E0100: a doc comment must come directly before a declaration |}];
  (* A doc comment after code on its line is the error, before the
     separators that follow it. *)
  show "trait/// Shares its line.\n;\npub fn f() {}";
  [%expect
    {| t.lt:1:6: E0100: a doc comment must come directly before a declaration |}];
  show "/// ex: f(\nfn f() {}";
  [%expect {| t.lt:1:11: E0100: unexpected end of the file |}];
  show "/// ex: 007\nfn f() {}";
  [%expect {| t.lt:1:9: E0004: a decimal literal can't have a leading zero |}]

(* tests.prop-lines: a property is parsed as an example is, and its tree is
   [(prop EXPR)]. *)
let%expect_test "properties" =
  show
    "/// prop: |xs: List<i64>| reverse(reverse(xs)) == xs //~ PASS\n\
     fn reverse(xs: List<i64>) -> List<i64> { xs }";
  [%expect
    {| (module (doc (prop (closure ((: xs (List i64))) (== (call reverse (call reverse xs)) xs))) (fn reverse () ((xs (List i64))) (List i64) (row) (block xs)))) |}];
  show "///   prop:|x: i64| x == x\nfn f() {}";
  [%expect
    {| (module (doc (prop (closure ((: x i64)) (== x x))) (fn f () () (tuple) (row) (block)))) |}];
  show "/// prop: |x: i64| x +\nfn f() {}";
  [%expect {| t.lt:1:23: E0100: unexpected end of the file |}];
  show "/// props: are text\nfn f() {}";
  [%expect
    {| (module (doc "props: are text" (fn f () () (tuple) (row) (block)))) |}]

let%expect_test "the first syntax error wins" =
  show "fn f() {\n  let x = )\n}\nlet y = 007";
  [%expect {| t.lt:2:11: E0100: unexpected `)` |}];
  show "fn f() {\n  let x = 007\n  let y = )\n}";
  [%expect {| t.lt:2:11: E0004: a decimal literal can't have a leading zero |}];
  show "/// Orphan.\nuse std.fs\nfn f( {}";
  [%expect
    {| t.lt:1:1: E0100: a doc comment must come directly before a declaration |}];
  show "fn f( {}\n/// ex: )\nfn g() {}";
  [%expect {| t.lt:1:7: E0100: unexpected `{` |}];
  show "\xEF\xBB\xBFfn f( {}";
  [%expect
    {| t.lt:1:1: E0001: a source file can't begin with a byte-order mark |}]

let%expect_test "the end of the file sits after the last token" =
  show "type Id = UserId\n\n\n// trailing\n";
  [%expect {| t.lt:1:17: E0100: unexpected end of the file |}];
  show "fn f() {\n  g(\n";
  [%expect {| t.lt:2:5: E0100: unexpected end of the file |}]

let%expect_test "a lexical error after a grammar error" =
  show "fn f() { foo {\n`\n}";
  [%expect {| t.lt:1:14: E0100: unexpected `{` |}];
  show "fn f() { \"a{ ) }";
  [%expect {| t.lt:1:10: E0005: unterminated string literal |}];
  show "fn f() {\n  \"abc{ fn }\n}";
  [%expect {| t.lt:2:3: E0005: unterminated string literal |}];
  show "type Id = UserId\n`";
  [%expect {| t.lt:2:1: E0002: unexpected backtick |}];
  show "fn f( {}\nlet x = 1\ry";
  [%expect
    {| t.lt:2:10: E0001: a carriage return must be followed by a newline |}]

let%expect_test "struct literals take only a path of identifiers" =
  body "(A) { x: 1 }";
  [%expect {| t.lt:2:5: E0100: unexpected `{` |}];
  body "(a).B {}";
  [%expect {| t.lt:2:7: E0100: unexpected `{` |}];
  body "Self.X { x: 1 }";
  [%expect {| t.lt:2:8: E0100: unexpected `{` |}];
  body "_1A {}";
  [%expect {| (struct _1A) |}];
  body "Order { a: 1 }.a";
  [%expect {| (field (struct Order (a 1)) a) |}];
  body "let p = make(\n  1,\n) { x: 1 }";
  [%expect {| t.lt:4:3: E0100: unexpected `{` |}]

let%expect_test ">> closes the arguments of raise" =
  show
    "fn f(a: List<fn() / raise<E>>, b: List<fn() -> T / raise<E>>) / \
     raise<fn() / raise<E>> = ?";
  [%expect
    {| (module (fn f () ((a (List (fn () (tuple) (row (raise E))))) (b (List (fn () T (row (raise E)))))) (tuple) (row (raise (fn () (tuple) (row (raise E))))) ?)) |}];
  show "fn f(m: Map<str, List<fn() -> i64 / raise<E>>>) = ?";
  [%expect
    {| (module (fn f () ((m (Map str (List (fn () i64 (row (raise E))))))) (tuple) (row) ?)) |}]

let%expect_test "one doc run documents one declaration" =
  show "/// doc\nfn f() {}; fn g() {}";
  [%expect
    {| (module (doc "doc" (fn f () () (tuple) (row) (block))) (fn g () () (tuple) (row) (block))) |}];
  show "/// ex: true\ntrait T { fn f(self); fn g(self) }";
  [%expect
    {| (module (doc (ex true) (trait T (fn f () (self) (tuple) (row)) (fn g () (self) (tuple) (row))))) |}];
  show "fn f() ->\n  /// returns a function\n  fn() -> i64 = ?";
  [%expect
    {| t.lt:2:3: E0100: a doc comment must come directly before a declaration |}];
  show "type H =\n  | Click(\n    /// the callback\n    fn() -> i64,\n  )";
  [%expect
    {| t.lt:3:5: E0100: a doc comment must come directly before a declaration |}];
  show "fn f() {}\n; /// doc\nfn g() {}";
  [%expect
    {| (module (fn f () () (tuple) (row) (block)) (doc "doc" (fn g () () (tuple) (row) (block)))) |}];
  show "/// doc\n;\nfn f() {}";
  [%expect
    {| t.lt:1:1: E0100: a doc comment must come directly before a declaration |}];
  show "/// Summary //~ ERROR E0100\n/// ex: true //~ PASS\nfn f() {}";
  [%expect
    {| (module (doc "Summary" (ex true) (fn f () () (tuple) (row) (block)))) |}];
  show "/// ex: ;true;\nfn f() {}";
  [%expect {| (module (doc (ex true) (fn f () () (tuple) (row) (block)))) |}];
  show "fn f() {}\n/// trailing doc";
  [%expect
    {| t.lt:2:1: E0100: a doc comment must come directly before a declaration |}]

let%expect_test "trailing commas after .." =
  body "match v { [a, ..,] | [..rest,] => 1, P { x, .., } => 2 }";
  [%expect
    {| (match v (arm (or (list a ..) (list (.. rest))) 1) (arm (record P (x x) ..) 2)) |}]

let%expect_test "payloads are never empty" =
  show "type V = | A() | B";
  [%expect {| t.lt:1:14: E0100: unexpected `)` |}];
  body "match v { A() => 1 }";
  [%expect {| t.lt:2:13: E0100: unexpected `)` |}]

let%expect_test "a lowercase type takes no arguments" =
  show "fn f(x: tuple<i64>) {}";
  [%expect {| t.lt:1:14: E0100: unexpected `<` |}]

let%expect_test "jumps as left operands" =
  body "return + 1";
  [%expect {| (+ (return) 1) |}];
  body "if return { 1 }";
  [%expect {| (if (return) (block 1)) |}]

(* effects.row-variables, and traits.bounds *)
let%expect_test "only functions declare row variables, and types take no bounds"
    =
  show "fn f<T: Ord, e>() {}\nimpl<T: Ord> W<T> {}";
  [%expect
    {| (module (fn f ((T Ord) e) () (tuple) (row) (block)) (impl ((T Ord)) (W T))) |}];
  show "type K<T: Ord> = {}";
  [%expect {| t.lt:1:9: E0100: unexpected `:` |}];
  (* generics.value-parameters: a type's and an impl's lowercase generic is a value
     parameter, so the error is where its [:] and type should be. *)
  show "type T<e> = {}";
  [%expect {| t.lt:1:9: E0100: unexpected `>` |}];
  show "impl<e> W {}";
  [%expect {| t.lt:1:7: E0100: unexpected `>` |}]

(* declarations.parameters, and lexical.contextual-keywords: [escaping] starts a parameter of
   function type, written with [fn], and takes no mode. *)
let%expect_test "escaping parameters" =
  show "fn f(escaping g: fn() -> i64 / io, escaping: i64) {}";
  [%expect {| t.lt:1:44: E0100: unexpected `:` |}];
  show "fn f(escaping g: i64) {}";
  [%expect {| t.lt:1:18: E0100: unexpected `i64` |}];
  show "fn f(escaping g: (fn())) {}";
  [%expect {| t.lt:1:18: E0100: unexpected `(` |}];
  show "fn f(inout escaping g: fn()) {}";
  [%expect {| t.lt:1:21: E0100: unexpected `g` |}];
  body "let escaping = 1";
  [%expect {| (let escaping 1) |}]
