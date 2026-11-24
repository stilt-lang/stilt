//! Code past the caps of instances (goal inline-values; facts.native-allocation):
//! polymorphic recursion makes type arguments without end, so past the caps a call goes to code
//! compiled once, where each type argument that would grow the instances is held in its box, and
//! each value whose type holds it is converted on the way in and back. Each program runs and
//! prints what value semantics says, under `stilt run` and as an executable.

use super::generics::CHOOSER;
use super::{P, runs_as, runs_boxing};

/// Calls of a trait's methods with type parameters of their own, on a receiver whose type nests
/// one constructor deeper at each level of the recursion.
const DEEP: &str = r#"fn deep<C: Chooser>(c: C, n: i64, p: P) -> i64 {
  if n == 0 {
    let q = c.choose(p, P { x: 10, y: 20 })
    match c.wrap(p) {
      Some(r) => r.x + r.y + q.x
      None => 0
    }
  } else {
    deep(Flip { inner: c }, n - 1, p)
  }
}

fn main() / io {
  let w = W { first: true }
  print("{deep(w, 3, P { x: 1, y: 2 })}")
  print("{deep(w, 40, P { x: 1, y: 2 })}")
  print("{deep(w, 41, P { x: 1, y: 2 })}")
}
"#;

#[test]
fn polymorphic_recursion_past_the_cap_of_constructors_runs() {
    let source = [P, CHOOSER, DEEP].concat();
    runs_boxing("deep", &source, "13\n4\n13\n");
}

/// A trait whose methods take and give values of each kind whose type holds the method's own
/// type parameter: the parameter itself, a list of a composite, a map, a recursive type, a
/// closure, an `inout` composite, a list of the parameter and an error.
const MOVER: &str = r#"type Tree<T> = | Leaf | Node(Tree<T>, T, Tree<T>)

trait Mover {
  fn pick<T>(self, a: T) -> T
  fn all<T>(self, xs: List<Option<T>>) -> List<Option<T>>
  fn table<T>(self, m: Map<str, (T, i64)>) -> Map<str, (T, i64)>
  fn tree<T>(self, t: Tree<T>) -> Tree<T>
  fn call<T>(self, f: fn(T) -> T, a: T) -> T
  fn bump<T>(self, inout a: (T, i64))
  fn list<T>(self, xs: List<T>) -> List<T>
  fn fail<T>(self, a: T) -> i64 / raise<T>
}

type W = { k: i64 }

impl Mover for W {
  fn pick<T>(self, a: T) -> T { a }
  fn all<T>(self, xs: List<Option<T>>) -> List<Option<T>> {
    var out = xs
    out.push(None)
    out
  }
  fn table<T>(self, m: Map<str, (T, i64)>) -> Map<str, (T, i64)> {
    var out = m
    match m.get("a") {
      Some((t, n)) => { out["b"] = (t, n + self.k) }
      None => {}
    }
    out
  }
  fn tree<T>(self, t: Tree<T>) -> Tree<T> {
    match t {
      Leaf => Leaf,
      Node(l, v, r) => Node(self.tree(r), v, self.tree(l)),
    }
  }
  fn call<T>(self, f: fn(T) -> T, a: T) -> T { f(f(a)) }
  fn bump<T>(self, inout a: (T, i64)) { a.1 = a.1 + self.k }
  fn list<T>(self, xs: List<T>) -> List<T> {
    var out = xs
    out.push(xs[0])
    out
  }
  fn fail<T>(self, a: T) -> i64 / raise<T> { raise a }
}

type Flip<C> = { inner: C }

impl<C: Mover> Mover for Flip<C> {
  fn pick<T>(self, a: T) -> T { self.inner.pick(a) }
  fn all<T>(self, xs: List<Option<T>>) -> List<Option<T>> { self.inner.all(xs) }
  fn table<T>(self, m: Map<str, (T, i64)>) -> Map<str, (T, i64)> { self.inner.table(m) }
  fn tree<T>(self, t: Tree<T>) -> Tree<T> { self.inner.tree(t) }
  fn call<T>(self, f: fn(T) -> T, a: T) -> T { self.inner.call(f, a) }
  fn bump<T>(self, inout a: (T, i64)) { self.inner.bump(inout a) }
  fn list<T>(self, xs: List<T>) -> List<T> { self.inner.list(xs) }
  fn fail<T>(self, a: T) -> i64 / raise<T> { try self.inner.fail(a) }
}

fn sum(t: Tree<P>) -> i64 {
  match t {
    Leaf => 0,
    Node(l, v, r) => sum(l) * 100 + v.x * 10 + v.y + sum(r) * 1000,
  }
}

fn go<C: Mover>(c: C, n: i64) -> str {
  if n > 0 { return go(Flip { inner: c }, n - 1) }
  let p = P { x: 1, y: 2 }
  let picked = c.pick(p)
  let xs = c.all([Some(p), None, Some(P { x: 3, y: 4 })])
  var m = Map.new()
  m["a"] = (p, 5)
  let t = c.table(m)
  let tree = c.tree(Node(Node(Leaf, P { x: 5, y: 6 }, Leaf), p, Leaf))
  let called = c.call(|q: P| P { x: q.x + 1, y: q.y * 2 }, p)
  var pair = (p, 7)
  c.bump(inout pair)
  let l = c.list([p, P { x: 8, y: 9 }])
  let e = try c.fail(P { x: 4, y: 5 }) catch q because "the test reads it" => q.x * 100 + q.y
  let b = t.get("b")
  "{picked} {xs} {b} {sum(tree)} {called} {pair} {l} {e}"
}

fn main() / io {
  print(go(W { k: 1 }, 2))
  print(go(W { k: 1 }, 30))
}
"#;

#[test]
fn a_crossing_converts_composites_lists_maps_recursive_types_closures_and_errors() {
    let source = [P, MOVER].concat();
    let line = "P { x: 1, y: 2 } [Some(P { x: 1, y: 2 }), None, Some(P { x: 3, y: 4 }), None] Some((P { x: 1, y: 2 }, 6)) 56012 P { x: 3, y: 8 } (P { x: 1, y: 2 }, 8) [P { x: 1, y: 2 }, P { x: 8, y: 9 }, P { x: 1, y: 2 }] 405\n";
    runs_boxing("crossing", &source, &line.repeat(2));
}

/// Functions that call themselves with a tuple of two of their type parameter's values, each
/// call twice the words of the last: shown, read through closures, and held in lists.
const GROW: &str = r#"fn shown<T: Show>(x: T, n: i64) -> str {
  if n == 0 { return "{x}" }
  shown((x, x), n - 1)
}

fn first<T>(x: T, n: i64, get: fn(T) -> i64) -> i64 {
  if n == 0 { return get(x) }
  first((x, x), n - 1, |p: (T, T)| get(p.1))
}

fn nested<T: Eq>(xs: List<T>, n: i64) -> i64 {
  if n == 0 { return xs.len() }
  let y = (xs[0], xs[0])
  nested([y, y], n - 1) + if xs[0] == xs[0] { 1 } else { 0 }
}

fn main() / io {
  let p = P { x: 3, y: 4 }
  print("{shown(p, 3)}")
  print("{shown(p, 9).len()}")
  print("{first(p, 10, |q: P| q.x * 10 + q.y)}")
  print("{nested([1], 10)}")
}
"#;

#[test]
fn polymorphic_recursion_past_the_cap_of_words_runs() {
    let source = [P, GROW].concat();
    let shown = "(((P { x: 3, y: 4 }, P { x: 3, y: 4 }), (P { x: 3, y: 4 }, P { x: 3, y: 4 })), \
                 ((P { x: 3, y: 4 }, P { x: 3, y: 4 }), (P { x: 3, y: 4 }, P { x: 3, y: 4 })))";
    runs_boxing("grow", &source, &format!("{shown}\n10236\n34\n12\n"));
}

/// Generic code that doesn't reach itself, with a type argument it builds from its own type
/// parameters of 300 words, and a receiver nested 21 constructors deep, whose impl's methods
/// call the inner receiver's, each with a smaller type.
const SHALLOW: &str = "fn id<T>(x: T) -> T { x }\n\nfn twice<T>(x: T) -> (T, T) { id((x, x)) }\n\nfn wrapped<T>(x: T) -> Option<(T, T)> { id(Some((x, x))) }\n\nfn score<C: Chooser>(c: C, a: Big, b: Big) -> i64 {\n  let picked = c.choose(a, b)\n  let w = match c.wrap((a, b)) {\n    Some((r, s)) => r.w149 * 1000 + s.w0\n    None => 0\n  }\n  let (d, e) = c.pair(b)\n  picked.w1 + w + d.w2 + e.w3\n}\n\nfn main() / io {\n  let (a, b) = twice(big(1))\n  let n = match wrapped(big(5)) {\n    Some((x, y)) => x.w149 + y.w0\n    None => 0\n  }\n  print(\"{a.w0} {b.w149} {n}\")\n  print(\"{score(DEEP, big(1), big(100))}\")\n}\n";

#[test]
fn generic_code_that_doesn_t_reach_itself_is_never_past_the_caps() {
    let fields: Vec<String> = (0..150).map(|i| format!("w{i}: i64")).collect();
    let values: Vec<String> = (0..150).map(|i| format!("w{i}: n + {i}")).collect();
    let big = format!(
        "type Big = {{ {} }}\n\nfn big(n: i64) -> Big {{ Big {{ {} }} }}\n\n",
        fields.join(", "),
        values.join(", ")
    );
    let deep = (0..20).fold("W { first: true }".to_owned(), |inner, _| {
        format!("Flip {{ inner: {inner} }}")
    });
    let source = [P, CHOOSER, &big, &SHALLOW.replace("DEEP", &deep)].concat();
    runs_as("shallow", &source, "1 150 159\n150307\n");
}

/// A function that calls itself with a record of two of its type parameter's values, each
/// changed in place through its dictionary's method that takes it `inout`.
const BUMP: &str = r#"trait Bump {
  fn bump(inout self, by: i64)
  fn total(self) -> i64
}

impl Bump for P {
  fn bump(inout self, by: i64) { self.x = self.x + by }
  fn total(self) -> i64 { self.x + self.y }
}

type Two<A> = { a: A, b: A }

impl<A: Bump> Bump for Two<A> {
  fn bump(inout self, by: i64) {
    self.a.bump(by)
    self.b.bump(by + 1)
  }
  fn total(self) -> i64 { self.a.total() + self.b.total() }
}

fn grow<T: Bump>(inout x: T, n: i64) -> i64 {
  x.bump(1)
  if n == 0 { return x.total() }
  var t = Two { a: x, b: x }
  let r = grow(inout t, n - 1)
  x.bump(t.total() % 7)
  r + x.total()
}

fn main() / io {
  var p = P { x: 1, y: 2 }
  print("{grow(inout p, 3)} {p}")
  var q = P { x: 1, y: 2 }
  print("{grow(inout q, 10)} {q}")
}
"#;

#[test]
fn an_inout_value_past_the_cap_of_words_is_changed_through_its_dictionary() {
    let source = [P, BUMP].concat();
    runs_boxing(
        "bump",
        &source,
        "156 P { x: 8, y: 2 }\n83016 P { x: 2, y: 2 }\n",
    );
}
