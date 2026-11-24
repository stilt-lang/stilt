use super::{P, allocates_nothing, runs_as};

#[test]
fn generic_functions_over_records_of_several_words_allocate_nothing() {
    let source = format!(
        "{P}type Pair<T> = {{ a: T, b: T }}\n\nfn id<T>(x: T) -> T {{ x }}\n\nfn pair<T>(x: T) -> Pair<T> {{ Pair {{ a: x, b: x }} }}\n\nfn swap<T>(inout a: T, inout b: T) {{\n  let t = a\n  a = b\n  b = t\n}}\n\nfn sum(p: P) -> i64 {{\n  var a = id(p)\n  var b = P {{ x: 3, y: 4 }}\n  swap(inout a, inout b)\n  let pp = pair(b)\n  let (q, n) = id((a, 5))\n  a.x * 1000 + b.x * 100 + pp.a.x + pp.b.y + q.y * n\n}}\n\nfn main() / io {{\n  print(\"{{sum(P {{ x: 1, y: 2 }})}}\")\n}}\n"
    );
    let mir = runs_as("generic", &source, "3123\n");
    for name in [
        "main.sum",
        "main.id<ss>",
        "main.pair<ss>",
        "main.swap<ss>",
        "main.id<sss>",
    ] {
        allocates_nothing(&mir, name);
    }
}

#[test]
fn an_option_of_a_record_is_built_and_matched_without_allocating() {
    let source = format!(
        "{P}fn pick<T>(first: bool, a: T, b: T) -> Option<T> {{\n  if first {{ Some(a) }} else if false {{ Some(b) }} else {{ None }}\n}}\n\nfn total(p: P, q: P) -> i64 {{\n  let o: Option<P> = Some(p)\n  let a = match o {{\n    Some(r) => r.x + r.y\n    None => 0\n  }}\n  let b = match pick(true, q, p) {{\n    Some(P {{ x, y }}) => x * y\n    None => -1\n  }}\n  let c = match pick(false, q, p) {{\n    Some(r) => r.x\n    None => 100\n  }}\n  a + b + c\n}}\n\nfn main() / io {{\n  print(\"{{total(P {{ x: 1, y: 2 }}, P {{ x: 3, y: 4 }})}}\")\n}}\n"
    );
    let mir = runs_as("option", &source, "115\n");
    allocates_nothing(&mir, "main.total");
    allocates_nothing(&mir, "main.pick<ss>");
}

#[test]
fn a_function_without_alloc_over_records_checks_and_allocates_nothing() {
    let source = format!(
        "{P}fn swap<T>(p: (T, T)) -> (T, T) {{ (p.1, p.0) }}\n\nfn larger<T>(first: bool, a: T, b: T) -> Option<T> {{\n  if first {{ Some(a) }} else {{ Some(b) }}\n}}\n\nfn score(m: Map<str, P>, k: str, p: P) -> i64 without alloc {{\n  let (a, b) = swap((p, P {{ x: 1, y: 1 }}))\n  let best = match larger(a.x > b.x, a, b) {{\n    Some(r) => r.x + r.y\n    None => 0\n  }}\n  let found = match m.get(k) {{\n    Some(q) => q.x * q.y\n    None => -1\n  }}\n  best * 100 + found\n}}\n\nfn main() / io {{\n  var m = Map.new()\n  m.insert(\"a\", P {{ x: 3, y: 4 }})\n  print(\"{{score(m, \"a\", P {{ x: 5, y: 6 }})}} {{score(m, \"b\", P {{ x: 0, y: 0 }})}}\")\n}}\n"
    );
    let mir = runs_as("without", &source, "1112 199\n");
    for name in ["main.score", "main.swap<ss>", "main.larger<ss>"] {
        allocates_nothing(&mir, name);
    }
}

pub(crate) const CHOOSER: &str = "trait Chooser {\n  fn choose<T>(self, a: T, b: T) -> T\n  fn wrap<T>(self, a: T) -> Option<T>\n  fn pair<T>(self, a: T) -> (T, T) {\n    (self.choose(a, a), a)\n  }\n}\n\ntype W = { first: bool }\n\nimpl Chooser for W {\n  fn choose<T>(self, a: T, b: T) -> T { if self.first { a } else { b } }\n  fn wrap<T>(self, a: T) -> Option<T> { if self.first { Some(a) } else { None } }\n}\n\ntype Flip<C> = { inner: C }\n\nimpl<C: Chooser> Chooser for Flip<C> {\n  fn choose<T>(self, a: T, b: T) -> T { self.inner.choose(b, a) }\n  fn wrap<T>(self, a: T) -> Option<T> { self.inner.wrap(a) }\n}\n\n";

#[test]
fn a_bound_s_methods_with_type_parameters_of_their_own_take_records_unboxed() {
    let source = format!(
        "{P}{CHOOSER}fn score<C: Chooser>(c: C, p: P, q: P) -> i64 {{\n  let a = c.choose(p, q)\n  let b = match c.wrap((q, p)) {{\n    Some((r, s)) => r.x * 10 + s.y\n    None => 0\n  }}\n  let (d, e) = c.pair(p)\n  a.x * 1000 + b * 10 + d.x + e.y\n}}\n\nfn main() / io {{\n  let p = P {{ x: 1, y: 2 }}\n  let q = P {{ x: 3, y: 4 }}\n  let w = W {{ first: true }}\n  print(\"{{score(w, p, q)}} {{score(Flip {{ inner: w }}, p, q)}} {{score(Flip {{ inner: W {{ first: false }} }}, p, q)}}\")\n}}\n"
    );
    let mir = runs_as("own-generics", &source, "1323 3323 1003\n");
    for name in [
        "main.score<main.W[]>",
        "main.score<main.Flip[main.W[]]>",
        "<main.Flip as main.Chooser>.wrap<main.W[],ssss>",
        "main.Chooser.pair<main.Flip[main.W[]],ss>",
    ] {
        allocates_nothing(&mir, name);
    }
}

#[test]
fn a_dictionary_s_method_gives_a_record_of_self_back_unboxed() {
    let source = format!(
        "{P}trait Monoid {{\n  fn combine(self, other: Self) -> Self\n  fn twice(self) -> Self {{ self.combine(self) }}\n}}\n\nimpl Monoid for P {{\n  fn combine(self, o: P) -> P {{ P {{ x: self.x + o.x, y: self.y + o.y }} }}\n}}\n\ntype Opt<T> = {{ v: Option<T> }}\n\nimpl<T: Monoid> Monoid for Opt<T> {{\n  fn combine(self, o: Opt<T>) -> Opt<T> {{\n    match (self.v, o.v) {{\n      (Some(a), Some(b)) => Opt {{ v: Some(a.combine(b)) }}\n      (Some(a), None) => Opt {{ v: Some(a) }}\n      (None, b) => Opt {{ v: b }}\n    }}\n  }}\n}}\n\nfn fold<M: Monoid>(xs: List<M>, z: M) -> M {{\n  var acc = z\n  for x in xs {{ acc = acc.combine(x).twice() }}\n  acc\n}}\n\nfn main() / io {{\n  let p = fold([P {{ x: 1, y: 2 }}, P {{ x: 3, y: 4 }}], P {{ x: 0, y: 0 }})\n  let o = fold([Opt {{ v: Some(P {{ x: 1, y: 1 }}) }}, Opt {{ v: None }}], Opt {{ v: None }})\n  print(\"{{p}} {{o.v}}\")\n}}\n"
    );
    let mir = runs_as(
        "self-results",
        &source,
        "P { x: 10, y: 16 } Some(P { x: 4, y: 4 })\n",
    );
    allocates_nothing(&mir, "main.fold<ss>");
    allocates_nothing(&mir, "main.fold<sss>");
}

/// A record of 58 words, more than a shape's mask tells, two of them strings.
const BIG: &str = r#"type Big = { w0: i64, w1: i64, w2: i64, w3: i64, w4: i64, w5: i64, w6: i64, w7: i64, w8: i64, w9: i64, w10: i64, w11: i64, w12: i64, w13: i64, w14: i64, w15: i64, w16: i64, w17: i64, w18: i64, w19: i64, w20: i64, w21: i64, w22: i64, w23: i64, w24: i64, w25: i64, w26: i64, w27: i64, w28: i64, w29: i64, w30: i64, w31: i64, w32: i64, w33: i64, w34: i64, w35: i64, w36: i64, w37: i64, w38: i64, w39: i64, w40: i64, w41: i64, w42: i64, w43: i64, w44: i64, w45: i64, w46: i64, w47: i64, w48: i64, w49: i64, w50: i64, w51: i64, w52: i64, w53: i64, w54: i64, w55: i64, name: str, tag: str }

fn id<T>(x: T) -> T { x }

fn pair<T>(x: T) -> (T, T) { (x, x) }

fn pick<T>(first: bool, a: T, b: T) -> Option<T> {
  if first { Some(a) } else { Some(b) }
}

fn swap<T>(inout a: T, inout b: T) {
  let t = a
  a = b
  b = t
}

fn apply<T>(f: fn(T) -> T, x: T) -> T { f(x) }

fn keep<T>(xs: List<T>, x: T) -> List<T> {
  var out = xs
  out.push(x)
  out
}

fn sum(b: Big) -> i64 { b.w0 + b.w55 + b.name.len() }

fn main() / io {
  let a = Big { w0: 1 + 0, w1: 1 + 1, w2: 1 + 2, w3: 1 + 3, w4: 1 + 4, w5: 1 + 5, w6: 1 + 6, w7: 1 + 7, w8: 1 + 8, w9: 1 + 9, w10: 1 + 10, w11: 1 + 11, w12: 1 + 12, w13: 1 + 13, w14: 1 + 14, w15: 1 + 15, w16: 1 + 16, w17: 1 + 17, w18: 1 + 18, w19: 1 + 19, w20: 1 + 20, w21: 1 + 21, w22: 1 + 22, w23: 1 + 23, w24: 1 + 24, w25: 1 + 25, w26: 1 + 26, w27: 1 + 27, w28: 1 + 28, w29: 1 + 29, w30: 1 + 30, w31: 1 + 31, w32: 1 + 32, w33: 1 + 33, w34: 1 + 34, w35: 1 + 35, w36: 1 + 36, w37: 1 + 37, w38: 1 + 38, w39: 1 + 39, w40: 1 + 40, w41: 1 + 41, w42: 1 + 42, w43: 1 + 43, w44: 1 + 44, w45: 1 + 45, w46: 1 + 46, w47: 1 + 47, w48: 1 + 48, w49: 1 + 49, w50: 1 + 50, w51: 1 + 51, w52: 1 + 52, w53: 1 + 53, w54: 1 + 54, w55: 1 + 55, name: "n1", tag: "t" }
  var b = Big { w0: 100 + 0, w1: 100 + 1, w2: 100 + 2, w3: 100 + 3, w4: 100 + 4, w5: 100 + 5, w6: 100 + 6, w7: 100 + 7, w8: 100 + 8, w9: 100 + 9, w10: 100 + 10, w11: 100 + 11, w12: 100 + 12, w13: 100 + 13, w14: 100 + 14, w15: 100 + 15, w16: 100 + 16, w17: 100 + 17, w18: 100 + 18, w19: 100 + 19, w20: 100 + 20, w21: 100 + 21, w22: 100 + 22, w23: 100 + 23, w24: 100 + 24, w25: 100 + 25, w26: 100 + 26, w27: 100 + 27, w28: 100 + 28, w29: 100 + 29, w30: 100 + 30, w31: 100 + 31, w32: 100 + 32, w33: 100 + 33, w34: 100 + 34, w35: 100 + 35, w36: 100 + 36, w37: 100 + 37, w38: 100 + 38, w39: 100 + 39, w40: 100 + 40, w41: 100 + 41, w42: 100 + 42, w43: 100 + 43, w44: 100 + 44, w45: 100 + 45, w46: 100 + 46, w47: 100 + 47, w48: 100 + 48, w49: 100 + 49, w50: 100 + 50, w51: 100 + 51, w52: 100 + 52, w53: 100 + 53, w54: 100 + 54, w55: 100 + 55, name: "n100", tag: "t" }
  let c = id(a)
  let (d, e) = pair(b)
  let f = match pick(false, a, b) {
    Some(x) => x
    None => a
  }
  var p = a
  swap(inout p, inout b)
  let g = apply(|x: Big| { var y = x
    y.w0 = x.w0 * 2
    y }, a)
  var xs = keep([a, b], c)
  xs[1].w3 = 7
  var m = Map.new()
  m["k"] = d
  m["k"].w1 = 9
  let mk = m["k"]
  print("{sum(c)} {sum(d)} {sum(e)} {sum(f)} {sum(p)} {sum(b)} {sum(g)}")
  print("{xs.len()} {xs[1].w3} {sum(xs[2])} {mk.w1} {xs == [a, a, a]}")
  print("{xs[0].name} {mk.w55}")
}
"#;

#[test]
fn a_record_of_more_than_forty_eight_words_goes_through_generic_code_without_a_box() {
    let mir = runs_as(
        "big-record",
        BIG,
        "59 259 259 259 259 59 60\n3 7 59 9 false\nn1 155\n",
    );
    for name in [
        "main.id<",
        "main.pair<",
        "main.pick<",
        "main.swap<",
        "main.apply<",
        "main.keep<",
    ] {
        let instances: Vec<&str> = mir
            .lines()
            .filter_map(|l| l.strip_prefix("fn ").filter(|f| f.starts_with(name)))
            .map(|f| f.split('(').next().unwrap_or(f))
            .collect();
        assert!(!instances.is_empty(), "no instance of {name}");
        for f in instances {
            allocates_nothing(&mir, f);
        }
    }
}

#[test]
fn an_inout_value_of_several_words_reaches_a_dictionary_s_method_and_comes_back() {
    let source = format!(
        "{P}trait Bump {{\n  fn bump(inout self, by: i64)\n}}\n\nimpl Bump for P {{\n  fn bump(inout self, by: i64) {{ self.x = self.x + by }}\n}}\n\nfn twice<T: Bump>(inout t: T) {{\n  t.bump(1)\n  t.bump(10)\n}}\n\nfn main() / io {{\n  var p = P {{ x: 1, y: 2 }}\n  twice(inout p)\n  var ps = [p, p]\n  twice(inout ps[1])\n  print(\"{{p}} {{ps}}\")\n}}\n"
    );
    runs_as(
        "inout-method",
        &source,
        "P { x: 12, y: 2 } [P { x: 12, y: 2 }, P { x: 23, y: 2 }]\n",
    );
}
