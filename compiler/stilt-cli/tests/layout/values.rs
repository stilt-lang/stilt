use super::{P, allocates, allocates_nothing, body, runs_as};

#[test]
fn an_option_that_pop_returns_is_two_words() {
    let source = "fn drain(xs: List<i64>) -> i64 {\n  var stack = xs\n  var total = 0\n  while true {\n    let top = stack.pop() else { break }\n    total += top\n  }\n  total\n}\n\nfn sign(o: Option<i64>) -> i64 {\n  match o {\n    Some(n) if n < 0 => -1\n    Some(_) => 1\n    None => 0\n  }\n}\n\nfn main() / io {\n  let xs = [4, 5, 6]\n  print(\"{drain(xs)} {sign(Some(-4))} {sign(xs.get(1))} {sign(xs.get(9))} {xs.find(|x| x > 4)}\")\n}\n";
    let mir = runs_as("pop", source, "15 -1 1 0 Some(5)\n");
    allocates_nothing(&mir, "main.drain");
    allocates_nothing(&mir, "main.sign");
    let pop = body(&mir, "main.drain")
        .into_iter()
        .find(|l| l.contains("call std.prelude.List.pop"))
        .expect("drain calls pop");
    assert!(pop.trim_start().starts_with("_5, _6 = call"), "{pop}");
    assert!(
        body(&mir, "main.sign")[0].contains("_1: Borrowed Scalar, _2: Borrowed Scalar"),
        "{mir}"
    );
}

#[test]
fn a_destructuring_let_and_a_record_in_locals_allocate_nothing() {
    let source = format!(
        "{P}fn moved(p: P, d: i64) -> P {{\n  let (a, b) = (p.x + d, p.y - d)\n  P {{ x: a, y: b }}\n}}\n\nfn main() / io {{\n  var p = P {{ x: 1, y: 2 }}\n  p = moved(p, 3)\n  p.x += 1\n  let q = p\n  p.y = 10\n  let t = (q, p.y)\n  let (r, n) = t\n  print(\"{{p}} {{q}} {{r.x + n}} {{q == r}}\")\n}}\n"
    );
    let mir = runs_as(
        "locals",
        &source,
        "P { x: 5, y: 10 } P { x: 5, y: -1 } 15 true\n",
    );
    allocates_nothing(&mir, "main.moved");
    assert!(
        body(&mir, "main.moved")
            .iter()
            .any(|l| l.contains("return _6, _7"))
    );
}

#[test]
fn an_inout_record_is_written_in_place() {
    let source = format!(
        "{P}fn bump(inout p: P, by: i64) {{\n  p.x += by\n  p.y = p.x * 2\n}}\n\nfn main() / io {{\n  var p = P {{ x: 1, y: 0 }}\n  let before = p\n  bump(inout p, 4)\n  var ps = [P {{ x: 0, y: 0 }}, p]\n  let first = ps[0]\n  bump(inout ps[0], 7)\n  ps[1].y = -1\n  print(\"{{before}} {{p}} {{first}} {{ps}}\")\n}}\n"
    );
    let mir = runs_as(
        "inout",
        &source,
        "P { x: 1, y: 0 } P { x: 5, y: 10 } P { x: 0, y: 0 } [P { x: 7, y: 14 }, P { x: 5, y: -1 }]\n",
    );
    allocates_nothing(&mir, "main.bump");
}

#[test]
fn a_variant_with_record_payloads_is_matched_inline() {
    let source = format!(
        "{P}type Shape = | Circle(P, i64) | Rect(P, P) | Empty\n\nfn area(s: Shape) -> i64 {{\n  match s {{\n    Circle(c, r) => c.x + r * r\n    Rect(a, b) => (b.x - a.x) * (b.y - a.y)\n    Empty => 0\n  }}\n}}\n\nfn grow(s: Shape) -> Shape {{\n  match s {{\n    Circle(c, r) => Circle(c, r + 1)\n    Rect(a, b) => Rect(a, P {{ x: b.x + 1, y: b.y + 1 }})\n    Empty => Empty\n  }}\n}}\n\nfn main() / io {{\n  let o = P {{ x: 0, y: 0 }}\n  let shapes = [Circle(o, 2), Rect(o, P {{ x: 2, y: 3 }}), Empty]\n  let grown = shapes.map(grow)\n  print(\"{{shapes.map(area)}} {{grown.map(area)}} {{grown[1]}} {{grown[2] == Empty}}\")\n}}\n"
    );
    let mir = runs_as(
        "variants",
        &source,
        "[4, 6, 0] [9, 12, 0] Rect(P { x: 0, y: 0 }, P { x: 3, y: 4 }) true\n",
    );
    allocates_nothing(&mir, "main.area");
    allocates_nothing(&mir, "main.grow");
}

#[test]
fn a_recursive_type_allocates_one_node_per_variant_with_a_payload() {
    let source = format!(
        "{P}type Tree = | Leaf | Node(Tree, P, Tree)\n\nfn insert(t: Tree, p: P) -> Tree {{\n  match t {{\n    Leaf => Node(Leaf, p, Leaf)\n    Node(l, q, r) => if p.x < q.x {{ Node(insert(l, p), q, r) }} else {{ Node(l, q, insert(r, p)) }}\n  }}\n}}\n\nfn sum(t: Tree) -> i64 {{\n  match t {{\n    Leaf => 0\n    Node(l, q, r) => sum(l) + q.y + sum(r)\n  }}\n}}\n\nfn main() / io {{\n  var t = Leaf\n  for x in [5, 2, 8, 1] {{ t = insert(t, P {{ x, y: x * 10 }}) }}\n  print(\"{{sum(t)}}\")\n}}\n"
    );
    let mir = runs_as("recursive", &source, "160\n");
    allocates(&mir, "main.insert", 3);
    allocates_nothing(&mir, "main.sum");
}

#[test]
fn a_value_of_more_words_than_registers_returns_through_memory() {
    let source = "type Wide = { a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64, i: i64, j: str }\n\nfn wide(n: i64) -> Wide / raise<Wide> {\n  let w = Wide { a: n, b: n + 1, c: n + 2, d: n + 3, e: n + 4, f: n + 5, g: n + 6, h: n + 7, i: n + 8, j: \"j{n}\" }\n  if n < 0 { raise w }\n  w\n}\n\nfn main() / io {\n  let w = try wide(1) catch { e => e }\n  let v = try wide(-1) catch { e => e }\n  print(\"{w.a + w.i} {w.j} {v.b} {v.j}\")\n}\n";
    let mir = runs_as("memory", source, "10 j1 0 j-1\n");
    allocates_nothing(&mir, "main.wide");
}

#[test]
fn a_constant_of_several_words_is_kept_in_its_words() {
    let source = format!(
        "{P}const ORIGIN: P = P {{ x: 1, y: 2 }}\n\nconst NAMED: (str, P) = (\"n\", P {{ x: 3, y: 4 }})\n\nconst MAYBE: Option<P> = Some(P {{ x: 5, y: 6 }})\n\nfn far() -> i64 {{\n  ORIGIN.x + NAMED.1.y + match MAYBE {{\n    Some(p) => p.y\n    None => 0\n  }}\n}}\n\nfn main() / io {{\n  print(\"{{far()}} {{far()}} {{NAMED.0}}\")\n}}\n"
    );
    let mir = runs_as("constants", &source, "11 11 n\n");
    allocates_nothing(&mir, "main.far");
}
