use super::{P, allocates, allocates_nothing, body, copies_nothing, runs_as};

const NAMED: &str = "type Named = { id: i64, name: str }\n\n";

#[test]
fn map_entries_of_records_are_held_without_boxes() {
    let source = format!(
        "{P}fn tally(ps: List<P>) -> Map<P, P> {{\n  var m: Map<P, P> = Map.new()\n  for p in ps {{\n    let k = P {{ x: p.x % 2, y: 0 }}\n    let old = m.get(k)\n    m.insert(k, match old {{\n      Some(q) => P {{ x: q.x + p.x, y: q.y + p.y }}\n      None => p\n    }})\n  }}\n  m\n}}\n\nfn main() / io {{\n  var m = tally([P {{ x: 1, y: 2 }}, P {{ x: 2, y: 3 }}, P {{ x: 3, y: 4 }}])\n  m[P {{ x: 0, y: 0 }}].y += 10\n  let gone = m.remove(P {{ x: 1, y: 0 }})\n  for (k, v) in m {{ print(\"{{k}} {{v}}\") }}\n  print(\"{{gone}} {{m.contains(P {{ x: 1, y: 0 }})}} {{m.len()}}\")\n}}\n"
    );
    let mir = runs_as(
        "entries",
        &source,
        "P { x: 0, y: 0 } P { x: 2, y: 13 }\nSome(P { x: 4, y: 6 }) false 1\n",
    );
    assert!(
        !mir.lines().any(|l| l.contains("= box[")),
        "a box in\n{mir}"
    );
}

#[test]
fn records_in_maps_and_closures_keep_their_values() {
    let source = format!(
        "{P}fn main() / io {{\n  let p = P {{ x: 1, y: 2 }}\n  var m = Map.new()\n  m[\"a\"] = p\n  m[\"a\"].x = 10\n  let shift = |q: P| P {{ x: q.x + p.x, y: q.y + p.y }}\n  let moved = shift(m[\"a\"])\n  for (k, v) in m {{ print(\"{{k}} {{v}}\") }}\n  print(\"{{p}} {{moved}} {{m.get(\"b\")}}\")\n}}\n"
    );
    runs_as(
        "maps",
        &source,
        "a P { x: 10, y: 2 }\nP { x: 1, y: 2 } P { x: 11, y: 4 } None\n",
    );
}

#[test]
fn a_record_that_a_closure_takes_is_borrowed_from_its_box() {
    // The closure goes to another user function, which calls it through its value: one that a
    // call of the standard library in its own function calls is inlined there, and compiled
    // nowhere else (Values and costs, "A cheap optimizer before Cranelift").
    let source = "type Item = { id: i64, name: str }\n\nfn retained(items: List<Item>, keep: fn(Item) -> bool) -> List<Item> {\n  items.filter(keep)\n}\n\nfn main() / io {\n  let items = [Item { id: 1, name: \"a{1}\" }, Item { id: 2, name: \"b{2}\" }]\n  let kept = retained(items, |it| it.id > 1)\n  print(\"{kept} {items.len()}\")\n}\n";
    let mir = runs_as("borrowed", source, "[Item { id: 2, name: \"b2\" }] 2\n");
    copies_nothing(&mir, "main.main#0");
}

#[test]
fn a_compound_assignment_reads_an_element_through_its_list_uncounted() {
    let source = "fn tally(n: i64) -> List<i64> {\n  var counts = [0, 0, 0]\n  for i in 0..n { counts[i % 3] += 1 }\n  counts\n}\n\nfn main() / io {\n  print(\"{tally(7)}\")\n}\n";
    let mir = runs_as("compound", source, "[3, 2, 2]\n");
    let lines = body(&mir, "main.tally");
    let read = lines
        .iter()
        .position(|l| l.contains("stilt_rt_list_index"))
        .expect("tally reads an element");
    let start = lines[..read]
        .iter()
        .rposition(|l| l.trim_end().ends_with(':'))
        .unwrap_or(0);
    let block = &lines[start..read];
    assert!(
        block.iter().all(|l| !l.trim_start().starts_with("dup ")),
        "{}",
        lines.join("\n")
    );
    assert!(lines[read - 1].contains("= *_"), "{}", lines.join("\n"));
}

#[test]
fn a_list_holds_its_records_inline_and_writes_them_in_place() {
    let source = format!(
        "{P}{NAMED}fn bump(inout ps: List<P>, by: i64) {{\n  for i in 0..ps.len() {{\n    ps[i].x += by\n    ps[i].y = ps[i].x * 2\n  }}\n}}\n\nfn total(ps: List<P>) -> i64 without alloc {{\n  var t = 0\n  for p in ps {{ t += p.x + p.y }}\n  t\n}}\n\nfn nearer(ps: List<P>, i: i64, j: i64) -> P without alloc {{\n  let a = ps[i]\n  let b = ps[j]\n  if a.x + a.y <= b.x + b.y && ps == ps {{ a }} else {{ P {{ x: b.x, y: ps[j].y }} }}\n}}\n\nfn main() / io {{\n  var ps = [P {{ x: 1, y: 0 }}, P {{ x: 2, y: 0 }}]\n  let b = ps[0]\n  bump(inout ps, 3)\n  ps.push(P {{ x: 10, y: 20 }})\n  let c = ps[2]\n  ps[2].x = 0\n  var ns = [Named {{ id: 1, name: \"a{{1}}\" }}]\n  let m = ns[0]\n  ns[0].name = \"b{{2}}\"\n  ns.push(m)\n  let copy = ns\n  ns[1].id = 7\n  var seen = Map.new()\n  seen[ns] = 1\n  seen[copy] = 2\n  print(\"{{b}} {{c}} {{ps}} {{total(ps)}} {{nearer(ps, 1, 2)}}\")\n  print(\"{{m}} {{ns}} {{copy}} {{ns == copy}} {{ns[1].name.len()}} {{seen.len()}}\")\n}}\n"
    );
    let mir = runs_as(
        "inline-elements",
        &source,
        "P { x: 1, y: 0 } P { x: 10, y: 20 } [P { x: 4, y: 8 }, P { x: 5, y: 10 }, P { x: 0, y: 20 }] 47 P { x: 5, y: 10 }\nNamed { id: 1, name: \"a1\" } [Named { id: 1, name: \"b2\" }, Named { id: 7, name: \"a1\" }] [Named { id: 1, name: \"b2\" }, Named { id: 1, name: \"a1\" }] false 2 2\n",
    );
    allocates_nothing(&mir, "main.bump");
    allocates_nothing(&mir, "main.total");
    allocates_nothing(&mir, "main.nearer");
    allocates(&mir, "main.main", 0);
    let bump = body(&mir, "main.bump");
    let slots = |call: &str| bump.iter().filter(|l| l.contains(call)).count();
    // The list is made unique once, before the loop, and no write checks its count or its
    // bounds, since the counter of `for i in 0..ps.len()` is in bounds of `ps` (goal
    // debug-speed).
    assert_eq!(
        (
            slots("stilt_rt_unique("),
            slots("list_element_at("),
            slots("list_slot_at("),
            slots("stilt_rt_list_slot(")
        ),
        (1, 2, 0, 0),
        "{}",
        bump.join("\n")
    );
    assert!(
        body(&mir, "main.main")
            .iter()
            .any(|l| l.contains("list_append(")),
        "{mir}"
    );
}

#[test]
fn a_list_packs_scalars_narrower_than_a_word() {
    let source = "fn sieve(n: i64) -> List<bool> {\n  var flags = []\n  for _ in 0..n { flags.push(true) }\n  flags[0] = false\n  flags[1] = false\n  for i in 2..n {\n    if flags[i] {\n      var k = i + i\n      while k < n {\n        flags[k] = false\n        k += i\n      }\n    }\n  }\n  flags\n}\n\nfn main() / io {\n  let flags = sieve(30)\n  var primes = []\n  for i in 0..30 { if flags[i] { primes.push(i) } }\n  let bytes = \"Az\".bytes()\n  var small: List<i8> = [-128, 127, -1]\n  small[2] -= 1\n  let mid: List<i16> = [-32768, 300]\n  var wide: List<i32> = [-2147483648, 7]\n  wide.push(-5)\n  let big: List<u32> = [4294967295]\n  var fs: List<f32> = [1.5, -0.25]\n  fs[0] *= 2.0\n  let last = wide.pop()\n  print(\"{primes} {flags.filter(|f| f).len()} {bytes} {bytes[1] - bytes[0]}\")\n  print(\"{small} {mid} {wide} {last} {big} {fs} {fs.map(|f| f.to_f64())}\")\n  print(\"{small.sorted()} {wide.contains(7)} {flags.slice(2, 6)} {[true, false] == [true, false]}\")\n}\n";
    let mir = runs_as(
        "packed",
        source,
        "[2, 3, 5, 7, 11, 13, 17, 19, 23, 29] 10 [65, 122] 57\n[-128, 127, -2] [-32768, 300] [-2147483648, 7] Some(-5) [4294967295] [3.0, -0.25] [3.0, -0.25]\n[-128, -2, 127] true [true, true, false, true] true\n",
    );
    allocates_nothing(&mir, "main.sieve");
    assert!(
        body(&mir, "main.sieve")
            .iter()
            .any(|l| l.contains("store_packed(")),
        "{mir}"
    );
}

#[test]
fn a_list_built_in_generic_code_reads_as_concrete_code_holds_it() {
    let source = format!(
        "{P}{NAMED}fn fill<T>(x: T, n: i64) -> List<T> {{\n  var out = [x]\n  for _ in 1..n {{ out.push(x) }}\n  out\n}}\n\nfn second<T>(xs: List<T>) -> T {{ xs[1] }}\n\nfn put<T>(inout xs: List<T>, i: i64, x: T) {{ xs[i] = x }}\n\nfn swap_at<T>(inout xs: List<T>, i: i64, j: i64) {{\n  let t = xs[i]\n  xs[i] = xs[j]\n  xs[j] = t\n}}\n\nfn set<T>(inout x: T, y: T) {{ x = y }}\n\nfn set_at<T>(inout xs: List<T>, i: i64, y: T) {{ set(inout xs[i], y) }}\n\nfn pairs<T, U>(xs: List<T>, ys: List<U>) -> List<(T, U)> {{ xs.zip(ys) }}\n\nfn main() / io {{\n  var ps = fill(P {{ x: 1, y: 2 }}, 3)\n  ps[1].y = 5\n  put(inout ps, 2, P {{ x: 7, y: 8 }})\n  swap_at(inout ps, 0, 2)\n  set(inout ps[1], P {{ x: 9, y: 9 }})\n  set_at(inout ps, 0, P {{ x: 6, y: 6 }})\n  var ns = fill(Named {{ id: 1, name: \"n{{1}}\" }}, 2)\n  set(inout ns[0].name, \"m{{0}}\")\n  swap_at(inout ns, 0, 1)\n  let flags = fill(true, 3)\n  var bs = [false, true]\n  put(inout bs, 0, true)\n  set_at(inout bs, 1, false)\n  let zipped = pairs(ps, flags)\n  let opts = ps.map(|p| Some(p))\n  print(\"{{ps}} {{second(ps).x}} {{ns}} {{second(ns).name}}\")\n  print(\"{{flags}} {{bs}} {{zipped[0].0.x}} {{zipped[2]}} {{opts[1]}} {{ps.fold(0, |a, p| a + p.y)}}\")\n}}\n"
    );
    runs_as(
        "generic-lists",
        &source,
        "[P { x: 6, y: 6 }, P { x: 9, y: 9 }, P { x: 1, y: 2 }] 9 [Named { id: 1, name: \"n1\" }, Named { id: 1, name: \"m0\" }] m0\n[true, true, true] [true, false] 6 (P { x: 1, y: 2 }, true) Some(P { x: 9, y: 9 }) 17\n",
    );
}

#[test]
fn an_element_of_more_words_than_a_shape_s_mask_tells_is_held_inline() {
    let fields: Vec<String> = (0..50).map(|i| format!("a{i}: i64")).collect();
    let values: Vec<String> = (0..50).map(|i| format!("a{i}: n")).collect();
    let source = format!(
        "type W = {{ {} }}\n\nfn w(n: i64) -> W {{ W {{ {} }} }}\n\nfn main() / io {{\n  var ws = [w(1), w(2)]\n  ws[1].a49 = 5\n  let a = ws[0]\n  ws[0].a0 = 9\n  ws.push(w(3))\n  print(\"{{a.a0}} {{ws[0].a0}} {{ws[1].a49}} {{ws.len()}} {{ws.map(|v| v.a1)}}\")\n}}\n",
        fields.join(", "),
        values.join(", ")
    );
    runs_as("large-elements", &source, "1 9 5 3 [1, 2, 3]\n");
}

#[test]
fn natives_and_patterns_take_elements_as_the_list_holds_them() {
    let source = format!(
        "{NAMED}fn describe(ns: List<Named>) -> str {{\n  match ns {{\n    [] => \"none\"\n    [only] => \"one {{only.name}}\"\n    [first, second, ..rest] => \"{{first.name}} {{second.id}} +{{rest.len()}}\"\n  }}\n}}\n\nfn main() / io {{\n  var ns = [Named {{ id: 3, name: \"c{{3}}\" }}, Named {{ id: 1, name: \"a{{1}}\" }}]\n  ns.insert(1, Named {{ id: 2, name: \"b{{2}}\" }})\n  let gone = ns.remove(0)\n  ns.push(gone)\n  let got = ns.get(1)\n  let sorted = ns.sorted_by(.id)\n  let flags = [true, false, true]\n  var fs = flags.reversed()\n  fs.insert(0, false)\n  let r = fs.remove(1)\n  print(\"{{describe(ns)}} {{describe(ns.slice(0, 1))}} {{describe([])}}\")\n  print(\"{{gone.name}} {{got}} {{sorted.map(.name)}} {{ns.first()}} {{ns.last()}}\")\n  print(\"{{fs}} {{r}} {{flags.enumerate(0)}} {{ns.find(|n| n.id == 1)}} {{ns.contains(gone)}}\")\n}}\n"
    );
    runs_as(
        "natives",
        &source,
        "b2 1 +1 one b2 none\nc3 Some(Named { id: 1, name: \"a1\" }) [\"a1\", \"b2\", \"c3\"] Some(Named { id: 2, name: \"b2\" }) Some(Named { id: 3, name: \"c3\" })\n[false, false, true] true [(0, true), (1, false), (2, true)] Some(Named { id: 1, name: \"a1\" }) true\n",
    );
}
