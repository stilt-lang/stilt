use super::{P, allocates_nothing, runs_as};

#[test]
fn an_error_of_several_words_is_raised_and_caught_in_words() {
    let source = format!(
        "{P}type Fail = | Bad(P) | Worse(str, i64)\n\nfn check(n: i64) -> i64 / raise<Fail> {{\n  if n == 1 {{ raise Bad(P {{ x: n, y: 2 }}) }}\n  if n == 2 {{ raise Worse(\"w\", n) }}\n  n * 10\n}}\n\nfn main() / io {{\n  for n in 0..3 {{\n    let r = try check(n) catch {{\n      Bad(p) => p.x + p.y\n      Worse(s, k) => s.len() + k\n    }}\n    print(\"{{r}}\")\n  }}\n}}\n"
    );
    let mir = runs_as("raised", &source, "0\n3\n3\n");
    allocates_nothing(&mir, "main.check");
}

#[test]
fn an_error_that_a_native_raises_comes_back_in_its_words() {
    let source = "use std.fs\nuse std.io\n\nfn main() / io {\n  let r = try fs.read(\"/nonexistent/stilt\") catch {\n    io.NotFound(p) => \"missing {p}\"\n    e => \"other {e}\"\n  }\n  print(r)\n}\n";
    runs_as("native-error", source, "missing /nonexistent/stilt\n");
}

#[test]
fn an_error_of_several_words_through_a_closure_or_a_row_variable_comes_back_in_its_words() {
    let source = "type Big = { a: i64, b: i64, c: str }\n\nfn apply<T>(f: fn(T) -> T, x: T) -> T {\n  f(f(x))\n}\n\nfn caught<E>(f: fn() -> i64 / raise<E>) -> Result<i64, E> {\n  Result.of(f)\n}\n\nfn grow(x: Big) -> Big / raise<Big> {\n  if x.a > 2 { raise Big { a: x.a * 100, b: x.b, c: \"{x.c}!\" } }\n  Big { a: x.a + 1, b: x.b, c: x.c }\n}\n\nfn key(x: i64) -> i64 / raise<Big> {\n  if x == 3 { raise Big { a: x, b: 2, c: \"k\" } }\n  0 - x\n}\n\nfn main() / io {\n  let r = try apply(|x| grow(x), Big { a: 2, b: 7, c: \"t\" }) catch e => e\n  print(\"{r.a} {r.c}\")\n  match caught(|| raise Big { a: 5, b: 6, c: \"q\" }) {\n    Ok(n) => print(\"ok {n}\"),\n    Err(e) => print(\"err {e.a} {e.c}\"),\n  }\n  let v = try [3, 1, 2].map(|x| if x == 1 { raise Big { a: x, b: 0, c: \"m\" } } else { x }) catch e => [e.a, e.b]\n  let s = try [1, 2, 3].sorted_by(|x| key(x)).len() catch e => e.a * 10 + e.b\n  print(\"{v} {s}\")\n}\n";
    runs_as("row-errors", source, "300 t!\nerr 5 q\n[1, 0] 32\n");
}
