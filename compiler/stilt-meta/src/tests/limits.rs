//! The memory of a run (macros.step-limits), past what the conformance suite shows: the
//! threads of the fibers that handlers which take control nest weigh in it, so that a run
//! which nests thousands stops as one out of memory does, before the system refuses the
//! compiler a thread, which the reference interpreter, with no threads, never needs.

use stilt_db::Database;

use super::{diagnostics, program};

/// Nests a `with` whose handler takes control in each of nine thousand frames, within the
/// 10,000 that a run may call, which would need a thread for each.
const NESTS: &str = "use std.meta

effect Ask {
  fn ask() -> i64
}

fn nest(n: i64) -> i64 / Ask {
  if n == 0 {
    Ask.ask()
  } else {
    let h = handler Ask -> i64 {
      fn ask() -> i64 { resume(1) + 1 }
    }
    with h { nest(n - 1) } + Ask.ask()
  }
}

fn top(n: i64) -> i64 {
  let h = handler Ask -> i64 {
    fn ask() -> i64 { resume(1) }
  }
  with h { nest(n) }
}

/// Gives the depth's answer.
pub macro deep(e: meta.Expr) -> meta.Expr {
  let n = top(9000)
  quote { $n + $e }
}
";

#[test]
fn a_run_that_nests_fibers_without_end_stops_as_one_out_of_memory() {
    let main = "meta use nests\n\nfn main() {\n  let _ = nests.deep!(1)\n}\n";
    let db = Database::default();
    let (program, _) = program(&db, &[("main.lt", main), ("nests.lt", NESTS)]);
    let found = diagnostics(&db, program);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].starts_with("E0226 `nests.deep!` didn't finish: it ran out of memory; running"),
        "{found:?}"
    );
}
