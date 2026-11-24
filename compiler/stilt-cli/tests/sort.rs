//! Sorting (std.list-sorting; goal debug-speed): keys whose order is the structural `Ord` of
//! an integer type are compared by the runtime as integers, signed or not, and keys of any
//! other order through their dictionary. Either way the sort is stable, both under
//! `stilt run` and as an executable that `stilt build` writes.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

/// Runs `source` under `stilt run` with its MIR written out, then as a built executable, checks
/// that both print `expected` and succeed, and returns the MIR.
fn runs_as(name: &str, source: &str, expected: &str) -> String {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("sort")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    let file = dir.join("main.lt");
    fs::write(&file, source).expect("the program can be written");
    let stilt = env!("CARGO_BIN_EXE_stilt");
    let run = Command::new(stilt)
        .arg("run")
        .arg(&file)
        .env("STILT_DUMP_MIR", "1")
        .output()
        .expect("stilt runs");
    let mir = String::from_utf8_lossy(&run.stderr).into_owned();
    assert_eq!(String::from_utf8_lossy(&run.stdout), expected, "{mir}");
    assert!(run.status.success(), "stilt run: {mir}");
    let exe = dir.join("program");
    let built = Command::new(stilt)
        .args(["build", "-o"])
        .arg(&exe)
        .arg(&file)
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let ran = Command::new(&exe).output().expect("the program runs");
    assert_eq!(String::from_utf8_lossy(&ran.stdout), expected);
    assert!(ran.status.success(), "the executable: {ran:?}");
    mir
}

#[test]
fn integer_keys_sort_as_integers_and_other_keys_through_their_order() {
    let source = "type Card = { rank: i64, suit: str }\n\nimpl Ord for Card {\n  fn compare(self, other: Card) -> Ordering { other.rank.compare(self.rank) }\n}\n\nfn main() / io {\n  let xs = [3, -1, 0, -5, 3]\n  let bytes: List<u8> = [200, 3, 255, 0]\n  let small: List<i8> = [-128, 127, -1, 0]\n  let big: List<u64> = [18446744073709551615, 1, 9223372036854775808]\n  print(\"{xs.sorted()} {bytes.sorted()} {small.sorted()} {big.sorted()}\")\n  let words = [\"bb\", \"a\", \"ccc\", \"dd\"]\n  print(\"{words.sorted_by(|w| w.len())} {words.sorted_desc_by(|w| w.len())}\")\n  let cards = [Card { rank: 2, suit: \"h\" }, Card { rank: 9, suit: \"s\" }, Card { rank: 2, suit: \"d\" }]\n  print(\"{cards.sorted().map(|c| c.suit)} {xs.sorted_desc_by(|x| x * x)}\")\n}\n";
    let mir = runs_as(
        "keys",
        source,
        "[-5, -1, 0, 3, 3] [0, 3, 200, 255] [-128, -1, 0, 127] [1, 9223372036854775808, 18446744073709551615]\n[\"a\", \"bb\", \"dd\", \"ccc\"] [\"ccc\", \"bb\", \"dd\", \"a\"]\n[\"s\", \"h\", \"d\"] [-5, 3, 3, -1, 0]\n",
    );
    // The dictionaries of the integer types' `Ord` tell their order by their tags, 1 for a
    // signed type and 2 for an unsigned one; those of `str` and of `Card` have tag 0.
    for (tag, ty) in [
        (1, "std.prelude.i64"),
        (1, "std.prelude.i8"),
        (2, "std.prelude.u8"),
        (2, "std.prelude.u64"),
        (0, "std.prelude.str"),
        (0, "main.Card"),
    ] {
        let dict = format!("data{tag}[&<{ty} as std.prelude.Ord>");
        assert!(mir.contains(&dict), "no {dict} in\n{mir}");
    }
}
