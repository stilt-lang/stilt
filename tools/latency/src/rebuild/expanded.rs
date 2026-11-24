//! The size of the benchmark's expansions (goal visible-expansion-size). `stilt show` prints each
//! function of the benchmark as written, and with `--expanded` each macro use in it replaced by its
//! expansion, and the line of the use saying how many lines the expansion takes (macros.showing).
//! The benchmark as written is the lines of its functions, and expanded, those lines with each
//! use's expansion in place of the line it stands on. The target, which is proposed, so that the
//! harness reports it without failing on it: the expanded benchmark is at most twice its source.

use std::path::Path;

use serde_json::Value;

use super::{Version, sources};

/// How many times its source the expanded benchmark may be (goal visible-expansion-size, proposed).
const VISIBLE_EXPANSION_SIZE: f64 = 2.0;

/// The lines of a version's functions: as written and expanded, and its macro uses with the
/// lines their expansions take.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct Size {
    pub(super) written: usize,
    pub(super) expanded: usize,
    pub(super) uses: usize,
    pub(super) generated: usize,
}

impl Size {
    /// The size of one function, from what `show` prints of it as written and expanded.
    fn of(written: &str, expanded: &str) -> Self {
        let mut size = Self {
            written: lines(written),
            expanded: lines(expanded),
            ..Self::default()
        };
        for taken in expansions(expanded) {
            size.uses += 1;
            size.generated += taken;
            size.expanded += taken.saturating_sub(1);
        }
        size
    }

    fn add(&mut self, other: Self) {
        self.written += other.written;
        self.expanded += other.expanded;
        self.uses += other.uses;
        self.generated += other.generated;
    }
}

/// The size of every function of the version, as `stilt show`, answered by its engine,
/// prints it.
pub(super) fn measure(version: &Version) -> Result<Size, String> {
    let mut size = Size::default();
    for module in modules(&version.dir)? {
        for function in functions(version, &module)? {
            let written = show(version, &["show", &function])?;
            let expanded = show(version, &["show", "--expanded", &function])?;
            size.add(Size::of(&written, &expanded));
        }
    }
    Ok(size)
}

/// The line of the report that gives the size, and whether it is at most twice the source.
pub(super) fn report(name: &str, size: Size) -> String {
    let float = |n: usize| f64::from(u32::try_from(n).unwrap_or(u32::MAX));
    let ratio = float(size.expanded) / float(size.written.max(1));
    let verdict = if ratio <= VISIBLE_EXPANSION_SIZE {
        "at most twice it"
    } else {
        "more than twice it"
    };
    format!(
        "{name}, expanded: its functions take {} lines as written and {} with the {} macro uses' \
         {} lines in place, {ratio:.2} times their source, {verdict} (visible-expansion-size, proposed)",
        size.written, size.expanded, size.uses, size.generated
    )
}

/// The modules of the program in `dir`, each named by its file's path there.
fn modules(dir: &Path) -> Result<Vec<String>, String> {
    let mut found = Vec::new();
    sources(dir, &mut found)?;
    let mut names: Vec<String> = (found.iter())
        .filter_map(|f| {
            f.strip_prefix(dir)
                .ok()?
                .with_extension("")
                .to_str()
                .map(str::to_owned)
        })
        .map(|path| path.replace(std::path::MAIN_SEPARATOR, "."))
        .collect();
    names.sort();
    Ok(names)
}

/// The addresses of the functions of `module`, as its record from `show --json` lists them.
fn functions(version: &Version, module: &str) -> Result<Vec<String>, String> {
    let shown = show(version, &["show", "--json", module])?;
    let record: Value = serde_json::from_str(&shown).map_err(|e| format!("{module}: {e}"))?;
    let listed = record["functions"].as_array().into_iter().flatten();
    Ok(listed
        .filter_map(|f| f["function"].as_str().map(str::to_owned))
        .collect())
}

/// What `stilt ARGS` on the version prints, or what it reported when it failed.
fn show(version: &Version, args: &[&str]) -> Result<String, String> {
    let output = version.engine.answer(args)?;
    if output.status.success() {
        return Ok(String::from_utf8_lossy(&output.stdout).into_owned());
    }
    let stderr = String::from_utf8_lossy(&output.stderr);
    Err(format!("`stilt {}` fails:\n{stderr}", args.join(" ")))
}

/// The lines of a function as `show` prints it, without its module's header, and, for a method,
/// without the first line of its impl or trait, before it, and the `}` that closes it, after it.
fn lines(shown: &str) -> usize {
    let all: Vec<&str> = shown.lines().collect();
    let own = match all.first() {
        Some(head) if head.starts_with("module ") => &all[1..],
        _ => &all[..],
    };
    // A method's lines are indented inside its impl's or trait's, which aren't.
    let method = (own.iter())
        .find(|l| declares(l))
        .is_some_and(|l| l.starts_with(' '));
    if method {
        own.len().saturating_sub(2)
    } else {
        own.len()
    }
}

/// Whether a line declares a function or a macro.
fn declares(line: &str) -> bool {
    let line = line.trim_start();
    let line = line.strip_prefix("pub ").unwrap_or(line);
    line.starts_with("fn ") || line.starts_with("macro ")
}

/// The lines that each use's expansion takes, as `show --expanded` says at the end of the use's
/// line: "`rx.regex!` expands to 12 lines".
fn expansions(shown: &str) -> Vec<usize> {
    (shown.split("!` expands to ").skip(1))
        .filter_map(|after| {
            let digits = after
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(after.len());
            after[..digits].parse().ok()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const WRITTEN: &str = "module patterns [core]\n/// A clock.\npub fn clock(text: str) -> Option<Captures> [panic] {\n  let m = rx.regex!(\"^(\\\\d\\\\d?):(\\\\d\\\\d)$\") // an index can panic\n  m(text)\n}\n";

    const EXPANDED: &str = "module patterns [core]\n/// A clock.\npub fn clock(text: str) -> Option<Captures> [panic] {\n  let m = { | line#1: str | matcher.search(line#1, 2, true, f) } // an index can panic; `rx.regex!` expands to 42 lines\n  m(text)\n}\n";

    const METHOD: &str = "module window [meta]\nimpl<n: i64> Window<n> {\n  /// Whether it holds `n` values.\n  pub fn full(self) -> bool { self.added >= n }\n}\n";

    #[test]
    fn a_function_is_its_lines_without_the_module_s_header() {
        assert_eq!(lines(WRITTEN), 5);
        assert_eq!(lines("module m [core]\nfn one() -> i64 { 1 }\n"), 1);
    }

    #[test]
    fn a_method_is_its_lines_without_its_impl_s() {
        assert_eq!(lines(METHOD), 2);
    }

    #[test]
    fn each_use_takes_the_lines_show_says_in_place_of_its_own() {
        assert_eq!(expansions(WRITTEN), Vec::<usize>::new());
        assert_eq!(expansions(EXPANDED), vec![42]);
        let two = "  f(a!(1), b!(2)) // `a!` expands to 1 line; `b!` expands to 3 lines\n";
        assert_eq!(expansions(two), vec![1, 3]);
        let size = Size::of(WRITTEN, EXPANDED);
        assert_eq!(
            size,
            Size {
                written: 5,
                expanded: 46,
                uses: 1,
                generated: 42
            }
        );
    }

    #[test]
    fn the_report_says_whether_the_expansion_is_at_most_twice_the_source() {
        let size = |written, expanded| Size {
            written,
            expanded,
            uses: 1,
            generated: expanded - written + 1,
        };
        assert!(
            report("meta", size(100, 200))
                .ends_with("at most twice it (visible-expansion-size, proposed)")
        );
        assert!(
            report("meta", size(100, 201))
                .ends_with("more than twice it (visible-expansion-size, proposed)")
        );
        assert!(report("meta", size(100, 150)).contains("1.50 times their source"));
    }
}
