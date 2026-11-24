//! The search for a smaller program that still fails as the given one does: whole files left out
//! first, then a file's top-level items, then its lines, each in chunks that halve as long as
//! leaving one out keeps the failure, as delta debugging does. Each candidate is tested by
//! `fails`, which runs the command on it.

use std::collections::BTreeMap;

/// A program's files, by their paths relative to its root, each as its lines.
pub(crate) type Files = BTreeMap<String, Vec<String>>;

/// How many candidates a search tests at most, so that it ends on a slow command.
const TRIES: usize = 2_000;

/// A search's state: the smallest failing program found, and how many candidates it tested.
pub(crate) struct Search<F> {
    pub(crate) best: Files,
    pub(crate) tried: usize,
    fails: F,
}

impl<F: FnMut(&Files) -> bool> Search<F> {
    pub(crate) fn new(files: Files, fails: F) -> Self {
        Self {
            best: files,
            tried: 0,
            fails,
        }
    }

    /// Reduces the program until no step finds a smaller one that fails, or the tries run out.
    pub(crate) fn run(mut self, keep: &str) -> Self {
        loop {
            let before = lines(&self.best);
            self.drop_files(keep);
            let paths: Vec<String> = (self.best.keys())
                .filter(|p| p.is_empty() || is_module(p))
                .cloned()
                .collect();
            for path in paths {
                self.shrink(&path, items);
                self.shrink(&path, |ls| (0..ls.len()).map(|i| (i, i + 1)).collect());
            }
            if lines(&self.best) == before || self.tried >= TRIES {
                return self;
            }
        }
    }

    fn test(&mut self, candidate: &Files) -> bool {
        if self.tried >= TRIES {
            return false;
        }
        self.tried += 1;
        (self.fails)(candidate)
    }

    /// Leaves out each file but `keep`, the program's entry, that the failure doesn't need.
    fn drop_files(&mut self, keep: &str) {
        let paths: Vec<String> = (self.best.keys())
            .filter(|p| *p != keep && is_module(p))
            .cloned()
            .collect();
        for path in paths {
            let mut candidate = self.best.clone();
            candidate.remove(&path);
            if self.test(&candidate) {
                self.best = candidate;
            }
        }
    }

    /// Leaves out chunks of the units of the file `path` that `units` splits it into, each a
    /// range of its lines, in halves, then quarters, down to single units.
    fn shrink(&mut self, path: &str, units: impl Fn(&[String]) -> Vec<(usize, usize)>) {
        let mut chunk = (units(&self.best[path]).len() / 2).max(1);
        loop {
            let mut start = 0;
            loop {
                let lines = &self.best[path];
                let found = units(lines);
                if start >= found.len() {
                    break;
                }
                let end = (start + chunk).min(found.len());
                let (from, to) = (found[start].0, found[end - 1].1);
                let mut candidate = self.best.clone();
                let file = candidate.get_mut(path).expect("the file is in the program");
                file.drain(from..to);
                if self.test(&candidate) {
                    self.best = candidate;
                } else {
                    start = end;
                }
            }
            if chunk == 1 {
                return;
            }
            chunk /= 2;
        }
    }
}

/// The top-level items of a file, each the range of its lines: one that starts at the first
/// column, with the lines after it that are blank or indented, and those that close it.
fn items(lines: &[String]) -> Vec<(usize, usize)> {
    let mut out: Vec<(usize, usize)> = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        let starts = !line.is_empty() && !line.starts_with([' ', '\t', '}', ')', ']']);
        match out.last_mut() {
            Some(last) if !starts => last.1 = i + 1,
            _ => out.push((i, i + 1)),
        }
    }
    out
}

/// Whether the file at `path` is a module, whose text a search shrinks, rather than a manifest.
pub(crate) fn is_module(path: &str) -> bool {
    std::path::Path::new(path)
        .extension()
        .is_some_and(|e| e == "lt")
}

/// How many lines a program has.
pub(crate) fn lines(files: &Files) -> usize {
    files.values().map(Vec::len).sum()
}

#[cfg(test)]
mod tests {
    use super::{Files, Search, lines};

    fn program(text: &str) -> Files {
        Files::from([(
            "main.lt".to_owned(),
            text.lines().map(str::to_owned).collect(),
        )])
    }

    #[test]
    fn a_search_keeps_only_what_the_failure_needs() {
        // The failure needs a function named `boom` and a call of it.
        let text = "fn a() -> i64 {\n  1\n}\n\nfn boom() {\n  let x = 2\n}\n\nfn main() / io {\n  let y = a()\n  boom()\n  print(\"{y}\")\n}\n";
        let fails = |f: &Files| {
            let all = f["main.lt"].join("\n");
            all.contains("fn boom()") && all.contains("  boom()")
        };
        let found = Search::new(program(text), fails).run("main.lt");
        assert_eq!(found.best["main.lt"], ["fn boom() {", "  boom()"]);
        assert!(lines(&found.best) < text.lines().count());
    }

    #[test]
    fn a_file_the_failure_doesnt_need_is_left_out() {
        let mut files = program("fn main() {}");
        files.insert("util.lt".to_owned(), vec!["fn f() {}".to_owned()]);
        let found = Search::new(files, |f: &Files| f.contains_key("main.lt")).run("main.lt");
        assert_eq!(found.best.keys().collect::<Vec<_>>(), ["main.lt"]);
    }
}
