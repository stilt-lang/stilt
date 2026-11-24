//! Tests that a walk kept from one version of a program to the next reaches what a walk from
//! scratch reaches, in its order, and gives every function whose code an edit changed, and none of
//! another module: when an edit changes a body, makes a function reachable, makes one unreachable,
//! edits one that isn't reached, and adds a root.

use std::collections::HashMap;
use std::sync::Arc;

use salsa::Setter as _;
use stilt_db::{Database, Program, SourceFile, program, source_file};

use super::{Walk, reached_from};
use crate::check_errors::CheckErrors;
use crate::mir::Function;
use crate::{FnRef, every_function};

/// A program whose entry reaches `main.shown` and `util.twice`, but not `util.spare`.
const MAIN: &str = "use util\n\nfn shown(n: i64) -> str { \"{util.twice(n)}\" }\n\nfn main() / io {\n  let f = |x: i64| shown(x)\n  print(f(3))\n}\n";

const UTIL: &str =
    "pub fn twice(n: i64) -> i64 { n * 2 }\n\npub fn spare(n: i64) -> i64 { n + 1 }\n";

/// A program held in a database, with the walk kept of it and what a walk from scratch reached
/// last.
struct Held {
    db: Database,
    program: Program,
    /// The file `util.lt`, which the tests edit.
    file: SourceFile,
    walk: Walk,
    last: HashMap<FnRef, Arc<Function>>,
}

impl Held {
    fn new() -> Self {
        Self::with(MAIN, UTIL)
    }

    /// The program of `main` and `util`.
    fn with(main: &str, util: &str) -> Self {
        let db = Database::default();
        let main = source_file(&db, "main.lt".into(), vec!["main".into()], main.into());
        let file = source_file(&db, "util.lt".into(), vec!["util".into()], util.into());
        let program = program(&db, vec![main, file]);
        Self {
            db,
            program,
            file,
            walk: Walk::default(),
            last: HashMap::new(),
        }
    }

    fn edit(&mut self, from: &str, to: &str) {
        let text = String::from_utf8(self.file.bytes(&self.db).clone()).expect("UTF-8");
        assert!(text.contains(from), "the program holds {from:?}");
        let text = text.replace(from, to);
        self.file.set_bytes(&mut self.db).to(text.into_bytes());
    }

    /// Walks the program from `roots` again, checks the walk against one from scratch, and
    /// returns the names of the functions it gives that changed, after checking that it gives
    /// every function that changed, and only functions of the module edited, whose lowering
    /// reads its file, unless it walks afresh.
    fn walk(&mut self, roots: &[FnRef]) -> Vec<String> {
        let errors = CheckErrors::default();
        let walked = self
            .walk
            .walk(&self.db, self.program, roots.to_vec(), &errors);
        let fresh = reached_from(&self.db, self.program, roots, &errors).functions;
        let all = walked.functions(&self.walk);
        assert_eq!(
            names(&all),
            names(&fresh),
            "the walk reaches what one from scratch does"
        );
        assert!(
            all.iter().zip(&fresh).all(|(a, b)| **a == **b),
            "the walk's functions are those of one from scratch"
        );
        let given = names(walked.renewed());
        let mut changed = Vec::new();
        for f in &fresh {
            if self.last.get(&f.name).is_none_or(|g| **g != **f) {
                let name = f.name.symbol();
                assert!(
                    given.contains(&name),
                    "{name} changed, so the walk gives it"
                );
                changed.push(name);
            }
        }
        if !self.last.is_empty() {
            assert!(
                given.iter().all(|f| f.starts_with("util.")),
                "an edit of `util` gives only its functions: {given:?}"
            );
        }
        self.last = fresh
            .iter()
            .map(|f| (f.name.clone(), Arc::clone(f)))
            .collect();
        self.walk.keep(walked);
        changed
    }
}

fn names(functions: &[Arc<Function>]) -> Vec<String> {
    functions.iter().map(|f| f.name.symbol()).collect()
}

fn main_only() -> Vec<FnRef> {
    vec![FnRef::Main]
}

#[test]
fn a_walk_after_no_edit_gives_nothing() {
    let mut held = Held::new();
    let first = held.walk(&main_only());
    assert!(first.contains(&"main.shown".to_owned()), "{first:?}");
    assert!(!first.contains(&"util.spare".to_owned()), "{first:?}");
    salsa::Database::synthetic_write(&mut held.db, salsa::Durability::LOW);
    assert_eq!(held.walk(&main_only()), Vec::<String>::new());
}

#[test]
fn a_body_edit_gives_the_edited_function() {
    let mut held = Held::new();
    held.walk(&main_only());
    held.edit("n * 2", "n * 3");
    assert_eq!(held.walk(&main_only()), ["util.twice"]);
}

#[test]
fn an_edit_that_reaches_a_function_gives_it() {
    let mut held = Held::new();
    held.walk(&main_only());
    held.edit("n * 2", "spare(n) * 2");
    assert_eq!(held.walk(&main_only()), ["util.twice", "util.spare"]);
}

#[test]
fn a_function_edited_while_unreachable_is_given_once_reached_again() {
    let mut held = Held::new();
    held.edit("n * 2", "spare(n) * 2");
    held.walk(&main_only());
    held.edit("spare(n) * 2", "n * 2");
    assert_eq!(held.walk(&main_only()), ["util.twice"]);
    held.edit("n + 1", "n + 10");
    assert_eq!(
        held.walk(&main_only()),
        Vec::<String>::new(),
        "`spare` isn't reached"
    );
    held.edit("n * 2", "spare(n) * 2");
    assert_eq!(held.walk(&main_only()), ["util.twice", "util.spare"]);
}

#[test]
fn a_new_root_gives_what_it_reaches() {
    let mut held = Held::new();
    held.walk(&main_only());
    let every = every_function(&held.db, held.program).clone();
    assert_eq!(held.walk(&every), ["util.spare"]);
}

#[test]
fn an_edit_with_errors_walks_afresh_after_it() {
    let mut held = Held::new();
    held.walk(&main_only());
    held.edit("n * 2", "n * 3");
    let errors = CheckErrors {
        any: true,
        ..CheckErrors::default()
    };
    let walked = held.walk.walk(&held.db, held.program, main_only(), &errors);
    held.walk.keep(walked);
    held.edit("n * 3", "n * 4");
    let walked = held
        .walk
        .walk(&held.db, held.program, main_only(), &CheckErrors::default());
    let given = names(walked.renewed());
    assert!(given.contains(&"main.shown".to_owned()), "{given:?}");
}

/// A generic function of `util` that `main` calls with a record of two words and with an
/// integer, so that two of its instances are reached.
const GENERIC_MAIN: &str = "use util\n\nfn main() / io {\n  let (a, b) = util.swap((util.P { x: 1, y: 2 }, util.P { x: 3, y: 4 }))\n  let (c, d) = util.swap((5, 6))\n  print(\"{a.x} {b.y} {c} {d}\")\n}\n";

const GENERIC_UTIL: &str =
    "pub type P = { x: i64, y: i64 }\n\npub fn swap<T>(p: (T, T)) -> (T, T) { (p.1, p.0) }\n";

#[test]
fn an_edit_of_a_generic_function_gives_each_of_its_instances_in_use() {
    let mut held = Held::with(GENERIC_MAIN, GENERIC_UTIL);
    held.walk(&main_only());
    held.edit("(p.1, p.0)", "(p.0, p.1)");
    let mut given = held.walk(&main_only());
    given.sort();
    assert_eq!(given, ["util.swap", "util.swap<ss>"]);
}
