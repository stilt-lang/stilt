//! Tests that the code a reach gives an image, update after update, leaves the image holding what
//! counting the program afresh gives each function reached, and that each update gives the
//! functions whose code changed: when an edit changes a body, changes what a function consumes, and
//! makes a function that consumes its parameter reachable (values.consumed-parameters).

use std::collections::HashMap;
use std::sync::Arc;

use salsa::Setter as _;
use stilt_db::{Database, Program, SourceFile, program, source_file};
use stilt_mir::mir::Function;
use stilt_mir::{CheckErrors, FnRef, reached};

use super::Reach;
use crate::cache::Counted;

const MAIN: &str = "use util\n\nfn shown(n: i64) -> str { util.label(\"x\", n) }\n\nfn main() / io {\n  print(shown(3))\n}\n";

/// `label` reads its parameter `s`, and `spare`, which no code calls, consumes its own.
const UTIL: &str = "pub fn label(s: str, n: i64) -> str {\n  if s.len() > 9 { \"long\" } else { \"hello {n}\" }\n}\n\npub fn spare(s: str) -> str { s }\n";

/// A program held in a database, with its reach and the code its image holds.
struct Held {
    db: Database,
    program: Program,
    /// The file `util.lt`, which the tests edit.
    file: SourceFile,
    reach: Reach,
    counted: Counted,
    image: HashMap<FnRef, Arc<Function>>,
}

impl Held {
    fn new() -> Self {
        let db = Database::default();
        let main = source_file(&db, "main.lt".into(), vec!["main".into()], MAIN.into());
        let file = source_file(&db, "util.lt".into(), vec!["util".into()], UTIL.into());
        let program = program(&db, vec![main, file]);
        let mut held = Self {
            db,
            program,
            file,
            reach: Reach::default(),
            counted: Counted::default(),
            image: HashMap::new(),
        };
        held.update();
        held
    }

    fn edit(&mut self, from: &str, to: &str) {
        let text = String::from_utf8(self.file.bytes(&self.db).clone()).expect("UTF-8");
        assert!(text.contains(from), "the program holds {from:?}");
        let text = text.replace(from, to);
        self.file.set_bytes(&mut self.db).to(text.into_bytes());
    }

    /// Gives the image what the reach gives it, checks that the image then holds what
    /// counting the program afresh gives, and returns the names of the functions whose code
    /// the update changed in the image.
    fn update(&mut self) -> Vec<String> {
        let (db, program) = (&self.db, self.program);
        let errors = CheckErrors::default();
        let roots = vec![FnRef::Main];
        let given = self
            .reach
            .update(db, program, roots, &errors, &mut self.counted);
        let mut changed = Vec::new();
        for f in given {
            if self.image.get(&f.name).is_none_or(|g| **g != *f) {
                changed.push(f.name.symbol());
            }
            self.image.insert(f.name.clone(), f);
        }
        let fresh = Counted::default().insert(db, program, reached(db, program, &errors).functions);
        for f in &fresh {
            let held = self.image.get(&f.name);
            assert!(
                held.is_some_and(|g| **g == **f),
                "the image holds {}",
                f.name
            );
        }
        changed
    }
}

#[test]
fn a_body_edit_gives_the_edited_function() {
    let mut held = Held::new();
    held.edit("\"hello {n}\"", "\"hi {n}\"");
    assert_eq!(held.update(), ["util.label"]);
}

#[test]
fn an_edit_that_changes_what_a_function_consumes_gives_its_callers() {
    let mut held = Held::new();
    held.edit("{ \"long\" }", "{ s }");
    assert_eq!(held.update(), ["main.shown", "util.label"]);
    held.edit("{ s }", "{ \"long\" }");
    assert_eq!(held.update(), ["main.shown", "util.label"]);
}

#[test]
fn an_edit_that_reaches_a_function_that_consumes_gives_it_and_its_caller() {
    let mut held = Held::new();
    held.edit("{ \"long\" }", "{ spare(s) }");
    assert_eq!(held.update(), ["main.shown", "util.label", "util.spare"]);
}
