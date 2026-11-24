//! Tests that a query runs again only when what it read has changed, and that an edit never
//! checks again what read only durable inputs.

use std::sync::{Arc, Mutex, PoisonError};

use salsa::{EventKind, Setter as _, Storage};

use crate::{Db, Program, SourceFile, parse, program, source_file, standard_library};

/// A database that counts the queries it runs, and those whose memos it proves unchanged.
#[salsa::db]
#[derive(Clone)]
struct Counting {
    storage: Storage<Self>,
    runs: Arc<Mutex<(usize, usize)>>,
    extras: crate::Extras,
}

impl Counting {
    fn new() -> Self {
        let runs = Arc::new(Mutex::new((0, 0)));
        let counted = Arc::clone(&runs);
        Self {
            storage: Storage::new(Some(Box::new(move |event| {
                let mut counts = counted.lock().unwrap_or_else(PoisonError::into_inner);
                match event.kind {
                    EventKind::WillExecute { .. } => counts.0 += 1,
                    EventKind::DidValidateMemoizedValue { .. } => counts.1 += 1,
                    _ => {}
                }
            }))),
            runs,
            extras: crate::Extras::default(),
        }
    }

    /// How many queries ran since this was last asked.
    fn runs(&self) -> usize {
        self.counts().0
    }

    /// How many queries ran, and how many memos were proved unchanged, since this was last
    /// asked.
    fn counts(&self) -> (usize, usize) {
        std::mem::take(&mut *self.runs.lock().unwrap_or_else(PoisonError::into_inner))
    }
}

#[salsa::db]
impl salsa::Database for Counting {}

#[salsa::db]
impl Db for Counting {
    fn extras(&self) -> &crate::Extras {
        &self.extras
    }
}

fn parse_all(db: &Counting, program: Program) {
    for &file in program.files(db) {
        parse(db, file);
    }
}

#[test]
fn an_edit_parses_only_its_file_again() {
    let mut db = Counting::new();
    let file = |name: &str, text: &str| {
        let path = format!("{name}.lt");
        SourceFile::new(&db, path, vec![name.to_owned()], text.as_bytes().to_vec())
    };
    let (a, b) = (file("a", "fn a() {}"), file("b", "fn b() {}"));
    let program = Program::new(&db, vec![a, b], Vec::new(), crate::Packages::default());
    parse_all(&db, program);
    assert_eq!(db.runs(), 2);
    a.set_bytes(&mut db).to(b"fn a() { 1 }".to_vec());
    parse_all(&db, program);
    assert_eq!(db.runs(), 1);
    parse_all(&db, program);
    assert_eq!(db.runs(), 0);
}

/// How many items the standard library's files have, from their parses.
#[salsa::tracked]
fn std_items(db: &dyn Db, program: Program) -> usize {
    program
        .std(db)
        .iter()
        .map(|&file| parse(db, file).tree().items().count())
        .sum()
}

#[test]
fn an_edit_proves_nothing_of_the_standard_library_again() {
    // A query that read only durable inputs is proved unchanged on its own, without visiting
    // what it read, which would prove each parse of the standard library again.
    let mut db = Counting::new();
    let a = source_file(
        &db,
        "a.lt".to_owned(),
        vec!["a".to_owned()],
        b"fn a() {}".to_vec(),
    );
    let program = program(&db, vec![a]);
    std_items(&db, program);
    assert_eq!(db.counts().0, 1 + program.std(&db).len());
    a.set_bytes(&mut db).to(b"fn a() { 1 }".to_vec());
    std_items(&db, program);
    assert_eq!(db.counts(), (0, 1));
}

#[test]
fn a_database_makes_the_standard_library_once() {
    let db = Counting::new();
    assert_eq!(standard_library(&db), standard_library(&db));
}

#[test]
fn std_examples_become_empty_doc_lines_in_place() {
    let text = "/// Doubles.\n  /// ex: f(1) == 2\n  ///   ex: g()\n/// exact\nfn f() {}\n";
    assert_eq!(
        super::without_examples(text),
        "/// Doubles.\n  ///\n  ///\n/// exact\nfn f() {}\n"
    );
}
