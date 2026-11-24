//! An edit of a type that a function reflects on: the function's body is
//! neither checked nor compiled again, since it takes the type's descriptor, and the code of the
//! descriptor follows the edit.

use salsa::Setter as _;
use stilt_db::{Database, Program, SourceFile};
use stilt_hir::hir::{Item, Name};

use crate::described::Described;
use crate::{FnRef, functions};

const MAIN: &str =
    "use geo\nuse show\n\nfn main() / io {\n  print(show.fields(geo.Point { x: 1, y: 2 }))\n}\n";

const SHOW: &str = "use std.meta\n\npub fn fields<T>(value: T) -> str {\n  var names: List<str> = []\n  match T.shape() {\n    Record(fields) => { for f in fields { names.push(f.name()) } }\n    _ => {}\n  }\n  \" \".join(names)\n}\n";

fn program(db: &Database, files: &[(&str, &str)]) -> (Program, Vec<SourceFile>) {
    let files: Vec<_> = files
        .iter()
        .map(|&(path, text)| {
            let module = path.trim_end_matches(".lt").split('/').map(str::to_owned);
            stilt_db::source_file(
                db,
                path.to_owned(),
                module.collect(),
                text.as_bytes().to_vec(),
            )
        })
        .collect();
    (stilt_db::program(db, files.clone()), files)
}

fn item(home: &str, name: &str) -> Item {
    Item {
        home: Name::from(home),
        name: Name::from(name),
    }
}

/// The text of the code of `f`.
fn code(db: &Database, program: Program, f: &FnRef) -> String {
    functions(db, program, f.clone())
        .iter()
        .map(|g| crate::print(g))
        .collect()
}

#[test]
fn an_edit_of_a_reflected_type_compiles_the_function_that_reflects_on_it_once() {
    let mut db = Database::recording();
    let geo = "pub type Point = { x: i64, y: i64 }\n";
    let (program, files) = program(
        &db,
        &[("main.lt", MAIN), ("show.lt", SHOW), ("geo.lt", geo)],
    );
    assert_eq!(stilt_types::check(&db, program), &[]);
    let reflecting = FnRef::Function(item("show", "fields"));
    let point = FnRef::Describe(Box::new(Described::Con(item("geo", "Point"), Box::new([]))));
    let before = code(&db, program, &reflecting);
    let described = code(&db, program, &point);
    assert!(
        described.find("\"x\"") < described.find("\"y\""),
        "{described}"
    );
    let _ = db.ran_queries();
    files[2]
        .set_bytes(&mut db)
        .to(b"pub type Point = { y: i64, x: i64 }\n".to_vec());
    assert_eq!(stilt_types::check(&db, program), &[]);
    assert_eq!(code(&db, program, &reflecting), before);
    let ran = db.ran_queries();
    assert!(
        !ran.iter().any(|q| q == "functions"),
        "the function that reflects is compiled once: {ran:?}"
    );
    let inferred = ran.iter().filter(|q| *q == "infer_body").count();
    assert_eq!(inferred, 1, "only `main` is checked again: {ran:?}");
    let described = code(&db, program, &point);
    assert!(
        described.find("\"y\"") < described.find("\"x\""),
        "{described}"
    );
    assert!(db.ran_queries().iter().any(|q| q == "functions"));
}
