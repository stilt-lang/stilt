//! The tests and doc examples that `stilt test` runs: the root package's own
//! (program.running-tests and program.doc-examples), or with `--std` the standard library's
//! (std.examples).

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::hir::{DeclKind, ItemHir};
use stilt_hir::module_hir;

/// A test or doc example of a program's own files: the file, and the index of its body in the
/// file's module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TestBody {
    /// The file.
    pub file: SourceFile,
    /// The index of its body in the file's module.
    pub index: u32,
}

/// The tests and doc examples of the root package's own files, in the order of the files, then of
/// their bodies in each file (program.test-declarations and program.doc-examples), never a
/// dependency's (program.running-tests). `stilt test` runs each through its [`FnRef::TestEntry`].
#[salsa::tracked(returns(ref))]
pub fn tests(db: &dyn Db, program: Program) -> Vec<TestBody> {
    program
        .files(db)
        .iter()
        .filter(|&&file| stilt_db::package_of(db, program, file) == 0)
        .flat_map(|&file| {
            let module = module_hir(db, program, file);
            test_bodies(module)
                .into_iter()
                .map(move |index| TestBody { file, index })
        })
        .collect()
}

/// The tests and doc examples of the standard library's files, which are the library's own
/// tests (std.examples): `stilt test --std` runs them, and `stilt test` never does.
#[salsa::tracked(returns(ref))]
pub fn std_tests(db: &dyn Db, program: Program) -> Vec<TestBody> {
    program
        .std(db)
        .iter()
        .flat_map(|&file| {
            let module = module_hir(db, program, file);
            test_bodies(module)
                .into_iter()
                .map(move |index| TestBody { file, index })
        })
        .collect()
}

/// The bodies of a module's tests and doc examples, in order.
pub(crate) fn test_bodies(module: &stilt_hir::hir::ModuleHir) -> Vec<u32> {
    let mut found = Vec::new();
    for entry in &module.items {
        match entry {
            ItemHir::Use => {}
            ItemHir::Decl(d) => {
                found.extend(d.examples.iter().map(|b| b.0));
                match &d.kind {
                    DeclKind::Test(_, body) => found.push(body.0),
                    DeclKind::Trait(t) => {
                        let examples = t.members.iter().flat_map(|m| m.examples.iter());
                        found.extend(examples.map(|b| b.0));
                    }
                    _ => {}
                }
            }
            ItemHir::Impl(imp) => {
                found.extend(
                    imp.members
                        .iter()
                        .flat_map(|m| m.examples.iter().map(|b| b.0)),
                );
            }
        }
    }
    found.sort_unstable();
    found
}
