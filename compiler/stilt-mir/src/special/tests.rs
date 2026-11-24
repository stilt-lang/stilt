//! Specialization on programs' MIR (builds.specialization and builds.what-stays-generic): what each
//! instantiation knows is in its code, a function that no root reaches isn't compiled,
//! instantiations whose code is the same are one function, and a polymorphic recursion and a
//! polymorphic argument keep their dictionaries, with a bounded number of instantiations whatever
//! the types do.

use std::sync::Arc;

use stilt_db::{Database, program, source_file};

use super::groups::groups;
use super::{Specialized, specialize};
use crate::mir::{Callee, Const, Function, Operand, Rvalue, Stmt, Terminator};
use crate::{CheckErrors, FnRef, reached};

/// The release build's code of a program of one file, and the functions that keep their
/// dictionaries.
fn special(source: &str) -> (Specialized, Vec<String>) {
    let db = Database::default();
    let main = source_file(&db, "main.lt".into(), vec!["main".into()], source.into());
    let program = program(&db, vec![main]);
    let functions = reached(&db, program, &CheckErrors::default()).functions;
    let found = groups(&db, program, &functions);
    let mut kept: Vec<String> = found.kept.iter().map(FnRef::symbol).collect();
    kept.sort();
    let special = specialize(&functions, &[FnRef::Main], &|f| found.kept.contains(f));
    (special, kept)
}

/// The compiled functions made from the function of the debug build named `name`.
fn made_from<'a>(s: &'a Specialized, name: &str) -> Vec<&'a Arc<Function>> {
    s.functions
        .iter()
        .filter(|f| {
            s.made_from
                .get(&f.name)
                .is_some_and(|g| g.generic().symbol() == name)
        })
        .collect()
}

/// The callees of a function's calls.
fn callees(f: &Function) -> Vec<&Callee> {
    f.blocks
        .iter()
        .filter_map(|b| match &b.term {
            Terminator::Call { callee, .. } => Some(callee),
            _ => None,
        })
        .collect()
}

const TWO_TYPES: &str = "trait Size {\n  fn size(self) -> i64\n}\n\nimpl Size for i64 {\n  fn size(self) -> i64 { self }\n}\n\nimpl Size for str {\n  fn size(self) -> i64 { self.len() }\n}\n\nfn total<T: Size>(xs: List<T>) -> i64 {\n  var n = 0\n  for x in xs {\n    n += x.size()\n  }\n  n\n}\n\nfn unused<T: Size>(x: T) -> i64 { x.size() }\n\nfn main() / io {\n  let a = total([1, 2, 3])\n  let b = total([\"ab\", \"c\"])\n  print(\"{a} {b}\")\n}\n";

#[test]
fn a_function_called_at_two_types_has_two_instantiations_that_call_directly() {
    let (s, kept) = special(TWO_TYPES);
    assert!(kept.is_empty(), "{kept:?}");
    let total = made_from(&s, "main.total");
    assert_eq!(
        total.len(),
        2,
        "{:?}",
        total.iter().map(|f| &f.name).collect::<Vec<_>>()
    );
    for f in total {
        let callees = callees(f);
        assert!(
            callees.iter().all(|c| matches!(c, Callee::Direct(_))),
            "{} calls through a dictionary: {callees:?}",
            f.name
        );
        let witness = f.params[1].local;
        let reads_witness = f.blocks.iter().flat_map(|b| &b.stmts).any(
            |s| matches!(s, Stmt::Assign(_, r) if r.operands().contains(&&Operand::Local(witness))),
        );
        assert!(!reads_witness, "{} reads its witness at run time", f.name);
    }
}

#[test]
fn a_function_that_no_root_reaches_is_not_compiled() {
    let (s, _) = special(TWO_TYPES);
    assert_eq!(made_from(&s, "main.unused").len(), 0);
    assert!(
        s.functions
            .iter()
            .all(|f| !f.name.symbol().contains("main.unused"))
    );
}

#[test]
fn instantiations_whose_code_is_the_same_are_one_function() {
    let source = "fn keep<T: Show>(x: T) -> T { x }\n\nfn main() / io {\n  let a = keep(1)\n  let b: u64 = keep(2)\n  print(\"{a} {b}\")\n}\n";
    let (s, _) = special(source);
    let keep = made_from(&s, "main.keep");
    assert_eq!(keep.len(), 1, "i64 and u64 are held alike: {:?}", s.folded);
    assert_eq!(s.folded.len(), 1, "{:?}", s.folded);
}

#[test]
fn a_value_parameter_is_its_number() {
    let source = "type Mod<p: u64> = { value: u64 }\n\nimpl<p: u64> Mod<p> {\n  fn plus(self, other: Mod<p>) -> Mod<p> { Mod { value: (self.value + other.value) % p } }\n}\n\nfn main() / io {\n  let a: Mod<7> = Mod { value: 5 }\n  let b: Mod<11> = Mod { value: 5 }\n  let x = a.plus(Mod { value: 4 })\n  let y = b.plus(Mod { value: 4 })\n  print(\"{x.value} {y.value}\")\n}\n";
    let (s, _) = special(source);
    let plus = made_from(&s, "main.Mod.plus");
    assert_eq!(plus.len(), 2);
    for f in plus {
        let modulus = f.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
            matches!(s, Stmt::Assign(_, Rvalue::Prim(_, args, _))
                if args.iter().any(|a| matches!(a, Operand::Const(Const::Word(7 | 11)))))
        });
        assert!(modulus, "{} takes its modulus at run time", f.name);
    }
}

#[test]
fn a_polymorphic_recursion_keeps_its_dictionaries() {
    let source = "type Nested<T> = Flat(T) | Deep(Nested<List<T>>)\n\nfn depth<T: Show>(n: Nested<T>) -> str {\n  match n {\n    Flat(x) => \"{x}\",\n    Deep(inner) => depth(inner),\n  }\n}\n\nfn main() / io {\n  print(depth(Deep(Deep(Flat([[1]])))))\n}\n";
    let (s, kept) = special(source);
    assert_eq!(kept, ["main.depth"]);
    let depth = made_from(&s, "main.depth");
    assert_eq!(depth.len(), 1);
    assert!(
        matches!(depth[0].name, FnRef::Function(_)),
        "{}",
        depth[0].name
    );
    assert!(
        callees(depth[0])
            .iter()
            .any(|c| matches!(c, Callee::Method(..))),
        "`depth` shows its value through the dictionary"
    );
}

#[test]
fn a_polymorphic_argument_is_called_through_its_dictionaries() {
    let source = "fn both(f: fn<T: Show>(T) -> str) -> str {\n  let a = f(1)\n  let b = f(\"a\")\n  \"{a} {b}\"\n}\n\nfn quoted<T: Show>(x: T) -> str { \"[{x}]\" }\n\nfn main() / io {\n  print(both(quoted))\n}\n";
    let (s, kept) = special(source);
    assert!(kept.is_empty(), "{kept:?}");
    let both = made_from(&s, "main.both");
    assert_eq!(both.len(), 1);
    assert!(
        callees(both[0])
            .iter()
            .all(|c| matches!(c, Callee::Value(_))),
        "{:?}",
        callees(both[0])
    );
}

#[test]
fn a_type_that_holds_itself_ever_more_deeply_stops_its_instantiations() {
    let source = "type Nested<T> = Flat(T) | Deep(Nested<List<T>>)\n\nfn main() / io {\n  let a: Nested<i64> = Deep(Deep(Flat([[1]])))\n  print(\"{a == a}\")\n}\n";
    let (s, _) = special(source);
    assert!(s.functions.len() < 2000, "{} functions", s.functions.len());
}
