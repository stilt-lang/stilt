use stilt_hir::hir::{Capabilities, Capability, Item, Limit, Limits, Name};
use stilt_syntax::{TextRange, TextSize};

use super::limits::{Limited, errors};
use super::remedies::{Negation, Remedy};
use super::sites::divides;
use super::{Effect, Effects, Fact, Key, Site, Summary, Via, effects, reach};
use crate::tast::{Expr, ExprKind};
use crate::ty::Ty;

fn function(name: &str) -> Key {
    Key::Function(Item {
        home: Name::from("app"),
        name: Name::from(name),
    })
}

fn summary(name: &str, panics: bool, names: &[&str]) -> Summary {
    Summary {
        key: function(name),
        panics: panics.then(|| Some(Fact::noun("index"))),
        panics_unproved: panics.then(|| Some(Fact::noun("index"))),
        overflows: None,
        allocates: None,
        diverges: None,
        diverges_unproved: None,
        locks: None,
        capabilities: Capabilities::default(),
        names: names.iter().map(|n| function(n)).collect(),
        descends: true,
        descends_unproved: true,
        limits: Limits::default(),
    }
}

fn at(start: u32) -> TextRange {
    TextRange::at(TextSize::from(start), TextSize::from(1))
}

fn keys(reached: &super::fixed::Reached) -> Vec<Key> {
    reached.keys().cloned().collect()
}

#[test]
fn nothing_panics_without_a_direct_panic() {
    let summaries = [summary("a", false, &["b"]), summary("b", false, &["a"])];
    assert!(reach(&summaries, Effect::Panic).is_empty());
    assert!(reach(&[], Effect::Panic).is_empty());
}

#[test]
fn panics_reach_every_caller_through_an_item_found_before() {
    // `d` reaches the panic of `a` only through `c` and `b`, which come after it, so finding
    // it takes several rounds, and each item keeps the one it panics through.
    let summaries = [
        summary("d", false, &["c"]),
        summary("c", false, &["b"]),
        summary("e", false, &["f"]),
        summary("b", false, &["a"]),
        summary("a", true, &[]),
    ];
    let reached = reach(&summaries, Effect::Panic);
    let expected: Vec<Key> = ["a", "b", "c", "d"].map(function).into();
    assert_eq!(keys(&reached), expected);
    assert_eq!(reached[&function("a")], Via::Own(Some(Fact::noun("index"))));
    assert_eq!(reached[&function("d")], Via::Through(function("c")));
}

#[test]
fn a_cycle_panics_if_one_of_its_items_does() {
    let summaries = [
        summary("a", false, &["b"]),
        summary("b", false, &["a", "c"]),
        summary("c", true, &[]),
    ];
    let expected: Vec<Key> = ["a", "b", "c"].map(function).into();
    assert_eq!(keys(&reach(&summaries, Effect::Panic)), expected);
}

#[test]
fn a_limited_item_counts_as_one_without_the_effect_it_rules_out() {
    let limited = Summary {
        limits: Limits {
            panic: true,
            ..Limits::default()
        },
        allocates: Some(None),
        ..summary("b", true, &[])
    };
    let summaries = [summary("a", false, &["b"]), limited];
    let found = effects(&summaries);
    assert!(found.panic.is_empty());
    assert_eq!(keys(&found.alloc), [function("a"), function("b")]);
}

#[test]
fn capabilities_reach_callers_but_not_through_a_limited_item() {
    // facts.capabilities and facts.without: `a` names the native `print` and `b`, which reads a
    // file but is limited by `without fs`, so it counts as one without it.
    let console = Capability::Console;
    let print = Summary {
        capabilities: Capabilities::one(console),
        ..summary("print", false, &[])
    };
    let limited = Summary {
        capabilities: Capabilities::one(Capability::Fs),
        limits: Limits {
            capabilities: Capabilities::one(Capability::Fs),
            ..Limits::default()
        },
        ..summary("b", false, &[])
    };
    let found = effects(&[summary("a", false, &["print", "b"]), print, limited]);
    let has = |c, name| found.has(Effect::Capability(c), &function(name));
    assert!(has(console, "a") && has(console, "print") && !has(console, "b"));
    assert!(!has(Capability::Fs, "a") && !has(Capability::Fs, "b"));
    assert_eq!(
        found.origin(Effect::Capability(console), &function("a")).0,
        &function("print")
    );
}

#[test]
fn a_built_in_method_allocates() {
    let show = Key::BuiltIn(stilt_hir::decls::prelude_item("Show"), Name::from("show"));
    let summaries = [Summary {
        names: vec![show.clone()],
        ..summary("a", false, &[])
    }];
    let found = effects(&summaries);
    assert_eq!(found.alloc[&function("a")], Via::Through(show.clone()));
    assert!(found.has(Effect::Alloc, &show));
    assert!(!found.has(Effect::Panic, &show));
}

/// Sites of a body: an index, a call of `risky`, which panics through `deep`, and a call of
/// `safe`, with the effects of the items they name.
fn checked_sites() -> ([Site; 3], Effects) {
    let sites = [
        Site {
            panic: Some(Fact::noun("index")),
            ..Site::new(at(0), Vec::new())
        },
        Site::new(
            at(4),
            vec![function("safe"), function("risky"), function("worse")],
        ),
        Site::new(at(8), vec![function("safe")]),
    ];
    let summaries = [
        summary("worse", true, &[]),
        summary("risky", false, &["deep"]),
        summary("deep", true, &[]),
    ];
    (sites, effects(&summaries))
}

#[test]
fn reports_direct_facts_and_the_first_name_that_has_the_effect() {
    let (sites, effects) = checked_sites();
    let (module, function_name) = (Name::from("app"), Name::from("f"));
    let header = [(Limit::Panic, at(40))];
    let limited = Limited {
        module: &module,
        function: &function_name,
        key: None,
        header: &header,
        own: &[],
        raises_str: false,
        effects: &effects,
    };
    let found: Vec<_> = errors(&limited, &sites, &|at| u32::from(at), &|_| String::new())
        .into_iter()
        .map(|d| (d.range, d.message, d.notes[0].clone()))
        .collect();
    let fact = |text: &str| format!("{text}, but the module's header says `without panic`");
    // The note is on the header, in the file's positions, which shifting the body leaves.
    let note = stilt_diag::Label {
        range: at(40),
        text: "the limit".to_owned(),
        in_file: true,
    };
    assert_eq!(
        found,
        [
            (at(0), fact("this index can panic"), note.clone()),
            (
                at(4),
                fact("`risky` can panic, through an index in `deep`"),
                note
            ),
        ]
    );
}

#[test]
fn a_function_s_own_limit_gets_a_note() {
    let (sites, effects) = checked_sites();
    let (module, function_name) = (Name::from("app"), Name::from("f"));
    let own = [(Limit::Panic, at(2))];
    let limited = Limited {
        module: &module,
        function: &function_name,
        key: None,
        header: &[],
        own: &own,
        raises_str: false,
        effects: &effects,
    };
    let d = &errors(&limited, &sites, &|at| u32::from(at), &|_| String::new())[0];
    assert_eq!(
        d.message,
        "this index can panic, but `f` says `without panic`"
    );
    assert_eq!(d.notes[0].range, at(2));
}

#[test]
fn only_a_nonzero_integer_literal_keeps_a_division_from_panicking() {
    let expr = |kind| Expr {
        kind,
        ty: Ty::i64(),
        at: at(0),
    };
    let int = |text: &str| expr(ExprKind::Int(text.to_owned()));
    let negated = |text: &str| {
        expr(ExprKind::Unary(
            stilt_hir::hir::UnaryOp::Neg,
            Box::new(int(text)),
        ))
    };
    let a = int("7");
    assert!(!divides(&a, &int("0x10")));
    assert!(!divides(&a, &negated("2")));
    assert!(divides(&a, &int("0")));
    assert!(divides(&a, &negated("0x0")));
    assert!(divides(
        &a,
        &expr(ExprKind::Local(stilt_hir::hir::LocalId(0)))
    ));
    let real = Expr {
        ty: Ty::f64(),
        ..int("7")
    };
    assert!(!divides(&real, &int("0")));
}

#[test]
fn a_callee_s_own_operation_or_native_function_is_named() {
    let native = Key::Member(stilt_hir::decls::prelude_item("List"), Name::from("insert"));
    let summaries = [
        summary("at", true, &[]),
        Summary {
            names: vec![native.clone()],
            ..summary("put", false, &[])
        },
        Summary {
            panics: Some(None),
            ..Summary {
                key: native.clone(),
                ..summary("x", false, &[])
            }
        },
    ];
    let effects = effects(&summaries);
    let sites = [
        Site::new(at(0), vec![function("at")]),
        Site::new(at(2), vec![function("put")]),
        Site::new(at(4), vec![native]),
    ];
    let (module, function_name) = (Name::from("app"), Name::from("f"));
    let own = [(Limit::Panic, at(9))];
    let limited = Limited {
        module: &module,
        function: &function_name,
        key: None,
        header: &[],
        own: &own,
        raises_str: false,
        effects: &effects,
    };
    let messages: Vec<String> = errors(&limited, &sites, &|at| u32::from(at), &|_| String::new())
        .into_iter()
        .map(|d| d.message)
        .collect();
    assert_eq!(
        messages,
        [
            "`at` can panic, through an index, but `f` says `without panic`",
            "`put` can panic, through `List.insert`, but `f` says `without panic`",
            "`List.insert` can panic, but `f` says `without panic`",
        ]
    );
}

fn range(a: u32, b: u32) -> TextRange {
    TextRange::new(TextSize::from(a), TextSize::from(b))
}

/// An index of a list of integers, which `get` with `0` keeps from panicking, and an `assert`.
fn remedied_sites() -> [Site; 2] {
    let index = Site {
        panic: Some(Fact::noun("index")),
        remedy: Some(Remedy::Get {
            start: TextSize::from(10),
            open: range(12, 13),
            close: range(14, 15),
            fallback: "0",
            map: false,
            parens: true,
        }),
        ..Site::new(range(10, 15), Vec::new())
    };
    let assert = Site {
        panic: Some(Fact::noun("`assert`")),
        remedy: Some(Remedy::Raise {
            keyword: range(20, 27),
            condition: range(27, 28),
            negation: Negation::Not,
        }),
        ..Site::new(range(20, 28), Vec::new())
    };
    [index, assert]
}

#[test]
fn an_operation_that_panics_gets_its_remedy_as_a_fix() {
    let effects = effects(&[]);
    let (module, function_name) = (Name::from("app"), Name::from("f"));
    let own = [(Limit::Panic, at(2))];
    let limited = |raises_str| Limited {
        module: &module,
        function: &function_name,
        key: None,
        header: &[],
        own: &own,
        raises_str,
        effects: &effects,
    };
    let sites = remedied_sites();
    let fixes = |raises_str| -> Vec<Vec<(TextRange, String)>> {
        errors(&limited(raises_str), &sites, &|at| u32::from(at), &|_| {
            String::new()
        })
        .into_iter()
        .map(|d| {
            d.fixes
                .iter()
                .flat_map(|f| f.edits.iter().map(|e| (e.range, e.text.clone())))
                .collect()
        })
        .collect()
    };
    let get = vec![
        (range(10, 10), "(".to_owned()),
        (range(12, 13), ".get(".to_owned()),
        (range(14, 15), ") else 0)".to_owned()),
    ];
    // An `assert` raises instead only in a function that raises a `str`.
    assert_eq!(fixes(false), [get.clone(), Vec::new()]);
    assert_eq!(
        fixes(true),
        [
            get,
            vec![
                (range(20, 27), "if !".to_owned()),
                (range(28, 28), " { raise \"assertion failed\" }".to_owned()),
            ]
        ]
    );
}
