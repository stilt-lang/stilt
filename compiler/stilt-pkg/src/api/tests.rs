use super::{Api, Entry, Kind, changes, needed};
use crate::version::Change;

fn entry(kind: Kind, shape: &str) -> Entry {
    Entry {
        kind,
        shape: shape.to_owned(),
        facts: Vec::new(),
        default: false,
    }
}

fn api(entries: &[(&str, Entry)]) -> Api {
    Api {
        entries: entries
            .iter()
            .map(|(a, e)| ((*a).to_owned(), e.clone()))
            .collect(),
        io: false,
        unsafe_code: false,
    }
}

/// What going from `old` to `new` needs, and the address of its first change.
fn verdict(old: &Api, new: &Api) -> (Change, String) {
    let steps = changes(old, new);
    let first = steps.first().map(|s| s.address.clone()).unwrap_or_default();
    (needed(&steps), first)
}

#[test]
fn classifies_each_change_of_rule_10() {
    let f = || entry(Kind::Item, "fn(i64) -> i64");
    let base = api(&[("json", entry(Kind::Module, "core")), ("json.parse", f())]);
    assert_eq!(verdict(&base, &base), (Change::Patch, String::new()));
    let removed = api(&[("json", entry(Kind::Module, "core"))]);
    assert_eq!(verdict(&base, &removed).0, Change::Major);
    let added = api(&[
        ("json", entry(Kind::Module, "core")),
        ("json.parse", f()),
        ("json.show", f()),
    ]);
    assert_eq!(
        verdict(&base, &added),
        (Change::Minor, "json.show".to_owned())
    );
    let changed = api(&[
        ("json", entry(Kind::Module, "core")),
        ("json.parse", entry(Kind::Item, "fn(str) -> i64")),
    ]);
    assert_eq!(verdict(&base, &changed).0, Change::Major);
    for fact in [
        "panic", "overflow", "alloc", "div", "copy", "locks", "clock",
    ] {
        let mut gained = base.clone();
        gained.entries.get_mut("json.parse").unwrap().facts = vec![fact.to_owned()];
        assert_eq!(verdict(&base, &gained).0, Change::Major, "gains `{fact}`");
        assert_eq!(verdict(&gained, &base).0, Change::Minor, "loses `{fact}`");
        let what: Vec<String> = changes(&base, &gained)
            .iter()
            .map(super::Step::described)
            .collect();
        assert_eq!(what, [format!("gains `{fact}` in `json.parse`")]);
    }
    let method = |default| Entry {
        default,
        ..entry(Kind::TraitMethod, "fn(Self) -> str")
    };
    let with = api(&[("json.Pretty.pretty", method(false))]);
    let defaulted = api(&[("json.Pretty.pretty", method(true))]);
    assert_eq!(verdict(&api(&[]), &with).0, Change::Major);
    assert_eq!(verdict(&with, &defaulted).0, Change::Minor);
    assert_eq!(verdict(&defaulted, &with).0, Change::Major);
    let tier = |t| api(&[("json", entry(Kind::Module, t))]);
    assert_eq!(verdict(&tier("core"), &tier("advanced")).0, Change::Major);
    assert_eq!(verdict(&tier("advanced"), &tier("core")).0, Change::Minor);
    let io = Api {
        io: true,
        ..base.clone()
    };
    assert_eq!(verdict(&base, &io).0, Change::Major);
    assert_eq!(verdict(&io, &base).0, Change::Minor);
    let wraps = Api {
        unsafe_code: true,
        ..base.clone()
    };
    assert_eq!(verdict(&base, &wraps).0, Change::Major);
    assert_eq!(verdict(&wraps, &base).0, Change::Minor);
}
