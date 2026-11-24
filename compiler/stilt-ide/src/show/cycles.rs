//! The fact that a type can form a cycle (cycles.can-form-cycle): `show` writes it at the end of
//! the first line of a declared type, as a comment that names the fields or variants through which
//! it can, and a type's record lists them under `cycle`.

use serde_json::{Value, json};
use stilt_db::{Database, Program};
use stilt_edit::Kind;
use stilt_hir::decls::Queried;
use stilt_hir::hir::{Item, Name};

use super::parts::FileParts;

/// The fields or variants through which the values of part `i` can form a cycle, in
/// declaration order, if it declares a type.
pub(super) fn through(db: &Database, program: Program, of: &FileParts, i: usize) -> Vec<String> {
    let part = &of.parts[i];
    if part.body || part.kind != Kind::Type {
        return Vec::new();
    }
    let Some(name) = part.path.rsplit('.').next() else {
        return Vec::new();
    };
    let item = Item {
        home: stilt_hir::module_hir(db, program, of.file).name,
        name: Name::from(name),
    };
    let decls = Queried { db, program };
    stilt_types::cycles::cycles(&decls, &item)
        .iter()
        .map(ToString::to_string)
        .collect()
}

/// The canonical text of a type with the fact written at the end of its first line, if it
/// can form a cycle.
pub(super) fn noted(text: &str, through: &[String]) -> String {
    if through.is_empty() {
        return text.to_owned();
    }
    let names: Vec<String> = through.iter().map(|n| format!("`{n}`")).collect();
    let listed = match names.split_last() {
        Some((last, rest)) if !rest.is_empty() => format!("{} and {last}", rest.join(", ")),
        _ => names.join(""),
    };
    let (first, rest) = text
        .split_once('\n')
        .map_or((text, None), |(f, r)| (f, Some(r)));
    let mut noted = format!("{first}  // can form a cycle, through {listed}");
    if let Some(rest) = rest {
        noted.push('\n');
        noted.push_str(rest);
    }
    noted
}

/// Adds the fields or variants through which part `i` can form a cycle to its record.
pub(super) fn annotate(
    db: &Database,
    program: Program,
    record: &mut Value,
    of: &FileParts,
    i: usize,
) {
    let through = through(db, program, of, i);
    if !through.is_empty() {
        record["cycle"] = json!(through);
    }
}

#[cfg(test)]
mod tests {
    use super::noted;

    #[test]
    fn the_fact_names_each_field_at_the_end_of_the_first_line() {
        let names = |ns: &[&str]| ns.iter().map(|n| (*n).to_owned()).collect::<Vec<_>>();
        assert_eq!(noted("type A = { x: i64 }", &[]), "type A = { x: i64 }");
        assert_eq!(
            noted(
                "type N = { next: Option<sync.Shared<N>> }",
                &names(&["next"])
            ),
            "type N = { next: Option<sync.Shared<N>> }  // can form a cycle, through `next`"
        );
        assert_eq!(
            noted("type G =\n  | A(X)\n  | B(Y)", &names(&["A", "B", "C"])),
            "type G =  // can form a cycle, through `A`, `B` and `C`\n  | A(X)\n  | B(Y)"
        );
    }
}
