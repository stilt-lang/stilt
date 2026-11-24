//! A counterexample's values, written by their structure as std.show-output shows a value
//! nested inside another, whatever `Show` impls the program writes (tests.property-verdict).

use stilt_types::generable::{Graph, Node};

use super::values::{Val, int_value};

/// The text of a value of a node's type, as it shows nested.
pub(super) fn shown(g: &Graph, k: usize, v: &Val) -> String {
    let list = |slots: &mut dyn Iterator<Item = (usize, &Val)>| -> Vec<String> {
        slots.map(|(s, x)| shown(g, s, x)).collect()
    };
    match (&g.nodes[k], v) {
        (Node::Bool, Val::Word(w)) => (if *w == 0 { "false" } else { "true" }).to_owned(),
        (Node::Int { signed, .. }, Val::Word(w)) => int_value(*w, *signed).to_string(),
        (Node::Float { f32 }, Val::Word(w)) => stilt_runtime::shown_float(*f32, *w),
        (Node::Str, Val::Str(s)) => stilt_runtime::quoted(s),
        (Node::Unit, _) => "()".to_owned(),
        (Node::Tuple(slots), Val::Seq(xs)) if slots.len() == 1 => {
            format!("({},)", shown(g, slots[0], &xs[0]))
        }
        (Node::Tuple(slots), Val::Seq(xs)) => {
            let parts = list(&mut slots.iter().copied().zip(xs));
            format!("({})", parts.join(", "))
        }
        (Node::List(elem), Val::Seq(xs)) => {
            let parts = list(&mut xs.iter().map(|x| (*elem, x)));
            format!("[{}]", parts.join(", "))
        }
        (Node::Map(key, value), Val::Map(entries)) => {
            let parts: Vec<String> = entries
                .iter()
                .map(|(kx, vx)| format!("{}: {}", shown(g, *key, kx), shown(g, *value, vx)))
                .collect();
            format!("{{{}}}", parts.join(", "))
        }
        (Node::Record(name, fields), _) if fields.is_empty() => format!("{name} {{}}"),
        (Node::Record(name, fields), Val::Seq(xs)) => {
            let parts: Vec<String> = fields
                .iter()
                .zip(xs)
                .map(|((f, s), x)| format!("{f}: {}", shown(g, *s, x)))
                .collect();
            format!("{name} {{ {} }}", parts.join(", "))
        }
        (Node::Variants(vs), Val::Variant(n, xs)) if xs.is_empty() => vs[*n].0.to_string(),
        (Node::Variants(vs), Val::Variant(n, xs)) => {
            let parts = list(&mut vs[*n].1.iter().copied().zip(xs));
            format!("{}({})", vs[*n].0, parts.join(", "))
        }
        _ => String::new(),
    }
}
