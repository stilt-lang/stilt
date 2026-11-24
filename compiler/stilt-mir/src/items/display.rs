//! How the functions of a compiled program, and what their keys hold, are written in printed
//! MIR and in the names of compiled code.

use std::fmt;

use stilt_hir::hir::Item;

use super::words::write_words;
use super::{Cross, FnRef, Held, ImplRef, Shape};

impl fmt::Display for Held {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Held::Word => write!(f, "w"),
            Held::Words(words) => write_words(f, words),
            Held::Impl(known) => {
                let args: Vec<String> = known.args.iter().map(ToString::to_string).collect();
                let con = &known.con;
                write!(f, "{}.{}[{}]", con.home, con.name, args.join(","))
            }
            Held::Con(con) => write!(f, "con:{}.{}", con.home, con.name),
            Held::Pack(Some(elements)) => {
                let each: Vec<String> = elements.iter().map(ToString::to_string).collect();
                write!(f, "pack[{}]", each.join(","))
            }
            Held::Pack(None) => write!(f, "pack*"),
            Held::Value(v) => write!(f, "v{v}"),
        }
    }
}

impl fmt::Display for Shape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Shape::Con(item) => write!(f, "{}.{}", item.home, item.name),
            Shape::Tuple(n) => write!(f, "tuple{n}"),
            Shape::Pack => write!(f, "pack"),
        }
    }
}

impl fmt::Display for FnRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let item = |i: &Item| format!("{}.{}", i.home, i.name);
        match self {
            FnRef::Function(i) | FnRef::Const(i) => write!(f, "{}", item(i)),
            FnRef::Member(o, n) | FnRef::MemberConst(o, n) => write!(f, "{}.{n}", item(o)),
            FnRef::ImplMethod(t, o, n) => write!(f, "<{} as {}>.{n}", item(o), item(t)),
            FnRef::DefaultMethod(t, n) => write!(f, "{}.{n}", item(t)),
            FnRef::Closure(parent, i) => write!(f, "{parent}#{i}"),
            FnRef::Structural(t, n, shape) => write!(f, "<{shape} as {}>.{n}#structural", item(t)),
            FnRef::Entry(imp, i) => match &**imp {
                ImplRef::Written { trait_item, owner } => {
                    write!(f, "<{} as {}>#entry{i}", item(owner), item(trait_item))
                }
                ImplRef::Structural { trait_item, shape } => {
                    write!(f, "<{shape} as {}>#structural-entry{i}", item(trait_item))
                }
            },
            FnRef::Value(g) => write!(f, "{g}#value"),
            FnRef::Method(t, i) => write!(f, "{}#method{i}", item(t)),
            FnRef::Constructor(v) => write!(f, "{}#constructor", item(v)),
            FnRef::Lent(n) => write!(f, "#lent{n}"),
            FnRef::Main => write!(f, "#main"),
            FnRef::Test(m, i) => write!(f, "{m}#test{i}"),
            FnRef::TestEntry(m, i) => write!(f, "{m}#test{i}#entry"),
            FnRef::PropEntry(m, i) => write!(f, "{m}#test{i}#property"),
            FnRef::Decode(m, i, k) => write!(f, "{m}#test{i}#decode{k}"),
            FnRef::Input(n) => write!(f, "#input{n}"),
            FnRef::InputEntry(n) => write!(f, "#input{n}#entry"),
            FnRef::Instance(g, held) => {
                let held: Vec<String> = held.iter().map(ToString::to_string).collect();
                write!(f, "{g}<{}>", held.join(","))
            }
            FnRef::Forward(t, i, words) => {
                let held = Held::Words(words.clone());
                write!(f, "<#boxed[{held}] as {}>#forward{i}", item(t))
            }
            FnRef::Rebuild(c, into) => write!(f, "#rebuild{}[{c}]", direction(*into)),
            FnRef::Adapt(c, into) => write!(f, "#adapt{}[{c}]", direction(*into)),
            FnRef::Describe(d) => write!(f, "#describe[{d}]"),
            FnRef::Access(d, a) => write!(f, "#{a}[{d}]"),
            FnRef::Shaped(t, w) => write!(f, "<#shaped-{w} as {}>", item(t)),
            FnRef::Specialized(g, n) => write!(f, "{g}@{n}"),
            FnRef::Foreign(c) => write!(f, "#c:{}", c.name),
        }
    }
}

/// The name of a direction of a conversion: into code past the caps, or out of it.
fn direction(into: bool) -> &'static str {
    if into { "-in" } else { "-out" }
}

impl fmt::Display for Cross {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = |cs: &[Cross]| {
            cs.iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(",")
        };
        match self {
            Cross::Boxed(inner) => write!(f, "box:{inner}"),
            Cross::Same(words) => write!(f, "{}", Held::Words(words.clone())),
            Cross::Tuple(cs) => write!(f, "({})", list(cs)),
            Cross::Con(i, cs) => write!(f, "{}.{}[{}]", i.home, i.name, list(cs)),
            Cross::Fn(ps, ret, err) => {
                let ps: Vec<String> = ps
                    .iter()
                    .map(|(inout, c)| {
                        if *inout {
                            format!("inout {c}")
                        } else {
                            c.to_string()
                        }
                    })
                    .collect();
                write!(f, "fn({})->{ret}", ps.join(","))?;
                err.as_ref().map_or(Ok(()), |e| write!(f, "/{e}"))
            }
            Cross::Poly(bounds, inner) => write!(f, "poly{}:{inner}", bounds.len()),
            Cross::Rigid(k) => write!(f, "'{k}"),
        }
    }
}
