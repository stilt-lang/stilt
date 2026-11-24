//! The values of value arguments (generics.value-arguments and generics.constant-arguments):
//! integer literals, and the constants of an integer type or `bool` that a type names, computed
//! while the program is checked.
//!
//! A constant's value is a constant expression (declarations.constant-expressions), so it is
//! computed from its syntax, through the scopes of the modules whose constants it names, and never
//! from their resolved bodies: the resolution of a module that names another's constant in a type
//! then depends only on that constant's text. The computation is no use of the constant's value, so
//! a run still evaluates it at its first use (declarations.constant-evaluation).

#![expect(
    clippy::drop_non_drop,
    reason = "salsa's macro drops each query's key, which an item's interned names leave with \
              nothing to free"
)]

use std::collections::HashSet;

use stilt_db::{Db, Program};
use stilt_syntax::SyntaxKind;
use stilt_syntax::ast;
use stilt_syntax::text::number_text;

use crate::hir::{Item, Name, Value};
use crate::items::primitive_name;
use crate::scope::{Kind, PRELUDE, Value as ScopeValue, def_map, module_scope};

/// What computing a constant gives, as a value argument reads it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ConstValue {
    /// The value of a constant of the primitive type named first.
    Value(Name, Value),
    /// A constant of the primitive type named first whose computation panics, as a unary `-`
    /// that overflows does (declarations.constant-evaluation).
    Panics(Name),
    /// A constant of another type, or one with an error of its own, which is reported where it
    /// is declared.
    Unknown,
    /// No constant: a type has no member constant of the name.
    Missing,
}

/// The value of the constant `item`, or of the member constant `member` of the type `item`.
// Salsa takes a query's key by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked]
pub fn const_value(db: &dyn Db, program: Program, item: Item, member: Option<Name>) -> ConstValue {
    let mut cx = Eval {
        db,
        program,
        visiting: HashSet::new(),
    };
    cx.constant(&item, member)
}

/// The value of the constant `item`, or of the member constant `member` of the type `item`,
/// when it is written as an integer literal, with or without a `-` directly before it, within
/// its type's range: the number it stands for wherever it is named (facts.terms).
// Salsa takes a query's key by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked]
pub fn literal_value(
    db: &dyn Db,
    program: Program,
    item: Item,
    member: Option<Name>,
) -> Option<i128> {
    let cx = Eval {
        db,
        program,
        visiting: HashSet::new(),
    };
    let c = cx.declaration(&item, member)?;
    let range = int_range(&primitive_name(c.ty()))?;
    let (token, negative) = match c.value()? {
        ast::Expr::Literal(l) => (l.token()?, false),
        ast::Expr::PrefixExpr(p) if is_minus(&p) => match p.expr()? {
            ast::Expr::Literal(l) => (l.token()?, true),
            _ => return None,
        },
        _ => return None,
    };
    if token.kind() != SyntaxKind::INT {
        return None;
    }
    match in_range(int_literal(&number_text(&token), negative), Some(range)) {
        Computed::Value(Value::Int(n)) => Some(n),
        _ => None,
    }
}

/// The integer types' ranges, by their names.
#[must_use]
pub fn int_range(ty: &str) -> Option<(i128, i128)> {
    let bits = match ty {
        "i8" | "u8" => 8,
        "i16" | "u16" => 16,
        "i32" | "u32" => 32,
        "i64" | "u64" => 64,
        _ => return None,
    };
    Some(if ty.starts_with('u') {
        (0, (1i128 << bits) - 1)
    } else {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    })
}

/// The value of an integer literal's text, `_` separators removed, negated if `negative`, or
/// `None` when it is beyond every integer type's range.
#[must_use]
pub fn int_literal(text: &str, negative: bool) -> Option<i128> {
    let lower = text.to_ascii_lowercase();
    let (radix, digits) = match lower.get(..2) {
        Some("0x") => (16, &lower[2..]),
        Some("0o") => (8, &lower[2..]),
        Some("0b") => (2, &lower[2..]),
        _ => (10, &lower[..]),
    };
    let magnitude = u128::from_str_radix(digits, radix).ok()?;
    let n = i128::try_from(magnitude).ok()?;
    Some(if negative { -n } else { n })
}

struct Eval<'a> {
    db: &'a dyn Db,
    program: Program,
    /// The constants being computed, so that a cycle, an error of its own
    /// (declarations.constant-cycles), gives no value.
    visiting: HashSet<(Item, Option<Name>)>,
}

impl Eval<'_> {
    fn constant(&mut self, item: &Item, member: Option<Name>) -> ConstValue {
        let key = (item.clone(), member);
        if !self.visiting.insert(key.clone()) {
            return ConstValue::Unknown;
        }
        let found = self
            .declaration(item, member)
            .map_or(ConstValue::Missing, |c| {
                let ty = primitive_name(c.ty());
                self.of_type(ty, item.home, c.value())
            });
        self.visiting.remove(&key);
        found
    }

    /// The syntax of a module-level constant, or of a member constant of an inherent impl of
    /// the type `item` in the type's module.
    fn declaration(&self, item: &Item, member: Option<Name>) -> Option<ast::Const> {
        let module = def_map(self.db, self.program).module(&item.home)?;
        let tree = stilt_db::parse(self.db, module.file).tree();
        let named = |c: &ast::Const, name: &str| c.name().is_some_and(|n| n.text() == name);
        match member {
            None => tree.items().find_map(|i| match i {
                ast::Item::Const(c) if named(&c, &item.name) => Some(c),
                _ => None,
            }),
            Some(member) => tree.items().find_map(|i| match i {
                ast::Item::Impl(block) if block.trait_ty().is_none() && impl_of(&block, item) => {
                    block.members().find_map(|m| match m {
                        ast::Item::Const(c) if named(&c, &member) => Some(c),
                        _ => None,
                    })
                }
                _ => None,
            }),
        }
    }

    /// The value of a constant of the type named `ty`, an integer type or `bool`, whose value
    /// is `e` in module `home`.
    fn of_type(&mut self, ty: Name, home: Name, e: Option<ast::Expr>) -> ConstValue {
        if int_range(&ty).is_none() && &*ty != "bool" {
            return ConstValue::Unknown;
        }
        match self.expr(ty, home, e) {
            Computed::Value(v) => ConstValue::Value(ty, v),
            Computed::Panics => ConstValue::Panics(ty),
            Computed::Unknown => ConstValue::Unknown,
        }
    }

    fn expr(&mut self, ty: Name, home: Name, e: Option<ast::Expr>) -> Computed {
        let range = int_range(&ty);
        match e {
            Some(ast::Expr::ParenExpr(p)) => self.expr(ty, home, p.expr()),
            Some(ast::Expr::Literal(l)) => match (l.token(), range) {
                (Some(t), Some(_)) if t.kind() == SyntaxKind::INT => {
                    in_range(int_literal(&number_text(&t), false), range)
                }
                (Some(t), None) if t.kind() == SyntaxKind::TRUE_KW => {
                    Computed::Value(Value::Bool(true))
                }
                (Some(t), None) if t.kind() == SyntaxKind::FALSE_KW => {
                    Computed::Value(Value::Bool(false))
                }
                _ => Computed::Unknown,
            },
            Some(ast::Expr::PrefixExpr(p)) if is_minus(&p) && range.is_some() => {
                // A `-` written directly before a literal is part of it
                // (numbers.negative-literals); any other negates its operand's value, and panics
                // when that overflows (declarations.constant-evaluation).
                if let Some(ast::Expr::Literal(l)) = p.expr()
                    && let Some(t) = l.token().filter(|t| t.kind() == SyntaxKind::INT)
                {
                    return in_range(int_literal(&number_text(&t), true), range);
                }
                match self.expr(ty, home, p.expr()) {
                    Computed::Value(Value::Int(n)) => match in_range(Some(-n), range) {
                        Computed::Unknown => Computed::Panics,
                        found => found,
                    },
                    other => other,
                }
            }
            Some(e @ (ast::Expr::NameRef(_) | ast::Expr::FieldExpr(_))) => self.named(ty, home, &e),
            _ => Computed::Unknown,
        }
    }

    /// The value of another constant that a constant's value names, of the same type.
    fn named(&mut self, ty: Name, home: Name, e: &ast::Expr) -> Computed {
        let Some((item, member)) = self.resolve(home, &segments(e)) else {
            return Computed::Unknown;
        };
        match self.constant(&item, member) {
            ConstValue::Value(t, v) if t == ty => Computed::Value(v),
            ConstValue::Panics(t) if t == ty => Computed::Panics,
            _ => Computed::Unknown,
        }
    }

    /// The constant that a path names in module `home`: `C`, `m.C`, or a member constant of a
    /// type, `T.C`.
    fn resolve(&self, home: Name, path: &[String]) -> Option<(Item, Option<Name>)> {
        let map = def_map(self.db, self.program);
        let scope_of = |ns: &str| {
            let module = map.module(ns)?;
            Some(&module_scope(self.db, self.program, module.file).scope)
        };
        let (last, front) = path.split_last()?;
        let mut ns = home.to_string();
        for (i, s) in front.iter().enumerate() {
            let scope = scope_of(&ns)?;
            if i + 1 == front.len()
                && let Some(t) = scope
                    .find(crate::scope::Namespace::Types, s)
                    .filter(|e| e.kind == Kind::Type)
                    .map(|_| ns.clone())
                    .or_else(|| prelude_type(s))
            {
                let owner = Item {
                    home: Name::from(t),
                    name: Name::from(s.as_str()),
                };
                return Some((owner, Some(Name::from(last.as_str()))));
            }
            ns = match scope.values.get(s.as_str()) {
                Some(ScopeValue::Import(m)) if i == 0 => m.to_string(),
                _ => format!("{ns}.{s}"),
            };
        }
        let scope = scope_of(&ns)?;
        let found = |scope: &crate::scope::Scope| matches!(scope.find(crate::scope::Namespace::Values, last), Some(e) if e.kind == Kind::Const);
        if found(scope) {
            return Some((item_at(&ns, last), None));
        }
        (front.is_empty() && scope_of(PRELUDE).is_some_and(found))
            .then(|| (item_at(PRELUDE, last), None))
    }
}

/// What a constant expression computes to.
enum Computed {
    Value(Value),
    Panics,
    Unknown,
}

fn in_range(n: Option<i128>, range: Option<(i128, i128)>) -> Computed {
    match (n, range) {
        (Some(n), Some((lo, hi))) if lo <= n && n <= hi => Computed::Value(Value::Int(n)),
        _ => Computed::Unknown,
    }
}

fn is_minus(p: &ast::PrefixExpr) -> bool {
    p.op().is_some_and(|t| t.kind() == SyntaxKind::MINUS)
}

/// The names of a path written as an expression, `a.b.C`.
fn segments(e: &ast::Expr) -> Vec<String> {
    match e {
        ast::Expr::NameRef(n) => vec![n.text()],
        ast::Expr::FieldExpr(f) => {
            let mut path = f.base().as_ref().map_or_else(Vec::new, segments);
            if path.is_empty() {
                return path;
            }
            match f.member() {
                Some(m) => path.push(m.text().to_owned()),
                None => path.clear(),
            }
            path
        }
        _ => Vec::new(),
    }
}

fn item_at(home: &str, name: &str) -> Item {
    Item {
        home: Name::from(home),
        name: Name::from(name),
    }
}

/// The prelude's module, for a primitive type name, whose member constants it declares.
fn prelude_type(name: &str) -> Option<String> {
    crate::scope::is_primitive(name).then(|| PRELUDE.to_owned())
}

/// Whether an inherent impl block is for the type `item`, written by its bare name.
fn impl_of(block: &ast::Impl, item: &Item) -> bool {
    match block.self_ty() {
        Some(ast::Type::NamedType(n)) => {
            let path: Vec<_> = n.path().into_iter().flat_map(|p| p.segments()).collect();
            matches!(path.as_slice(), [one] if one.text() == &*item.name)
        }
        _ => false,
    }
}
