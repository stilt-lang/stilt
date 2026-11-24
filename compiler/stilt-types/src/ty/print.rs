//! Types as a program writes them, for messages.

use stilt_hir::hir::{GenericId, Mode, Name};

use super::{Kind, Row, RowParam, Table, Ty};

impl Table {
    /// The type as a program would write it. `names` gives the names of type parameters and
    /// row variables.
    #[must_use]
    pub fn show(&self, t: &Ty, names: &dyn Fn(&GenericId) -> Name) -> String {
        match self.shape(t) {
            Ty::App(head, args) => {
                return format!("{}<{}>", self.show(&head, names), self.list(&args, names));
            }
            shaped if matches!(self.resolve(t), Ty::App(..)) => return self.show(&shaped, names),
            _ => {}
        }
        match self.resolve(t) {
            // An anonymous record type, its fields in alphabetical order (records.field-order).
            Ty::Con(item, args) if item.is_record() => {
                let fields: Vec<String> = item
                    .record_fields()
                    .iter()
                    .zip(args)
                    .map(|(f, t)| format!("{f}: {}", self.show(t, names)))
                    .collect();
                format!("{{ {} }}", fields.join(", "))
            }
            Ty::Con(item, args) if args.is_empty() => item.name.to_string(),
            Ty::Con(item, args) => format!("{}<{}>", item.name, self.list(args, names)),
            Ty::Param(p) => names(p).to_string(),
            // A value argument as its value, in decimal (generics.constant-arguments).
            Ty::Value(v) => v.to_string(),
            Ty::SelfTy => "Self".to_owned(),
            Ty::Tuple(ts) => {
                let ts = self.elements(ts);
                match ts.as_slice() {
                    [one] if one.as_spread().is_none() => format!("({},)", self.show(one, names)),
                    ts => format!("({})", self.list(ts, names)),
                }
            }
            Ty::Spread(s) => format!("..{}", self.show(&s.elem, names)),
            Ty::Fn(f) => {
                let params: Vec<String> = f
                    .params
                    .iter()
                    .map(|(m, t)| format!("{}{}", mode(*m), self.show(t, names)))
                    .collect();
                let ret = match self.resolve(&f.ret) {
                    Ty::Tuple(ts) if ts.is_empty() => String::new(),
                    t => format!(" -> {}", self.show(t, names)),
                };
                let row = match self.show_row(&f.row, names) {
                    row if row.is_empty() => row,
                    row => format!(" / {row}"),
                };
                format!(
                    "fn{}({}){ret}{row}",
                    self.generics(f, names),
                    params.join(", ")
                )
            }
            Ty::Var(_) => match self.unsolved(t).map(|v| v.kind) {
                Some(Kind::IntLiteral) => "{integer}".to_owned(),
                Some(Kind::FloatLiteral) => "{float}".to_owned(),
                _ => "_".to_owned(),
            },
            Ty::Handler(h) => self.show_handler(h, names),
            Ty::App(..) => unreachable!("an applied constructor is shown above"),
            Ty::Error => "{error}".to_owned(),
        }
    }

    /// The type parameters of a polymorphic function type, with their bounds and the bounds'
    /// arguments, as `<T: Show, U: Convert<i64>>`, or nothing for a monomorphic one
    /// (polymorphism.function-types).
    fn generics(&self, f: &super::FnTy, names: &dyn Fn(&GenericId) -> Name) -> String {
        if f.generics.is_empty() {
            return String::new();
        }
        let each: Vec<String> = f
            .generics
            .iter()
            .map(|(g, bounds)| {
                let traits: Vec<String> = bounds
                    .iter()
                    .map(|b| {
                        let args = f.bound_args.iter().find(|(p, t, _)| p == g && t == b);
                        match args {
                            Some((.., args)) => format!("{}<{}>", b.name, self.list(args, names)),
                            None => b.name.to_string(),
                        }
                    })
                    .collect();
                if traits.is_empty() {
                    names(g).to_string()
                } else {
                    format!("{}: {}", names(g), traits.join(" + "))
                }
            })
            .collect();
        format!("<{}>", each.join(", "))
    }

    /// A handler's type, as a program writes it (handlers.handler-types).
    fn show_handler(&self, h: &super::HandlerTy, names: &dyn Fn(&GenericId) -> Name) -> String {
        let answer = match &h.answer {
            Some(t) => format!(" -> {}", self.show(t, names)),
            None => String::new(),
        };
        let row = match self.show_row(&h.row, names) {
            row if row.is_empty() => row,
            row => format!(" / {row}"),
        };
        format!(
            "handler {}{answer}{row}",
            self.show_effect(&h.effect, &h.args, names)
        )
    }

    /// An effect with its type arguments, as a row writes it (handlers.effects-in-rows).
    #[must_use]
    pub fn show_effect(
        &self,
        e: &stilt_hir::hir::Item,
        args: &[Ty],
        names: &dyn Fn(&GenericId) -> Name,
    ) -> String {
        if args.is_empty() {
            e.name.to_string()
        } else {
            format!("{}<{}>", e.name, self.list(args, names))
        }
    }

    fn list(&self, ts: &[Ty], names: &dyn Fn(&GenericId) -> Name) -> String {
        ts.iter()
            .map(|t| self.show(t, names))
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// A row as a signature writes it, empty when the row holds nothing. The implicit row
    /// variables of non-escaping parameters are never written (effects.non-escaping-parameters).
    #[must_use]
    pub fn show_row(&self, r: &Row, names: &dyn Fn(&GenericId) -> Name) -> String {
        match self.row_elements(r, names).as_slice() {
            [] => String::new(),
            [e] => e.clone(),
            es => format!("{{{}}}", es.join(", ")),
        }
    }

    /// The elements of a row as a signature writes them, in order: `io`, its `raise`, and its
    /// row variables. The implicit row variables of non-escaping parameters are never written
    /// (effects.closure-parameters).
    #[must_use]
    pub fn row_elements(&self, r: &Row, names: &dyn Fn(&GenericId) -> Name) -> Vec<String> {
        let r = self.row_contents(r);
        let mut elements = Vec::new();
        if r.io {
            elements.push("io".to_owned());
        }
        if let Some(t) = &r.raise {
            elements.push(format!("raise<{}>", self.show(t, names)));
        }
        for (e, args) in &r.effects {
            elements.push(self.show_effect(e, args, names));
        }
        for p in r.tail.params() {
            if let RowParam::Written(g) = p {
                elements.push(names(g).to_string());
            }
        }
        elements
    }
}

/// A parameter's mode as a function type writes it, before the parameter's type.
pub(super) fn mode(m: Mode) -> &'static str {
    match m {
        Mode::Let => "",
        Mode::Inout => "inout ",
    }
}
