//! Two types that differ, shown with only the parts that differ, as the program writes them
//! (goal mismatch-diffs).

use stilt_hir::hir::{GenericId, Name};

use super::{FnTy, Table, Ty};

/// What stands for a part that the two types share.
const SAME: &str = "…";

impl Table {
    /// Two types as a program writes them, each part that they share elided as `…`. Parts are
    /// compared where the types have the same shape: the same type constructor, tuples of one
    /// length, or functions with as many parameters, of the same modes. Elsewhere each type is
    /// shown whole.
    #[must_use]
    pub fn show_diff(
        &self,
        left: &Ty,
        right: &Ty,
        names: &dyn Fn(&GenericId) -> Name,
    ) -> (String, String) {
        match (self.resolve(left), self.resolve(right)) {
            (Ty::Con(item, args), Ty::Con(other, others))
                if item == other && !args.is_empty() && args.len() == others.len() =>
            {
                let (l, r) = self.diff_list(args, others, names);
                (
                    format!("{}<{l}>", item.name),
                    format!("{}<{r}>", other.name),
                )
            }
            (Ty::Tuple(parts), Ty::Tuple(others))
                if parts.len() > 1 && parts.len() == others.len() =>
            {
                let (l, r) = self.diff_list(parts, others, names);
                (format!("({l})"), format!("({r})"))
            }
            (Ty::Fn(f), Ty::Fn(g))
                if f.params.len() == g.params.len()
                    && f.params.iter().zip(&g.params).all(|(p, q)| p.0 == q.0) =>
            {
                self.diff_fn(f, g, names)
            }
            (l, r) => (self.show(l, names), self.show(r, names)),
        }
    }

    /// Two lists of types, with `…` for each pair that is the same.
    fn diff_list(
        &self,
        xs: &[Ty],
        ys: &[Ty],
        names: &dyn Fn(&GenericId) -> Name,
    ) -> (String, String) {
        let (l, r): (Vec<String>, Vec<String>) = xs
            .iter()
            .zip(ys)
            .map(|(x, y)| {
                if self.show(x, names) == self.show(y, names) {
                    (SAME.to_owned(), SAME.to_owned())
                } else {
                    self.show_diff(x, y, names)
                }
            })
            .unzip();
        (l.join(", "), r.join(", "))
    }

    /// Two function types with the same modes: their parameters, return types and rows, each
    /// part that they share elided, and a return type or row that is nothing left out.
    fn diff_fn(&self, f: &FnTy, g: &FnTy, names: &dyn Fn(&GenericId) -> Name) -> (String, String) {
        let params = |fty: &FnTy| {
            fty.params
                .iter()
                .map(|(_, t)| t.clone())
                .collect::<Vec<_>>()
        };
        let (pl, pr) = self.diff_list(&params(f), &params(g), names);
        let modes: Vec<&str> = f
            .params
            .iter()
            .map(|(m, _)| super::print::mode(*m))
            .collect();
        let with_modes = |list: String| {
            let parts: Vec<String> = list
                .split(", ")
                .zip(&modes)
                .map(|(t, m)| format!("{m}{t}"))
                .collect();
            parts.join(", ")
        };
        let unit = |t: &Ty| matches!(self.resolve(t), Ty::Tuple(ts) if ts.is_empty());
        let (rl, rr) = match (unit(&f.ret), unit(&g.ret)) {
            (true, true) => (String::new(), String::new()),
            _ if self.show(&f.ret, names) == self.show(&g.ret, names) => {
                (format!(" -> {SAME}"), format!(" -> {SAME}"))
            }
            _ => {
                let (l, r) = self.show_diff(&f.ret, &g.ret, names);
                (format!(" -> {l}"), format!(" -> {r}"))
            }
        };
        let (wl, wr) = (self.show_row(&f.row, names), self.show_row(&g.row, names));
        let row = |w: &str| {
            if w.is_empty() {
                String::new()
            } else {
                format!(" / {w}")
            }
        };
        let (wl, wr) = if wl == wr && !wl.is_empty() {
            (format!(" / {SAME}"), format!(" / {SAME}"))
        } else {
            (row(&wl), row(&wr))
        };
        (
            format!("fn({}){rl}{wl}", with_modes(pl)),
            format!("fn({}){rr}{wr}", with_modes(pr)),
        )
    }
}

#[cfg(test)]
mod tests {
    use stilt_hir::decls::prelude_item;
    use stilt_hir::hir::{GenericId, Mode, Name};

    use crate::ty::{Row, Table, Ty};

    fn name(_: &GenericId) -> Name {
        Name::from("_")
    }

    fn con(n: &str, args: Vec<Ty>) -> Ty {
        Ty::Con(prelude_item(n), args)
    }

    #[test]
    fn elides_the_arguments_that_agree() {
        let map = |v: Ty| con("Map", vec![Ty::str(), Ty::list(v)]);
        let (a, b) = Table::default().show_diff(&map(Ty::i64()), &map(Ty::str()), &name);
        assert_eq!(
            (a.as_str(), b.as_str()),
            ("Map<…, List<i64>>", "Map<…, List<str>>")
        );
    }

    #[test]
    fn shows_types_of_other_shapes_whole() {
        let (a, b) = Table::default().show_diff(&Ty::list(Ty::i64()), &Ty::str(), &name);
        assert_eq!((a.as_str(), b.as_str()), ("List<i64>", "str"));
    }

    #[test]
    fn elides_the_parts_of_functions_that_agree() {
        let f = |t: Ty| {
            Ty::func(
                vec![(Mode::Let, Ty::i64()), (Mode::Inout, t)],
                Ty::bool(),
                Row::EMPTY,
            )
        };
        let (a, b) = Table::default().show_diff(&f(Ty::str()), &f(Ty::i64()), &name);
        assert_eq!(
            (a.as_str(), b.as_str()),
            ("fn(…, inout str) -> …", "fn(…, inout i64) -> …")
        );
    }
}
