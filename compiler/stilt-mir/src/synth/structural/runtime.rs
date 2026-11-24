//! The structural impls that the runtime holds: those of lists and maps, and of a tuple of a
//! pack whose length is known at run time only (traits.structural-impls).

use stilt_hir::decls::prelude_item;
use stilt_hir::hir::Item;

use super::Values;
use crate::lower::Lower;
use crate::lower::words::word;
use crate::mir::{Operand, Repr, Runtime, Rvalue};

impl Lower<'_> {
    /// The runtime's structural impls of a tuple of a pack whose length is known at run time
    /// only, which call its elements' impls through the lists of their dictionaries that the
    /// impl's environment holds in place of its argument's dictionaries.
    pub(super) fn pack_method(&mut self, method: &str, v: &Values<'_>) -> Operand {
        let (f, name, repr) = match method {
            "eq" => (Runtime::PackEq, "Eq", Repr::Scalar),
            "compare" => (Runtime::PackCompare, "Ord", Repr::Scalar),
            "hash" => (Runtime::PackHash, "Hash", Repr::Scalar),
            _ => (Runtime::PackShow, "Show", Repr::Heap),
        };
        let t = prelude_item(name);
        let dicts = self
            .generics
            .first()
            .and_then(|(_, g)| g.dicts.iter().find(|(d, _)| *d == t))
            .map_or(Operand::word(0), |(_, d)| d.clone());
        let mut all = vec![self.here(), dicts, word(v.a, 0)];
        if matches!(method, "eq" | "compare") {
            all.push(word(v.b, 0));
        }
        self.b.define_op(repr, Rvalue::Runtime(f, all))
    }

    /// The runtime's structural impls of lists and maps, which call their elements' impls
    /// through dictionaries.
    pub(super) fn builtin(&mut self, item: &Item, method: &str, v: &Values<'_>) -> Operand {
        let map = &*item.name == "Map";
        let (f, dicts, repr) = match (method, map) {
            ("eq", false) => (Runtime::ListEq, self.element_dicts("Eq"), Repr::Scalar),
            ("compare", _) => (
                Runtime::ListCompare,
                self.element_dicts("Ord"),
                Repr::Scalar,
            ),
            ("hash", _) => (Runtime::ListHash, self.element_dicts("Hash"), Repr::Scalar),
            ("eq", true) => {
                let mut dicts = self.element_dicts("Eq");
                let hash = self.element_dicts("Hash");
                dicts.insert(1, hash[0].clone());
                (Runtime::MapEq, dicts, Repr::Scalar)
            }
            (_, false) => (Runtime::ListShow, self.element_dicts("Show"), Repr::Heap),
            (_, true) => (Runtime::MapShow, self.element_dicts("Show"), Repr::Heap),
        };
        let mut all = vec![self.here()];
        all.extend(dicts);
        all.push(word(v.a, 0));
        if matches!(method, "eq" | "compare") {
            all.push(word(v.b, 0));
        }
        self.b.define_op(repr, Rvalue::Runtime(f, all))
    }
}
