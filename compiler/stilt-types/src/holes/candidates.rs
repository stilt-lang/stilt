//! The functions a hole's context may call, in the order `show` lists those that fit
//! (goal hole-context): the functions of the hole's module; the methods of the bindings in
//! scope whose type isn't the expected type, inherent then of traits, which make the value out
//! of what is at hand; the public functions of the modules it imports; the functions of the
//! expected type's own impls; the prelude's functions; and last the methods of the bindings of
//! the expected type, which only make one such value of another.

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::decls::{FnSig, Lookup, MemberKindInfo};
use stilt_hir::hir::{self, DeclKind, Item, ItemHir, Mode, ModuleHir, Name};
use stilt_hir::module_hir;

use super::Fit;
use crate::analyses::implicit::Key;
use crate::implements::{Bounds, implements_trait};
use crate::ty::Ty;

/// A function that a hole may call.
pub(super) struct Candidate<'d> {
    pub(super) fit: Fit,
    pub(super) sig: &'d FnSig,
    /// The type of an impl's receiver, with the impl's type parameters, for an inherent member.
    pub(super) self_ty: Option<&'d hir::Ty>,
    /// The type of the binding in scope that a method is called on, which is also what `Self`
    /// means in a trait's method.
    pub(super) receiver: Option<Ty>,
    /// The function in the implicit effects of the program, where it is known.
    pub(super) key: Option<Key>,
}

/// Where a hole's candidates come from.
pub(super) struct Sources<'a> {
    pub(super) db: &'a dyn Db,
    pub(super) program: Program,
    pub(super) decls: &'a dyn Lookup,
    pub(super) module: &'a ModuleHir,
    /// The path of the function the hole is in, which isn't its own completion.
    pub(super) enclosing: Option<String>,
    /// The type parameters of the function the hole is in, with their bounds.
    pub(super) bounds: Bounds,
}

impl<'a> Sources<'a> {
    pub(super) fn new(
        db: &'a dyn Db,
        program: Program,
        decls: &'a dyn Lookup,
        file: SourceFile,
    ) -> Self {
        Self {
            db,
            program,
            decls,
            module: module_hir(db, program, file),
            enclosing: None,
            bounds: Vec::new(),
        }
    }

    /// Every candidate, in order: see the module's documentation. `receivers` are the types of
    /// the bindings in scope, each once, with whether one of them may be passed `inout`.
    pub(super) fn all(&self, expected: &Ty, receivers: &[(Ty, bool)]) -> Vec<Candidate<'a>> {
        let (same, other): (Vec<_>, Vec<_>) = receivers.iter().partition(|(r, _)| r == expected);
        let mut found = self.functions(self.module, None, false);
        for (r, mutable) in other {
            found.extend(self.methods(r, *mutable));
        }
        for import in &self.module.imports {
            if let Some(m) = self.module_named(import) {
                let qualifier = import.rsplit('.').next().map(Name::from);
                found.extend(self.functions(m, qualifier.as_ref(), true));
            }
        }
        found.extend(self.statics(expected));
        if let Some(prelude) = self.module_named("std.prelude")
            && !std::ptr::eq(prelude, self.module)
        {
            found.extend(self.functions(prelude, None, true));
        }
        for (r, mutable) in same {
            found.extend(self.methods(r, *mutable));
        }
        found.retain(|c| Some(&c.fit.path) != self.enclosing.as_ref());
        found
    }

    /// The module of this name, of the program or of the standard library.
    fn module_named(&self, name: &str) -> Option<&'a ModuleHir> {
        let (db, program) = (self.db, self.program);
        program
            .files(db)
            .iter()
            .chain(program.std(db))
            .map(|&f| &**module_hir(db, program, f))
            .find(|m| &*m.name == name)
    }

    /// The functions that `module` declares at module level, in source order, only its public
    /// ones if `public`, each written after `qualifier` if it is given.
    fn functions(
        &self,
        module: &ModuleHir,
        qualifier: Option<&Name>,
        public: bool,
    ) -> Vec<Candidate<'a>> {
        module
            .items
            .iter()
            .filter_map(|item| match item {
                ItemHir::Decl(d) if d.is_pub || !public => match &d.kind {
                    DeclKind::Fn(f) => Some(&f.name),
                    _ => None,
                },
                _ => None,
            })
            .filter_map(|name| {
                let item = Item {
                    home: module.name,
                    name: *name,
                };
                Some(Candidate {
                    fit: Fit {
                        path: format!("{}.{name}", module.name),
                        qualifier: qualifier.copied(),
                    },
                    sig: self.decls.function(&item)?,
                    self_ty: None,
                    receiver: None,
                    key: Some(Key::Function(item)),
                })
            })
            .collect()
    }

    /// The members of `owner`'s inherent impls that the hole's module may name: its methods if
    /// `methods`, its functions without a receiver otherwise, in source order.
    fn members(&self, owner: &Item, methods: bool) -> Vec<Candidate<'a>> {
        let own = owner.home == self.module.name;
        self.decls
            .inherent_members(owner)
            .iter()
            .filter(|m| m.is_pub || own)
            .filter(|m| match m.kind {
                MemberKindInfo::Method(_) => methods,
                MemberKindInfo::Function => !methods,
                MemberKindInfo::Constant => false,
            })
            .map(|m| Candidate {
                fit: Fit {
                    path: format!("{}.{}.{}", owner.home, owner.name, m.name),
                    qualifier: Some(owner.name),
                },
                sig: &m.signature,
                self_ty: Some(&m.self_ty),
                receiver: None,
                key: Some(Key::Member(owner.clone(), m.name)),
            })
            .collect()
    }

    /// The methods that a binding of type `receiver` may call: its inherent methods, then those
    /// of the traits it implements, the prelude's, the module's and the imports' in turn
    /// (traits.method-resolution). A method whose receiver is `inout` needs a binding that is
    /// `mutable`.
    fn methods(&self, receiver: &Ty, mutable: bool) -> Vec<Candidate<'a>> {
        let mut found = match receiver {
            Ty::Con(owner, _) => self.members(owner, true),
            _ => Vec::new(),
        };
        for t in self.visible_traits() {
            if !implements_trait(self.decls, (&self.bounds, &[]), receiver, &t) {
                continue;
            }
            let Some(info) = self.decls.trait_info(&t) else {
                continue;
            };
            for m in &info.methods {
                let key = match receiver {
                    Ty::Con(owner, _) if self.decls.trait_impl(&t, owner).is_some() => {
                        Some(Key::ImplMethod(t.clone(), owner.clone(), m.name))
                    }
                    Ty::Con(..) => Some(Key::BuiltIn(t.clone(), m.name)),
                    _ => None,
                };
                found.push(Candidate {
                    fit: Fit {
                        path: format!("{}.{}.{}", t.home, t.name, m.name),
                        qualifier: Some(t.name),
                    },
                    sig: &m.signature,
                    self_ty: None,
                    receiver: None,
                    key,
                });
            }
        }
        found.retain(|c| mutable || c.sig.params.first().is_none_or(|(m, _)| *m != Mode::Inout));
        for c in &mut found {
            c.receiver = Some(receiver.clone());
        }
        found
    }

    /// The functions without a receiver of the expected type's own impls, as `List.new`.
    fn statics(&self, expected: &Ty) -> Vec<Candidate<'a>> {
        match expected {
            Ty::Con(owner, _) => self.members(owner, false),
            _ => Vec::new(),
        }
    }

    /// The traits whose methods the hole's module may call: the prelude's, its own, and those
    /// of the modules it imports (traits.traits-in-scope).
    fn visible_traits(&self) -> Vec<Item> {
        let mut traits = self.decls.module_traits("std.prelude").to_vec();
        if &*self.module.name != "std.prelude" {
            traits.extend_from_slice(self.decls.module_traits(&self.module.name));
        }
        for import in &self.module.imports {
            traits.extend_from_slice(self.decls.module_traits(import));
        }
        traits
    }
}
