//! The walk of what a macro reaches: from its body, through the typed bodies of the functions,
//! methods and constants it calls, the impls of the traits it calls through, and its records and
//! variants.

use std::collections::HashSet;

use rustc_hash::FxHashMap;
use stilt_db::{Db, Program};
use stilt_hir::decls::{Lookup, QueriedOnce, TypeDefInfo};
use stilt_hir::hir::{GenericId, Item, Name};
use stilt_mir::{Code as Where, FnRef};
use stilt_types::tast::walk::{Part, parts, stmt_exprs};
use stilt_types::tast::{Block, Callee, Code, Definition, Expr, ExprKind, Pat, PatKind};
use stilt_types::ty::Ty;

use super::{ImplImage, Place, Reach, Reached};

/// The traits whose impls the structural impls and the natives call.
const PRELUDE_TRAITS: [&str; 4] = ["Eq", "Ord", "Hash", "Show"];

struct Builder<'a> {
    db: &'a dyn Db,
    program: Program,
    decls: QueriedOnce<'a>,
    reach: Reach,
    /// Each function's and member's type parameters, in the order of its signature.
    params: FxHashMap<FnRef, Vec<GenericId>>,
    todo: Vec<FnRef>,
    seen: HashSet<FnRef>,
    traits: HashSet<(Item, Name)>,
}

/// What the function `start` of `program` reaches.
pub(super) fn reach(db: &dyn Db, program: Program, start: &Item) -> Reach {
    let mut b = Builder {
        db,
        program,
        decls: QueriedOnce::new(db, program),
        reach: Reach::default(),
        params: FxHashMap::default(),
        todo: vec![FnRef::Function(start.clone())],
        seen: HashSet::new(),
        traits: HashSet::new(),
    };
    for name in PRELUDE_TRAITS {
        let item = crate::value::prelude(name);
        for method in ["eq", "compare", "hash", "show", "show_nested"] {
            b.trait_method(&item, Name::from(method));
        }
    }
    for t in ["Some", "None", "Ok", "Err", "Less", "Equal", "Greater"] {
        b.variant(&crate::value::prelude(t));
    }
    let kinds = [
        "Word",
        "Number",
        "Text",
        "Interpolated",
        "Punct",
        "Group",
        "Paren",
        "Bracket",
        "Brace",
    ];
    for t in kinds {
        b.variant(&crate::value::meta_item(t));
    }
    for r in ["Tokens", "File", "Cursor"] {
        b.record(&crate::value::meta_item(r));
    }
    while let Some(f) = b.todo.pop() {
        b.function(f);
    }
    for r in &mut b.reach.functions {
        r.params = b.params.remove(&r.f);
    }
    b.reach
}

/// The name a frame of `f` shows.
fn shown(f: &FnRef) -> Name {
    match f {
        FnRef::Function(item) => item.name,
        FnRef::Member(owner, name) | FnRef::ImplMethod(_, owner, name) => {
            Name::from(format!("{}.{name}", owner.name))
        }
        FnRef::DefaultMethod(t, name) => Name::from(format!("{}.{name}", t.name)),
        _ => Name::from("?"),
    }
}

impl<'a> Builder<'a> {
    fn reach(&mut self, f: FnRef) {
        if self.seen.insert(f.clone()) {
            self.todo.push(f);
        }
    }

    /// Reads the code of `f`, and reaches what its body reaches.
    /// Whether `f` is a foreign function, which C gives (c.foreign-functions).
    fn foreign(&self, f: &FnRef) -> bool {
        let FnRef::Function(item) = f else {
            return false;
        };
        self.decls.function(item).is_some_and(|sig| sig.foreign)
    }

    fn function(&mut self, f: FnRef) {
        let place = match stilt_mir::code_of(self.db, self.program, f.clone()) {
            Some(Where::Body(file, index)) => {
                let body = &stilt_types::infer_body(self.db, self.program, file, index).body;
                let module = stilt_hir::module_hir(self.db, self.program, file).name;
                match &body.code {
                    Definition::Code(code) => {
                        match code {
                            Code::Block(b) => self.block(b),
                            Code::Expr(e) => self.expr(e),
                        }
                        Place::Body {
                            file,
                            index,
                            module,
                        }
                    }
                    Definition::Native => Place::Native,
                    Definition::Broken => Place::Broken,
                }
            }
            Some(Where::Native) => Place::Native,
            None if self.foreign(&f) => Place::Foreign,
            None => return,
        };
        let name = shown(&f);
        self.reach
            .index
            .insert(f.clone(), self.reach.functions.len());
        self.reach.functions.push(Reached {
            f,
            place,
            name,
            params: None,
        });
    }

    fn block(&mut self, b: &'a Block) {
        for s in b {
            for e in stmt_exprs(s) {
                self.expr(e);
            }
            if let stilt_types::tast::StmtKind::Let(binding)
            | stilt_types::tast::StmtKind::Var(binding) = &s.kind
            {
                self.pattern(&binding.pattern);
            }
        }
    }

    fn expr(&mut self, e: &'a Expr) {
        match &e.kind {
            ExprKind::Call(c, ..) | ExprKind::Callee(c, _) | ExprKind::Project(c, ..) => {
                self.callee(c);
            }
            ExprKind::Constant(item) => self.reach(FnRef::Const(item.clone())),
            ExprKind::MemberConstant(owner, name, _) => {
                self.reach(FnRef::MemberConst(owner.clone(), *name));
            }
            ExprKind::Record(item, ..) => self.record(item),
            ExprKind::Construct(item, ..) | ExprKind::Constructor(item, _) => self.variant(item),
            ExprKind::Closure(params, _) => {
                for p in params {
                    self.pattern(p);
                }
            }
            ExprKind::Match(_, arms)
            | ExprKind::Try(_, Some(stilt_types::tast::Catch { arms, .. })) => {
                for arm in arms {
                    self.pattern(&arm.pattern);
                }
            }
            ExprKind::IfLet(p, ..) | ExprKind::For(p, ..) => self.pattern(p),
            _ => {}
        }
        for part in parts(e) {
            match part {
                Part::Expr(x) => self.expr(x),
                Part::Block(b) => self.block(b),
            }
        }
    }

    fn pattern(&mut self, p: &'a Pat) {
        match &p.kind {
            PatKind::Variant(item, ps) => {
                self.variant(item);
                for p in ps {
                    self.pattern(p);
                }
            }
            PatKind::Tuple(ps) | PatKind::Or(ps) | PatKind::List(ps, _) => {
                for p in ps {
                    self.pattern(p);
                }
            }
            PatKind::Record(fields) => {
                for (_, p) in fields {
                    self.pattern(p);
                }
            }
            PatKind::Const(e) => self.expr(e),
            _ => {}
        }
    }

    fn callee(&mut self, c: &Callee) {
        match c {
            Callee::Function(item) => {
                if let Some(sig) = self.decls.function(item) {
                    let params = sig.type_params.iter().map(|(g, _)| g.clone()).collect();
                    self.params.insert(FnRef::Function(item.clone()), params);
                }
                self.reach(FnRef::Function(item.clone()));
            }
            Callee::Member(owner, name) => {
                let f = FnRef::Member(owner.clone(), *name);
                if let Some(m) = self
                    .decls
                    .inherent_members(owner)
                    .iter()
                    .find(|m| m.name == *name)
                {
                    let params = m
                        .signature
                        .type_params
                        .iter()
                        .map(|(g, _)| g.clone())
                        .collect();
                    self.params.insert(f.clone(), params);
                }
                self.reach(f);
            }
            Callee::TraitMethod(t, name, _) => self.trait_method(t, *name),
            Callee::Operation(..) => {}
        }
    }

    /// Reaches every impl's method `name` of trait `t`, and the trait's default.
    fn trait_method(&mut self, t: &Item, name: Name) {
        if !self.traits.insert((t.clone(), name)) {
            return;
        }
        self.reach(FnRef::DefaultMethod(t.clone(), name));
        let owners: Vec<Item> = stilt_mir::bodies(self.db, self.program)
            .code
            .keys()
            .filter_map(|f| match f {
                FnRef::ImplMethod(tr, owner, n) if tr == t && *n == name => Some(owner.clone()),
                _ => None,
            })
            .collect();
        for owner in owners {
            self.impl_of(t, &owner);
            self.reach(FnRef::ImplMethod(t.clone(), owner, name));
        }
    }

    fn impl_of(&mut self, t: &Item, owner: &Item) {
        let key = (t.clone(), owner.clone());
        if self.reach.impls.contains_key(&key) {
            return;
        }
        let Some(info) = self.decls.trait_impl(t, owner) else {
            return;
        };
        let members = info
            .members
            .iter()
            .map(|m| {
                (
                    m.name,
                    m.signature
                        .type_params
                        .iter()
                        .map(|(g, _)| g.clone())
                        .collect(),
                )
            })
            .collect();
        let image = ImplImage {
            self_ty: Ty::from_hir(&info.self_ty, None),
            members,
        };
        self.reach.impls.insert(key, image);
    }

    fn record(&mut self, item: &Item) {
        if self.reach.records.contains_key(item) {
            return;
        }
        let fields = if item.is_record() {
            item.record_fields()
        } else {
            match self.decls.type_info(item).map(|t| &t.def) {
                Some(TypeDefInfo::Record(fields)) => fields.iter().map(|(n, _)| *n).collect(),
                _ => Vec::new(),
            }
        };
        self.reach.records.insert(item.clone(), fields);
    }

    fn variant(&mut self, item: &Item) {
        if self.reach.variants.contains_key(item) {
            return;
        }
        if let Some(v) = self.decls.variant(item) {
            self.reach
                .variants
                .insert(item.clone(), (v.ty.clone(), v.index));
        }
    }
}
