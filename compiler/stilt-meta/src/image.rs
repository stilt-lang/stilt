//! The code a macro's run may reach, read from the database before the run starts: the typed
//! bodies of the functions, methods and constants that the macro's body reaches through its
//! calls, the impls of the traits it calls through, and what its records and variants are.
//! The run then reads nothing else, so that it runs on a thread of its own, with a stack deep
//! enough for 10,000 frames (macros.step-limits), apart from the database.
//!
//! What a macro reaches is a query of its own, [`reach`], which walks the typed bodies once and
//! is kept while the code it read doesn't change, so that every run of the macro, on any use,
//! starts from it (macros.running); a run's image only takes the typed bodies it
//! names.

#![expect(
    clippy::drop_non_drop,
    reason = "salsa's macro drops each query's key, which an item's interned names leave with \
              nothing to free"
)]

mod walk;

use std::sync::Arc;

use rustc_hash::FxHashMap;
use stilt_db::{Db, Program, SourceFile};
use stilt_hir::decls::Declarations;
use stilt_hir::hir::{GenericId, Item, Name};
use stilt_mir::FnRef;
use stilt_types::tast::TypedBody;
use stilt_types::ty::Ty;

use crate::frame::FrameInfo;
use crate::natives::{Run, native};

/// What the function `start` of `program`, a macro, may reach: read once from the typed bodies
/// of its module and of what it calls, and kept while they don't change.
// A query's arguments are its key, which salsa takes by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
pub(crate) fn reach(db: &dyn Db, program: Program, start: Item) -> Reach {
    walk::reach(db, program, &start)
}

/// Where the code of a function, a method or a constant is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Place {
    /// The body `index` of `file`, of the module `module`.
    Body {
        file: SourceFile,
        index: u32,
        module: Name,
    },
    Native,
    /// A foreign function, which a run can't call (c.calls).
    Foreign,
    Broken,
}

/// An impl of a trait for a type: its type, which binds its type parameters, and the type
/// parameters of each of its members' signatures.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct ImplImage {
    pub(crate) self_ty: Ty,
    pub(crate) members: Vec<(Name, Vec<GenericId>)>,
}

/// A function, a method or a constant that a macro's run may reach.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Reached {
    pub(crate) f: FnRef,
    pub(crate) place: Place,
    /// The name a frame of it shows.
    pub(crate) name: Name,
    /// A function's or a member's type parameters, in the order of its signature.
    pub(crate) params: Option<Vec<GenericId>>,
}

/// What a macro's run may reach, by where its code is.
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct Reach {
    pub(crate) functions: Vec<Reached>,
    /// The index of each among `functions`.
    pub(crate) index: FxHashMap<FnRef, usize>,
    pub(crate) impls: FxHashMap<(Item, Item), ImplImage>,
    /// Each variant's type and place among its type's variants.
    pub(crate) variants: FxHashMap<Item, (Item, u32)>,
    /// Each record type's fields, in its order.
    pub(crate) records: FxHashMap<Item, Vec<Name>>,
}

/// The code of a function, a method or a constant.
#[derive(Debug)]
pub(crate) enum FnCode<'a> {
    Body {
        body: &'a TypedBody,
        /// The module of its file.
        module: Name,
        /// The name its frames show.
        name: Name,
        /// What its frames share where it has no type arguments.
        info: Arc<FrameInfo<'a>>,
    },
    /// A native, with what runs it if it performs nothing ([`crate::natives::native`]).
    Native(Option<Run>),
    Broken,
}

/// What a run may reach: what the macro reaches, and the typed bodies of its code.
#[derive(Debug)]
pub(crate) struct Image<'a> {
    /// The program's declarations, which reflection reads (meta.reflects).
    pub(crate) decls: &'a Declarations,
    reach: &'a Reach,
    /// The code of each of `reach`'s functions, in its order.
    code: Vec<FnCode<'a>>,
}

/// The image of what the function `start` of `program` reaches, for one run.
pub(crate) fn image<'a>(db: &'a dyn Db, program: Program, start: &Item) -> Image<'a> {
    let reach = reach(db, program, start.clone());
    let code = reach
        .functions
        .iter()
        .map(|Reached { f, place, name, .. }| match place {
            Place::Body {
                file,
                index,
                module,
            } => {
                let body = &stilt_types::infer_body(db, program, *file, *index).body;
                let info = FrameInfo {
                    body,
                    module: *module,
                    tenv: Vec::new(),
                    self_ty: None,
                };
                FnCode::Body {
                    body,
                    module: *module,
                    name: *name,
                    info: Arc::new(info),
                }
            }
            Place::Native => FnCode::Native(native_run(f)),
            Place::Foreign => FnCode::Native(Some(crate::natives::reaches_c)),
            Place::Broken => FnCode::Broken,
        })
        .collect();
    Image {
        decls: stilt_hir::declarations(db, program),
        reach,
        code,
    }
}

/// What runs the native `f`, if it performs nothing.
fn native_run(f: &FnRef) -> Option<Run> {
    match f {
        FnRef::Function(item) => native(&item.home, None, &item.name),
        FnRef::Member(owner, name) | FnRef::ImplMethod(_, owner, name) => {
            native(&owner.home, Some(&owner.name), name)
        }
        _ => None,
    }
}

impl<'a> Image<'a> {
    /// The code of `f`, which the image holds when a run reaches it, with the type parameters
    /// of its signature when it is a function or a member.
    pub(crate) fn function(&self, f: &FnRef) -> Option<(&FnCode<'a>, Option<&'a [GenericId]>)> {
        let i = *self.reach.index.get(f)?;
        Some((&self.code[i], self.reach.functions[i].params.as_deref()))
    }

    /// Whether the image holds the code of `f`.
    pub(crate) fn holds(&self, f: &FnRef) -> bool {
        self.reach.index.contains_key(f)
    }

    /// The impl of the trait `t` for the type `owner`.
    pub(crate) fn impl_of(&self, t: &Item, owner: &Item) -> Option<&'a ImplImage> {
        self.reach.impls.get(&(t.clone(), owner.clone()))
    }

    /// A variant's type, and its place among its type's variants.
    pub(crate) fn variant(&self, item: &Item) -> Option<&'a (Item, u32)> {
        self.reach.variants.get(item)
    }

    /// A record type's fields, in its order.
    pub(crate) fn record(&self, item: &Item) -> Option<&'a Vec<Name>> {
        self.reach.records.get(item)
    }
}
