//! The frames of running bodies and closures: what their code is, the types its type
//! parameters stand for, and its locals, a vector indexed by each local's id. A frame's locals are
//! held where a window of a writable view reaches them (projections.places-through-views), and a
//! name that a `when` makes the place of an earlier one's reads and writes that one's
//! (shared.when).

use std::sync::{Arc, PoisonError, RwLock, RwLockWriteGuard};

use stilt_hir::hir::{GenericId, LocalId, Name};
use stilt_types::tast::TypedBody;
use stilt_types::ty::Ty;

use crate::value::Value;

/// What a body's frames share: the body, its module, and its type arguments.
#[derive(Clone, Debug)]
pub(crate) struct FrameInfo<'a> {
    pub(crate) body: &'a TypedBody,
    pub(crate) module: Name,
    pub(crate) tenv: Vec<(GenericId, Ty)>,
    /// The type that `Self` stands for in a trait's default method.
    pub(crate) self_ty: Option<Ty>,
}

/// The locals of a frame, by their ids. Only one thread of a run runs at a time, so the lock
/// is never waited on: a frame's is made and dropped with no call to the system.
pub(crate) type Locals<'a> = Arc<RwLock<Vec<Option<Value<'a>>>>>;

/// The locals of a running body or closure.
#[derive(Debug)]
pub(crate) struct Frame<'a> {
    pub(crate) info: Arc<FrameInfo<'a>>,
    pub(crate) locals: Locals<'a>,
    /// The names that a `when` makes the places of earlier ones, each with that one.
    pub(crate) aliases: Vec<(LocalId, LocalId)>,
}

/// The most frames' locals a pool keeps.
const POOLED: usize = 256;

/// The locals of frames that ended, kept for the frames that start after them, so that a call
/// allocates no locals.
#[derive(Debug, Default)]
pub(crate) struct Pool<'a>(Vec<Locals<'a>>);

impl<'a> Pool<'a> {
    /// A frame of a body of `info`, its locals unset.
    pub(crate) fn frame(&mut self, info: Arc<FrameInfo<'a>>) -> Frame<'a> {
        let Some(locals) = self.0.pop() else {
            return Frame::new(info);
        };
        lock(&locals).resize(info.body.locals.len(), None);
        Frame {
            info,
            locals,
            aliases: Vec::new(),
        }
    }

    /// A frame of a closure of `info`, its locals those the closure captured.
    pub(crate) fn frame_with(
        &mut self,
        info: Arc<FrameInfo<'a>>,
        captured: &[Option<Value<'a>>],
    ) -> Frame<'a> {
        let Some(locals) = self.0.pop() else {
            return Frame::with_locals(info, captured.to_vec());
        };
        lock(&locals).extend_from_slice(captured);
        Frame {
            info,
            locals,
            aliases: Vec::new(),
        }
    }

    /// Takes back the locals of a frame that ended, unless a window or a place still holds
    /// them.
    pub(crate) fn recycle(&mut self, frame: Frame<'a>) {
        let mut locals = frame.locals;
        if let Some(held) = Arc::get_mut(&mut locals) {
            held.get_mut()
                .unwrap_or_else(PoisonError::into_inner)
                .clear();
            if self.0.len() < POOLED {
                self.0.push(locals);
            }
        }
    }
}

/// The locals, however a thread that held them ended.
pub(crate) fn lock<'g, 'a>(locals: &'g Locals<'a>) -> RwLockWriteGuard<'g, Vec<Option<Value<'a>>>> {
    locals.write().unwrap_or_else(PoisonError::into_inner)
}

impl<'a> Frame<'a> {
    pub(crate) fn new(info: Arc<FrameInfo<'a>>) -> Self {
        let n = info.body.locals.len();
        Self::with_locals(info, vec![None; n])
    }

    pub(crate) fn with_locals(info: Arc<FrameInfo<'a>>, locals: Vec<Option<Value<'a>>>) -> Self {
        Self {
            info,
            locals: Arc::new(RwLock::new(locals)),
            aliases: Vec::new(),
        }
    }

    /// The local that `id` names: itself, or the one a `when` made it the place of.
    pub(crate) fn slot(&self, id: LocalId) -> usize {
        let root = self
            .aliases
            .iter()
            .find(|(alias, _)| *alias == id)
            .map_or(id, |(_, root)| *root);
        root.0 as usize
    }

    pub(crate) fn get(&self, id: LocalId) -> Option<Value<'a>> {
        lock(&self.locals).get(self.slot(id)).cloned().flatten()
    }

    pub(crate) fn set(&mut self, id: LocalId, v: Value<'a>) {
        let i = self.slot(id);
        let mut locals = lock(&self.locals);
        if i >= locals.len() {
            locals.resize(i + 1, None);
        }
        locals[i] = Some(v);
    }

    /// A copy of every local, as a closure literal captures them (expressions.capture), the names
    /// of the `when`s around it holding their places' values.
    pub(crate) fn snapshot(&self) -> Vec<Option<Value<'a>>> {
        let mut locals = lock(&self.locals).clone();
        for (alias, root) in &self.aliases {
            let i = alias.0 as usize;
            let value = locals.get(root.0 as usize).cloned().flatten();
            if i >= locals.len() {
                locals.resize(i + 1, None);
            }
            locals[i] = value;
        }
        locals
    }

    /// The frame's type arguments with `bound` in place of those of the same type parameters, as
    /// the fresh types of an arm or a loop's body and the element type of a spread's body bind
    /// them (meta.fresh-types; variadics.spread-expressions).
    pub(crate) fn bind_types(&mut self, bound: Vec<(GenericId, Ty)>) {
        if bound.is_empty() {
            return;
        }
        let info = Arc::make_mut(&mut self.info);
        let earlier = std::mem::take(&mut info.tenv);
        let mut tenv = bound;
        let kept: Vec<_> = earlier
            .into_iter()
            .filter(|(g, _)| !tenv.iter().any(|(h, _)| h == g))
            .collect();
        tenv.extend(kept);
        info.tenv = tenv;
    }
}
