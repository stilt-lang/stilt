//! Building a function: its locals, its blocks, and the statements of the block being built.

use std::cell::Cell;
use stilt_hir::hir::Name;

use crate::FnRef;
use crate::mir::{
    Block, BlockId, Function, Local, LocalDecl, Operand, Param, ParamMode, Repr, Runtime, Rvalue,
    Stmt, Terminator,
};

/// A function being built. Code after a jump goes to a fresh block that nothing jumps to,
/// which [`Builder::finish`] removes.
#[derive(Debug)]
pub(crate) struct Builder {
    name: FnRef,
    params: Vec<Param>,
    locals: Vec<LocalDecl>,
    blocks: Vec<(Vec<Stmt>, Option<Terminator>)>,
    current: BlockId,
    /// The location word of the source being lowered, or 0 where there is none, and for each
    /// block the last location its markers gave (goal debuggable-builds).
    at: u64,
    marked: Vec<u64>,
    /// Whether lowering met the error type.
    broken: Cell<bool>,
    /// Whether lowering met a value larger than any that compiled code holds
    /// (generics.large-arrays).
    too_large: Cell<bool>,
    /// The number of parameters that stand for the function's type and value arguments, the
    /// location first ([`Function::hidden`]).
    hidden: usize,
}

impl Builder {
    pub(crate) fn new(name: FnRef) -> Self {
        Self {
            name,
            params: Vec::new(),
            locals: Vec::new(),
            blocks: vec![(Vec::new(), None)],
            current: BlockId(0),
            at: 0,
            marked: vec![0],
            broken: Cell::new(false),
            too_large: Cell::new(false),
            hidden: 0,
        }
    }

    /// Records that the parameters so far stand for the function's type and value arguments,
    /// or are the location, which a release build specializes it for (builds.specialization).
    pub(crate) fn hide(&mut self) {
        self.hidden = self.hidden.max(self.params.len());
    }

    /// Records that lowering met the error type.
    pub(crate) fn met_error(&self) {
        self.broken.set(true);
    }

    /// Records that lowering met a value too large for compiled code to hold, so that the function
    /// ends the program as running out of memory does (generics.large-arrays;
    /// program.exit-statuses).
    pub(crate) fn met_too_large(&self) {
        self.too_large.set(true);
    }

    pub(crate) fn local(&mut self, repr: Repr, name: Option<Name>) -> Local {
        let local = Local(u32::try_from(self.locals.len()).expect("under 4G locals"));
        self.locals.push(LocalDecl {
            repr,
            slot: false,
            grouped: false,
            borrowed: false,
            var: false,
            name,
            shown: None,
        });
        local
    }

    /// How a local holds its value.
    pub(crate) fn repr_of(&self, local: Local) -> Repr {
        self.locals[local.0 as usize].repr
    }

    /// Puts the locals that hold the words of one value in memory, one slot after the other,
    /// so that a pointer to the first reaches them all. They are consecutive locals.
    pub(crate) fn make_slots(&mut self, locals: &[Local]) {
        for (i, &l) in locals.iter().enumerate() {
            debug_assert!(i == 0 || l.0 == locals[i - 1].0 + 1, "the words of a value");
            let decl = &mut self.locals[l.0 as usize];
            decl.slot = true;
            decl.grouped = i > 0;
        }
    }

    /// Lowers the code that follows as coming from the source at this location word, or from
    /// nowhere in particular for 0.
    pub(crate) fn set_at(&mut self, at: u64) {
        self.at = at;
    }

    /// Marks the current block with the current location, if it has another.
    fn mark(&mut self) {
        let b = self.current.0 as usize;
        if self.at != 0 && self.marked[b] != self.at && self.blocks[b].1.is_none() {
            self.marked[b] = self.at;
            self.blocks[b].0.push(Stmt::At(self.at));
        }
    }

    pub(crate) fn temp(&mut self, repr: Repr) -> Local {
        self.local(repr, None)
    }

    pub(crate) fn param(&mut self, repr: Repr, mode: ParamMode, name: Option<Name>) -> Local {
        let local = self.local(repr, name);
        self.params.push(Param { local, mode });
        local
    }

    /// Makes a local a parameter, after the others.
    pub(crate) fn add_param(&mut self, local: Local, mode: ParamMode) {
        self.params.push(Param { local, mode });
    }

    pub(crate) fn name(&self) -> &FnRef {
        &self.name
    }

    pub(crate) fn decl_mut(&mut self, local: Local) -> &mut LocalDecl {
        &mut self.locals[local.0 as usize]
    }

    pub(crate) fn new_block(&mut self) -> BlockId {
        let id = BlockId(u32::try_from(self.blocks.len()).expect("under 4G blocks"));
        self.blocks.push((Vec::new(), None));
        self.marked.push(0);
        id
    }

    pub(crate) fn switch_to(&mut self, block: BlockId) {
        self.current = block;
    }

    pub(crate) fn emit(&mut self, stmt: Stmt) {
        self.mark();
        self.blocks[self.current.0 as usize].0.push(stmt);
    }

    pub(crate) fn assign(&mut self, dest: Local, rvalue: Rvalue) {
        self.emit(Stmt::Assign(dest, rvalue));
    }

    /// A new local of this representation, assigned the rvalue.
    pub(crate) fn define(&mut self, repr: Repr, rvalue: Rvalue) -> Local {
        let dest = self.temp(repr);
        self.assign(dest, rvalue);
        dest
    }

    pub(crate) fn define_op(&mut self, repr: Repr, rvalue: Rvalue) -> Operand {
        Operand::Local(self.define(repr, rvalue))
    }

    /// Ends the current block with `term`, and goes on in a fresh block that nothing reaches
    /// yet.
    pub(crate) fn terminate(&mut self, term: Terminator) {
        self.mark();
        let block = &mut self.blocks[self.current.0 as usize];
        if block.1.is_none() {
            block.1 = Some(term);
        }
        self.current = self.new_block();
    }

    pub(crate) fn goto(&mut self, target: BlockId) {
        self.terminate(Terminator::Goto(target));
    }

    pub(crate) fn branch(&mut self, cond: Operand, then: BlockId, otherwise: BlockId) {
        self.terminate(Terminator::Branch {
            cond,
            then,
            otherwise,
        });
    }

    /// The function, which returns `results` words, without the blocks that its entry can't
    /// reach.
    pub(crate) fn finish(self, results: u32) -> Function {
        let Builder {
            name,
            params,
            locals,
            blocks,
            broken,
            too_large,
            hidden,
            ..
        } = self;
        // The code of an object takes it after the location.
        let object = if crate::special::object_code(&name) {
            2
        } else {
            1
        };
        let hidden = u32::try_from(hidden.max(object).min(params.len())).expect("under 4G");
        let mut blocks: Vec<Block> = blocks
            .into_iter()
            .map(|(stmts, term)| Block {
                stmts,
                term: term.unwrap_or(Terminator::Unreachable),
            })
            .collect();
        if too_large.get() {
            blocks = vec![Block {
                stmts: vec![Stmt::Effect(Runtime::OutOfMemory, Vec::new())],
                term: Terminator::Unreachable,
            }];
            broken.set(false);
        }
        crate::prune::reachable(Function {
            name,
            params,
            hidden,
            results,
            locals,
            blocks,
            broken: broken.get(),
        })
    }
}
