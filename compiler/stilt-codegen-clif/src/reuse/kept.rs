//! A function's machine code as a build keeps it: with the questions its translation asked of
//! the registry, and for each number of a function or a data object in its relocations and its
//! DWARF, the question that gave it, so that a later build relocates it against the
//! answers the questions give again.

use std::borrow::Cow;
use std::sync::Arc;

use cranelift_module::{DataId, FuncId, ModuleReloc, ModuleRelocTarget};
use rustc_hash::FxHashMap as HashMap;
use stilt_mir::mir::Function;

use crate::compile::Compiled;
use crate::debug::piece::Piece;
use crate::module::{Answer, Asked};

/// A function's machine code, with what it was compiled from.
pub(super) struct Kept {
    pub(super) function: Arc<Function>,
    /// The readable part of its code's symbol ([`crate::module::readable`]).
    pub(super) symbol: Box<str>,
    /// What its translation asked of the registry, in order, each once.
    pub(super) asked: Vec<Asked>,
    pub(super) code: Compiled,
    /// Each number of a function or a data object in its code and facts, with the index of the
    /// question in `asked` that gave it.
    functions: Vec<(FuncId, usize)>,
    data: Vec<(DataId, usize)>,
}

impl Kept {
    /// The code compiled from `function`, kept with the question that gave each number in it,
    /// or `None` when a number is no answer to what its translation asked, as no number of a
    /// function's code is.
    pub(super) fn new(
        function: Arc<Function>,
        asked: Vec<(Asked, Answer)>,
        code: Compiled,
    ) -> Option<Self> {
        let answers: Vec<Answer> = asked.iter().map(|&(_, a)| a).collect();
        let (mut functions, mut data) = (Vec::new(), Vec::new());
        for r in &code.relocs {
            match r.name {
                ModuleRelocTarget::User {
                    namespace: 0,
                    index,
                } => note(
                    &mut functions,
                    FuncId::from_u32(index),
                    &answers,
                    Answer::Function,
                )?,
                ModuleRelocTarget::User {
                    namespace: 1,
                    index,
                } => note(&mut data, DataId::from_u32(index), &answers, Answer::Data)?,
                ModuleRelocTarget::User { .. } => return None,
                _ => {}
            }
        }
        for &id in code.dwarf.iter().flat_map(|p| &p.data) {
            note(&mut data, id, &answers, Answer::Data)?;
        }
        Some(Self {
            symbol: crate::module::readable(&function.name).into(),
            function,
            asked: asked.into_iter().map(|(a, _)| a).collect(),
            code,
            functions,
            data,
        })
    }

    /// The code's relocations and facts, against the numbers that `answers`, the answers its
    /// questions gave again, give them, the function's own being `id`: as they are when every
    /// number is the same.
    pub(super) fn relocated(
        &self,
        answers: &[Answer],
        id: FuncId,
    ) -> (Cow<'_, [ModuleReloc]>, Option<Arc<Piece>>) {
        match self.renumbered(answers, id) {
            Some((relocs, dwarf)) => (Cow::Owned(relocs), dwarf),
            None => (Cow::Borrowed(&self.code.relocs), self.code.dwarf.clone()),
        }
    }

    /// The code as [`Kept::relocated`] gives it, kept so, so that a later build that gives the
    /// same numbers takes it as it is.
    pub(super) fn settled(mut self, answers: &[Answer], id: FuncId) -> Self {
        if let Some((relocs, dwarf)) = self.renumbered(answers, id) {
            (self.code.relocs, self.code.dwarf, self.code.id) = (relocs, dwarf, id);
            for (was, i) in &mut self.functions {
                *was = FuncId::from_u32(number(answers[*i]));
            }
            for (was, i) in &mut self.data {
                *was = DataId::from_u32(number(answers[*i]));
            }
        }
        self
    }

    /// The code's relocations and facts against the numbers of `answers` and `id`, or `None`
    /// when every number is the same.
    fn renumbered(
        &self,
        answers: &[Answer],
        id: FuncId,
    ) -> Option<(Vec<ModuleReloc>, Option<Arc<Piece>>)> {
        let functions = (self.functions.iter()).map(|&(was, i)| (was.as_u32(), number(answers[i])));
        let data = (self.data.iter()).map(|&(was, i)| (was.as_u32(), number(answers[i])));
        if id == self.code.id
            && functions
                .clone()
                .chain(data.clone())
                .all(|(was, now)| was == now)
        {
            return None;
        }
        let functions: HashMap<u32, u32> = functions.collect();
        let data: HashMap<u32, u32> = data.collect();
        let relocs = (self.code.relocs.iter())
            .map(|r| {
                let name = match r.name {
                    ModuleRelocTarget::User {
                        namespace: 0,
                        index,
                    } => ModuleRelocTarget::user(0, functions[&index]),
                    ModuleRelocTarget::User { namespace, index } => {
                        ModuleRelocTarget::user(namespace, data[&index])
                    }
                    ModuleRelocTarget::FunctionOffset(_, offset) => {
                        ModuleRelocTarget::FunctionOffset(id, offset)
                    }
                    ref other => other.clone(),
                };
                ModuleReloc { name, ..r.clone() }
            })
            .collect();
        let dwarf = self.code.dwarf.as_ref().map(|p| {
            let mut p = Piece::clone(p);
            p.id = id;
            for d in &mut p.data {
                *d = DataId::from_u32(data[&d.as_u32()]);
            }
            Arc::new(p)
        });
        Some((relocs, dwarf))
    }
}

/// The number that an answer gives.
fn number(answer: Answer) -> u32 {
    match answer {
        Answer::Function(f) => f.as_u32(),
        Answer::Data(d) => d.as_u32(),
        Answer::None => u32::MAX,
    }
}

/// Notes the question whose answer `id` is, `answer` making the answer of a number, unless it
/// is noted already; `None` when no question gave it.
fn note<I: Copy + Eq>(
    names: &mut Vec<(I, usize)>,
    id: I,
    answers: &[Answer],
    answer: impl Fn(I) -> Answer,
) -> Option<()> {
    if !names.iter().any(|(i, _)| *i == id) {
        names.push((id, answers.iter().position(|&a| a == answer(id))?));
    }
    Some(())
}
