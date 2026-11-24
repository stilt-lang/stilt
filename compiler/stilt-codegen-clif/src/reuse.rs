//! Machine code kept from one build of a program to the next, so that a build after an edit
//! compiles with Cranelift only the functions whose code the edit changed, and defines every
//! other function from the code it kept (goals compile-time-code-rebuilds and one-engine).
//!
//! A function's machine code follows its MIR, as inlining and reference counting leave it, the
//! target, the settings of a build, which every build shares, and the answers its translation
//! had from the module's registry ([`Asked`]): a build reuses the code of a function whose MIR is
//! the same once the registry, asked again in the order of translation, answers as it did. The
//! code's relocations and its DWARF name the module's functions and data by their numbers,
//! which a later build gives otherwise when an edit adds or removes a function or a constant
//! before them, so the code is kept with the question that gave each number, and a build that
//! reuses it relocates it against the answers that the questions asked again give ([`Kept`]).
//! The object is then the one a build that compiles every function writes, byte for byte. A
//! build keeps the code of the functions it reached alone, so the code of a function no longer
//! reached goes once the build that no longer reaches it ends (goal bounded-cache).

mod kept;
#[cfg(test)]
mod tests;

use std::sync::Arc;

use cranelift_codegen::isa::TargetIsa;
use cranelift_frontend::FunctionBuilderContext;
use cranelift_module::{FuncId, Module};
use rustc_hash::{FxBuildHasher, FxHashMap as HashMap, FxHashSet as HashSet};
use stilt_db::parallel;
use stilt_mir::FnRef;
use stilt_mir::mir::Function;

use crate::compile::{Compiled, Translated, compile_all, translate};
use crate::debug::piece::Piece;
use crate::draft::Asks;
use crate::module::{Answer, Asked, Registry};
use crate::target::Target;

use kept::Kept;

/// The machine code of each function that the last build of a program for a target compiled,
/// which the next build reuses.
#[derive(Default)]
pub struct Built {
    target: Option<Target>,
    functions: HashMap<FnRef, Arc<Kept>>,
    /// How many objects of static data the build declared for constants.
    data: usize,
}

impl std::fmt::Debug for Built {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Built")
            .field("target", &self.target)
            .field("functions", &self.functions.len())
            .field("data", &self.data)
            .finish()
    }
}

impl Built {
    /// The code kept of `f`, if it was compiled from the same MIR. A function that didn't
    /// change is the same `Arc` as before, which tells it apart at no cost.
    fn of(&self, f: &Arc<Function>) -> Option<Arc<Kept>> {
        self.functions
            .get(&f.name)
            .filter(|k| Arc::ptr_eq(&k.function, f) || *k.function == **f)
            .cloned()
    }
}

/// How a build defines a function: from the code kept of it, with the answers its questions
/// gave again; from the code compiled from its draft, the `k`th, with what the draft's
/// translation asked and the answers it gave, and the answers they give again
/// ([`crate::draft`]); or from code it compiles from a translation into the module, with what
/// it asked. The number is the one the module gives the function's code.
enum Step {
    Kept(Arc<Kept>, FuncId, Vec<Answer>),
    Drafted(Arc<Function>, FuncId, Asks, Vec<Answer>, usize),
    Fresh(Arc<Function>, Asks),
}

/// The steps of a build, with the functions translated into the module, which it compiles once
/// the steps are settled.
type Settled<'f> = (Vec<Step>, Vec<Translated<'f>>);

/// The functions of a build in the order they are translated in, each with the number of its
/// code in the module and the code kept of it.
type Order<'f> = Vec<(&'f Arc<Function>, FuncId, Option<Arc<Kept>>)>;

/// Code compiled in a build: from translations into the module, then from drafts.
type Compiling = (Vec<Result<Compiled, String>>, Vec<Result<Compiled, String>>);

/// Compiles the functions into `module`, for `target`, whose ISA is `isa`, as
/// [`crate::compile::compile`] does, but with the code that `built` kept of each one that didn't
/// change, and keeps the code of each in `built` for the next build. The others are translated
/// apart and compiled across the machine's cores while the build declares every function and
/// asks again what the kept code asked, but the entry, whose translation reads the cells of the
/// constants that every other function declared. With `reg.debug`, returns the DWARF of each.
pub(crate) fn compile(
    module: &mut dyn Module,
    reg: &mut Registry,
    functions: &[Arc<Function>],
    (built, target, isa): (&mut Built, Target, &dyn TargetIsa),
) -> Result<Vec<Arc<Piece>>, String> {
    if built.target != Some(target) {
        *built = Built {
            target: Some(target),
            functions: HashMap::default(),
            data: 0,
        };
    }
    reg.reserve(functions.len(), built.data);
    let mut kept: Vec<_> = functions.iter().map(|f| built.of(f)).collect();
    let order = in_order(functions);
    // Each function whose code isn't kept, but the entry, by its place in the order.
    let mut changed = vec![None; order.len()];
    let mut drafted = Vec::new();
    for (at, &i) in order.iter().enumerate() {
        if kept[i].is_none() && functions[i].name != FnRef::Main {
            changed[at] = Some(drafted.len());
            drafted.push(&functions[i]);
        }
    }
    let drafts = crate::draft::drafts(reg, functions, drafted);
    let mut index = vec![0; drafts.len()];
    for (i, &(k, _)) in drafts.iter().enumerate() {
        index[k] = i;
    }
    let debug = reg.debug;
    let (settled, compiled) = parallel::map_costly_alongside(
        drafts,
        |(_, draft), asked| draft.compile(isa, debug, asked),
        |early| {
            let ids = declare(module, reg, functions, &kept)?;
            let order = (order.iter())
                .map(|&i| (&functions[i], ids[i], kept[i].take()))
                .collect();
            let draft = |at: usize| changed[at].map(|k| (index[k], early.wait(index[k])));
            settle(module, reg, order, &draft)
        },
    );
    let (steps, translated) = settled?;
    let fresh = compile_all(translated, isa, debug);
    let pieces = define(module, steps, (fresh, compiled), built);
    built.data = reg.data_count();
    pieces
}

/// The places of the functions in the order they are translated in: the entry last, as in
/// `crate::compile::define`.
fn in_order(functions: &[Arc<Function>]) -> Vec<usize> {
    let (main, others): (Vec<usize>, Vec<usize>) =
        (0..functions.len()).partition(|&i| functions[i].name == FnRef::Main);
    others.into_iter().chain(main).collect()
}

/// Declares each function in `module`, in their order, under the symbol of the code kept of it
/// if there is any: the number of each.
fn declare(
    module: &mut dyn Module,
    reg: &mut Registry,
    functions: &[Arc<Function>],
    kept: &[Option<Arc<Kept>>],
) -> Result<Vec<FuncId>, String> {
    let mut ids = Vec::with_capacity(functions.len());
    for (f, kept) in functions.iter().zip(kept) {
        ids.push(match kept {
            Some(k) => reg.declare_as(module, f, &k.symbol)?,
            None => reg.declare(module, f)?,
        });
    }
    Ok(ids)
}

/// The draft of the function at a place among the functions, if it has one: its index among the
/// drafts, and what its translation asked, once it is translated, or `None` when translating it
/// panicked.
type DraftOf<'a> = dyn Fn(usize) -> Option<(usize, Option<Result<Asks, String>>)> + 'a;

/// Asks again, in the order of the functions, what the translation of each function whose code
/// is kept asked, and what the draft of each changed function asked, and translates into the
/// module each other function, the entry among them, and those whose answers differ: the step of
/// each function, with the translations to compile, in their order.
fn settle<'f>(
    module: &mut dyn Module,
    reg: &mut Registry,
    order: Order<'f>,
    draft: &DraftOf<'_>,
) -> Result<Settled<'f>, String> {
    let mut fbc = FunctionBuilderContext::new();
    let (mut steps, mut translated) = (Vec::new(), Vec::new());
    for (at, (f, id, kept)) in order.into_iter().enumerate() {
        if let Some(kept) = kept {
            if let Some(answers) = reg.ask_again(module, kept.asked.iter())? {
                steps.push(Step::Kept(kept, id, answers));
                continue;
            }
        } else if let Some((k, asked)) = draft(at) {
            let asked = asked.ok_or("translating a function panicked")??;
            if let Some(answers) = reg.ask_again(module, asked.iter().map(|(a, _)| a))? {
                steps.push(Step::Drafted(Arc::clone(f), id, asked, answers, k));
                continue;
            }
        }
        reg.asked = Some(Vec::new());
        let t = translate(module, reg, &mut fbc, f, id);
        let asked = once_each(reg.asked.take().unwrap_or_default());
        translated.push(t?);
        steps.push(Step::Fresh(Arc::clone(f), asked));
    }
    Ok((steps, translated))
}

/// What translation asked, without what it asked again: a declaration asked again finds what
/// the first declared, and a question has one answer in a build. The cells of the constants are
/// kept each time, since a constant declared between two looks at them changes the second.
pub(crate) fn once_each(mut asked: Vec<(Asked, Answer)>) -> Vec<(Asked, Answer)> {
    let first: Vec<bool> = {
        let mut seen = HashSet::default();
        (asked.iter())
            .map(|(a, _)| matches!(a, Asked::Constants(_)) || seen.insert(a))
            .collect()
    };
    let mut first = first.into_iter();
    asked.retain(|_| first.next().unwrap_or(true));
    asked
}

/// Defines each function in the order of its step, from the code kept of it or from the code
/// compiled now, `fresh` from translations into the module and `drafted` from drafts, and keeps
/// the code of each in `built`, in place of what it held.
fn define(
    module: &mut dyn Module,
    steps: Vec<Step>,
    (fresh, drafted): Compiling,
    built: &mut Built,
) -> Result<Vec<Arc<Piece>>, String> {
    let mut fresh = fresh.into_iter();
    let mut drafted: Vec<Option<Result<Compiled, String>>> =
        drafted.into_iter().map(Some).collect();
    let mut pieces = Vec::with_capacity(steps.len());
    let mut kept = HashMap::with_capacity_and_hasher(steps.len(), FxBuildHasher);
    for step in steps {
        let (code, answers, id) = match step {
            Step::Kept(k, id, answers) => (k, answers, id),
            Step::Drafted(function, id, asked, answers, k) => {
                let c = drafted.get_mut(k).and_then(Option::take);
                let c = c.ok_or("a function wasn't compiled")??;
                let name = c.name.clone();
                let k = Kept::new(function, asked, c)
                    .ok_or_else(|| format!("{name}'s draft names what it didn't ask"))?;
                (Arc::new(k.settled(&answers, id)), answers, id)
            }
            Step::Fresh(function, asked) => {
                let c = fresh.next().ok_or("a function wasn't compiled")??;
                module
                    .define_function_bytes(c.id, c.alignment, &c.bytes, &c.relocs)
                    .map_err(|e| format!("cannot compile {}: {e:?}", c.name))?;
                pieces.extend(c.dwarf.clone());
                if let Some(k) = Kept::new(function, asked, c) {
                    kept.insert(k.code.name.clone(), Arc::new(k));
                }
                continue;
            }
        };
        let (relocs, piece) = code.relocated(&answers, id);
        let c = &code.code;
        module
            .define_function_bytes(id, c.alignment, &c.bytes, &relocs)
            .map_err(|e| format!("cannot compile {}: {e:?}", c.name))?;
        pieces.extend(piece);
        kept.insert(c.name.clone(), Arc::clone(&code));
    }
    parallel::free(std::mem::replace(&mut built.functions, kept));
    Ok(pieces)
}
