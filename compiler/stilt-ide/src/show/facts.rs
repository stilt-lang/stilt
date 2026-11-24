//! The inferred facts of a module's functions, each with the line that causes it, as the
//! queries that compute them give them (goal shown-facts): the parameters each function consumes
//! and the calls at which it loses reuse, from `stilt-rc` (values.consumed-parameters), the modes
//! of its bindings that aren't at their defaults, from `stilt-rc` too (modes.show), and the
//! sources its views read, from `stilt-types` (views.show), its `panic`, `overflow`, `alloc` and
//! `div`, from the implicit effects that the limits of `without` read (facts.inference and
//! facts.visibility), its in-place parameters, from `stilt-types` too, and its `copy`, and the
//! copies that shared writes make allocate, from `stilt-rc` (facts.copy-at-call and facts.copy),
//! its `locks`, from `stilt-types` (shared.locks), its capabilities below `io`, from
//! `stilt-types` too (facts.capabilities), and the operations that may share values between
//! threads, whose counts are then atomic, from `stilt-types` too (par.atomic-sites). A module's
//! tier is a fact of its own (program.module-tier), from `stilt-types` too.

use stilt_hir::hir::Name;

use serde_json::{Value, json};
use stilt_db::{Database, Program, SourceFile};
use stilt_diag::LineIndex;
use stilt_hir::hir::Capability;
use stilt_mir::FnRef;
use stilt_rc::{LostReuse, Need};
use stilt_types::facts::{Effect, effect_causes};
use stilt_types::tast::Definition;

use super::locals::{Local, untyped};
use super::modes::{self, Modes};
use super::views::{self, Views};
use crate::text;

mod declared;
mod listed;
mod table;

pub(crate) use table::FACTS;

pub use declared::declared;

/// A line of a function that causes one of its facts, and what it does there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cause {
    /// The line, 1-based.
    pub line: u32,
    /// The parameter consumed, for a cause of consumption, and the place passed, for a call that
    /// loses reuse.
    pub name: Option<Name>,
    /// What the line does there, as `show` writes it in a comment.
    pub says: String,
}

/// A function of the program, with its facts.
#[derive(Clone, Debug)]
pub struct Function {
    /// Its path (edits.paths): its module and name, and for a method, its type's or trait's
    /// name between them, as in `main.Point.norm`, and for a method of a trait impl, its type's
    /// and its trait's, as in `main.Point.Show.show`.
    pub address: String,
    /// The file that declares it.
    pub file: SourceFile,
    /// Its module's tier (program.module-tier).
    tier: &'static str,
    /// Its body, among its module's.
    pub index: u32,
    /// The line of its name.
    pub line: u32,
    /// The offset of its name in its file.
    pub name_at: usize,
    /// Its code, as the MIR names it.
    pub code: FnRef,
    /// Whether its body has an error, which leaves it no inferred fact (facts.bodies-with-errors).
    pub broken: bool,
    /// Whether it is exported to C, written `pub extern fn` (c.exported-fact).
    pub exported: bool,
    /// The parameters it consumes, each at the line that consumes it (values.passing-values).
    pub consumes: Vec<Cause>,
    /// The calls that consume a value the function still needs, which can't reuse its memory.
    pub lost_reuse: Vec<Cause>,
    /// The modes of its bindings that aren't at their defaults (modes.show).
    pub modes: Modes,
    /// The sources its views read or write, and the parameters its result views or writes
    /// (views.show; projections.show).
    pub views: Views,
    /// Its parameters that it updates in place (facts.in-place-parameters).
    pub in_place: Vec<Cause>,
    /// The lines that can panic (effects.panicking-operations).
    pub panic: Vec<Cause>,
    /// The lines whose integer arithmetic can overflow (effects.overflow-effect).
    pub overflow: Vec<Cause>,
    /// The lines that allocate (facts.allocation).
    pub alloc: Vec<Cause>,
    /// The lines that may not end (facts.div).
    pub div: Vec<Cause>,
    /// The lines that copy a shared value (facts.copy).
    pub copy: Vec<Cause>,
    /// The lines where it holds shared values (shared.locks).
    pub locks: Vec<Cause>,
    /// The lines that give it each capability, in the order of facts.capabilities.
    pub capabilities: [Vec<Cause>; 8],
    /// The lines that may share values between threads (par.atomic-sites).
    pub atomic: Vec<Cause>,
    /// The checks that a rule of acceptance proves can't fail, where a `panic` would have been,
    /// each with what it rules out, as `bounds`, and the rule's name (facts.shown-proofs).
    pub proved: Vec<(Cause, &'static str, &'static str)>,
    /// The patterns of its `let` and `var` statements that write no type, with their types.
    pub locals: Vec<Local>,
    /// The type parameters it reflects on (meta.reflects).
    pub reflects: Vec<String>,
    /// The lines of its own `unsafe` blocks, each with its reason (c.unsafe-and-foreign).
    pub unsafe_blocks: Vec<Cause>,
    /// The lines that name foreign functions, each with the function (c.unsafe-and-foreign).
    pub foreign: Vec<Cause>,
}

impl Function {
    /// The words of the facts written after the function's signature, as in
    /// `[consumes xs, alloc]`, in the order [`Function::listed`] gives.
    #[must_use]
    pub fn summary(&self) -> Vec<String> {
        self.listed().into_iter().map(|f| f.text).collect()
    }

    /// Infers the function's facts.
    pub fn infer(&mut self, db: &Database, program: Program) {
        self.broken = matches!(
            stilt_types::infer_body(db, program, self.file, self.index)
                .body
                .code,
            Definition::Broken
        );
        if self.broken {
            return;
        }
        let module = &stilt_hir::module_hir(db, program, self.file).name;
        self.consumes = consumes(db, program, module, &self.code, self.line);
        let lost = stilt_rc::losing_reuse(db, program, &self.code);
        let found = stilt_rc::modes(db, program, &self.code);
        self.lost_reuse = lost_reuse(&lost, module, self.line);
        self.modes = modes::shown(db, self.file, module, &found);
        self.views = views::shown(db, program, self.file, self.index);
        let [panic, overflow, alloc, div, copy, locks, capabilities @ ..] =
            effects(db, program, self.file, self.index);
        [self.panic, self.overflow, self.alloc] = [panic, overflow, alloc];
        [self.div, self.copy] = [div, copy];
        self.locks = locks;
        self.capabilities = capabilities;
        self.in_place = in_place(db, program, self.file, self.index);
        self.atomic = atomic(db, program, self.file, self.index);
        self.proved = proved(db, program, self.file, self.index);
        self.locals = untyped(db, program, self.file, self.index);
        self.reflects = reflected(db, program, &self.code);
        (self.unsafe_blocks, self.foreign) = unsafe_code(db, program, self.file, self.index);
    }

    /// The function as a JSON record: its address, file and line, its module's tier, each
    /// fact's causes, with the parameter each consumes, the place each call that loses reuse is
    /// given, the binding each mode is of and the source each view reads, and the types of the
    /// patterns that write none.
    pub fn json(&self, db: &Database) -> Value {
        let causes = |causes: &[Cause], key: Option<&str>| -> Vec<Value> {
            causes
                .iter()
                .map(|c| {
                    let mut record = json!({ "line": c.line, "cause": c.says });
                    if let (Some(key), Some(name)) = (key, &c.name) {
                        record[key] = json!(&**name);
                    }
                    record
                })
                .collect()
        };
        json!({
            "function": self.address,
            "file": self.file.path(db),
            "line": self.line,
            "tier": self.tier,
            "exported": self.exported,
            "consumes": causes(&self.consumes, Some("param")),
            "lost_reuse": causes(&self.lost_reuse, Some("place")),
            "escapes": causes(&self.modes.escapes, Some("name")),
            "shared": causes(&self.modes.shared, Some("name")),
            "once": causes(&self.modes.once, Some("name")),
            "views": causes(&self.views.causes, Some("name")),
            "writes": causes(&self.views.writes, Some("name")),
            "in_place": causes(&self.in_place, Some("param")),
            "panic": causes(&self.panic, None),
            "overflow": causes(&self.overflow, None),
            "alloc": causes(&self.alloc, None),
            "div": causes(&self.div, None),
            "copy": causes(&self.copy, None),
            "locks": causes(&self.locks, None),
            "atomic": causes(&self.atomic, None),
            "proved": self.proved.iter().map(|(c, kind, rule)| {
                json!({ "line": c.line, "proved": kind, "cause": c.says, "rule": rule })
            }).collect::<Vec<_>>(),
            "reflects": self.reflects,
            "unsafe": causes(&self.unsafe_blocks, None),
            "foreign": causes(&self.foreign, Some("name")),
            "capabilities": Capability::ALL
                .iter()
                .zip(&self.capabilities)
                .map(|(c, found)| (c.text().to_owned(), json!(causes(found, None))))
                .collect::<serde_json::Map<_, _>>(),
            "locals": self.locals.iter().map(|l| {
                json!({ "pattern": l.pattern, "line": l.line, "type": l.ty })
            }).collect::<Vec<_>>(),
        })
    }
}

/// The lines by which a function consumes its parameters. A use that lowering marked with no
/// line is put at the function's name, on `name_line`.
fn consumes(
    db: &Database,
    program: Program,
    module: &str,
    f: &FnRef,
    name_line: u32,
) -> Vec<Cause> {
    let found = stilt_rc::consuming(db, program, f).into_iter().map(|c| {
        let line = match stilt_mir::mir::line_of(c.at) {
            0 => name_line,
            line => line,
        };
        let says = match &c.through {
            None => format!("consumes `{}`", c.param),
            Some(g) => format!("consumes `{}`, through {}", c.param, describe(module, g)),
        };
        Cause {
            line,
            name: Some(c.param),
            says,
        }
    });
    distinct(found)
}

/// The lines of the calls at which a function loses reuse, as `found` gives them: each consumes a
/// place that the function uses after it or passes to it twice (values.consumed-parameters), or the
/// value of an `inout` parameter, which goes back to the caller when the function returns or raises
/// unless it assigns the whole parameter before (values.inout-arguments). A call that lowering
/// marked with no line is put at the function's name, on `name_line`.
fn lost_reuse(found: &[LostReuse], module: &str, name_line: u32) -> Vec<Cause> {
    let found = found.iter().map(|l| {
        let line = match stilt_mir::mir::line_of(l.at) {
            0 => name_line,
            line => line,
        };
        let why = match l.need {
            Need::After => "is used after this call",
            Need::Twice => "is passed twice in this call",
            Need::Back { raises: false, .. } => "goes back to the caller when the function returns",
            Need::Back { returns: false, .. } => "goes back to the caller when the function raises",
            Need::Back { .. } => "goes back to the caller when the function returns or raises",
        };
        let says = format!(
            "`{}` {why}, so {} can't reuse it",
            l.place,
            describe(module, &l.callee)
        );
        Cause {
            line,
            name: Some(l.place),
            says,
        }
    });
    distinct(found)
}

/// The effects that `show` prints, in its order: `panic`, `overflow`, `alloc`, `div`, `copy`
/// and `locks`, and the capabilities in the order of facts.capabilities.
pub const SHOWN: [Effect; 14] = [
    Effect::Panic,
    Effect::Overflow,
    Effect::Alloc,
    Effect::Div,
    Effect::Copy,
    Effect::Locks,
    Effect::Capability(Capability::Fs),
    Effect::Capability(Capability::Net),
    Effect::Capability(Capability::Clock),
    Effect::Capability(Capability::Env),
    Effect::Capability(Capability::Console),
    Effect::Capability(Capability::Rand),
    Effect::Capability(Capability::Spawn),
    Effect::Capability(Capability::Exec),
];

/// The lines by which a function can panic, allocates, may not end, copies shared data, holds
/// shared values and has each capability, in the order of [`SHOWN`].
fn effects(db: &Database, program: Program, file: SourceFile, index: u32) -> [Vec<Cause>; 14] {
    let text = text(db, file);
    let lines = LineIndex::new(&text);
    let causes: Vec<(Effect, Cause)> = effect_causes(db, program, file, index)
        .into_iter()
        .map(|c| (c.effect, c.at, c.says))
        .chain(stilt_rc::copy_causes(db, program, file, index))
        .map(|(effect, at, says)| {
            let cause = Cause {
                line: lines.position(&text, at.start()).line,
                name: None,
                says,
            };
            (effect, cause)
        })
        .collect();
    SHOWN.map(|effect| {
        distinct(
            causes
                .iter()
                .filter(|(e, _)| *e == effect)
                .map(|(_, c)| c.clone()),
        )
    })
}

/// The type parameters a function reflects on, by their names.
fn reflected(db: &Database, program: Program, f: &FnRef) -> Vec<String> {
    use stilt_types::reflects::Key;
    let key = match f {
        FnRef::Function(item) => Key::Function(item.clone()),
        FnRef::Member(owner, name) => Key::Member(owner.clone(), *name),
        FnRef::ImplMethod(t, owner, name) => Key::ImplMethod(t.clone(), owner.clone(), *name),
        FnRef::DefaultMethod(t, name) => Key::DefaultMethod(t.clone(), *name),
        _ => return Vec::new(),
    };
    stilt_types::reflects::reflected(db, program, key)
}

/// The lines that may share values between threads, each with what it shares.
fn atomic(db: &Database, program: Program, file: SourceFile, index: u32) -> Vec<Cause> {
    let text = text(db, file);
    let lines = LineIndex::new(&text);
    let found = stilt_types::facts::atomic_causes(db, program, file, index)
        .into_iter()
        .map(|(at, says)| Cause {
            line: lines.position(&text, at.start()).line,
            name: None,
            says,
        });
    distinct(found)
}

/// The lines whose checks a rule of acceptance proves, each with what it rules out and the rule
/// (facts.shown-proofs).
fn proved(
    db: &Database,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Vec<(Cause, &'static str, &'static str)> {
    let text = text(db, file);
    let lines = LineIndex::new(&text);
    let mut out: Vec<(Cause, &'static str, &'static str)> = Vec::new();
    for p in stilt_types::facts::proved_checks(db, program, file, index) {
        let Some(kind) = p.check.shown() else {
            continue;
        };
        let rule = p.rule.name();
        let cause = Cause {
            line: lines.position(&text, p.at.start()).line,
            name: None,
            says: format!("proved {kind} by a {rule}"),
        };
        let found = (cause, kind, rule);
        if !out.iter().any(|(c, k, _)| *c == found.0 && *k == found.1) {
            out.push(found);
        }
    }
    out
}

/// The lines that make the function's parameters in place, each with the parameter.
fn in_place(db: &Database, program: Program, file: SourceFile, index: u32) -> Vec<Cause> {
    let text = text(db, file);
    let lines = LineIndex::new(&text);
    let found = stilt_types::promises::in_place_causes(db, program, file, index)
        .into_iter()
        .map(|(name, at)| Cause {
            line: lines.position(&text, at.start()).line,
            says: format!("updates `{name}` in place"),
            name: Some(name),
        });
    distinct(found)
}

/// The lines of a function's own `unsafe` blocks, each with its reason, and the lines that name
/// foreign functions, each with the function (c.unsafe-and-foreign).
fn unsafe_code(
    db: &Database,
    program: Program,
    file: SourceFile,
    index: u32,
) -> (Vec<Cause>, Vec<Cause>) {
    let text = text(db, file);
    let lines = LineIndex::new(&text);
    let blocks = stilt_types::facts::unsafe_blocks(db, program, file, index)
        .into_iter()
        .map(|(at, reason)| Cause {
            line: lines.position(&text, at.start()).line,
            name: None,
            says: format!("unsafe because {}", stilt_runtime::quoted(&reason)),
        });
    let foreign = stilt_types::facts::foreign_uses(db, program, file, index)
        .into_iter()
        .map(|(at, name, trusted)| Cause {
            line: lines.position(&text, at.start()).line,
            says: match trusted.names().as_slice() {
                [] => format!("`{name}` is C code"),
                names => format!("`{name}` is C code, trusted without {}", names.join(", ")),
            },
            name: Some(name),
        });
    (distinct(blocks), distinct(foreign))
}

/// The causes, each once, in their first order.
pub fn distinct(causes: impl Iterator<Item = Cause>) -> Vec<Cause> {
    let mut out: Vec<Cause> = Vec::new();
    for c in causes {
        if !out.contains(&c) {
            out.push(c);
        }
    }
    out
}

/// A function as code in `module` names it: without its module when it is the module's own
/// or the prelude's, and by its type's or trait's name when it is a method.
#[must_use]
pub fn describe(module: &str, f: &FnRef) -> String {
    match f {
        FnRef::Function(item) if &*item.home == module || &*item.home == "std.prelude" => {
            format!("`{}`", item.name)
        }
        FnRef::Function(item) => {
            let last = item.home.rsplit('.').next().unwrap_or(&item.home);
            format!("`{last}.{}`", item.name)
        }
        FnRef::Member(owner, name) | FnRef::ImplMethod(_, owner, name) => {
            format!("`{}.{name}`", owner.name)
        }
        FnRef::DefaultMethod(t, name) => format!("`{}.{name}`", t.name),
        other => format!("`{other}`"),
    }
}
