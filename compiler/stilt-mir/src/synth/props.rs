//! The entry of a property, which `stilt test` runs once for each run of its closure
//! (tests.property-cases and tests.running-cases), and the decoders of its parameters' values.
//!
//! The compiler generates and shrinks a property's values as data (`stilt-cli`'s
//! `test::prop`), and gives each run's values on a tape (`stilt_runtime::Tape`), which the
//! entry takes as its one word. The entry reads each parameter's value from the tape through the
//! decoder of its type, [`FnRef::Decode`], which builds the value as code that names the type
//! builds it, then calls the closure with the values. It gives 1 when the closure returns
//! `true` and 0 when it returns `false`, and raises the text of what the closure raises, as its
//! `Show` impl shows it. A panic ends the run's thread, which the runtime reports.

use stilt_hir::hir::Name;
use stilt_hir::module_body;
use stilt_types::generable::{self, Graph, Node};
use stilt_types::infer_body;
use stilt_types::tast::{self, Definition, StmtKind, TestKind};
use stilt_types::ty::{FnTy, Ty};

use crate::FnRef;
use crate::items::{Code, code_of};
use crate::lower::calls::{can_raise, error_type};
use crate::lower::words::{operands, word};
use crate::lower::{Catcher, Conv, Cx, Lower};
use crate::mir::{
    Arg, Callee, Function, Local, NumKind, Operand, ParamMode, Prim, Repr, Runtime, Rvalue, Stmt,
    Terminator,
};

/// A property, as its entry and decoders see it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Property {
    /// Its closure's type.
    pub closure: FnTy,
    /// The types its parameters' types hold.
    pub graph: Graph,
    /// The type of each node of the graph.
    pub types: Vec<Ty>,
    /// The node of each parameter's type.
    pub params: Vec<usize>,
    /// Its text, which seeds its cases (tests.seeds).
    pub text: String,
}

/// The property whose body is `index` in the module of `file`, if that body is a property
/// without errors.
#[must_use]
pub fn property(
    db: &dyn stilt_db::Db,
    program: stilt_db::Program,
    file: stilt_db::SourceFile,
    index: u32,
) -> Option<Property> {
    let inferred = &infer_body(db, program, file, index).body;
    if inferred.tested.as_ref()?.kind != TestKind::Property {
        return None;
    }
    let Definition::Code(tast::Code::Block(stmts)) = &inferred.code else {
        return None;
    };
    let StmtKind::Expr(closure) = &stmts.first()?.kind else {
        return None;
    };
    let Ty::Fn(fty) = &closure.ty else {
        return None;
    };
    let stilt_hir::hir::BodyValue::Property(_, text) = &module_body(db, program, file, index).value
    else {
        return None;
    };
    let roots: Vec<Ty> = fty.params.iter().map(|(_, t)| t.clone()).collect();
    let decls = stilt_hir::decls::Queried { db, program };
    let (graph, types, params) = generable::graph(&decls, &roots).ok()?;
    Some(Property {
        closure: (**fty).clone(),
        graph,
        types,
        params,
        text: text.clone(),
    })
}

fn of_module(cx: &Cx<'_>, module: Name, index: u32) -> Option<Property> {
    let Some(Code::Body(file, _)) = code_of(cx.db, cx.program, FnRef::Test(module, index)) else {
        return None;
    };
    property(cx.db, cx.program, file, index)
}

/// Calls the decoder of node `k`, and returns the words of the value it reads.
fn decode(
    l: &mut Lower<'_>,
    p: &Property,
    (module, index): (Name, u32),
    k: usize,
    tape: Local,
) -> Vec<Operand> {
    let ty = &p.types[k];
    let dest = l.temps(ty);
    let next = l.b.new_block();
    let node = u32::try_from(k).expect("under 4G nodes");
    l.b.terminate(Terminator::Call {
        callee: Callee::Direct(FnRef::Decode(module, index, node)),
        args: vec![
            Arg::Borrow(Operand::word(0)),
            Arg::Borrow(Operand::Local(tape)),
        ],
        dest: dest.clone(),
        next,
        raised: None,
    });
    l.b.switch_to(next);
    operands(&dest)
}

/// The entry `f` of the property whose body is `index` in `module`.
pub(super) fn entry(cx: &Cx<'_>, f: &FnRef, module: Name, index: u32) -> Option<Function> {
    let p = of_module(cx, module, index)?;
    let mut l = Lower::new(cx, f.clone(), false);
    super::load_libraries(cx, &mut l);
    l.ret = Conv::of(Ty::bool());
    l.err = Conv::of(Ty::str());
    let tape = l.loc;
    let loc = Operand::word(0);
    let closure = l.b.temp(Repr::Heap);
    let next = l.b.new_block();
    l.b.terminate(Terminator::Call {
        callee: Callee::Direct(FnRef::Test(module, index)),
        args: vec![Arg::Borrow(loc.clone())],
        dest: vec![closure],
        next,
        raised: None,
    });
    l.b.switch_to(next);
    let mut args = Vec::new();
    for &k in &p.params {
        args.extend(
            decode(&mut l, &p, (module, index), k, tape)
                .into_iter()
                .map(Arg::Borrow),
        );
    }
    let error = error_type(&p.closure.row);
    let raises = error != Ty::never() && can_raise(&p.closure.row);
    let arms = l.b.new_block();
    let caught = l.temps(&error);
    if raises {
        l.catchers.push(Catcher {
            ty: error.clone(),
            error: caught.clone(),
            arms,
        });
    }
    let ret = Conv::of(Ty::bool());
    let err = Conv::boxed(error.clone());
    let callee = Callee::Value(Operand::Local(closure));
    let result = l.finish_call(callee, args, &[], loc.clone(), raises, &ret, &err);
    l.b.terminate(Terminator::Return(vec![word(&result, 0)]));
    l.b.switch_to(arms);
    if raises {
        l.catchers.pop();
        let shown = l.trait_call("Show", "show", &error, vec![operands(&caught)], loc);
        l.b.terminate(Terminator::Raise(vec![shown]));
    } else {
        l.b.terminate(Terminator::Unreachable);
    }
    Some(l.into_function())
}

/// The decoder `f` of node `k` of the property whose body is `index` in `module`: it reads a
/// value of the node's type from the tape its parameter points to.
pub(super) fn decoder(
    cx: &Cx<'_>,
    f: &FnRef,
    module: Name,
    index: u32,
    k: u32,
) -> Option<Function> {
    let p = of_module(cx, module, index)?;
    let k = k as usize;
    let ty = p.types.get(k)?.clone();
    let mut l = Lower::new(cx, f.clone(), false);
    l.ret = Conv::of(ty.clone());
    let tape = l.b.param(Repr::Scalar, ParamMode::Borrowed, None);
    let at = (module, index);
    let read = |l: &mut Lower<'_>, op: Runtime, repr: Repr| {
        l.b.define_op(repr, Rvalue::Runtime(op, vec![Operand::Local(tape)]))
    };
    let words = match p.graph.nodes[k].clone() {
        Node::Unit => vec![Operand::word(0)],
        Node::Str => vec![read(&mut l, Runtime::PropStr, Repr::Heap)],
        Node::Bool | Node::Int { .. } | Node::Float { .. } => {
            vec![read(&mut l, Runtime::PropWord, Repr::Scalar)]
        }
        Node::Tuple(slots) => {
            let values = slots
                .iter()
                .map(|&s| decode(&mut l, &p, at, s, tape))
                .collect();
            l.build(&ty, 0, values)
        }
        Node::Record(_, fields) => {
            let values = fields
                .iter()
                .map(|&(_, s)| decode(&mut l, &p, at, s, tape))
                .collect();
            l.build(&ty, 0, values)
        }
        Node::Variants(variants) => variant(&mut l, &p, at, (&ty, &variants), tape),
        Node::List(elem) => vec![list(&mut l, &p, at, elem, tape)],
        Node::Map(key, value) => vec![map(&mut l, &p, at, (key, value), tape)],
    };
    l.b.terminate(Terminator::Return(words));
    Some(l.into_function())
}

/// A value of a variant type: its variant's number, then that variant's payloads.
fn variant(
    l: &mut Lower<'_>,
    p: &Property,
    at: (Name, u32),
    (ty, variants): (&Ty, &[(Name, Vec<usize>)]),
    tape: Local,
) -> Vec<Operand> {
    let number = l.b.define_op(
        Repr::Scalar,
        Rvalue::Runtime(Runtime::PropWord, vec![Operand::Local(tape)]),
    );
    let result = l.temps(ty);
    let (join, none) = (l.b.new_block(), l.b.new_block());
    let blocks: Vec<_> = variants.iter().map(|_| l.b.new_block()).collect();
    l.b.terminate(Terminator::Switch {
        value: number,
        cases: (0..).zip(blocks.iter().copied()).collect(),
        otherwise: none,
    });
    for (v, (block, (_, payload))) in blocks.into_iter().zip(variants).enumerate() {
        l.b.switch_to(block);
        let values = payload.iter().map(|&s| decode(l, p, at, s, tape)).collect();
        let words = l.build(ty, v, values);
        for (&t, w) in result.iter().zip(words) {
            l.b.assign(t, Rvalue::Use(w));
        }
        l.b.goto(join);
    }
    l.b.switch_to(none);
    l.b.terminate(Terminator::Unreachable);
    l.b.switch_to(join);
    operands(&result)
}

/// Lowers a loop that runs `body` as many times as the next word of the tape says.
fn repeat(l: &mut Lower<'_>, tape: Local, mut body: impl FnMut(&mut Lower<'_>)) -> Operand {
    let n = l.b.define_op(
        Repr::Scalar,
        Rvalue::Runtime(Runtime::PropWord, vec![Operand::Local(tape)]),
    );
    let i = l.b.temp(Repr::Scalar);
    l.b.assign(i, Rvalue::Use(Operand::word(0)));
    let (head, again, done) = (l.b.new_block(), l.b.new_block(), l.b.new_block());
    l.b.goto(head);
    l.b.switch_to(head);
    let more = l.b.define_op(
        Repr::Scalar,
        Rvalue::Prim(
            Prim::Lt(NumKind::I64),
            vec![Operand::Local(i), n.clone()],
            Operand::word(0),
        ),
    );
    l.b.branch(more, again, done);
    l.b.switch_to(again);
    body(l);
    let step = Rvalue::Prim(
        Prim::AddWrap(NumKind::I64),
        vec![Operand::Local(i), Operand::word(1)],
        Operand::word(0),
    );
    l.b.assign(i, step);
    l.b.goto(head);
    l.b.switch_to(done);
    n
}

/// A list: its length, then its elements.
fn list(l: &mut Lower<'_>, p: &Property, at: (Name, u32), elem: usize, tape: Local) -> Operand {
    let ty = p.types[elem].clone();
    let shape = l.witness(&ty);
    let list = l.b.define(
        Repr::Heap,
        Rvalue::Runtime(Runtime::ListNew, vec![Operand::word(0), shape]),
    );
    repeat(l, tape, |l| {
        let words = decode(l, p, at, elem, tape);
        l.push_fresh(list, words, &ty);
    });
    Operand::Local(list)
}

/// A map: its length, then its entries, each a key then a value, inserted in order.
fn map(
    l: &mut Lower<'_>,
    p: &Property,
    at: (Name, u32),
    (key, value): (usize, usize),
    tape: Local,
) -> Operand {
    let (kty, vty) = (p.types[key].clone(), p.types[value].clone());
    let shapes = vec![l.witness(&kty), l.witness(&vty)];
    let built = l.b.temp(Repr::Heap);
    l.b.assign(built, Rvalue::Runtime(Runtime::PropMap, shapes));
    l.b.make_slots(&[built]);
    repeat(l, tape, |l| {
        let entry = (decode(l, p, at, key, tape), decode(l, p, at, value, tape));
        let k = l.map_word(entry.0, &kty);
        let v = l.map_word(entry.1, &vty);
        let (eq, hash) = l.key_dicts(&kty);
        let slot = l.b.define_op(Repr::Scalar, Rvalue::SlotOf(built));
        let args = vec![Operand::Local(tape), Operand::word(0), eq, hash, slot, k, v];
        l.b.emit(Stmt::Effect(Runtime::PropStore, args));
    });
    l.b.define_op(Repr::Heap, Rvalue::Use(Operand::Local(built)))
}
