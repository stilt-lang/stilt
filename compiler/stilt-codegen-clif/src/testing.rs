//! What the back end's tests share: functions written in MIR by hand, the Cranelift IR they
//! translate to, and what debuggers get of them.

use std::sync::Arc;

use cranelift_codegen::ir::Function as ClifFunction;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::Module;
use stilt_mir::FnRef;
use stilt_mir::mir::{
    Block, Function, Local, LocalDecl, NumKind, Operand, Param, ParamMode, Prim, Repr, Rvalue,
    Shown, ShownKind, Stmt, Terminator,
};

use crate::debug::Facts;
use crate::module::signature;
use crate::target::Target;
use crate::translate::Translator;

/// The location every operation of a test's function reports.
pub(crate) const LOC: Operand = Operand::word(1 << 20 | 1);

/// The bits of `1.5`.
pub(crate) const ONE_AND_A_HALF: u64 = 0x3ff8_0000_0000_0000;

/// A local of a scalar.
pub(crate) fn scalar() -> LocalDecl {
    LocalDecl {
        repr: Repr::Scalar,
        slot: false,
        grouped: false,
        borrowed: false,
        var: false,
        name: None,
        shown: None,
    }
}

/// A local of a heap word.
pub(crate) fn heap() -> LocalDecl {
    LocalDecl {
        repr: Repr::Heap,
        ..scalar()
    }
}

/// A local of an `f64` the source names `name`.
pub(crate) fn named_f64(name: &str) -> LocalDecl {
    LocalDecl {
        name: Some(name.into()),
        shown: Some(Shown {
            name: "f64".into(),
            kind: ShownKind::Float(64),
            by_ref: false,
            variants: Arc::from(Vec::new()),
            elements: None,
        }),
        ..scalar()
    }
}

/// The entry, whose first parameter is its location and whose others are those of `params`,
/// with the locals `locals` after them, and these blocks.
pub(crate) fn function(params: &[LocalDecl], locals: &[LocalDecl], blocks: Vec<Block>) -> Function {
    let all: Vec<LocalDecl> = std::iter::once(scalar())
        .chain(params.iter().cloned())
        .chain(locals.iter().cloned())
        .collect();
    Function {
        name: FnRef::Main,
        params: (0..=params.len())
            .map(|i| Param {
                local: local(i),
                mode: ParamMode::Borrowed,
            })
            .collect(),
        hidden: 1,
        results: 1,
        locals: all,
        blocks,
        broken: false,
    }
}

pub(crate) fn local(i: usize) -> Local {
    Local(u32::try_from(i).expect("a few locals"))
}

pub(crate) fn op(i: usize) -> Operand {
    Operand::Local(local(i))
}

/// `dest = p(args)` at [`LOC`].
pub(crate) fn prim(dest: usize, p: Prim, args: &[Operand]) -> Stmt {
    Stmt::Assign(local(dest), Rvalue::Prim(p, args.to_vec(), LOC))
}

/// A block of `stmts` that ends in `term`.
pub(crate) fn block(stmts: Vec<Stmt>, term: Terminator) -> Block {
    Block { stmts, term }
}

/// A loop that squares `_2` and adds 1.5 to it `_1` times, counting in `_3`, then returns it:
/// `_2` and the temporaries `_5` and `_6` hold `f64`s, and `_3`, `_4` and `_7` integers.
pub(crate) fn float_loop() -> Function {
    let goto = |b| Terminator::Goto(stilt_mir::mir::BlockId(b));
    let blocks = vec![
        block(
            vec![
                Stmt::Assign(local(2), Rvalue::Use(Operand::word(0))),
                Stmt::Assign(local(3), Rvalue::Use(Operand::word(0))),
            ],
            goto(1),
        ),
        block(
            vec![prim(4, Prim::Lt(NumKind::I64), &[op(3), op(1)])],
            Terminator::Branch {
                cond: op(4),
                then: stilt_mir::mir::BlockId(2),
                otherwise: stilt_mir::mir::BlockId(3),
            },
        ),
        block(
            vec![
                prim(5, Prim::Mul(NumKind::F64), &[op(2), op(2)]),
                prim(
                    6,
                    Prim::Add(NumKind::F64),
                    &[op(5), Operand::word(ONE_AND_A_HALF)],
                ),
                Stmt::Assign(local(2), Rvalue::Use(op(6))),
                prim(7, Prim::Add(NumKind::I64), &[op(3), Operand::word(1)]),
                Stmt::Assign(local(3), Rvalue::Use(op(7))),
            ],
            goto(1),
        ),
        block(Vec::new(), Terminator::Return(vec![op(2)])),
    ];
    function(&[scalar()], &vec![scalar(); 6], blocks)
}

/// The Cranelift IR that `f` translates to, before Cranelift optimizes it.
pub(crate) fn clif(f: &Function) -> String {
    let (mut module, mut reg) = crate::object::module(Target::Aarch64Macos).expect("a module");
    reg.declare(&mut module, f).expect("declared");
    let mut func = ClifFunction::new();
    func.signature = signature(&module, f.params.len(), f.results as usize);
    let config = module.isa().frontend_config();
    let mut fbc = FunctionBuilderContext::new();
    let fb = FunctionBuilder::new(&mut func, &mut fbc);
    let mut t = Translator::new(fb, &mut module, &mut reg, f);
    t.run().expect("translated");
    t.finish(config);
    func.display().to_string()
}

/// What debuggers get of `f` compiled for `target`.
pub(crate) fn facts(f: &Function, target: Target) -> Facts {
    let (mut module, mut reg) = crate::object::module(target).expect("a module");
    let id = reg.declare(&mut module, f).expect("declared");
    let mut fbc = FunctionBuilderContext::new();
    let t = crate::compile::translate(&mut module, &mut reg, &mut fbc, f, id).expect("translated");
    t.facts(module.isa()).expect("compiled")
}

/// A block of Cranelift IR as it prints: its header, such as `block3 cold:`, and its
/// instructions.
pub(crate) struct ClifBlock<'a> {
    pub(crate) header: &'a str,
    pub(crate) insts: Vec<&'a str>,
}

impl ClifBlock<'_> {
    pub(crate) fn cold(&self) -> bool {
        self.header.ends_with(" cold:")
    }

    pub(crate) fn has(&self, opcode: &str) -> bool {
        self.insts.iter().any(|i| opcode_of(i) == opcode)
    }

    /// The opcode of its last instruction.
    pub(crate) fn ends_in(&self) -> &str {
        self.insts.last().map_or("", |i| opcode_of(i))
    }
}

/// The opcode of an instruction as it prints, such as `fadd` of `v5 = fadd.f64 v3, v4`, which
/// may end in a comment after `;`.
fn opcode_of(inst: &str) -> &str {
    let inst = inst.split(';').next().unwrap_or("");
    let rhs = inst.split_once(" = ").map_or(inst, |(_, r)| r);
    let word = rhs.split_whitespace().next().unwrap_or("");
    word.split('.').next().unwrap_or("")
}

/// The blocks of a function's Cranelift IR.
pub(crate) fn clif_blocks(clif: &str) -> Vec<ClifBlock<'_>> {
    let mut blocks: Vec<ClifBlock<'_>> = Vec::new();
    for line in clif.lines().map(str::trim) {
        if line.starts_with("block") {
            blocks.push(ClifBlock {
                header: line,
                insts: Vec::new(),
            });
        } else if let Some(b) = blocks.last_mut()
            && !line.is_empty()
            && line != "}"
        {
            b.insts.push(line);
        }
    }
    blocks
}
