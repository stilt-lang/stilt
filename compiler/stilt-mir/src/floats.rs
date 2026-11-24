//! Which locals hold `f64`s, which both back ends keep in float registers or as C `double`s
//! (goal debug-speed). The MIR gives a local a representation but no type, so the type is
//! inferred: the result of an `f64` operation and its operands hold `f64`s, as does a local the
//! source names with that type, and a copy joins two locals into one type. A local that holds
//! a pointer, as an `inout` parameter does, or a heap word, holds no `f64`. Each back end
//! converts a value by keeping its bits where it meets a word, so the inference decides where
//! values live, never what a program computes.

use crate::mir::{
    Function, Local, NumKind, Operand, ParamMode, Prim, Repr, Rvalue, ShownKind, Stmt,
};

/// The kind of an operation's operands, if they are floats.
#[must_use]
pub fn float_operands(p: Prim) -> Option<NumKind> {
    let (Prim::Add(kind)
    | Prim::Sub(kind)
    | Prim::Mul(kind)
    | Prim::Div(kind)
    | Prim::Rem(kind)
    | Prim::Neg(kind)
    | Prim::Eq(kind)
    | Prim::Lt(kind)
    | Prim::Le(kind)
    | Prim::Compare(kind)
    | Prim::ToFloat(kind, _)
    | Prim::FloatFits(kind, _)
    | Prim::FloatToInt(kind, _)
    | Prim::Abs(kind)
    | Prim::Min(kind)
    | Prim::Max(kind)
    | Prim::Sqrt(kind)
    | Prim::Floor(kind)
    | Prim::Ceil(kind)
    | Prim::Trunc(kind)
    | Prim::Round(kind)
    | Prim::IsNan(kind)) = p
    else {
        return None;
    };
    kind.is_float().then_some(kind)
}

/// The kind of an operation's result, if it is a float.
#[must_use]
pub fn float_result(p: Prim) -> Option<NumKind> {
    let (Prim::Add(kind)
    | Prim::Sub(kind)
    | Prim::Mul(kind)
    | Prim::Div(kind)
    | Prim::Rem(kind)
    | Prim::Neg(kind)
    | Prim::ToFloat(_, kind)
    | Prim::Abs(kind)
    | Prim::Min(kind)
    | Prim::Max(kind)
    | Prim::Sqrt(kind)
    | Prim::Floor(kind)
    | Prim::Ceil(kind)
    | Prim::Trunc(kind)
    | Prim::Round(kind)) = p
    else {
        return None;
    };
    kind.is_float().then_some(kind)
}

/// Whether each local of `f` holds an `f64`.
pub fn f64_locals(f: &Function) -> Vec<bool> {
    let mut classes = Classes::of(f);
    let mut holds = vec![false; f.locals.len()];
    for stmt in f.blocks.iter().flat_map(|b| &b.stmts) {
        if let Stmt::Assign(dest, Rvalue::Prim(op, args, _)) = stmt {
            holds[index(*dest)] |= float_result(*op) == Some(NumKind::F64);
            if float_operands(*op) == Some(NumKind::F64) {
                for arg in args.iter().filter_map(Operand::local) {
                    holds[index(arg)] = true;
                }
            }
        }
    }
    for (held, decl) in holds.iter_mut().zip(&f.locals) {
        *held |= decl
            .shown
            .as_ref()
            .is_some_and(|shown| shown.kind == ShownKind::Float(64) && !shown.by_ref);
    }
    let mut class_holds = vec![false; holds.len()];
    for (local, _) in holds.iter().enumerate().filter(|(_, held)| **held) {
        class_holds[classes.root(local)] = true;
    }
    let pointers: Vec<usize> = f
        .params
        .iter()
        .filter(|param| param.mode == ParamMode::Ref)
        .map(|param| index(param.local))
        .collect();
    (0..holds.len())
        .map(|local| {
            class_holds[classes.root(local)]
                && f.locals[local].repr == Repr::Scalar
                && !pointers.contains(&local)
        })
        .collect()
}

fn index(local: Local) -> usize {
    local.0 as usize
}

/// The classes of locals that copies join, which hold values of one type.
struct Classes(Vec<usize>);

impl Classes {
    /// The classes of `f`'s locals.
    fn of(f: &Function) -> Self {
        let mut classes = Self((0..f.locals.len()).collect());
        for stmt in f.blocks.iter().flat_map(|b| &b.stmts) {
            if let Stmt::Assign(dest, Rvalue::Use(Operand::Local(source))) = stmt {
                let (a, b) = (classes.root(index(*dest)), classes.root(index(*source)));
                classes.0[a] = b;
            }
        }
        classes
    }

    /// The representative of the class of `local`.
    fn root(&mut self, local: usize) -> usize {
        let mut root = local;
        while self.0[root] != root {
            root = self.0[root];
        }
        let mut next = local;
        while self.0[next] != root {
            next = std::mem::replace(&mut self.0[next], root);
        }
        root
    }
}
