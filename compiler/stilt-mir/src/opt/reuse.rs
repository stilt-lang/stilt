//! Repeated operations: a primitive operation on the same operands as one before it in the same
//! block, none of them changed since, gives the same result, so it copies that result instead,
//! and its check, which the first passed, goes with it. `(i + j) * (i + j + 1)` adds `i + j`
//! once. Primitive operations read only their operands, so a store between the two leaves the
//! result as it was; a local that lives in memory, which a pointer can change, takes no part.

use crate::mir::{Block, Function, Local, Operand, Prim, Rvalue, Stmt};

/// An operation computed earlier in the block, and the local that holds its result.
struct Computed {
    op: Prim,
    args: Vec<Operand>,
    into: Local,
}

/// Replaces each repeated operation of `f` by a copy of the first's result.
pub(crate) fn reuse(f: &mut Function) {
    let slot: Vec<bool> = f.locals.iter().map(|d| d.slot).collect();
    for block in &mut f.blocks {
        reuse_in(block, &slot);
    }
}

fn reuse_in(block: &mut Block, slot: &[bool]) {
    let in_memory = |o: &Operand| o.local().is_some_and(|l| slot[l.0 as usize]);
    let mut computed: Vec<Computed> = Vec::new();
    // Each local that copies another, which stands for it while neither changes.
    let mut copies: Vec<(Local, Local)> = Vec::new();
    for s in &mut block.stmts {
        let Stmt::Assign(d, r) = s else { continue };
        let d = *d;
        let args_of = |args: &[Operand]| -> Vec<Operand> {
            args.iter().map(|a| canonical(a, &copies)).collect()
        };
        let earlier = match &*r {
            Rvalue::Prim(op, args, _) => {
                let args = args_of(args);
                computed
                    .iter()
                    .find(|c| c.op == *op && c.args == args && c.into != d)
                    .map(|c| c.into)
            }
            _ => None,
        };
        let recorded = match &*r {
            Rvalue::Prim(op, args, _) if !args.iter().any(in_memory) && !slot[d.0 as usize] => {
                Some(Computed {
                    op: *op,
                    args: args_of(args),
                    into: d,
                })
            }
            _ => None,
        };
        forget(d, &mut computed, &mut copies);
        if let Some(l) = earlier {
            *r = Rvalue::Use(Operand::Local(l));
        }
        if let Rvalue::Use(o @ Operand::Local(s)) = &*r
            && !slot[s.0 as usize]
            && !slot[d.0 as usize]
            && let Operand::Local(source) = canonical(o, &copies)
        {
            copies.push((d, source));
        }
        if earlier.is_none()
            && let Some(c) = recorded.filter(|c| !c.args.contains(&Operand::Local(d)))
        {
            computed.push(c);
        }
    }
}

/// The operand that `o` stands for: the local it copies, if any.
fn canonical(o: &Operand, copies: &[(Local, Local)]) -> Operand {
    match o {
        Operand::Local(l) => copies
            .iter()
            .find(|(c, _)| c == l)
            .map_or(o.clone(), |(_, s)| Operand::Local(*s)),
        Operand::Const(_) => o.clone(),
    }
}

/// Forgets what depends on the value of `d`, which is given a new one.
fn forget(d: Local, computed: &mut Vec<Computed>, copies: &mut Vec<(Local, Local)>) {
    computed.retain(|c| c.into != d && !c.args.contains(&Operand::Local(d)));
    copies.retain(|(c, s)| *c != d && *s != d);
}
