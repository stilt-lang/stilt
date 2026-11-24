//! What a release that keeps memory knows of the object it releases, and what an object built in
//! that memory finds there already, so that the release tests only the count, and the object is
//! built by writing what changes (Perceus's reuse specialization).
//!
//! A value whose fields the code read as those of a variant of a declared type, on every path to
//! a release, is an object of that variant there ([`Variant`]): a pointer to a data object of the
//! program's, of the variant's tag and, when the heapness of its words is fixed, of its layout.
//! An object built in its memory, when the release kept it, finds the header it needs when it is
//! of the same variant, and in each word the value the old object held there, which a field read
//! from the old object and put back in the same place has.

use stilt_mir::mir::{
    Function, Heapness, Kept, Local, Operand, Rvalue, Stmt, Variant, data_layout,
};

use super::Site;

/// What every path to a statement knows of a local's object, from the fields it read.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Fact {
    /// No path reaches it yet.
    Unreached,
    /// Each path read it as this variant.
    Is(Variant),
    /// Some path didn't, or read it as another.
    Unknown,
}

impl Fact {
    fn meet(self, other: Fact) -> Fact {
        match (self, other) {
            (Fact::Unreached, x) | (x, Fact::Unreached) => x,
            (Fact::Is(a), Fact::Is(b)) if a == b => self,
            _ => Fact::Unknown,
        }
    }
}

/// What is known of `x` after the statement `s`, from what was known before it: a read of a field
/// of it tells its variant, and an assignment to it a new value, of which nothing is known.
fn step(known: Fact, s: &Stmt, x: Local) -> Fact {
    match s {
        Stmt::Assign(
            _,
            Rvalue::Field {
                base: Operand::Local(b),
                variant: Some(v),
                ..
            },
        ) if *b == x => Fact::Is(*v),
        Stmt::Assign(d, _) if *d == x => Fact::Unknown,
        _ => known,
    }
}

/// The variant that every path from the function's entry to `site` read `x` as, if one did.
pub(super) fn variant_at(f: &Function, x: Local, site: Site) -> Option<Variant> {
    let mut ins = vec![Fact::Unreached; f.blocks.len()];
    ins[0] = Fact::Unknown;
    let after = |block: usize, fact: Fact| {
        (f.blocks[block].stmts.iter()).fold(fact, |known, stmt| step(known, stmt, x))
    };
    let mut changed = true;
    while changed {
        changed = false;
        for block in 0..f.blocks.len() {
            if ins[block] == Fact::Unreached {
                continue;
            }
            let leaving = after(block, ins[block]);
            for next in f.blocks[block].term.successors() {
                let next = next.0 as usize;
                let met = ins[next].meet(leaving);
                if met != ins[next] {
                    ins[next] = met;
                    changed = true;
                }
            }
        }
    }
    let (block, at) = site;
    let known =
        (f.blocks[block].stmts[..at].iter()).fold(ins[block], |known, stmt| step(known, stmt, x));
    match known {
        Fact::Is(variant) => Some(variant),
        _ => None,
    }
}

/// The object and the word that each local was read from, through copies: a local that one
/// statement defines as a copy of another has the other's.
pub(super) fn origins(f: &Function, fields: &[Option<(Local, u32)>]) -> Vec<Option<(Local, u32)>> {
    let defs = stilt_mir::opt::definitions(f);
    let mut copied: Vec<Option<Local>> = vec![None; f.locals.len()];
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        if let Stmt::Assign(to, Rvalue::Use(Operand::Local(from))) = s
            && defs[to.0 as usize] == 1
            && defs[from.0 as usize] == 1
        {
            copied[to.0 as usize] = Some(*from);
        }
    }
    (0..f.locals.len())
        .map(|l| {
            let mut at = l;
            // A chain of copies is at most as long as the function has locals.
            for _ in 0..f.locals.len() {
                // The tokens the pass added come after the locals it read fields of.
                if let Some(origin) = fields.get(at).copied().flatten() {
                    return Some(origin);
                }
                at = copied[at]?.0 as usize;
            }
            None
        })
        .collect()
}

/// The word that tells a release what it knows of the object it releases, the last operand of
/// [`stilt_mir::mir::Runtime::Reclaim`]: 0 when nothing, or the variant
/// ([`stilt_mir::mir::known_object`]).
pub(super) fn known_word(v: Option<Variant>) -> u64 {
    stilt_mir::mir::known_object(v)
}

/// What memory kept from the object of `x`, known to be `variant`, holds already of a data
/// object of tag `tag` and fields `fields` built there; `fields_of` gives the object and the
/// word each local was read from.
pub(super) fn kept(
    variant: Option<Variant>,
    x: Local,
    (tag, fields): (u16, &[(Operand, Heapness)]),
    fields_of: &[Option<(Local, u32)>],
) -> Kept {
    let mut at = 0usize;
    let mut mask = 0u64;
    let mut words = 0u64;
    let mut fixed = true;
    for (o, h) in fields {
        match h {
            Heapness::Static(heap) => {
                if *heap && at < 64 {
                    mask |= 1 << at;
                }
            }
            Heapness::Witness(_) | Heapness::Array(_) => fixed = false,
        }
        if let (Operand::Local(v), Heapness::Static(_) | Heapness::Witness(_)) = (o, h)
            && fields_of[v.0 as usize] == Some((x, u32::try_from(at).unwrap_or(u32::MAX)))
            && at < 64
        {
            words |= 1 << at;
        }
        at += h.words();
    }
    let layout = (fixed && at < 64).then(|| data_layout(at, mask));
    let header = variant.is_some_and(|v| v.tag == tag && v.layout.is_some() && v.layout == layout);
    Kept { header, words }
}
