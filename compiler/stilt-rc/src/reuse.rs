//! Building in place, as Perceus reuses memory (values.consumed-parameters; Compiler architecture,
//! "Reference counting"). Once the counting is inserted, a release of a local whose value is a
//! data object of `n` words, which the code reads field by field, as a `match` takes a variant
//! apart, keeps the object's memory when that was its last reference ([`Runtime::Reclaim`]), and
//! the first data object of `n` words that the code builds on each path after it is built there
//! ([`Rvalue::AllocIn`]). Memory that no object takes goes back before the function returns or
//! raises ([`Runtime::Discard`]).
//!
//! Whether memory is kept is the runtime's test of the object's count, made where the release
//! was, so nothing the program does changes: a value that something else still references is
//! released as before, and an object finds memory in the pool when none was kept. A box, and an
//! object that holds a function's code, as a closure does, are built as before, so that what the
//! release build knows of their contents stays known.

use std::collections::HashMap;

use stilt_mir::mir::{
    BOX, Block, BlockId, Const, Function, Heapness, Local, LocalDecl, Operand, Repr, Runtime,
    Rvalue, Stmt, Terminator, Variant,
};

/// A statement's place: its block and its index there.
type Site = (usize, usize);

/// A release whose memory an object can take: where it is, what it releases, and its words.
struct Release {
    site: Site,
    local: Local,
    words: usize,
}

/// Builds each new data object of a function's counted MIR, where it can, in the memory of a
/// value that a release before it lets go of.
pub(crate) fn reuse(f: &mut Function) {
    let fields = sink::fields_of(f);
    sink::sink_drops(f, &fields);
    sink::sink_dups(f, &fields);
    let words = object_words(f);
    let releases: Vec<Release> = sites(f)
        .filter_map(|(site, s)| match s {
            Stmt::Drop(l) => words[l.0 as usize].map(|words| Release {
                site,
                local: *l,
                words,
            }),
            _ => None,
        })
        .collect();
    if releases.is_empty() {
        return;
    }
    let mut taker: HashMap<Site, usize> = HashMap::new();
    for (r, release) in releases.iter().enumerate() {
        for site in first_builds(f, release, &taker) {
            taker.insert(site, r);
        }
    }
    let mut used: Vec<usize> = taker.values().copied().collect();
    used.sort_unstable();
    used.dedup();
    if used.is_empty() {
        return;
    }
    let tokens: Vec<(usize, Local)> = used.iter().map(|&r| (r, token(f))).collect();
    let known: Vec<Option<Variant>> = releases
        .iter()
        .map(|r| known::variant_at(f, r.local, r.site))
        .collect();
    let origins = known::origins(f, &fields);
    rewrite(f, (&releases, &known), &tokens, &taker, &origins);
    sink::fuse(f, &fields);
}

/// The number of words of the data object each local holds, for a local of one heap word whose
/// fields the code reads, all as fields of an object of the same number of words.
fn object_words(f: &Function) -> Vec<Option<usize>> {
    let mut words: Vec<Option<Option<usize>>> = vec![None; f.locals.len()];
    for (_, s) in sites(f) {
        if let Stmt::Assign(
            _,
            Rvalue::Field {
                base: Operand::Local(l),
                len,
                ..
            },
        ) = s
            && f.locals[l.0 as usize].repr == Repr::Heap
        {
            let at = &mut words[l.0 as usize];
            let len = *len as usize;
            *at = Some(match *at {
                None => Some(len),
                Some(known) => known.filter(|&k| k == len),
            });
        }
    }
    words.into_iter().map(Option::flatten).collect()
}

/// Each statement of a function, with its place.
fn sites(f: &Function) -> impl Iterator<Item = (Site, &Stmt)> {
    f.blocks.iter().enumerate().flat_map(|(b, block)| {
        block
            .stmts
            .iter()
            .enumerate()
            .map(move |(i, s)| ((b, i), s))
    })
}

/// The words of the data object that a statement builds, if it builds one whose memory can be
/// one a release kept: no box, and no object that holds a function's code.
fn built_words(s: &Stmt) -> Option<usize> {
    let Stmt::Assign(_, Rvalue::Alloc(tag, fields)) = s else {
        return None;
    };
    let code = matches!(fields.first(), Some((Operand::Const(Const::Code(_)), _)));
    (*tag != BOX && !code).then(|| fields.iter().map(|(_, h)| heapness_words(h)).sum())
}

fn heapness_words(h: &Heapness) -> usize {
    match h {
        Heapness::Array(e) => e.words(),
        Heapness::Static(_) | Heapness::Witness(_) => 1,
    }
}

/// The objects of the release's size that the code builds first on each path from it, of those
/// no earlier release's memory goes to, through any number of blocks, but not past the release
/// again.
fn first_builds(f: &Function, release: &Release, taken: &HashMap<Site, usize>) -> Vec<Site> {
    let (start, at) = release.site;
    let mut found = Vec::new();
    let mut seen = vec![false; f.blocks.len()];
    let mut todo: Vec<(usize, usize)> = vec![(start, at + 1)];
    while let Some((b, from)) = todo.pop() {
        let stmts = &f.blocks[b].stmts;
        let mut i = from;
        let mut ended = false;
        while i < stmts.len() {
            if (b, i) == release.site {
                ended = true;
                break;
            }
            if built_words(&stmts[i]) == Some(release.words) && !taken.contains_key(&(b, i)) {
                found.push((b, i));
                ended = true;
                break;
            }
            i += 1;
        }
        if ended {
            continue;
        }
        for s in f.blocks[b].term.successors() {
            let s = s.0 as usize;
            if !seen[s] {
                seen[s] = true;
                todo.push((s, 0));
            }
        }
    }
    found
}

/// A new local of the function, a scalar that holds kept memory or 0.
fn token(f: &mut Function) -> Local {
    let l = Local(u32::try_from(f.locals.len()).expect("under 4G locals"));
    f.locals.push(LocalDecl {
        repr: Repr::Scalar,
        slot: false,
        grouped: false,
        borrowed: false,
        var: false,
        name: None,
        shown: None,
    });
    l
}

/// Rewrites the releases that keep memory, the objects built in it, and the exits that give
/// back what nothing took, with each token 0 from the function's entry.
fn rewrite(
    f: &mut Function,
    (releases, known): (&[Release], &[Option<Variant>]),
    tokens: &[(usize, Local)],
    taker: &HashMap<Site, usize>,
    fields_of: &[Option<(Local, u32)>],
) {
    let mut edits: Vec<(Site, Vec<Stmt>)> = Vec::new();
    for &(r, t) in tokens {
        let release = &releases[r];
        let mut with = Vec::new();
        if looping(f, release.site.0) {
            with.push(Stmt::Effect(Runtime::Discard, vec![Operand::Local(t)]));
        }
        let words = u64::try_from(release.words).expect("under 2^64 words");
        let args = vec![
            Operand::Local(release.local),
            Operand::word(words),
            Operand::word(0),
            Operand::word(known::known_word(known[r])),
        ];
        with.push(Stmt::Assign(t, Rvalue::Runtime(Runtime::Reclaim, args)));
        edits.push((release.site, with));
    }
    for (&site, r) in taker {
        let Some(&(_, t)) = tokens.iter().find(|(of, _)| of == r) else {
            continue;
        };
        let Stmt::Assign(d, Rvalue::Alloc(tag, fields)) = &f.blocks[site.0].stmts[site.1] else {
            continue;
        };
        let release = &releases[*r];
        let kept = known::kept(known[*r], release.local, (*tag, fields), fields_of);
        let built = Rvalue::AllocIn(Operand::Local(t), *tag, fields.clone(), kept);
        let spent = Stmt::Assign(t, Rvalue::Use(Operand::word(0)));
        edits.push((site, vec![Stmt::Assign(*d, built), spent]));
    }
    edits.sort_by_key(|edit| std::cmp::Reverse(edit.0));
    for ((b, i), with) in edits {
        f.blocks[b].stmts.splice(i..=i, with);
    }
    give_back(f, releases, tokens);
    let zeros = tokens
        .iter()
        .map(|&(_, t)| Stmt::Assign(t, Rvalue::Use(Operand::word(0))));
    let zeros: Vec<Stmt> = zeros.collect();
    entry(f).stmts.splice(0..0, zeros);
}

/// Gives back, before each return or raise that a token's release reaches, what it holds.
fn give_back(f: &mut Function, releases: &[Release], tokens: &[(usize, Local)]) {
    for &(r, t) in tokens {
        for b in reached(f, releases[r].site.0) {
            let block = &mut f.blocks[b];
            if matches!(block.term, Terminator::Return(_) | Terminator::Raise(_)) {
                let discard = Stmt::Effect(Runtime::Discard, vec![Operand::Local(t)]);
                block.stmts.push(discard);
            }
        }
    }
}

/// The blocks reachable from block `from`, itself among them.
fn reached(f: &Function, from: usize) -> Vec<usize> {
    let mut seen = vec![false; f.blocks.len()];
    seen[from] = true;
    let mut todo = vec![from];
    while let Some(b) = todo.pop() {
        for s in f.blocks[b].term.successors() {
            let s = s.0 as usize;
            if !seen[s] {
                seen[s] = true;
                todo.push(s);
            }
        }
    }
    (0..f.blocks.len()).filter(|&b| seen[b]).collect()
}

/// Whether block `b` is in a loop: whether a block it goes to reaches it.
fn looping(f: &Function, b: usize) -> bool {
    f.blocks[b]
        .term
        .successors()
        .iter()
        .any(|s| reached(f, s.0 as usize).contains(&b))
}

/// The block that starts the function, made one that no edge enters, so that what it does
/// first runs once: when an edge enters the first block, it moves to the end, and a new first
/// block goes to it.
fn entry(f: &mut Function) -> &mut Block {
    let entered = f
        .blocks
        .iter()
        .any(|b| b.term.successors().contains(&BlockId(0)));
    if entered {
        let moved = BlockId(u32::try_from(f.blocks.len()).expect("under 4G blocks"));
        for block in &mut f.blocks {
            crate::retarget_edge(&mut block.term, BlockId(0), moved);
        }
        let first = std::mem::replace(
            &mut f.blocks[0],
            Block {
                stmts: Vec::new(),
                term: Terminator::Goto(moved),
            },
        );
        f.blocks.push(first);
    }
    &mut f.blocks[0]
}

mod known;
mod sink;
#[cfg(test)]
mod tests;
