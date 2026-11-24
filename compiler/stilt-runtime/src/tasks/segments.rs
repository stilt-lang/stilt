//! The output of a run whose tasks run on threads, as a tree of segments
//! (tasks.same-output-under-every-handler): one per task, inserted in the segment of the code that
//! started it at the point of its `spawn`, so that the tree's order is the order of the sequential
//! run.
//!
//! A segment holds what its task wrote that can't go out yet, and the segments of the tasks it
//! started, in order. The *front* is the first segment in that order whose task hasn't ended:
//! what it writes goes out at once, and what a later one writes waits in its segment. Once the
//! front's task ends, what follows it goes out, up to the next segment whose task hasn't ended,
//! the new front. A read of standard input, a panic and an `exit` wait for their segment to be
//! the front, so they happen where the sequential run has them.
//!
//! A scope cuts its function's segment after the task that raised first in that order
//! (tasks.scope-failure): what follows the task is dropped, the segments there are *cancelled*, out
//! of the tree, and nothing written to them, or to the function's segment from then on, goes out.

use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, Ordering};

use crate::io::{self, Kind};

/// A segment, by its index in the tree.
pub(crate) type SegId = usize;

/// The turn of a segment's thread at a point it can't take back: wait, go on, or stop for good.
pub(crate) const WAIT: u8 = 0;
pub(crate) const FRONT: u8 = 1;
pub(crate) const CLOSED: u8 = 2;

#[derive(Debug)]
enum Item {
    Out(Kind, Vec<u8>),
    Child(SegId),
}

/// What became of a segment: nothing, or what its thread writes from now on is dropped and
/// its thread stops at a point it can't take back, since it was cut, or cancelled, and so is
/// out of the tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Fate {
    Open,
    Cut,
    Cancelled,
}

/// What a cut or a cancel of a segment tells whoever waits for its task, once (`super::Waited`).
struct Detach(Box<dyn FnOnce() + Send>);

impl std::fmt::Debug for Detach {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Detach")
    }
}

#[derive(Debug)]
struct Seg {
    parent: Option<SegId>,
    items: VecDeque<Item>,
    /// Whether its task's code has ended.
    ended: bool,
    /// Whether it was cut or cancelled.
    fate: Fate,
    /// Whether a `when` after it waits until it ends (`super::order`).
    blocks: bool,
    /// Its turn, which the fault handler reads without the tree's lock.
    turn: Arc<AtomicU8>,
    /// What its cut or its cancel tells whoever waits for its task.
    detach: Option<Detach>,
}

/// The segments of a run, with the values its `when`s hold.
#[derive(Debug)]
pub(crate) struct Tree {
    segs: Vec<Option<Seg>>,
    free: Vec<SegId>,
    front: SegId,
    /// The handles that the running `when`s of each thread hold (`super::order`).
    pub(crate) held: Vec<(u64, std::thread::ThreadId)>,
}

impl Tree {
    /// A tree of one segment, the root's, at the front.
    pub(crate) fn new() -> (Self, SegId) {
        let mut tree = Self {
            segs: Vec::new(),
            free: Vec::new(),
            front: 0,
            held: Vec::new(),
        };
        let root = tree.alloc(None, false);
        tree.set_front(root);
        (tree, root)
    }

    fn alloc(&mut self, parent: Option<SegId>, blocks: bool) -> SegId {
        let seg = Seg {
            parent,
            items: VecDeque::new(),
            ended: false,
            fate: Fate::Open,
            blocks,
            turn: Arc::new(AtomicU8::new(WAIT)),
            detach: None,
        };
        if let Some(id) = self.free.pop() {
            self.segs[id] = Some(seg);
            return id;
        }
        self.segs.push(Some(seg));
        self.segs.len() - 1
    }

    fn seg(&self, id: SegId) -> &Seg {
        self.segs[id].as_ref().expect("a live segment")
    }

    fn seg_mut(&mut self, id: SegId) -> &mut Seg {
        self.segs[id].as_mut().expect("a live segment")
    }

    fn set_front(&mut self, id: SegId) {
        let old = self.front;
        if old != id
            && let Some(seg) = self.segs[old].as_ref()
            && seg.fate == Fate::Open
        {
            seg.turn.store(WAIT, Ordering::Release);
        }
        self.front = id;
        let seg = self.seg(id);
        let turn = if seg.fate == Fate::Open {
            FRONT
        } else {
            CLOSED
        };
        seg.turn.store(turn, Ordering::Release);
    }

    /// The turn of segment `id`.
    pub(crate) fn turn(&self, id: SegId) -> u8 {
        self.seg(id).turn.load(Ordering::Acquire)
    }

    /// The flag the fault handler reads for segment `id`'s turn.
    pub(crate) fn turn_flag(&self, id: SegId) -> Arc<AtomicU8> {
        Arc::clone(&self.seg(id).turn)
    }

    /// Whether what segment `id` writes is dropped.
    pub(crate) fn closed(&self, id: SegId) -> bool {
        self.seg(id).fate != Fate::Open
    }

    /// A write of `kind` by segment `id`'s thread: out now at the front, kept otherwise.
    pub(crate) fn write(&mut self, id: SegId, kind: Kind, bytes: &[u8]) {
        let front = self.front;
        let seg = self.seg_mut(id);
        if seg.fate != Fate::Open {
            return;
        }
        if id == front {
            io::emit(kind, bytes);
        } else {
            seg.items.push_back(Item::Out(kind, bytes.to_vec()));
        }
    }

    /// The segment of a task that segment `id`'s thread starts now, after what it wrote, which
    /// blocks the `when`s after it if `blocks`. A segment that a cut or a cancel closed, since
    /// the check that its code is reached, starts a cancelled one, out of the tree: the
    /// sequential run never starts that task (tasks.scope-failure).
    pub(crate) fn spawn(&mut self, id: SegId, blocks: bool) -> SegId {
        let child = self.alloc(Some(id), blocks);
        if self.seg(id).fate != Fate::Open {
            let seg = self.seg_mut(child);
            seg.fate = Fate::Cancelled;
            seg.parent = None;
            seg.turn.store(CLOSED, Ordering::Release);
            return child;
        }
        self.seg_mut(id).items.push_back(Item::Child(child));
        self.settle();
        child
    }

    /// Has `detach` run once segment `id` is cut or cancelled, at once if it already is. It runs
    /// with the tree locked.
    pub(crate) fn on_close(&mut self, id: SegId, detach: Box<dyn FnOnce() + Send>) {
        let seg = self.seg_mut(id);
        if seg.fate == Fate::Open {
            seg.detach = Some(Detach(detach));
        } else {
            detach();
        }
    }

    /// Ends segment `id`, whose task's code ended: once what it holds is out, what follows it
    /// goes out.
    pub(crate) fn end(&mut self, id: SegId) {
        let seg = self.seg_mut(id);
        seg.ended = true;
        if seg.fate == Fate::Cancelled {
            self.release(id);
        } else {
            self.settle();
        }
    }

    fn release(&mut self, id: SegId) {
        self.segs[id] = None;
        self.free.push(id);
    }

    /// Writes out what the front holds, moving the front on past every segment that holds
    /// nothing more and has ended, or was cut, since nothing its code writes from then on
    /// appears: a cut one then leaves the tree, as a cancelled one does, until its code ends.
    fn settle(&mut self) {
        loop {
            let front = self.front;
            let seg = self.seg_mut(front);
            match seg.items.pop_front() {
                Some(Item::Out(kind, bytes)) => io::emit(kind, &bytes),
                Some(Item::Child(child)) => {
                    seg.items.push_front(Item::Child(child));
                    self.set_front(child);
                }
                None => match seg.parent {
                    Some(parent) if seg.ended || seg.fate == Fate::Cut => {
                        if seg.ended {
                            self.release(front);
                        } else {
                            seg.fate = Fate::Cancelled;
                            seg.parent = None;
                        }
                        let first = self.seg_mut(parent).items.pop_front();
                        debug_assert!(matches!(first, Some(Item::Child(c)) if c == front));
                        self.set_front(parent);
                    }
                    _ => return,
                },
            }
        }
    }

    /// Cuts segment `f` after its child `at`, whose task raised first in the sequential order:
    /// what follows `at` in it is dropped, and so is what `f`'s thread writes from now on.
    pub(crate) fn cut(&mut self, f: SegId, at: SegId) {
        let seg = self.seg_mut(f);
        let Some(i) = seg
            .items
            .iter()
            .position(|item| matches!(item, Item::Child(c) if *c == at))
        else {
            return;
        };
        seg.fate = Fate::Cut;
        seg.turn.store(CLOSED, Ordering::Release);
        if let Some(Detach(detach)) = seg.detach.take() {
            detach();
        }
        let seg = self.seg_mut(f);
        let dropped: Vec<Item> = seg.items.drain(i + 1..).collect();
        for item in dropped {
            if let Item::Child(child) = item {
                self.cancel(child);
            }
        }
    }

    /// Cancels segment `id` and every segment in it: they leave the tree, and each is freed
    /// once its task's code ends.
    fn cancel(&mut self, id: SegId) {
        let mut pending = vec![id];
        while let Some(at) = pending.pop() {
            let seg = self.seg_mut(at);
            seg.fate = Fate::Cancelled;
            seg.parent = None;
            seg.turn.store(CLOSED, Ordering::Release);
            if let Some(Detach(detach)) = seg.detach.take() {
                detach();
            }
            let seg = self.seg_mut(at);
            for item in std::mem::take(&mut seg.items) {
                if let Item::Child(child) = item {
                    pending.push(child);
                }
            }
            if seg.ended {
                self.release(at);
            }
        }
    }

    /// Whether a segment before the point that segment `id`'s thread has reached blocks a
    /// `when` there: one in it, or before it in its parents, whose task hasn't ended and holds
    /// handles or may raise, or that holds such a segment.
    pub(crate) fn blocked(&self, id: SegId) -> bool {
        let mut pending: Vec<SegId> = self.children(id, None);
        let mut at = id;
        while let Some(parent) = self.seg(at).parent {
            pending.extend(self.children(parent, Some(at)));
            at = parent;
        }
        while let Some(child) = pending.pop() {
            let seg = self.seg(child);
            if seg.blocks && !seg.ended {
                return true;
            }
            pending.extend(self.children(child, None));
        }
        false
    }

    /// The children of segment `id`, those before `before` if it is given.
    fn children(&self, id: SegId, before: Option<SegId>) -> Vec<SegId> {
        self.seg(id)
            .items
            .iter()
            .map_while(|item| match item {
                Item::Child(c) if Some(*c) == before => None,
                Item::Child(c) => Some(Some(*c)),
                Item::Out(..) => Some(None),
            })
            .flatten()
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::{CLOSED, FRONT, Tree, WAIT};

    #[test]
    fn a_child_is_the_front_until_it_ends() {
        let (mut tree, root) = Tree::new();
        let child = tree.spawn(root, false);
        assert_eq!(tree.turn(child), FRONT);
        assert_eq!(tree.turn(root), WAIT);
        tree.end(child);
        assert_eq!(tree.turn(root), FRONT);
    }

    #[test]
    fn a_later_sibling_waits_for_the_earlier() {
        let (mut tree, root) = Tree::new();
        let a = tree.spawn(root, false);
        let b = tree.spawn(root, true);
        assert_eq!(tree.turn(b), WAIT);
        assert!(!tree.blocked(a));
        assert!(tree.blocked(root));
        tree.end(a);
        assert_eq!(tree.turn(b), FRONT);
    }

    #[test]
    fn a_cut_cancels_what_follows_the_task() {
        let (mut tree, root) = Tree::new();
        let f = tree.spawn(root, false);
        let raised = tree.spawn(f, true);
        let later = tree.spawn(f, true);
        tree.cut(f, raised);
        assert_eq!(tree.turn(later), CLOSED);
        assert!(tree.closed(f));
        tree.end(raised);
        assert_eq!(tree.turn(f), CLOSED);
        tree.end(later);
        tree.end(f);
        assert_eq!(tree.turn(root), FRONT);
    }

    #[test]
    fn the_front_passes_a_cut_segment_whose_code_goes_on() {
        let (mut tree, root) = Tree::new();
        let f = tree.spawn(root, false);
        let raised = tree.spawn(f, true);
        tree.cut(f, raised);
        tree.end(raised);
        assert_eq!(tree.turn(root), FRONT);
        assert!(tree.closed(f));
        let late = tree.spawn(f, true);
        assert!(tree.closed(late));
        tree.end(late);
        tree.end(f);
    }
}
