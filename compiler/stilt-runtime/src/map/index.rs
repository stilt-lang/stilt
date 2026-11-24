//! The index of a map's entries: an open-addressing table of their positions, probed linearly
//! from where each key's own hash points, so that a lookup hashes nothing again and allocates
//! nothing.
//!
//! A slot is empty, or holds the position of an entry with bits of its hash, its *tag*, so that
//! a probe passes most other entries without reading them, or marks an entry removed. An entry
//! takes the first empty slot of its probe, and a removed entry's slot stays marked until the
//! table is built again, in the order of the entries. So the entries of one hash, which share a
//! probe, lie along it in their insertion order, which is the order in which a map calls `eq`
//! on them (std.finding-keys).

/// The bits of a slot that hold one more than its entry's position.
const POSITION_BITS: u32 = 40;
const POSITION: u64 = (1 << POSITION_BITS) - 1;

/// An empty slot, which ends a probe.
const EMPTY: u64 = 0;

/// The slot of a removed entry, which a probe passes over: no entry's position is one less.
const REMOVED: u64 = POSITION;

/// The most entries a map holds, which no host has the memory for: one less than [`REMOVED`].
pub(super) const MAX_ENTRIES: usize = (REMOVED - 1) as usize;

/// The golden ratio's fraction of 2^64, an odd number, by which a hash is multiplied so that its
/// every bit reaches the high bits of the product, which choose the probe's first slot.
const SPREAD: u64 = 0x9e37_79b9_7f4a_7c15;

/// The fewest slots of a table that isn't empty.
const MIN_SLOTS: usize = 8;

#[derive(Clone, Debug, Default)]
pub(super) struct Index {
    slots: Vec<u64>,
    /// The slots that aren't empty: entries' and removed ones'.
    used: usize,
}

/// A probe for the entries of one hash: the next slot to look at, and the tag that the slots of
/// its entries hold.
#[derive(Clone, Copy, Debug)]
pub(super) struct Probe {
    at: usize,
    tag: u64,
}

/// The number of slots of a table that holds `n` entries, at most half of them full.
fn slots_for(n: usize) -> usize {
    (2 * n).next_power_of_two().max(MIN_SLOTS)
}

impl Index {
    /// A table of the entries `entries` gives, by their positions and hashes, in their order.
    pub(super) fn of(n: usize, entries: impl Iterator<Item = (usize, u64)>) -> Self {
        let mut index = Self {
            slots: vec![EMPTY; slots_for(n)],
            used: 0,
        };
        for (position, hash) in entries {
            index.put(position, hash);
        }
        index
    }

    /// The probe for the entries whose hash is `hash`.
    pub(super) fn probe(&self, hash: u64) -> Probe {
        let spread = hash.wrapping_mul(SPREAD);
        let at = if self.slots.is_empty() {
            0
        } else {
            (spread >> (64 - self.slots.len().trailing_zeros())) as usize
        };
        // The tag takes bits of the product below those that choose the first slot.
        Probe {
            at,
            tag: (spread >> 16) << POSITION_BITS,
        }
    }

    /// Whether a table can take one more entry, still at most three quarters full.
    pub(super) fn has_room(&self) -> bool {
        4 * (self.used + 1) <= 3 * self.slots.len()
    }

    /// Adds the entry at `position`, whose hash is `hash`, at the first empty slot of its probe.
    /// The table has room for it.
    pub(super) fn put(&mut self, position: usize, hash: u64) {
        debug_assert!(position < MAX_ENTRIES && self.has_room());
        let mask = self.slots.len() - 1;
        let mut probe = self.probe(hash);
        while self.slots[probe.at] != EMPTY {
            probe.at = (probe.at + 1) & mask;
        }
        self.slots[probe.at] = probe.tag | (position as u64 + 1);
        self.used += 1;
    }

    /// Marks removed the slot of the entry at `position`, whose hash is `hash`.
    pub(super) fn remove(&mut self, position: usize, hash: u64) {
        let mask = self.slots.len() - 1;
        let mut probe = self.probe(hash);
        let slot = probe.tag | (position as u64 + 1);
        while self.slots[probe.at] != slot {
            debug_assert!(self.slots[probe.at] != EMPTY, "an indexed entry");
            probe.at = (probe.at + 1) & mask;
        }
        self.slots[probe.at] = REMOVED;
    }
}

impl Probe {
    /// The position of the next entry along the probe whose slot holds its tag and for which
    /// `same` holds, or `None` at the probe's end.
    pub(super) fn next(&mut self, index: &Index, same: impl Fn(usize) -> bool) -> Option<usize> {
        let mask = index.slots.len().checked_sub(1)?;
        loop {
            let slot = index.slots[self.at];
            if slot == EMPTY {
                return None;
            }
            self.at = (self.at + 1) & mask;
            if slot != REMOVED && slot & !POSITION == self.tag {
                let position = (slot & POSITION) as usize - 1;
                if same(position) {
                    return Some(position);
                }
            }
        }
    }
}
