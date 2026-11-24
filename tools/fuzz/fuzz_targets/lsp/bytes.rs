//! The fuzz input read as a stream of choices, and the pieces of text the choices build from.

/// Bytes read from the front: past the end each read gives 0, or, when cycling, the bytes
/// again from the front, so that a backend has answers for as long as it is asked.
pub struct Bytes<'a> {
    data: &'a [u8],
    at: usize,
    cycle: bool,
}

impl<'a> Bytes<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Bytes {
            data,
            at: 0,
            cycle: false,
        }
    }

    pub fn cycling(data: &'a [u8]) -> Self {
        Bytes {
            data,
            at: 0,
            cycle: true,
        }
    }

    /// Whether every byte has been read, which a cycling stream never has.
    pub fn done(&self) -> bool {
        !self.cycle && self.at >= self.data.len()
    }

    pub fn byte(&mut self) -> u8 {
        let b = match self.data.len() {
            0 => 0,
            n if self.cycle => self.data[self.at % n],
            _ => self.data.get(self.at).copied().unwrap_or(0),
        };
        self.at = self.at.wrapping_add(1);
        b
    }

    /// A number below `n`, which is at most 256.
    pub fn below(&mut self, n: usize) -> usize {
        usize::from(self.byte()) % n.max(1)
    }

    pub fn flag(&mut self) -> bool {
        self.byte() & 1 == 1
    }

    pub fn u16(&mut self) -> u16 {
        u16::from_le_bytes([self.byte(), self.byte()])
    }

    pub fn u32(&mut self) -> u32 {
        u32::from_le_bytes([self.byte(), self.byte(), self.byte(), self.byte()])
    }

    pub fn u64(&mut self) -> u64 {
        u64::from(self.u32()) << 32 | u64::from(self.u32())
    }

    pub fn pick<T: Clone>(&mut self, from: &[T]) -> T {
        from[self.below(from.len())].clone()
    }

    /// The next `n` bytes, or as many as are left; a cycling stream gives none.
    pub fn take(&mut self, n: usize) -> &'a [u8] {
        if self.cycle {
            return &[];
        }
        let start = self.at.min(self.data.len());
        let end = start.saturating_add(n).min(self.data.len());
        self.at = end;
        &self.data[start..end]
    }

    /// A few pieces of text of every width, in UTF-8 and in UTF-16.
    pub fn words(&mut self) -> String {
        let n = self.below(5);
        (0..n).map(|_| self.pick(&PIECES)).collect()
    }
}

/// Text of one, two, three and four bytes a character, of one and two UTF-16 units, line ends
/// of both kinds, a combining mark, a byte order mark, and the shapes of snippets and code.
const PIECES: [&str; 20] = [
    "",
    "x",
    "fn main() {}",
    "\n",
    "\r\n",
    "\u{e9}",
    "\u{20ac}",
    "\u{1F600}",
    "\u{FEFF}",
    "a\u{301}",
    "\u{1D54F}\u{1D550}",
    "\t",
    "{",
    "}",
    "\"",
    "\\u{1F600}",
    "(${1:x})$0",
    "()$0",
    "let x = 1\n",
    "f(x: Int) -> Int",
];
