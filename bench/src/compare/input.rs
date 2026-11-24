//! The input of the tools' comparison: a JSON document of 300,000 books, about 80 MB, which a
//! fixed sequence of pseudo-random numbers draws, so that every run reads the same bytes.

use std::fmt::Write as _;
use std::path::Path;

/// How many books the document holds.
const BOOKS: u64 = 300_000;

const WORDS: [&str; 8] = [
    "red", "green", "blue", "amber", "violet", "slate", "ochre", "teal",
];

/// A linear congruential generator: Knuth's MMIX constants, read from the high bits.
struct Draws(u64);

impl Draws {
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % n
    }

    fn word(&mut self) -> &'static str {
        WORDS[usize::try_from(self.below(8)).unwrap_or(0)]
    }
}

/// Writes the document at `path`, unless a file is there already.
pub(crate) fn books(path: &Path) -> Result<(), String> {
    if path.is_file() {
        return Ok(());
    }
    let mut draws = Draws(7);
    let mut text = String::from("{\n  \"books\": [\n");
    for id in 0..BOOKS {
        let title = [draws.word(), draws.word(), draws.word()].join(" ");
        let year = 1900 + draws.below(125);
        let cents = 100 + draws.below(5_900);
        let stock = draws.below(20);
        let tags = [draws.word(), draws.word(), draws.word()].map(|t| format!("\"{t}\""));
        let name = draws.word();
        let born = 1850 + draws.below(150);
        let comma = if id + 1 < BOOKS { "," } else { "" };
        let _ = write!(
            text,
            "    {{\n      \"id\": {id},\n      \"title\": \"{title}\",\n      \"year\": {year},\n      \
             \"price\": {}.{:02},\n      \"stock\": {stock},\n      \"tags\": [{}],\n      \
             \"author\": {{\n        \"name\": \"{name}\",\n        \"born\": {born}\n      }}\n    }}{comma}\n",
            cents / 100,
            cents % 100,
            tags.join(", ")
        );
    }
    text.push_str("  ]\n}\n");
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir).map_err(|e| format!("cannot write {}: {e}", dir.display()))?;
    }
    std::fs::write(path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))
}
