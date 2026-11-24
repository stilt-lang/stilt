//! The text of a body's file, for the messages that write it back.

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::body_starts;
use stilt_syntax::TextSize;

/// The text of a file from the start of the body `index`.
pub(super) fn body_text(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
) -> Option<String> {
    let start = usize::from(body_starts(db, program, file)[index as usize]);
    String::from_utf8(file.bytes(db).get(start..)?.to_vec()).ok()
}

/// The line, counted from 1, of the offset `at` of the body `index`.
pub(super) fn line_of(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    index: u32,
    at: TextSize,
) -> u32 {
    let end = usize::from(body_starts(db, program, file)[index as usize] + at);
    let before = file.bytes(db).get(..end).unwrap_or_default();
    u32::try_from(before.split(|b| *b == b'\n').count()).unwrap_or(0)
}
