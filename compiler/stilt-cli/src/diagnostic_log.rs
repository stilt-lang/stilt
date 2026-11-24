//! The log of diagnostics that `STILT_DIAGNOSTIC_LOG` asks for, for a study of what people
//! meet: each check of `stilt check` and of the language server appends one line of JSON to
//! the file it names, with the time, the tool and the compiler's version, and the code and the
//! byte span of each diagnostic of the program, under a hash of its file's path. It holds no
//! source text and no path. Each line covers the whole program, so a diagnostic that one line
//! has and the next of the same tool lacks is one that the edit between them removed.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::json;
use stilt_db::{Database, Program};

/// The variable that names the log.
const VARIABLE: &str = "STILT_DIAGNOSTIC_LOG";

/// One diagnostic as the log keeps it: its file's path, its code and its span.
pub(crate) struct Seen<'a> {
    pub(crate) path: &'a Path,
    pub(crate) code: &'a str,
    pub(crate) start: u32,
    pub(crate) end: u32,
}

/// The file that `STILT_DIAGNOSTIC_LOG` names, when it is set and not empty.
pub(crate) fn path() -> Option<PathBuf> {
    std::env::var_os(VARIABLE)
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
}

/// Appends the diagnostics of `program` to the log, as `stilt check` reports them.
pub(crate) fn record_program(log: &Path, db: &Database, program: Program) {
    let found = stilt_rc::check_in_parallel(db, program);
    let paths: Vec<PathBuf> = found
        .iter()
        .map(|d| PathBuf::from(d.file.path(db)))
        .collect();
    let seen = found.iter().zip(&paths).map(|(d, path)| Seen {
        path,
        code: d.diagnostic.code.as_str(),
        start: d.diagnostic.range.start().into(),
        end: d.diagnostic.range.end().into(),
    });
    record(log, "check", seen);
}

/// Appends one line for a check by `tool` that found `seen`. A log that can't be written is
/// left as it is: the study never stops a check.
pub(crate) fn record<'a>(log: &Path, tool: &str, seen: impl Iterator<Item = Seen<'a>>) {
    let diagnostics: Vec<_> = seen
        .map(|s| json!({ "file": hashed(s.path), "code": s.code, "start": s.start, "end": s.end }))
        .collect();
    let time = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    let line = json!({
        "time": time,
        "tool": tool,
        "version": env!("CARGO_PKG_VERSION"),
        "diagnostics": diagnostics,
    });
    let file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(log);
    if let Ok(mut file) = file {
        let _ = file.write_all(format!("{line}\n").as_bytes());
    }
}

/// The first 16 hexadecimal digits of the BLAKE3 hash of a path, which tell two files apart
/// without naming either.
fn hashed(path: &Path) -> String {
    let hash = blake3::hash(path.as_os_str().as_encoded_bytes());
    hash.to_hex()[..16].to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_line_holds_codes_and_spans_and_no_path() {
        let dir = std::env::temp_dir().join(format!("stilt-diagnostic-log-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let log = dir.join("log.jsonl");
        let path = Path::new("/home/someone/secret/main.lt");
        let seen = |code| Seen {
            path,
            code,
            start: 3,
            end: 7,
        };
        record(&log, "check", [seen("E0211"), seen("W0303")].into_iter());
        record(&log, "check", std::iter::empty());
        let written = std::fs::read_to_string(&log).unwrap();
        std::fs::remove_dir_all(&dir).unwrap();
        let lines: Vec<serde_json::Value> = written
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect();
        assert_eq!(lines.len(), 2);
        assert!(!written.contains("secret"));
        let first = &lines[0]["diagnostics"];
        assert_eq!(first[1]["code"], "W0303");
        assert_eq!(first[0]["file"], first[1]["file"]);
        assert_eq!(first[0]["start"], 3);
        assert_eq!(lines[1]["diagnostics"].as_array().map(Vec::len), Some(0));
    }
}
