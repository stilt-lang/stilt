//! The header annotations of a test (conformance.header-annotations): its `//~ key: value` lines,
//! the output blocks that `stdout:` and `stderr:` open, and what they make a run test expect.

use super::values::{
    parse_exit, parse_location, parse_panic, parse_quoted, parse_rules, parse_tier, parse_words,
    utf8,
};
use super::{RunSpec, Tier};

#[derive(Clone, Copy)]
pub(super) enum Stream {
    Stdout,
    Stderr,
}

/// The header annotations seen so far. A field is `Some` once its key has been given.
#[derive(Default)]
pub(super) struct Header {
    pub(super) tier: Option<Tier>,
    pub(super) rules: Option<Vec<String>>,
    args: Option<Vec<String>>,
    stdin: Option<Vec<u8>>,
    run_output: Option<String>,
    stdout: Option<Vec<String>>,
    stderr: Option<Vec<String>>,
    exit: Option<i32>,
    panic: Option<String>,
    panic_at: Option<String>,
}

impl Header {
    /// Reads one `key: value` annotation. Returns the stream whose block it opens, if any.
    pub(super) fn key(&mut self, annotation: &str) -> Result<Option<Stream>, String> {
        let body = annotation
            .strip_prefix(' ')
            .ok_or("expected a space after `//~`")?;
        let (key, value) = body
            .split_once(':')
            .ok_or_else(|| format!("expected `key: value`, found `{body}`"))?;
        let value = value.trim();
        match key {
            "tier" => set(&mut self.tier, key, parse_tier(value)?)?,
            "rule" => set(&mut self.rules, key, parse_rules(value)?)?,
            "args" => set(&mut self.args, key, parse_words(value)?)?,
            "stdin" => set(&mut self.stdin, key, parse_quoted(value)?)?,
            "run-output" => set(&mut self.run_output, key, utf8(parse_quoted(value)?)?)?,
            "stdout" | "stderr" => {
                if !value.is_empty() {
                    return Err(format!(
                        "`{key}:` takes no value; its lines follow as `//~ |`"
                    ));
                }
                let (slot, stream) = match key {
                    "stdout" => (&mut self.stdout, Stream::Stdout),
                    _ => (&mut self.stderr, Stream::Stderr),
                };
                set(slot, key, Vec::new())?;
                return Ok(Some(stream));
            }
            "exit" => set(&mut self.exit, key, parse_exit(value)?)?,
            "panic" => set(&mut self.panic, key, parse_panic(value)?)?,
            "panic-at" => set(&mut self.panic_at, key, parse_location(value)?)?,
            _ => return Err(format!("unknown key `{key}`")),
        }
        Ok(None)
    }

    pub(super) fn block(&mut self, stream: Stream) -> &mut Vec<String> {
        let block = match stream {
            Stream::Stdout => &mut self.stdout,
            Stream::Stderr => &mut self.stderr,
        };
        block.get_or_insert_with(Vec::new)
    }

    pub(super) fn has_run_keys(&self) -> bool {
        self.args.is_some()
            || self.stdin.is_some()
            || self.run_output.is_some()
            || self.stdout.is_some()
            || self.stderr.is_some()
            || self.exit.is_some()
            || self.panic.is_some()
            || self.panic_at.is_some()
    }
}

fn set<T>(slot: &mut Option<T>, key: &str, value: T) -> Result<(), String> {
    if slot.is_some() {
        return Err(format!("`{key}` is given twice"));
    }
    *slot = Some(value);
    Ok(())
}

/// Returns the output line held by a `//~ | text` annotation, given what follows `//~`.
pub(super) fn block_line(annotation: &str) -> Option<&str> {
    if annotation == " |" {
        Some("")
    } else {
        annotation.strip_prefix(" | ")
    }
}

/// What a run test expects from its run keys. A program with errors exits with status 2 however
/// it ends (conformance.run-statuses), so that is the only status its test may expect.
pub(super) fn run_spec(header: &Header, has_errors: bool) -> Result<RunSpec, String> {
    let stdout = match (&header.run_output, &header.stdout) {
        (Some(_), Some(_)) => return Err("both `run-output` and `stdout` are given".to_owned()),
        (Some(text), None) => format!("{text}\n"),
        (None, Some(lines)) => joined(lines),
        (None, None) => String::new(),
    };
    let exit = match (header.exit, &header.panic) {
        (Some(code), _) if has_errors && code != 2 => {
            return Err("a test of a program with errors must exit with status 2".to_owned());
        }
        _ if has_errors => 2,
        (Some(code), Some(_)) if code != 101 => {
            return Err("a test that expects a panic must exit with status 101".to_owned());
        }
        (Some(code), _) => code,
        (None, Some(_)) => 101,
        (None, None) => 0,
    };
    if header.panic_at.is_some() && header.panic.is_none() {
        return Err("`panic-at` needs `panic`".to_owned());
    }
    // program.stderr-with-status-2: what a run that ends with status 2 writes to stderr is
    // unspecified.
    if exit == 2 && header.stderr.is_some() {
        return Err("a test that expects status 2 can't have a `stderr` block".to_owned());
    }
    Ok(RunSpec {
        args: header.args.clone().unwrap_or_default(),
        stdin: header.stdin.clone().unwrap_or_default(),
        stdout,
        stderr: header.stderr.as_deref().map(joined),
        exit,
        panic: header.panic.clone(),
        panic_at: header.panic_at.clone(),
    })
}

fn joined(lines: &[String]) -> String {
    let mut text = String::new();
    for line in lines {
        text.push_str(line);
        text.push('\n');
    }
    text
}
