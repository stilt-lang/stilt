//! What `stilt` prints when it panics, or when a phase of its own returns an error that only a
//! bug can cause ([`internal`]): either is a bug in it, never in the program it was given, so it
//! says so, with the toolchain's version, where to report it, where the engines write their
//! errors, and the command that writes a smaller program that still stops it (`crate::reduce`).
//! A query that a write to the database cancels unwinds with no panic of its own, and prints
//! nothing.

/// Where bugs are reported.
pub(crate) const ISSUES: &str = "https://github.com/stilt-lang/stilt/issues";

/// Makes every panic, after Rust's own message, print [`note`].
pub(crate) fn install() {
    let rust = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        rust(info);
        let args: Vec<String> = std::env::args().skip(1).collect();
        eprint!("{}", note(env!("STILT_VERSION"), &args));
    }));
}

/// An error that only a bug in `stilt` can cause, `message`, with the note that a panic gets,
/// as a command reports it.
pub(crate) fn internal(message: impl std::fmt::Display) -> String {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let note = note(env!("STILT_VERSION"), &args);
    format!("{INTERNAL}{message}\n{}", note.trim_matches('\n'))
}

/// What the line of an error of [`internal`] starts with, which `stilt reduce` looks for.
pub(crate) const INTERNAL: &str = "internal error: ";

/// The note under a panic of `stilt` at `version`, run with `args`.
fn note(version: &str, args: &[String]) -> String {
    let reduce = match args.first().map(String::as_str) {
        None | Some("reduce" | "lsp" | "repl") => String::new(),
        Some(_) => format!(
            "note: `stilt reduce {}` writes a smaller program that still stops it, with a report \
             to attach\n",
            args.iter().map(|a| quoted(a)).collect::<Vec<_>>().join(" ")
        ),
    };
    format!(
        "\nerror: stilt stopped on an internal error, which is a bug in stilt and not in your \
         program\nnote: please report it at {ISSUES}, with the program and the command that \
         gave it\n{reduce}note: the engines that answer commands write their own errors to the \
         `.log` files of {}\nnote: stilt {version}, on {}-{}\n",
        crate::engine::directory().display(),
        std::env::consts::ARCH,
        std::env::consts::OS,
    )
}

/// An argument as a shell reads it back: as it is when it holds only safe characters, and
/// otherwise in single quotes.
fn quoted(arg: &str) -> String {
    let safe = |c: char| c.is_ascii_alphanumeric() || "-_./=:,+@".contains(c);
    if !arg.is_empty() && arg.chars().all(safe) {
        arg.to_owned()
    } else {
        format!("'{}'", arg.replace('\'', "'\\''"))
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn the_note_names_the_bug_the_version_and_where_to_report_it() {
        let args = ["check".to_owned(), "my dir".to_owned()];
        let note = super::note("2027.1.0 (abc 2026-11-15)", &args);
        assert!(note.contains("`stilt reduce check 'my dir'`"), "{note}");
        assert!(
            note.contains("a bug in stilt and not in your program"),
            "{note}"
        );
        assert!(
            note.contains("stilt 2027.1.0 (abc 2026-11-15), on "),
            "{note}"
        );
        assert!(note.contains(super::ISSUES), "{note}");
        assert!(
            note.contains("write their own errors to the `.log` files of"),
            "{note}"
        );
    }

    #[test]
    fn an_internal_error_carries_the_note_that_reduce_looks_for() {
        let error = super::internal("no entry for `main.f`");
        assert!(
            error.starts_with("internal error: no entry for `main.f`\nerror: stilt stopped"),
            "{error}"
        );
        assert!(
            error.contains("an internal error, which is a bug in stilt"),
            "{error}"
        );
        assert!(!error.ends_with('\n'), "{error}");
    }
}
