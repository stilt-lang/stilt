//! The checks of what the registry's help says (`reference/messages.md`): it is written for the
//! person who made the mistake, so it cites no paragraph of the Reference, no file of the
//! repository, and none of the words of how the language is specified.

use std::collections::BTreeMap;

use crate::paragraphs::Paragraph;
use crate::registry::Entry;

/// Words that the help of a code never uses, since they name how the language is specified
/// rather than what the code does.
const WORDS: [&str; 5] = ["the Reference", "grammar", "phase", "paragraph", "registry"];

/// The files that a help may name: those a user writes or reads.
const USER_FILES: [&str; 3] = ["docs.lock", "main.lt", "stilt.toml"];

/// An error for each help in `entries` that cites a paragraph, names a file of the repository
/// or uses one of [`WORDS`].
pub(crate) fn check(entries: &[Entry], paragraphs: &BTreeMap<String, Paragraph>) -> Vec<String> {
    let mut errors = Vec::new();
    for e in entries {
        let help = e.help.as_str();
        for word in WORDS.iter().filter(|w| uses(help, w)) {
            errors.push(format!(
                "{}'s help says `{word}`: say what the code does instead",
                e.code
            ));
        }
        let cited = help
            .split(|c: char| !(c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_' | '/')))
            .map(|word| word.trim_end_matches('.'))
            .filter(|word| is_paragraph(word, paragraphs) || is_repository_file(word));
        for word in cited {
            errors.push(format!(
                "{}'s help cites `{word}`, which its reader doesn't have",
                e.code
            ));
        }
    }
    errors
}

/// Whether `word` is the ID of a paragraph, but for those of the standard library's modules,
/// whose IDs are the modules' names, as `std.fs`.
fn is_paragraph(word: &str, paragraphs: &BTreeMap<String, Paragraph>) -> bool {
    paragraphs.contains_key(word) && !word.starts_with("std.")
}

/// Whether `help` uses `word` as a word of its own.
fn uses(help: &str, word: &str) -> bool {
    let lower = help.to_lowercase();
    let word = word.to_lowercase();
    lower.match_indices(&word).any(|(at, _)| {
        let before = lower[..at].chars().next_back();
        let after = lower[at + word.len()..].chars().next();
        !before.is_some_and(char::is_alphanumeric) && !after.is_some_and(char::is_alphanumeric)
    })
}

/// Whether `word` names a file of the repository, by a path or an extension that no user's
/// file has.
fn is_repository_file(word: &str) -> bool {
    let extensions = [".md", ".rs", ".ml", ".mli", ".toml", ".txt"];
    !USER_FILES.contains(&word)
        && (extensions.iter().any(|x| word.ends_with(x)) || word.starts_with("reference/"))
}

#[cfg(test)]
mod tests {
    use super::{is_repository_file, uses};

    #[test]
    fn finds_whole_words_only() {
        assert!(uses("Each phase runs.", "phase"));
        assert!(!uses("Each phases runs.", "phase"));
        assert!(uses("The Grammar says.", "grammar"));
    }

    #[test]
    fn tells_the_repository_s_files_from_the_user_s() {
        assert!(is_repository_file("reference/03-syntax.md"));
        assert!(is_repository_file("errors.toml"));
        assert!(!is_repository_file("stilt.toml"));
        assert!(!is_repository_file("x.y"));
    }
}
