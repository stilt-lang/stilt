//! Publishes the grammar of `reference/03-syntax.md` as GBNF and as llguidance's Lark-like format,
//! and checks that each accepts every prefix of the programs of the language. Writes the files that
//! restate the words and tokens of `reference/02-lexical.md` for the lexers and the editors.

mod check;
mod copies;
mod ebnf;
mod expand;
mod facts;
mod gbnf;
mod heads;
mod lark;
mod lexical;
mod lexicon;
mod names;
mod ocaml;
mod print;
mod recursion;
mod rust;
mod shape;
mod sources;
mod suite;
mod textmate;
mod treesitter;
mod treesitter_queries;
mod treesitter_scanner;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use clap::{Parser, Subcommand};

const GRAMMAR: &str = "reference/03-syntax.md";

#[derive(Parser)]
#[command(about = "Publishes the grammar of Stilt for constrained decoders, and checks it")]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Writes `stilt.gbnf` and `stilt.lark` to the directory, or with `--check` fails if
    /// they are not what the grammar gives.
    Generate {
        #[arg(long, default_value = "reference/grammar")]
        out: PathBuf,
        #[arg(long)]
        check: bool,
    },
    /// Writes the tables of words and tokens of both lexers, the editors' grammars and the
    /// manifest's schema, or with `--check` fails if one is not what the Reference gives; and
    /// fails if a list that the guide or the design documents restate isn't the Reference's.
    Sources {
        #[arg(long)]
        check: bool,
    },
    /// Prints the path of each program, one to a line: the conformance suite's without a syntax
    /// error, and those of the directories.
    Programs {
        /// The conformance suite, whose programs without a syntax error are listed.
        #[arg(long, value_name = "DIR")]
        conformance: Option<PathBuf>,
        /// Directories of programs.
        programs: Vec<PathBuf>,
    },
    /// Feeds the bytes of programs to grammars in the Lark-like format, and fails if a
    /// prefix of one is not viable.
    Check {
        /// A grammar to check: the Lark form, or the GBNF form converted to it. Repeat the
        /// flag to check several.
        #[arg(long, required = true)]
        grammar: Vec<PathBuf>,
        /// The conformance suite, whose programs without a syntax error are checked.
        #[arg(long, value_name = "DIR")]
        conformance: Option<PathBuf>,
        /// The documents whose Stilt examples are checked.
        #[arg(long, value_name = "DIR")]
        guide: Option<PathBuf>,
        /// Directories of programs.
        programs: Vec<PathBuf>,
    },
}

fn main() -> ExitCode {
    match run(Args::parse().command) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("ERROR {message}");
            ExitCode::FAILURE
        }
    }
}

fn run(command: Command) -> Result<(), String> {
    match command {
        Command::Generate { out, check } => generate(&out, check),
        Command::Sources { check } => sources::write(Path::new("."), check),
        Command::Programs {
            conformance,
            programs,
        } => {
            let mut all = Vec::new();
            if let Some(root) = conformance {
                all.extend(suite::directory(&root, true)?);
            }
            for root in &programs {
                all.extend(suite::directory(root, false)?);
            }
            for program in all {
                println!("{}", program.name);
            }
            Ok(())
        }
        Command::Check {
            grammar,
            conformance,
            guide,
            programs,
        } => check_programs(
            &grammar,
            conformance.as_deref(),
            guide.as_deref(),
            &programs,
        ),
    }
}

/// The two published forms of the grammar, as `(file name, text)`.
fn published(
    markdown: &str,
    lexical: &lexical::Lexical,
) -> Result<Vec<(&'static str, String)>, String> {
    let mut grammar = expand::expand(&ebnf::extract(markdown)?)?;
    heads::derive(&mut grammar)?;
    recursion::eliminate(&mut grammar)?;
    let grammar = shape::publish(grammar, &lexical.macro_tokens()?)?;
    Ok(vec![
        ("stilt.gbnf", gbnf::emit(&grammar)),
        ("stilt.lark", lark::emit(&grammar)),
    ])
}

fn generate(out: &Path, check: bool) -> Result<(), String> {
    let markdown = fs::read_to_string(GRAMMAR).map_err(|e| format!("{GRAMMAR}: {e}"))?;
    for (name, text) in published(&markdown, &sources::read(Path::new("."))?)? {
        let path = out.join(name);
        if check {
            if fs::read_to_string(&path).ok().as_deref() != Some(&text) {
                return Err(format!(
                    "{} is not what {GRAMMAR} gives; run `just grammar-generate`",
                    path.display()
                ));
            }
        } else {
            fs::create_dir_all(out).map_err(|e| e.to_string())?;
            fs::write(&path, text).map_err(|e| format!("{}: {e}", path.display()))?;
        }
    }
    Ok(())
}

fn check_programs(
    grammars: &[PathBuf],
    conformance: Option<&Path>,
    guide: Option<&Path>,
    directories: &[PathBuf],
) -> Result<(), String> {
    let mut programs = Vec::new();
    if let Some(root) = conformance {
        programs.extend(suite::directory(root, true)?);
    }
    if let Some(root) = guide {
        programs.extend(suite::examples(root)?);
    }
    for root in directories {
        programs.extend(suite::directory(root, false)?);
    }
    for grammar in grammars {
        check_grammar(grammar, &programs)?;
    }
    Ok(())
}

fn check_grammar(grammar: &Path, programs: &[suite::Program]) -> Result<(), String> {
    let start = Instant::now();
    let text = fs::read_to_string(grammar).map_err(|e| format!("{}: {e}", grammar.display()))?;
    let rejections = check::Checker::new(text)?.check_all(programs)?;
    for r in rejections.iter().take(20) {
        eprintln!(
            "{}: byte {} (line {}): {}\n    after: {:?}",
            r.program, r.offset, r.line, r.reason, r.context
        );
    }
    if !rejections.is_empty() {
        return Err(format!(
            "{} of {} programs are not accepted by {}",
            rejections.len(),
            programs.len(),
            grammar.display()
        ));
    }
    let bytes: usize = programs.iter().map(|p| p.bytes.len()).sum();
    println!(
        "{}: {} programs, {bytes} bytes, every prefix viable ({:.1} s)",
        grammar.display(),
        programs.len(),
        start.elapsed().as_secs_f64()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const MARKDOWN: &str = include_str!("../../../reference/03-syntax.md");
    const LEXICAL: &str = include_str!("../../../reference/02-lexical.md");

    fn forms() -> Vec<(&'static str, String)> {
        published(MARKDOWN, &lexical::read(LEXICAL, MARKDOWN).unwrap()).unwrap()
    }

    fn form(name: &str) -> String {
        forms().into_iter().find(|(n, _)| *n == name).unwrap().1
    }

    /// The lines of a rule of the Lark form.
    fn rule(lark: &str, name: &str) -> String {
        let mut lines = lark
            .lines()
            .skip_while(|l| !l.starts_with(&format!("{name}:")));
        let mut text = lines.next().unwrap().to_owned();
        for line in lines.take_while(|l| l.starts_with(' ')) {
            text.push_str(line);
        }
        text
    }

    #[test]
    fn heads_lack_the_forms_they_cannot_hold() {
        let lark = form("stilt.lark");
        let head = rule(&lark, "primary_h");
        assert!(!head.contains("struct") && !head.contains("kw_match") && !head.contains("block"));
        let full = rule(&lark, "primary");
        assert!(full.contains("struct") && full.contains("kw_match") && full.contains("block"));
    }

    #[test]
    fn gbnf_rules_do_not_begin_with_themselves() {
        for line in form("stilt.gbnf").lines().filter(|l| l.contains(" ::= ")) {
            let (name, body) = line.split_once(" ::= ").unwrap();
            assert!(!body.starts_with(&format!("{name} ")), "{line}");
        }
    }

    #[test]
    fn the_forms_are_what_the_grammar_gives() {
        for (name, text) in forms() {
            let committed = fs::read_to_string(format!("../../reference/grammar/{name}")).unwrap();
            assert_eq!(committed, text, "run `just grammar-generate`");
        }
    }
}
