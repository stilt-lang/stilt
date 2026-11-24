//! `stilt-bench shootout`: the edit loop of the same project in Stilt, Rust, Go, OCaml and
//! Swift (LAUNCH-6's headline). It writes the project in each language ([`project`],
//! [`sources`]), about `--lines` lines in each, then for each version times a clean check and a
//! clean debug build, the time from an edit that breaks the middle module to its diagnostics and
//! from the edit that fixes it to a clean check, and the time from an edit to the running program
//! printing what the edit changed: through `stilt run`, which patches each edit into the program
//! as it runs, and in the other languages through a debug build and a start of the program
//! ([`measure`]). Every built version must print what the Stilt version prints. It writes the
//! results to `results.md` in the output directory, with the machine and each tool's version, and
//! fails when a version can't be built or prints something else; a language whose tool isn't
//! found is left out.

mod measure;
mod project;
mod report;
mod sources;
mod tools;

use std::path::PathBuf;
use std::process::ExitCode;

use measure::Measured;
use project::Shape;

/// Times the edit loop of the same project in Stilt and other languages.
#[derive(Debug, clap::Args)]
pub(crate) struct Args {
    /// About how many lines each version of the project holds.
    #[arg(long, default_value_t = 50_000)]
    lines: usize,
    /// Where to write the projects and the results.
    #[arg(long, default_value = "target/shootout")]
    out: PathBuf,
    /// How many times each clean step runs.
    #[arg(long, default_value_t = 3)]
    runs: usize,
    /// How many edits each warm measurement makes.
    #[arg(long, default_value_t = 10)]
    edits: usize,
    /// The languages to run, such as `stilt,rust`: every language unless given. Stilt's always
    /// runs, since the others must print what it prints.
    #[arg(long, value_delimiter = ',')]
    languages: Vec<String>,
    #[command(flatten)]
    tools: tools::Tools,
}

/// A language of the shootout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Language {
    Stilt,
    Rust,
    Go,
    OCaml,
    Swift,
}

impl Language {
    const ALL: [Language; 5] = [
        Language::Stilt,
        Language::Rust,
        Language::Go,
        Language::OCaml,
        Language::Swift,
    ];

    pub(crate) fn name(self) -> &'static str {
        match self {
            Language::Stilt => "Stilt",
            Language::Rust => "Rust",
            Language::Go => "Go",
            Language::OCaml => "OCaml",
            Language::Swift => "Swift",
        }
    }
}

/// A version measured, with its tool's version.
pub(crate) struct Version {
    pub(crate) language: Language,
    pub(crate) tool: String,
    pub(crate) measured: Measured,
}

pub(crate) fn main(args: &Args) -> ExitCode {
    match shootout(args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("ERROR {message}");
            ExitCode::FAILURE
        }
    }
}

fn shootout(args: &Args) -> Result<(), String> {
    let out = std::path::absolute(&args.out).map_err(|e| format!("cannot find the output: {e}"))?;
    let shape = Shape::of_lines(args.lines);
    let mut versions: Vec<Version> = Vec::new();
    let mut missing = Vec::new();
    for language in wanted(&args.languages)? {
        let tool = match args.tools.version(language) {
            Ok(tool) => tool,
            Err(why) => {
                eprintln!("note: {} is left out: {why}", language.name());
                missing.push((language, why));
                continue;
            }
        };
        let dir = out.join(language.name().to_lowercase());
        let _ = std::fs::remove_dir_all(&dir);
        project::write(language, &dir, shape)?;
        eprintln!("{}: measuring {}", language.name(), dir.display());
        let measured =
            measure::version(&args.tools, language, &dir, shape, (args.runs, args.edits))?;
        if let Some(first) = versions.first()
            && first.measured.printed != measured.printed
        {
            return Err(format!(
                "the {} version prints {:?}, and the Stilt version {:?}",
                language.name(),
                measured.printed,
                first.measured.printed
            ));
        }
        eprintln!("{}", report::progress(language, &measured));
        versions.push(Version {
            language,
            tool,
            measured,
        });
    }
    let text = report::markdown(&args.tools, &versions, &missing, shape, args);
    let path = out.join("results.md");
    std::fs::write(&path, &text).map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    println!("{text}");
    eprintln!("wrote {}", path.display());
    Ok(())
}

/// The languages that `names` asks for, Stilt first, or every language.
fn wanted(names: &[String]) -> Result<Vec<Language>, String> {
    if names.is_empty() {
        return Ok(Language::ALL.to_vec());
    }
    let mut wanted = vec![Language::Stilt];
    for name in names {
        let language = Language::ALL
            .into_iter()
            .find(|l| l.name().eq_ignore_ascii_case(name))
            .ok_or_else(|| format!("no language {name}"))?;
        if !wanted.contains(&language) {
            wanted.push(language);
        }
    }
    Ok(wanted)
}
