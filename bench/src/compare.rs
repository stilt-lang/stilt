//! `stilt-bench compare`: Stilt's release builds of the benchmark programs against their
//! versions in other languages.
//!
//! It runs five suites ([`suites`]): the six programs of the Perceus paper (Reinking, Xie,
//! de Moura and Leijen, PLDI 2021) in Stilt, Rust, Koka, OCaml, Haskell, Swift and Java, the
//! benchmark suite's programs in Stilt, Rust, Go, Swift and OCaml, programs of `std.par` in
//! Stilt and in Rust with Rayon, each on every number of threads up to one per core, which
//! `STILT_THREADS` and `RAYON_NUM_THREADS` set, so that each prints the same on every number, as
//! par.sequential-meaning says Stilt's must, the programs that allocate most against their Rust
//! versions linked with mimalloc, and `examples/pick` against jq and jaq on a large document
//! ([`input`]). It builds each version with its language's release flags
//! ([`toolchains`]), runs each once untimed and checks that it prints what the suite's reference
//! prints, Rust's version or jq, then times each by the meter's counts, as `just bench` does (Goals,
//! Timing): the versions of a program take turns, each at least `--runs` times and as many more
//! as its runs take to add up to `--seconds`, and a version's time is that of its runs' counts
//! added together, divided by their number. A version that ends with an error, as by running out
//! of memory, is reported with its error. It writes the results to `results.md` and
//! `results.json` in the output directory, with the machine, its load, and each toolchain's
//! version and flags, and fails when a version prints something else than Rust's.

mod input;
mod json;
pub(crate) mod machine;
mod report;
pub(crate) mod sample;
mod suites;
#[cfg(test)]
mod tests;
mod toolchains;

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use sample::{Runs, float};
use suites::{Program, Setting, Suite};
use toolchains::{Language, Toolchain};

/// Times the benchmark programs against their versions in other languages.
#[derive(Debug, clap::Args)]
pub(crate) struct Args {
    /// The benchmark's directory, which holds `programs/` and `compare/`.
    #[arg(long, default_value = "bench")]
    suite: PathBuf,
    /// Where to write the executables and the results.
    #[arg(long, default_value = "target/compare")]
    out: PathBuf,
    /// The least number of timed runs of each version of a program.
    #[arg(long, default_value_t = 5)]
    runs: usize,
    /// The least time, in seconds, that each version's timed runs add up to.
    #[arg(long, default_value_t = 1.0)]
    seconds: f64,
    /// Run only the programs whose name contains this text.
    #[arg(long)]
    filter: Option<String>,
    /// The languages to run, such as `stilt,ocaml`, and Rust's versions, whose output the others
    /// must print: every language unless given.
    #[arg(long, value_delimiter = ',')]
    languages: Vec<String>,
    #[command(flatten)]
    tools: toolchains::Tools,
}

/// What a program's version in one language gave.
#[derive(Debug)]
pub(crate) enum Outcome {
    /// Its timed runs.
    Measured(Runs),
    /// It ended with an error status, and this is the last line it wrote on stderr.
    Failed(i32, String),
    /// It printed something else than the Rust version.
    Wrong,
}

/// A program's outcome in each language.
#[derive(Debug)]
pub(crate) struct Row {
    pub(crate) program: String,
    pub(crate) results: Vec<(Language, Outcome)>,
}

/// Everything the report shows.
#[derive(Debug)]
pub(crate) struct Results {
    pub(crate) date: String,
    pub(crate) machine: machine::Machine,
    /// The load averages before the first build and after the last run.
    pub(crate) load: (String, String),
    pub(crate) runs: usize,
    pub(crate) seconds: f64,
    pub(crate) toolchains: Vec<Toolchain>,
    pub(crate) missing: Vec<(Language, String)>,
    pub(crate) suites: Vec<(Suite, Vec<Row>)>,
}

pub(crate) fn main(args: &Args) -> ExitCode {
    match compare(args) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(message) => {
            eprintln!("ERROR {message}");
            ExitCode::FAILURE
        }
    }
}

/// Measures every program, writes the results, and tells whether every version printed what
/// the Rust version printed.
fn compare(args: &Args) -> Result<bool, String> {
    let wanted = wanted(&args.languages)?;
    let absolute =
        |p: &Path| std::path::absolute(p).map_err(|e| format!("cannot find {}: {e}", p.display()));
    let (dir, out) = (absolute(&args.suite)?, absolute(&args.out)?);
    std::fs::create_dir_all(&out).map_err(|e| format!("cannot write {}: {e}", out.display()))?;
    let suites = suites::load(&dir, args.filter.as_deref(), &out)?;
    raise_stack_limit();
    let (toolchains, missing) = toolchains::find(&args.tools, &wanted, &out);
    for (language, why) in &missing {
        eprintln!("note: {} is left out: {why}", language.name());
    }
    if !toolchains.iter().any(|t| t.language == Language::Rust) {
        return Err(
            "no Rust toolchain, whose versions give the output the others must print".into(),
        );
    }
    let before = machine::load();
    let mut measured = Vec::new();
    for suite in suites {
        let rows = measure_suite(args, &out, &suite, &toolchains)?;
        measured.push((suite, rows));
    }
    let results = Results {
        date: machine::now(),
        machine: machine::describe(),
        load: (before, machine::load()),
        runs: args.runs,
        seconds: args.seconds,
        toolchains,
        missing,
        suites: measured,
    };
    let markdown = report::markdown(&results);
    let write = |name: &str, text: &str| {
        let path = out.join(name);
        std::fs::write(&path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))
    };
    write("results.md", &markdown)?;
    write("results.json", &json::results(&results))?;
    println!("{markdown}");
    eprintln!(
        "wrote {} and results.json",
        out.join("results.md").display()
    );
    let wrong = results
        .suites
        .iter()
        .flat_map(|(_, rows)| rows)
        .any(|row| row.results.iter().any(|(_, o)| matches!(o, Outcome::Wrong)));
    Ok(!wrong)
}

/// Measures every program of `suite` under `out`, or none when no toolchain runs its reference.
fn measure_suite(
    args: &Args,
    out: &Path,
    suite: &Suite,
    toolchains: &[Toolchain],
) -> Result<Vec<Row>, String> {
    let mut rows = Vec::new();
    if !suite.programs.is_empty() && !toolchains.iter().any(|t| t.language == suite.reference) {
        eprintln!(
            "note: {} is left out: it has no {}, whose output the others must print",
            suite.title,
            suite.reference.name()
        );
        return Ok(rows);
    }
    for program in &suite.programs {
        let out = out.join(suite.key);
        rows.extend(measure(args, &out, program, toolchains, suite.reference)?);
    }
    Ok(rows)
}

/// The languages that `names` asks for, Rust among them, or every language.
fn wanted(names: &[String]) -> Result<Vec<Language>, String> {
    if names.is_empty() {
        return Ok(Language::ALL.to_vec());
    }
    let mut wanted = vec![Language::Rust];
    for name in names {
        let language = Language::named(name).ok_or_else(|| format!("no language {name}"))?;
        if !wanted.contains(&language) {
            wanted.push(language);
        }
    }
    Ok(wanted)
}

/// The stack of a program's main thread follows its limit on Linux: raise it as far as the
/// system lets, up to 512 MiB, as macOS builds set theirs ([`toolchains`]).
fn raise_stack_limit() {
    #[cfg(target_os = "linux")]
    {
        use nix::sys::resource::{Resource, getrlimit, setrlimit};
        if let Ok((_, hard)) = getrlimit(Resource::RLIMIT_STACK) {
            let _ = setrlimit(Resource::RLIMIT_STACK, hard.min(512 << 20), hard);
        }
    }
}

/// A program's version in one language, built, and its runs so far.
#[derive(Debug)]
struct Version {
    language: Language,
    command: Vec<OsString>,
    dir: PathBuf,
    runs: Runs,
    /// How many timed runs it gets.
    wanted: usize,
    /// How it ended, if it ended early.
    ended: Option<Outcome>,
}

/// Builds and measures each version of `program` that a toolchain builds, under `out`: one row,
/// or one for each of its settings, each version checked against `reference`'s.
fn measure(
    args: &Args,
    out: &Path,
    program: &Program,
    toolchains: &[Toolchain],
    reference: Language,
) -> Result<Vec<Row>, String> {
    let built = build(out, program, toolchains)?;
    let plain = Setting {
        label: String::new(),
        env: Vec::new(),
        args: Vec::new(),
    };
    let settings: Vec<&Setting> = if program.settings.is_empty() {
        vec![&plain]
    } else {
        program.settings.iter().collect()
    };
    let mut rows = Vec::new();
    for setting in settings {
        let mut versions: Vec<Version> = (built.iter())
            .map(|(language, command, dir)| Version {
                language: *language,
                command: with(command, setting),
                dir: dir.clone(),
                runs: Runs::default(),
                wanted: 0,
                ended: None,
            })
            .collect();
        let name = if setting.label.is_empty() {
            program.name.clone()
        } else {
            format!("{}, {}", program.name, setting.label)
        };
        let expected = untimed(&mut versions, args, &name, reference)?;
        timed(&mut versions, &expected)?;
        let row = Row {
            program: name,
            results: (versions.into_iter())
                .map(|v| (v.language, v.ended.unwrap_or(Outcome::Measured(v.runs))))
                .collect(),
        };
        eprintln!("{}", report::progress(&row));
        rows.push(row);
    }
    Ok(rows)
}

/// Builds each version of `program` that a toolchain builds, in a new directory under `out`:
/// its language, the command that runs it, and its directory.
fn build(
    out: &Path,
    program: &Program,
    toolchains: &[Toolchain],
) -> Result<Vec<(Language, Vec<OsString>, PathBuf)>, String> {
    let mut built = Vec::new();
    for (language, source) in &program.sources {
        let Some(toolchain) = toolchains.iter().find(|t| t.language == *language) else {
            continue;
        };
        let dir = out.join(&program.name).join(language.name().to_lowercase());
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir)
            .map_err(|e| format!("cannot write {}: {e}", dir.display()))?;
        eprintln!("{}: building the {} version", program.name, language.name());
        let command = match (&program.manifest, language) {
            (Some(manifest), Language::Rust) => {
                toolchain.build_cargo(manifest, &program.name, &dir)?
            }
            _ => toolchain.build(source, &dir)?,
        };
        built.push((*language, command, dir));
    }
    Ok(built)
}

/// `command` run in the environment of `setting`, with its arguments.
fn with(command: &[OsString], setting: &Setting) -> Vec<OsString> {
    let mut run: Vec<OsString> = Vec::new();
    if !setting.env.is_empty() {
        run.push("env".into());
        run.extend(setting.env.iter().map(|(k, v)| format!("{k}={v}").into()));
    }
    run.extend(command.iter().cloned());
    run.extend(setting.args.iter().cloned());
    run
}

/// Runs each version once, untimed, since a system may check a new executable on its first run,
/// the reference's first, and gives what it printed, which every other version must print.
/// Sets how many timed runs each version gets.
fn untimed(
    versions: &mut [Version],
    args: &Args,
    name: &str,
    reference: Language,
) -> Result<Vec<u8>, String> {
    let first = versions
        .iter()
        .position(|v| v.language == reference)
        .ok_or_else(|| format!("{name} has no {} version", reference.name()))?;
    let order = std::iter::once(first).chain((0..versions.len()).filter(|&i| i != first));
    let mut expected = None;
    for i in order {
        let version = &mut versions[i];
        let (sample, printed, errors) = sample::run(&version.command, &version.dir)?;
        if sample.status != 0 {
            let last = errors
                .lines()
                .rev()
                .find(|l| !l.trim().is_empty())
                .unwrap_or("");
            version.ended = Some(Outcome::Failed(sample.status, last.trim().to_owned()));
        } else if expected.as_ref().is_some_and(|e| *e != printed) {
            eprintln!(
                "ERROR {name}: the {} version prints something else",
                version.language.name()
            );
            version.ended = Some(Outcome::Wrong);
        } else {
            expected.get_or_insert(printed);
        }
        version.wanted = runs_for(args, sample.time().as_secs_f64());
    }
    match (&versions[first].ended, expected) {
        (None, Some(expected)) => Ok(expected),
        _ => Err(format!("{name}: the {} version fails", reference.name())),
    }
}

/// How many timed runs a version whose untimed run took `seconds` gets.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "the count is positive and small: the runs a second takes"
)]
fn runs_for(args: &Args, seconds: f64) -> usize {
    let more = (args.seconds / seconds.max(1e-6)).ceil().min(1e6) as usize;
    args.runs.max(1).max(more)
}

/// Times the versions that the untimed run left measuring, taking turns, so that a change in the
/// machine's load touches each alike.
fn timed(versions: &mut [Version], expected: &[u8]) -> Result<(), String> {
    let rounds = versions.iter().map(|v| v.wanted).max().unwrap_or(0);
    for round in 0..rounds {
        for version in versions.iter_mut() {
            if version.ended.is_some() || round >= version.wanted {
                continue;
            }
            let (sample, printed, errors) = sample::run(&version.command, &version.dir)?;
            if sample.status != 0 {
                let last = errors
                    .lines()
                    .rev()
                    .find(|l| !l.trim().is_empty())
                    .unwrap_or("");
                version.ended = Some(Outcome::Failed(sample.status, last.trim().to_owned()));
            } else if printed != expected {
                version.ended = Some(Outcome::Wrong);
            } else {
                version.runs.samples.push(sample);
            }
        }
    }
    Ok(())
}

/// The geometric mean of `ratios`, or nothing when there are none.
pub(crate) fn geometric_mean(ratios: &[f64]) -> Option<f64> {
    if ratios.is_empty() {
        return None;
    }
    let n = float(ratios.len() as u64);
    Some((ratios.iter().map(|r| r.ln()).sum::<f64>() / n).exp())
}
