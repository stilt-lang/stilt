//! `stilt-test` runs the conformance suite against any implementation of Stilt.
//!
//! The implementation is driven only through the command-line protocol of conformance.commands, so
//! the reference interpreter and the compiler are tested the same way. The runner prints one
//! `ERROR` line per failing test and a summary, and writes the details of each failure to a log
//! file. It exits with status 0 when every test passes, 1 when any test fails, and 2 when it can't
//! run the suite at all.
//!
//! With `--examples`, it runs the Stilt examples of Markdown documents, such as the guide,
//! instead of conformance tests. With `--coverage`, it runs nothing and reports which paragraphs
//! of the Reference the tests cite instead, exiting with status 1 when a paragraph is uncited.
//! With `--diff`, it compares each run with the same program's run under another
//! implementation instead of with the expected output, which tests generated programs that
//! have none, with `--tests` their tests' results too, and with `--succeed` that each run
//! exits with status 0. With `--parse`, it compares each program's syntax trees with those under another
//! implementation instead of running anything, which tests a parser against the reference
//! interpreter's. With `--check`, it compares each program's diagnostics with those under another
//! implementation, perhaps only those of some phases, which tests a compiler's checks against
//! the reference interpreter's. With `--runs`, it compares each program's run with its run under
//! another implementation, whatever the program expects and whether or not it has errors, with
//! the arguments and input that its annotations give, which tests that the two run programs with
//! errors alike (program.programs-with-errors). With `--cache`, the
//! other implementation's results are kept in a directory and reused. With `--approve`, it runs
//! nothing and approves the drafts under the paths that cite only paragraphs of the Reference,
//! exiting with status 1 when it holds any back.

mod annotations;
mod approval;
mod cache;
mod coverage;
mod declines;
mod discovery;
mod erased;
mod examples;
mod judge;
mod process;
mod protocol;
mod report;
mod runner;
mod sampling;

use std::ffi::OsString;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, PoisonError};
use std::thread;
use std::time::{Duration, Instant};

use clap::Parser;

use crate::annotations::{Kind, Tier};
use crate::coverage::{Coverage, Paragraphs, Registry};
use crate::discovery::Test;
use crate::protocol::Implementation;
use crate::report::{Logs, Summary};
use crate::runner::{Against, Also, Case, Outcome, Record};

/// The kinds of test, as `--kinds` names them (conformance.kinds-of-test).
#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
enum KindName {
    Run,
    Check,
    Test,
}

impl KindName {
    const fn of(kind: &Kind) -> Self {
        match kind {
            Kind::Run(_) => KindName::Run,
            Kind::Check => KindName::Check,
            Kind::TestBlocks(_) => KindName::Test,
        }
    }
}

/// Runs Stilt conformance tests against an implementation.
#[derive(Debug, Parser)]
#[command(version)]
struct Args {
    /// The implementation to test, such as `stilt-ref`.
    #[arg(
        long = "impl",
        value_name = "PROGRAM",
        required_unless_present_any = ["coverage", "approve"]
    )]
    implementation: Option<PathBuf>,

    /// Run nothing, and report which paragraphs of the Reference in this directory the tests
    /// cite, and which codes of its registry, `errors.toml`, they expect.
    #[arg(long, value_name = "REFERENCE", conflicts_with_all = ["implementation", "fast"])]
    coverage: Option<PathBuf>,

    /// Compare each run test's run with its run under this other implementation, instead of
    /// with the expected output. Both must report the expected diagnostics.
    #[arg(
        long,
        value_name = "PROGRAM",
        requires = "implementation",
        conflicts_with = "examples"
    )]
    diff: Option<PathBuf>,

    /// Compare each test's syntax trees, as `parse --sexp` prints them, with those under this
    /// other implementation, instead of running the test.
    #[arg(
        long,
        value_name = "PROGRAM",
        requires = "implementation",
        conflicts_with = "diff"
    )]
    parse: Option<PathBuf>,

    /// Compare each test's diagnostics, as `check --json` reports them, with those under this
    /// other implementation, instead of running the test: their codes, files, lines and
    /// columns.
    #[arg(
        long,
        value_name = "PROGRAM",
        requires = "implementation",
        conflicts_with_all = ["diff", "parse"]
    )]
    check: Option<PathBuf>,

    /// Compare each test's run with its run under this other implementation, whatever the test
    /// expects and whether or not its program has errors (program.programs-with-errors): their exit
    /// statuses, their stdout, and the kind and place of a panic that ends them.
    #[arg(
        long,
        value_name = "PROGRAM",
        requires = "implementation",
        conflicts_with_all = ["diff", "parse", "check", "examples"]
    )]
    runs: Option<PathBuf>,

    /// With `--diff`, also compare each program's tests and doc examples, as `test --json`
    /// reports them, with their results under the other implementation (program.test-results).
    #[arg(long, requires = "diff")]
    tests: bool,

    /// With `--diff`, also require each run to exit with status 0, for programs that must run
    /// to their end, so that two runs that fail alike don't pass.
    #[arg(long, requires = "diff")]
    succeed: bool,

    /// Keep the results of the other implementation's commands in this directory, and answer
    /// from it a command whose binary, arguments, standard input and program are as they were.
    /// It never applies to `--impl`.
    #[arg(long, value_name = "DIR", requires = "implementation")]
    cache: Option<PathBuf>,

    /// With `--check`, compare only the diagnostics of these phases of the registry,
    /// `reference/errors.toml` (errors.registry-phases), separated by commas.
    #[arg(long, value_name = "PHASES", value_delimiter = ',', requires = "check")]
    phases: Vec<String>,

    /// Run nothing, and approve the drafts under the paths that cite only paragraphs of the
    /// Reference in this directory, moving each out of its `_pending` directory.
    #[arg(
        long,
        value_name = "REFERENCE",
        conflicts_with_all = ["implementation", "coverage", "examples", "fast"]
    )]
    approve: Option<PathBuf>,

    /// Run the Stilt examples of the Markdown documents under the paths instead of conformance
    /// tests, writing each example to a directory of its own under this one.
    #[arg(long, value_name = "DIR", conflicts_with = "coverage")]
    examples: Option<PathBuf>,

    /// Test files and directories to run.
    #[arg(value_name = "PATH", default_value = "conformance")]
    paths: Vec<PathBuf>,

    /// Run only the tests whose path contains this text.
    #[arg(long, value_name = "TEXT")]
    filter: Option<String>,

    /// Leave out the tests whose path contains this text, once for each time it is given.
    #[arg(long, value_name = "TEXT")]
    skip: Vec<String>,

    /// Run only the tests of this tier and the tiers it includes.
    #[arg(long, value_enum, default_value = "systems")]
    tier: Tier,

    /// Run only the tests of these kinds, separated by commas: `run`, `check` and `test`, for
    /// test-block tests. An implementation without `test` runs the others.
    #[arg(long, value_enum, value_name = "KINDS", value_delimiter = ',')]
    kinds: Vec<KindName>,

    /// Run a deterministic sample of about one test in ten, or in the number `--one-in` gives.
    #[arg(long)]
    fast: bool,

    /// The key that chooses the `--fast` sample. Each agent uses its own.
    #[arg(long, value_name = "KEY", default_value = "local", requires = "fast")]
    sample_key: String,

    /// The size of the `--fast` sample: about one test in this many.
    #[arg(long, value_name = "N", default_value_t = sampling::ONE_IN, requires = "fast")]
    one_in: u64,

    /// How many tests to run at once. Defaults to the number of available cores.
    #[arg(long, short, value_name = "N")]
    jobs: Option<NonZeroUsize>,

    /// Where to write the log of each failing test.
    #[arg(long, value_name = "DIR", default_value = "target/test-logs")]
    logs: PathBuf,

    /// The exit status by which the implementation declines to run a program, as one that
    /// implements part of the language does: a run test whose `run` ends with it is declined,
    /// neither passed nor failed.
    #[arg(long, value_name = "STATUS", requires = "implementation")]
    declines: Option<i32>,

    /// A file that lists, one to a line, the tests the implementation may decline: a test it
    /// declines that the file doesn't list fails, so that no test moves from passing to
    /// declined unseen.
    #[arg(long, value_name = "FILE", requires = "declines")]
    known_declines: Option<PathBuf>,

    /// Whether the implementation's panic reports name their place: `absent`, as the formal
    /// model's don't, asks no run test's `panic-at` of it, and the rest of the test.
    #[arg(
        long,
        value_enum,
        default_value = "reported",
        requires = "implementation"
    )]
    locations: Locations,

    /// Fail when running the tests takes longer than this many seconds of wall-clock time.
    #[arg(long, value_name = "SECONDS", requires = "implementation")]
    budget: Option<u64>,

    /// Kill each command after this many seconds on the processor, or twelve times as many in
    /// all. Conformance tests run under the limits of conformance.environment; larger workloads,
    /// such as the scale projects, set their own.
    #[arg(
        long,
        value_name = "SECONDS",
        default_value_t = process::TIME_LIMIT.as_secs(),
        requires = "implementation"
    )]
    time_limit: u64,
}

fn main() -> ExitCode {
    let args = Args::parse();
    let result = match (&args.coverage, &args.approve, &args.implementation) {
        (Some(reference), _, _) => report_coverage(&args, reference),
        (None, Some(reference), _) => approve(&args, reference),
        (None, None, Some(implementation)) => run(&args, implementation),
        (None, None, None) => {
            unreachable!("clap requires one of `--impl`, `--coverage` and `--approve`")
        }
    };
    match result {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(message) => {
            eprintln!("stilt-test: {message}");
            ExitCode::from(2)
        }
    }
}

/// Whether the filter, the texts to leave out and the sample select the test of this name.
fn selected(args: &Args, name: &str) -> bool {
    args.filter
        .as_ref()
        .is_none_or(|text| name.contains(text.as_str()))
        && !args.skip.iter().any(|text| name.contains(text.as_str()))
        && (!args.fast || sampling::selected(&args.sample_key, name, args.one_in))
}

/// Whether `--kinds` selects tests of this kind.
fn kind_wanted(args: &Args, kind: &Kind) -> bool {
    args.kinds.is_empty() || args.kinds.contains(&KindName::of(kind))
}

/// Whether `--kinds` selects a case: one whose spec can't be read is always run, to report it.
fn wanted(args: &Args, case: &Case) -> bool {
    case.spec.as_ref().is_err()
        || case
            .spec
            .as_ref()
            .is_ok_and(|spec| kind_wanted(args, &spec.kind))
}

/// The conformance tests under the given paths that the filter and the sample select.
fn select(args: &Args) -> Result<Vec<Test>, String> {
    Ok(discovery::discover(&args.paths)
        .map_err(|error| error.to_string())?
        .into_iter()
        .filter(|test| selected(args, &test.name))
        .collect())
}

/// The selected tests of the selected tier, or the selected examples.
fn cases(args: &Args) -> Result<Vec<Case>, String> {
    if let Some(work) = &args.examples {
        let mut cases = examples::load(&args.paths, work)?;
        cases.retain(|case| selected(args, &case.test.name) && wanted(args, case));
        return Ok(cases);
    }
    Ok(select(args)?
        .into_iter()
        .filter_map(|test| {
            let spec = match annotations::parse(&test.files, &test.header_file) {
                Ok(spec) if spec.tier > args.tier => return None,
                Ok(spec) if !kind_wanted(args, &spec.kind) => return None,
                Ok(spec) => Ok(spec),
                Err(malformed) => Err(malformed.to_string()),
            };
            Some(Case { test, spec })
        })
        .collect())
}

/// Prints which paragraphs the selected tests of the selected tier cite, and tells whether they
/// cite every paragraph that no other test checks. A malformed test cites nothing, and is
/// reported.
fn report_coverage(args: &Args, reference: &Path) -> Result<bool, String> {
    let paragraphs = Paragraphs::read(reference)?;
    let registry = Registry::new();
    let mut coverage = Coverage::default();
    let mut malformed = false;
    for test in select(args)? {
        match annotations::parse(&test.files, &test.header_file) {
            Ok(spec) if spec.tier > args.tier => {}
            Ok(spec) => coverage.add(&paragraphs, &registry, &test.name, &spec),
            Err(reason) => {
                malformed = true;
                println!("ERROR {}: {reason}", test.name);
            }
        }
    }
    let (report, complete) = coverage.report(&paragraphs, &registry, args.tier);
    print!("{report}");
    Ok(complete && !malformed)
}

/// Approves the selected drafts that may be approved, prints the report, and tells whether
/// every one was approved.
fn approve(args: &Args, reference: &Path) -> Result<bool, String> {
    let paragraphs = Paragraphs::read(reference)?;
    let (report, complete) = approval::approve(&paragraphs, &select(args)?)?;
    print!("{report}");
    Ok(complete)
}

/// Locates the implementation that `--diff`, `--parse`, `--check` or `--runs` names, with the
/// cache of `--cache` if given.
fn locate_other(
    args: &Args,
    path_env: OsString,
    time_limit: Duration,
) -> Result<Option<Implementation>, String> {
    let Some(program) = args
        .diff
        .as_deref()
        .or(args.parse.as_deref())
        .or(args.check.as_deref())
        .or(args.runs.as_deref())
    else {
        return Ok(None);
    };
    let other = Implementation::locate(program, path_env, time_limit)?;
    match &args.cache {
        Some(dir) => other.cached_in(dir).map(Some),
        None => Ok(Some(other)),
    }
}

/// Whether an implementation's panic reports name their place (program.panic-location).
#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
enum Locations {
    /// They do, as the toolchain's and the reference interpreter's do.
    Reported,
    /// They don't, as the formal model's don't.
    Absent,
}

/// Runs the selected tests, prints a line for each failure and a summary, and tells whether
/// every test passed within the budget.
fn run(args: &Args, implementation: &Path) -> Result<bool, String> {
    let path_env = std::env::var_os("PATH").unwrap_or_default();
    let time_limit = Duration::from_secs(args.time_limit);
    let implementation = Implementation::locate(implementation, path_env.clone(), time_limit)?
        .declining(args.declines)
        .locating(args.locations == Locations::Absent);
    let other = locate_other(args, path_env, time_limit)?;
    let codes = if args.phases.is_empty() {
        None
    } else {
        Some(Registry::new().codes_in(&args.phases)?)
    };
    let cases = cases(args)?;
    let logs = Logs::create(&args.logs)
        .map_err(|error| format!("cannot create {}: {error}", args.logs.display()))?;
    let jobs = args
        .jobs
        .or_else(|| thread::available_parallelism().ok())
        .map_or(1, NonZeroUsize::get);

    let start = Instant::now();
    let against = match &other {
        None => Against::Expected,
        Some(other) if args.parse.is_some() => Against::Trees(other),
        Some(other) if args.check.is_some() => Against::Checks(other, codes.as_ref()),
        Some(other) if args.runs.is_some() => Against::Alike(other),
        Some(other) => Against::Runs(
            other,
            Also {
                tests: args.tests,
                succeeds: args.succeed,
            },
        ),
    };
    let mut records = execute_all(&implementation, against, &cases, jobs);
    if let Some(file) = &args.known_declines {
        declines::fail_unknown(&mut records, file)?;
    }
    let elapsed = start.elapsed();
    let summary = report_failures(records, &logs)?;
    let over_budget = args
        .budget
        .is_some_and(|budget| elapsed > Duration::from_secs(budget));
    if over_budget {
        println!(
            "ERROR the tests took {:.1} s, over their budget of {} s",
            elapsed.as_secs_f64(),
            args.budget.unwrap_or_default()
        );
    }
    let what = if args.examples.is_some() {
        "examples"
    } else {
        "tests"
    };
    println!("{}", summary.line(cases.len(), what, elapsed));
    Ok(summary.all_passed() && !over_budget)
}

/// Counts the outcomes of the records, and for each test that didn't pass, writes its log and
/// prints its line.
fn report_failures(records: Vec<Record>, logs: &Logs) -> Result<Summary, String> {
    let mut summary = Summary::default();
    for record in records {
        summary.add(&record.outcome);
        if !matches!(record.outcome, Outcome::Passed | Outcome::Declined) {
            let log = logs
                .write(&record)
                .map_err(|error| format!("cannot write a log: {error}"))?;
            println!("{}", report::error_line(&record, &log));
        }
    }
    Ok(summary)
}

/// Runs the tests on `jobs` threads, and returns their records in the order of the tests.
fn execute_all(
    implementation: &Implementation,
    against: Against<'_>,
    cases: &[Case],
    jobs: usize,
) -> Vec<Record> {
    let results = Mutex::new((0..cases.len()).map(|_| None).collect::<Vec<_>>());
    let next = AtomicUsize::new(0);
    thread::scope(|scope| {
        for _ in 0..jobs.min(cases.len()) {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(case) = cases.get(index) else { break };
                    let record = runner::execute(implementation, against, case);
                    results.lock().unwrap_or_else(PoisonError::into_inner)[index] = Some(record);
                }
            });
        }
    });
    results
        .into_inner()
        .unwrap_or_else(PoisonError::into_inner)
        .into_iter()
        .flatten()
        .collect()
}
