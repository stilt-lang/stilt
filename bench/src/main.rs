//! `stilt-bench`, the benchmark harness (Goals, Run-time performance).
//!
//! It builds each program of the benchmark suite with `stilt build`, the debug build that
//! clean-debug-build times, with `stilt build --release`, its release build
//! (builds.release-builds), timed from an empty cache, its wrapping variant's release build, a
//! release build with the profile of a debug run (builds.profiles), and its Rust baseline under
//! Rust's release profile, checks that all of them print the same output, and times several runs
//! of each, by their cycles on a performance core at the reference machine's clock (Goals,
//! Timing). It fails when a measurement exceeds its budget in `budgets.toml`:
//! release-speed, the geometric mean of the run-time ratios of the release builds to the baselines,
//! measured without profiles, and printed with them too, against no budget, and no-outliers, the
//! largest of them; memory, the geometric mean of the release builds' peak-memory ratios to the
//! baselines'; cheap-checks, the largest ratio of a release build's time to its wrapping variant's;
//! debug-speed, the geometric mean of the debug builds'; free-success, the geometric mean of the
//! raising variants' times over the programs', and the slowest microbenchmark's raising variant;
//! small-runtime, how far an empty program's peak memory exceeds an empty Rust program's; and
//! inline-values, the boxes that the debug builds make, which hold the words of records, tuples and
//! variants on the heap.
//!
//! `stilt-bench compare` times Stilt's release builds against other languages, on the Perceus
//! paper's programs and the suite's ([`compare`]), against no budget, and `stilt-bench shootout`
//! the edit loop of the same project in each ([`shootout`]).

mod budgets;
mod compare;
mod measure;
mod release;
mod report;
mod shootout;
mod suite;

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;

use clap::{Parser, Subcommand};

use budgets::Budgets;
use report::{Micro, Row};
use suite::{Program, Suite};

/// Times Stilt's debug and release builds of the benchmark suite against their Rust baselines.
#[derive(Debug, Parser)]
#[command(args_conflicts_with_subcommands = true)]
struct Args {
    #[command(subcommand)]
    command: Option<Command>,
    /// The suite's directory.
    #[arg(long, default_value = "bench")]
    suite: PathBuf,
    /// The `stilt` that builds the Stilt programs.
    #[arg(long, default_value = "target/release/stilt")]
    stilt: PathBuf,
    /// The `rustc` that builds the baselines.
    #[arg(long, default_value = "rustc")]
    rustc: PathBuf,
    /// Where to write the executables.
    #[arg(long, default_value = "target/bench")]
    out: PathBuf,
    /// How many timed runs each executable gets (Goals, Timing).
    #[arg(long, default_value_t = 5)]
    runs: usize,
    /// Run only the programs and microbenchmarks whose name contains this text. The budgets
    /// aren't checked.
    #[arg(long)]
    filter: Option<String>,
    /// Run each program at its size of `long.toml`, at which its baseline runs for at least a
    /// second, as published results are measured, rather than at its default size.
    #[arg(long)]
    long: bool,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Print the peak resident memory of a run of a program, in bytes.
    #[command(hide = true)]
    Peak {
        exe: PathBuf,
        /// The arguments it runs with.
        args: Vec<String>,
    },
    /// Time the Perceus paper's programs and the suite's in Stilt and other languages.
    Compare(Box<compare::Args>),
    /// Time the edit loop of the same project in Stilt and other languages.
    Shootout(Box<shootout::Args>),
    /// Run a program once and print what it cost, for `compare`.
    #[command(hide = true)]
    Sample(compare::sample::SampleArgs),
}

fn main() -> ExitCode {
    let args = Args::parse();
    match &args.command {
        Some(Command::Peak { exe, args }) => return measure::print_peak(exe, args),
        Some(Command::Compare(compare)) => return compare::main(compare),
        Some(Command::Shootout(shootout)) => return shootout::main(shootout),
        Some(Command::Sample(sample)) => return compare::sample::print(sample),
        None => {}
    }
    match bench(&args) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(message) => {
            eprintln!("ERROR {message}");
            ExitCode::FAILURE
        }
    }
}

/// Measures the suite, prints the report, and tells whether every budget holds.
fn bench(args: &Args) -> Result<bool, String> {
    let text = std::fs::read_to_string(args.suite.join("budgets.toml"))
        .map_err(|e| format!("cannot read the budgets: {e}"))?;
    let budgets = Budgets::parse(&text)?;
    let suite = suite::load(&args.suite, args.filter.as_deref(), args.long)?;
    std::fs::create_dir_all(&args.out)
        .map_err(|e| format!("cannot write {}: {e}", args.out.display()))?;
    let rows = suite
        .programs
        .iter()
        .map(|p| program(args, p))
        .collect::<Result<Vec<_>, _>>()?;
    let micro = suite
        .micro
        .iter()
        .map(|p| microbenchmark(args, p))
        .collect::<Result<Vec<_>, _>>()?;
    let (stilt, rust) = empty(args, &suite)?;
    report::table(&rows, &micro, stilt, rust);
    sizes(args, &suite)?;
    if args.filter.is_some() {
        return Ok(true);
    }
    report::verdicts(&budgets, &rows, &micro, stilt, rust)
}

/// The executable of `program`'s variant `variant` in the output directory.
fn exe(args: &Args, program: &Program, variant: &str) -> PathBuf {
    args.out.join(format!("{}-{variant}", program.name))
}

/// Builds and times a program, its raising variant, its release build, its wrapping variant's, its
/// release build with a profile and its baseline, which must all print the same output, and
/// measures the peak memory of the release build and the baseline.
fn program(args: &Args, p: &Program) -> Result<Row, String> {
    let [plain, raising, release, wrapping, profiled, baseline] = [
        "stilt", "raising", "release", "wrapping", "profiled", "rust",
    ]
    .map(|v| exe(args, p, v));
    measure::build_stilt(&args.stilt, &p.plain, &plain)?;
    measure::build_stilt(&args.stilt, &p.raising, &raising)?;
    let home = args.out.join(format!("{}-home", p.name));
    let build = measure::build_release(&args.stilt, &p.plain, &release, &home)?;
    measure::build_release(&args.stilt, &p.wrapping, &wrapping, &home)?;
    let counted = args.out.join(format!("{}-profile", p.name));
    let counted = measure::profile(&args.stilt, &p.plain, &counted)?;
    measure::build_release(&args.stilt, &counted, &profiled, &home)?;
    let _ = std::fs::remove_dir_all(&home);
    measure::build_rust(&args.rustc, &p.baseline, &baseline)?;
    let twin = measure::build_twin(&args.suite, &p.name, &args.out)?;
    let mut exes = vec![&baseline, &plain, &raising, &release, &wrapping, &profiled];
    exes.extend(&twin);
    let exes: Vec<&Path> = exes.into_iter().map(PathBuf::as_path).collect();
    let (runs, outputs) = measure::timed(&exes, &p.args, args.runs)?;
    let times: Vec<Duration> = runs.iter().map(|t| t.time).collect();
    same(&p.name, "the Stilt program", &outputs[1], &outputs[0])?;
    same(&p.name, "the raising variant", &outputs[2], &outputs[0])?;
    same(&p.name, "the release build", &outputs[3], &outputs[0])?;
    same(&p.name, "the wrapping variant", &outputs[4], &outputs[0])?;
    same(
        &p.name,
        "the release build with a profile",
        &outputs[5],
        &outputs[0],
    )?;
    if let Some(output) = outputs.get(6) {
        same(
            &p.name,
            "the baseline linked with mimalloc",
            output,
            &outputs[0],
        )?;
    }
    Ok(Row {
        name: p.name.clone(),
        rust: times[0],
        stilt: times[1],
        raising: times[2],
        release: times[3],
        wrapping: times[4],
        profiled: times[5],
        twin: times.get(6).copied(),
        checked: runs[3].instructions.zip(runs[4].instructions),
        spread: runs.iter().map(|t| t.spread).fold(0.0, f64::max),
        release_peak: least_peak(args, &release, &p.args)?,
        rust_peak: least_peak(args, &baseline, &p.args)?,
        build,
        boxes: measure::boxes(&plain)?,
    })
}

/// The least peak resident memory of a run of `exe` with `program_args` among the runs that
/// `args` asks for, in bytes.
fn least_peak(args: &Args, exe: &Path, program_args: &[String]) -> Result<u64, String> {
    let mut least = u64::MAX;
    for _ in 0..=args.runs {
        least = least.min(measure::peak(exe, program_args)?);
    }
    Ok(least)
}

/// Builds and times a microbenchmark and its raising variant, which must print the same output.
fn microbenchmark(args: &Args, p: &Program) -> Result<Micro, String> {
    let (plain, raising) = (exe(args, p, "stilt"), exe(args, p, "raising"));
    measure::build_stilt(&args.stilt, &p.plain, &plain)?;
    measure::build_stilt(&args.stilt, &p.raising, &raising)?;
    let (timed, outputs) = measure::timed(&[&plain, &raising], &p.args, args.runs)?;
    same(&p.name, "the raising variant", &outputs[1], &outputs[0])?;
    Ok(Micro {
        name: p.name.clone(),
        plain: timed[0].time,
        raising: timed[1].time,
    })
}

/// The peak resident memory of the empty Stilt program and of the empty Rust program, in
/// bytes, each the least of its runs.
fn empty(args: &Args, suite: &Suite) -> Result<(u64, u64), String> {
    let (stilt, rust) = (
        exe(args, &suite.empty, "stilt"),
        exe(args, &suite.empty, "rust"),
    );
    measure::build_stilt(&args.stilt, &suite.empty.plain, &stilt)?;
    measure::build_rust(&args.rustc, &suite.empty.baseline, &rust)?;
    Ok((
        least_peak(args, &stilt, &[])?,
        least_peak(args, &rust, &[])?,
    ))
}

/// Prints the size of the empty program's executable, in a debug build and a release build, and
/// of the empty Rust program's, which no budget limits (Goals, Workloads).
fn sizes(args: &Args, suite: &Suite) -> Result<(), String> {
    let release = exe(args, &suite.empty, "stilt-release");
    let home = args.out.join("empty-home");
    measure::build_release(&args.stilt, &suite.empty.plain, &release, &home)?;
    let _ = std::fs::remove_dir_all(&home);
    let size = |path: &std::path::Path| {
        std::fs::metadata(path)
            .map(|m| m.len())
            .map_err(|e| format!("{}: {e}", path.display()))
    };
    let kib = |n: u64| n.div_ceil(1024);
    println!(
        "an empty program's executable: {} KiB in a debug build, {} KiB in a release build, and an empty Rust program's {} KiB",
        kib(size(&exe(args, &suite.empty, "stilt"))?),
        kib(size(&release)?),
        kib(size(&exe(args, &suite.empty, "rust"))?),
    );
    Ok(())
}

fn same(name: &str, what: &str, output: &[u8], expected: &[u8]) -> Result<(), String> {
    if output == expected {
        Ok(())
    } else {
        Err(format!(
            "{name}: {what} printed\n{}\nbut its baseline printed\n{}",
            String::from_utf8_lossy(output),
            String::from_utf8_lossy(expected)
        ))
    }
}

/// A time in milliseconds.
fn ms(time: Duration) -> f64 {
    time.as_secs_f64() * 1000.0
}
