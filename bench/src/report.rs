//! The report of a run of the suite: a table of times, and a verdict for each goal.

use std::time::Duration;

use crate::budgets::Budgets;
use crate::ms;

/// The times of a program, its raising variant, its release build, the release build of its
/// wrapping variant, its release build with a profile and its baseline, the release build's and the
/// baseline's peak memory, and how long the release build took.
#[derive(Debug)]
pub(crate) struct Row {
    pub(crate) name: String,
    pub(crate) rust: Duration,
    pub(crate) stilt: Duration,
    pub(crate) raising: Duration,
    pub(crate) release: Duration,
    pub(crate) wrapping: Duration,
    pub(crate) profiled: Duration,
    /// The baseline's time linked with mimalloc, for a program that allocates many small objects
    /// and has such a twin in `compare/alloc/` (README, Allocators).
    pub(crate) twin: Option<Duration>,
    /// The instructions a run of the release build and of its wrapping variant retires, where
    /// the system counts them (cheap-checks).
    pub(crate) checked: Option<(u64, u64)>,
    /// The largest spread of the times of its six versions' runs: the slowest run's time less the
    /// fastest's, over their mean.
    pub(crate) spread: f64,
    /// The least peak resident memory of the release build's runs, and of the baseline's, in bytes.
    pub(crate) release_peak: u64,
    pub(crate) rust_peak: u64,
    /// How long `stilt build --release` took, with an empty cache.
    pub(crate) build: Duration,
    /// The boxes a run of the debug build makes (inline-values).
    pub(crate) boxes: u64,
}

impl Row {
    /// The run time of the debug build divided by the baseline's (debug-speed).
    fn ratio(&self) -> f64 {
        self.stilt.as_secs_f64() / self.rust.as_secs_f64()
    }

    /// The run time of the raising variant divided by the program's (free-success).
    fn raising_ratio(&self) -> f64 {
        self.raising.as_secs_f64() / self.stilt.as_secs_f64()
    }
}

/// The times of a microbenchmark and its raising variant.
#[derive(Debug)]
pub(crate) struct Micro {
    pub(crate) name: String,
    pub(crate) plain: Duration,
    pub(crate) raising: Duration,
}

impl Micro {
    fn ratio(&self) -> f64 {
        self.raising.as_secs_f64() / self.plain.as_secs_f64()
    }
}

pub(crate) fn geomean(ratios: impl Iterator<Item = f64>) -> f64 {
    let (sum, count) = ratios.fold((0.0, 0.0), |(s, n), r| (s + r.ln(), n + 1.0));
    if count == 0.0 {
        1.0
    } else {
        (sum / count).exp()
    }
}

pub(crate) fn megabytes(bytes: u64) -> f64 {
    // A peak is far below 2^52 bytes, so it converts exactly.
    #[expect(clippy::cast_precision_loss)]
    let bytes = bytes as f64;
    bytes / 1_048_576.0
}

/// Prints the times of every program and microbenchmark, and the empty programs' memory.
pub(crate) fn table(rows: &[Row], micro: &[Micro], stilt: u64, rust: u64) {
    println!(
        "{:<16}{:>10}{:>11}{:>8}{:>12}{:>10}{:>12}{:>9}{:>8}{:>9}",
        "program",
        "rust ms",
        "stilt ms",
        "ratio",
        "raising ms",
        "raising",
        "release ms",
        "release",
        "boxes",
        "spread"
    );
    for r in rows {
        println!(
            "{:<16}{:>10.1}{:>11.1}{:>8.2}{:>12.1}{:>10.3}{:>12.1}{:>9.2}{:>8}{:>8.1}%",
            r.name,
            ms(r.rust),
            ms(r.stilt),
            r.ratio(),
            ms(r.raising),
            r.raising_ratio(),
            ms(r.release),
            r.release_ratio(),
            r.boxes,
            r.spread * 100.0
        );
    }
    println!(
        "{:<16}{:>29.2}{:>22.3}{:>21.2}",
        "geometric mean",
        geomean(rows.iter().map(Row::ratio)),
        geomean(rows.iter().map(Row::raising_ratio)),
        geomean(rows.iter().map(Row::release_ratio))
    );
    println!(
        "{:<16}{:>10}{:>11}{:>8}",
        "microbenchmark", "plain ms", "raising ms", "ratio"
    );
    for m in micro {
        println!(
            "{:<16}{:>10.1}{:>11.1}{:>8.3}",
            m.name,
            ms(m.plain),
            ms(m.raising),
            m.ratio()
        );
    }
    println!(
        "an empty program's peak memory: {:.2} MB, and an empty Rust program's {:.2} MB",
        megabytes(stilt),
        megabytes(rust)
    );
    crate::release::table(rows);
}

/// Prints one line per goal, and tells whether each holds.
pub(crate) fn verdicts(
    budgets: &Budgets,
    rows: &[Row],
    micro: &[Micro],
    stilt: u64,
    rust: u64,
) -> Result<bool, String> {
    let line = |met: bool, text: String| {
        println!("{} {text}", if met { "MET    " } else { "NOT MET" });
        met
    };
    let mut all = crate::release::verdicts(budgets, rows, &line)?;
    let speed = geomean(rows.iter().map(Row::ratio));
    let rt3 = budgets.get("debug-speed", "geomean")?;
    all &= line(
        speed <= rt3,
        format!(
            "debug-speed: the debug builds' geometric mean run-time ratio is {speed:.2}, at most {rt3}"
        ),
    );
    let (slowest, name) = crate::release::largest(rows, Row::ratio);
    let rt3_one = budgets.get("debug-speed", "largest")?;
    all &= line(
        slowest <= rt3_one,
        format!(
            "debug-speed: the debug builds' largest ratio is {slowest:.2}, {name}'s, at most {rt3_one}"
        ),
    );
    let raising = geomean(rows.iter().map(Row::raising_ratio));
    let rt4 = budgets.get("free-success", "geomean")?;
    all &= line(
        raising <= rt4,
        format!(
            "free-success: the raising variants' geometric mean ratio is {raising:.3}, at most {rt4}"
        ),
    );
    let slowest = micro.iter().map(Micro::ratio).fold(1.0, f64::max);
    let rt4_micro = budgets.get("free-success", "microbenchmark")?;
    all &= line(
        slowest <= rt4_micro,
        format!(
            "free-success: the slowest microbenchmark's raising ratio is {slowest:.3}, at most {rt4_micro}"
        ),
    );
    let above = megabytes(stilt.saturating_sub(rust));
    let rt9 = budgets.get("small-runtime", "megabytes")?;
    all &= line(
        above <= rt9,
        format!(
            "small-runtime: an empty program's peak memory is {above:.2} MB above Rust's, at most {rt9} MB"
        ),
    );
    let boxes: u64 = rows.iter().map(|r| r.boxes).sum();
    let rt10 = budgets.get("inline-values", "boxes")?;
    // A count is far below 2^52, so it converts exactly.
    #[expect(clippy::cast_precision_loss)]
    let counted = boxes as f64;
    all &= line(
        counted <= rt10,
        format!(
            "inline-values: the debug builds made {boxes} boxes of records, tuples and variants, at most {rt10}"
        ),
    );
    Ok(all)
}
