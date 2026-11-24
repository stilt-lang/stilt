//! The release builds' part of the report: their times against the baselines' (release-speed,
//! no-outliers), their peak memory against the baselines' (memory), their times against their
//! wrapping variants', which check no overflow (cheap-checks), how long each takes to build from an
//! empty cache, which no budget limits (Goals, Compile speed), and their times with a profile
//! against the baselines', which release-speed doesn't count, since the baselines use none.

use crate::budgets::Budgets;
use crate::ms;
use crate::report::{Row, geomean, megabytes};

impl Row {
    /// The run time of the release build divided by that of the Rust a programmer would write
    /// for it (release-speed, no-outliers): the baseline, or for a program that allocates many
    /// small objects, the baseline linked with mimalloc, since a Rust program built for that
    /// links an allocator of small blocks, as a Stilt program has one (README, Allocators).
    pub(crate) fn release_ratio(&self) -> f64 {
        self.release.as_secs_f64() / self.twin.unwrap_or(self.rust).as_secs_f64()
    }

    /// The release build's peak memory divided by the baseline's (memory).
    fn memory_ratio(&self) -> f64 {
        // A peak is far below 2^52 bytes, so it converts exactly.
        #[expect(clippy::cast_precision_loss)]
        let (stilt, rust) = (self.release_peak as f64, self.rust_peak as f64);
        stilt / rust
    }

    /// The run time of the release build with a profile divided by the baseline's.
    fn profiled_ratio(&self) -> f64 {
        self.profiled.as_secs_f64() / self.rust.as_secs_f64()
    }

    /// The run time of the release build divided by its wrapping variant's.
    fn wrapping_ratio(&self) -> f64 {
        self.release.as_secs_f64() / self.wrapping.as_secs_f64()
    }

    /// What a program's checks cost (cheap-checks): the lesser of its time ratio to its
    /// wrapping variant and its ratio of instructions, where the system counts them. Time
    /// exceeds what the checks cost only when something else moves it, as the allocator does
    /// binary-trees' runs by up to 70% at the suite's sizes, and instructions exceed it only
    /// where the processor overlaps them, as it does `spectral_norm`'s; a real slowdown
    /// raises both.
    fn checks_cost(&self) -> f64 {
        self.checks_ratio()
            .map_or_else(|| self.wrapping_ratio(), |c| c.min(self.wrapping_ratio()))
    }

    /// The instructions the release build retires over those its wrapping variant retires,
    /// where the system counts them: how much code its checks add, which a processor that
    /// overlaps them with other work may hide from its time, as `spectral_norm`'s 70% more
    /// instructions run in 0.95 of its time.
    fn checks_ratio(&self) -> Option<f64> {
        let (release, wrapping) = self.checked?;
        // Counts of instructions are far below 2^52, so they convert exactly.
        #[expect(clippy::cast_precision_loss)]
        (wrapping > 0).then(|| release as f64 / wrapping as f64)
    }
}

/// Prints the release builds' times, peaks and build times, and their times with a profile.
pub(crate) fn table(rows: &[Row]) {
    println!(
        "{:<16}{:>12}{:>12}{:>10}{:>8}{:>9}{:>9}{:>8}{:>9}{:>13}{:>10}",
        "release",
        "mimalloc ms",
        "wrapping ms",
        "wrapping",
        "checks",
        "peak MB",
        "rust MB",
        "memory",
        "build s",
        "profiled ms",
        "profiled"
    );
    for r in rows {
        let twin = r
            .twin
            .map_or_else(|| "-".to_owned(), |t| format!("{:.1}", ms(t)));
        println!(
            "{:<16}{:>12}{:>12.1}{:>10.3}{:>8}{:>9.2}{:>9.2}{:>8.2}{:>9.2}{:>13.1}{:>10.2}",
            r.name,
            twin,
            ms(r.wrapping),
            r.wrapping_ratio(),
            r.checks_ratio()
                .map_or_else(|| "-".to_owned(), |c| format!("{c:.3}")),
            megabytes(r.release_peak),
            megabytes(r.rust_peak),
            r.memory_ratio(),
            r.build.as_secs_f64(),
            ms(r.profiled),
            r.profiled_ratio(),
        );
    }
    println!(
        "{:<16}{:>34.3}{:>8.3}{:>26.2}{:>32.2}",
        "geometric mean",
        geomean(rows.iter().map(Row::wrapping_ratio)),
        geomean(rows.iter().filter_map(Row::checks_ratio)),
        geomean(rows.iter().map(Row::memory_ratio)),
        geomean(rows.iter().map(Row::profiled_ratio)),
    );
}

/// The verdicts of the release builds: release-speed, no-outliers, memory and cheap-checks.
pub(crate) fn verdicts(
    budgets: &Budgets,
    rows: &[Row],
    line: &dyn Fn(bool, String) -> bool,
) -> Result<bool, String> {
    let release = geomean(rows.iter().map(Row::release_ratio));
    let rt1 = budgets.get("release-speed", "geomean")?;
    let mut all = line(
        release <= rt1,
        format!(
            "release-speed: the release builds' geometric mean run-time ratio is {release:.2}, at most {rt1}"
        ),
    );
    let (worst, without) = left_out(rows);
    all &= line(
        worst <= rt1,
        format!(
            "release-speed with each program left out: the largest mean is {worst:.2}, without {without}, at most {rt1}"
        ),
    );
    let profiled = geomean(rows.iter().map(Row::profiled_ratio));
    println!(
        "{:8}release-speed with profiles, which no budget limits: the geometric mean ratio is {profiled:.2}",
        ""
    );
    let (biggest, name) = largest(rows, Row::release_ratio);
    let rt2 = budgets.get("no-outliers", "largest")?;
    all &= line(
        biggest <= rt2,
        format!(
            "no-outliers: the release builds' largest ratio is {biggest:.2}, {name}'s, at most {rt2}"
        ),
    );
    let memory = geomean(rows.iter().map(Row::memory_ratio));
    let rt5 = budgets.get("memory", "geomean")?;
    all &= line(
        memory <= rt5,
        format!(
            "memory: the release builds' geometric mean peak-memory ratio is {memory:.2}, at most {rt5}"
        ),
    );
    let checks = geomean(rows.iter().map(Row::wrapping_ratio));
    let rt8 = budgets.get("cheap-checks", "geomean")?;
    all &= line(
        checks <= rt8,
        format!(
            "cheap-checks: the geometric mean ratio to a wrapping variant is {checks:.3}, at most {rt8}"
        ),
    );
    let (slowest, name) = largest(rows, Row::checks_cost);
    let rt8 = budgets.get("cheap-checks", "largest")?;
    all &= line(
        slowest <= rt8,
        format!(
            "cheap-checks: the largest cost of a program's checks is {slowest:.3}, {name}'s, at most {rt8}"
        ),
    );
    Ok(all)
}

/// The largest geometric mean of the release ratios with one program left out, and that
/// program's name: the verdict mustn't rest on any one program.
fn left_out(rows: &[Row]) -> (f64, &str) {
    let mut worst = (0.0, "");
    for (i, r) in rows.iter().enumerate() {
        let rest = rows.iter().enumerate().filter(|(j, _)| *j != i);
        let mean = geomean(rest.map(|(_, r)| r.release_ratio()));
        if rows.len() > 1 && mean > worst.0 {
            worst = (mean, r.name.as_str());
        }
    }
    worst
}

/// The largest of `ratio` over the rows, with its program's name.
pub(crate) fn largest(rows: &[Row], ratio: fn(&Row) -> f64) -> (f64, &str) {
    (rows.iter())
        .map(|r| (ratio(r), r.name.as_str()))
        .fold((0.0, ""), |a, b| if b.0 > a.0 { b } else { a })
}
