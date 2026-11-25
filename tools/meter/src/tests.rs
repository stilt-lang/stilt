use std::process::Command;
use std::time::Duration;

use super::{Counts, Performance, REFERENCE_CLOCK, own, run};

/// Busy work that the optimizer can't drop.
fn spin(n: u64) -> u64 {
    (0..n).fold(0u64, |acc, i| {
        std::hint::black_box(acc.wrapping_mul(31).wrapping_add(i))
    })
}

#[test]
fn own_counts_grow_with_work() {
    let before = own().expect("the meter reads this process");
    std::hint::black_box(spin(200_000_000));
    let spent = own().expect("the meter reads this process").since(before);
    assert!(spent.cpu > Duration::from_millis(10), "{spent:?}");
    // macOS counts them, but not in a virtual machine, as a hosted runner is.
    if let (Some(instructions), Some(cycles)) = (spent.instructions, spent.cycles) {
        assert!(instructions > 200_000_000, "{spent:?}");
        assert!(cycles > 0, "{spent:?}");
    }
}

/// The CPU time from the counts is the one `ps` reports, so the units of `rusage_info` are read
/// right.
#[test]
fn cpu_time_agrees_with_ps() {
    std::hint::black_box(spin(300_000_000));
    let ours = own().expect("the meter reads this process").cpu;
    let usage = rusage_self();
    let ratio = ours.as_secs_f64() / usage.as_secs_f64();
    assert!((0.8..1.25).contains(&ratio), "meter {ours:?}, ps {usage:?}");
}

/// This process's CPU time as `ps` reports it.
fn rusage_self() -> Duration {
    let output = Command::new("ps")
        .args(["-o", "time=", "-p"])
        .arg(std::process::id().to_string())
        .output()
        .expect("ps runs");
    // `ps` writes `[[hh:]mm:]ss.cc`, with a comma for a decimal point in some locales.
    let seconds = String::from_utf8_lossy(&output.stdout)
        .trim()
        .replace(',', ".")
        .split(':')
        .fold(0.0, |acc, part| {
            acc * 60.0 + part.parse::<f64>().unwrap_or(0.0)
        });
    Duration::from_secs_f64(seconds)
}

#[test]
fn a_child_is_counted_once_it_ends() {
    let mut command = Command::new("/bin/sh");
    command.args([
        "-c",
        "i=0; while [ $i -lt 20000 ]; do i=$((i+1)); done; echo done",
    ]);
    let (output, counts) = run(&mut command).expect("the child runs");
    assert!(output.status.success());
    assert_eq!(output.stdout, b"done\n");
    assert!(counts.cpu > Duration::ZERO, "{counts:?}");
    if let Some(instructions) = counts.instructions {
        assert!(instructions > 1_000_000, "{counts:?}");
    }
}

#[test]
fn cycles_are_time_at_the_reference_clock() {
    let counts = Counts {
        instructions: Some(1),
        cycles: Some(4_000_000_000),
        performance: None,
        cpu: Duration::from_secs(9),
    };
    assert_eq!(REFERENCE_CLOCK, 4.0e9);
    assert_eq!(counts.time(), Duration::from_secs(1));
    let uncounted = Counts {
        cycles: None,
        ..counts
    };
    assert_eq!(uncounted.time(), Duration::from_secs(9));
}

#[test]
fn spans_subtract_and_add() {
    let a = Counts {
        instructions: Some(10),
        cycles: Some(20),
        performance: None,
        cpu: Duration::from_millis(30),
    };
    let b = Counts {
        instructions: Some(3),
        cycles: None,
        performance: None,
        cpu: Duration::from_millis(5),
    };
    assert_eq!(a.since(b).instructions, Some(7));
    assert_eq!(a.since(b).cycles, None);
    assert_eq!(a.plus(b).cpu, Duration::from_millis(35));
}

#[test]
fn idle_time_is_the_lesser_bound() {
    let counts = Counts {
        instructions: Some(1),
        cycles: Some(8_000_000_000),
        performance: None,
        cpu: Duration::from_secs(2),
    };
    assert_eq!(
        counts.idle_time(Duration::from_secs(5)),
        Duration::from_secs(2)
    );
    assert_eq!(
        counts.idle_time(Duration::from_secs(1)),
        Duration::from_secs(1)
    );
}

/// A run that spent half its instructions on the efficiency cores counts the cycles a
/// performance core would have run for all of them.
#[test]
fn performance_cycles_scale_to_every_instruction() {
    let counts = Counts {
        instructions: Some(1_000),
        cycles: Some(900),
        performance: Some(Performance {
            instructions: 500,
            cycles: 250,
        }),
        cpu: Duration::ZERO,
    };
    assert_eq!(counts.performance_cycles(), Some(500));
    let on_efficiency_cores_only = Counts {
        performance: Some(Performance::default()),
        ..counts
    };
    assert_eq!(on_efficiency_cores_only.performance_cycles(), Some(900));
}
