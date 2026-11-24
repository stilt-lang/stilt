//! The counts that Linux gives of each process without the kernel's leave: its CPU time, from
//! `/proc/PID/stat`, for a process running or ended and not yet reaped. Its instructions and
//! cycles need `perf_event_open`, which most machines allow only to root, and virtual machines
//! often to nobody, so the meter doesn't count them here.

use std::io;
use std::time::Duration;

use crate::Counts;

pub(crate) fn counts(pid: u32) -> io::Result<Counts> {
    let stat = std::fs::read_to_string(format!("/proc/{pid}/stat"))?;
    // The command's name, in parentheses, may hold spaces; the fields after it don't.
    let rest = stat
        .rsplit_once(')')
        .map(|(_, rest)| rest)
        .ok_or_else(|| io::Error::other("an unreadable /proc/PID/stat"))?;
    let fields: Vec<&str> = rest.split_whitespace().collect();
    // After the name come the state, the third field, and so on: utime is the 14th field and
    // stime the 15th, in clock ticks.
    let tick = |i: usize| -> io::Result<u64> {
        fields
            .get(i)
            .and_then(|f| f.parse().ok())
            .ok_or_else(|| io::Error::other("an unreadable /proc/PID/stat"))
    };
    let ticks = tick(11)? + tick(12)?;
    Ok(Counts {
        instructions: None,
        cycles: None,
        performance: None,
        cpu: Duration::from_nanos(ticks.saturating_mul(1_000_000_000) / clock_ticks()),
    })
}

/// The clock ticks in a second, in which `/proc` gives CPU time.
fn clock_ticks() -> u64 {
    // SAFETY: `sysconf` reads a constant of the system and touches no memory of ours.
    let n = unsafe { libc::sysconf(libc::_SC_CLK_TCK) };
    u64::try_from(n).ok().filter(|&n| n > 0).unwrap_or(100)
}
