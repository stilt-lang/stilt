//! The counts that macOS keeps of each process, which `proc_pid_rusage` reads, for a process of
//! the same user, running or ended and not yet reaped: of all its cores, and of its performance
//! cores alone.

use std::io;
use std::sync::OnceLock;
use std::time::Duration;

use crate::{Counts, Performance};

pub(crate) fn counts(pid: u32) -> io::Result<Counts> {
    let pid = libc::c_int::try_from(pid).map_err(io::Error::other)?;
    let mut info = RusageInfoV6 {
        uuid: [0; 16],
        fields: [0; FIELDS],
    };
    // SAFETY: with the flavor `RUSAGE_INFO_V6`, `proc_pid_rusage` writes at most a
    // `rusage_info_v6` into the buffer, which `RusageInfoV6` is laid out as, and reads nothing
    // from it.
    let status = unsafe {
        libc::proc_pid_rusage(
            pid,
            RUSAGE_INFO_V6,
            (&raw mut info).cast::<libc::rusage_info_t>(),
        )
    };
    if status != 0 {
        return Err(io::Error::last_os_error());
    }
    let field = |i: usize| info.fields[i];
    let cpu = ticks(field(USER_TIME).saturating_add(field(SYSTEM_TIME)));
    // A virtual machine, as a hosted runner is, keeps no counts of the processor: they stay 0
    // while the CPU time grows, which no processor that counts allows. The meter then gives
    // the CPU time alone, as on Linux.
    let counted = field(INSTRUCTIONS) > 0 || field(CYCLES) > 0 || cpu.is_zero();
    Ok(Counts {
        instructions: counted.then(|| field(INSTRUCTIONS)),
        cycles: counted.then(|| field(CYCLES)),
        performance: counted.then(|| Performance {
            instructions: field(P_INSTRUCTIONS),
            cycles: field(P_CYCLES),
        }),
        cpu,
    })
}

/// `struct rusage_info_v6` of `<sys/resource.h>`, macOS 13's: a UUID, then 56 counters, of which
/// the meter reads those at the indices below. `libc` stops at the fourth version, which lacks
/// the counts of the performance cores.
#[repr(C)]
struct RusageInfoV6 {
    uuid: [u8; 16],
    fields: [u64; FIELDS],
}

const RUSAGE_INFO_V6: libc::c_int = 6;
const FIELDS: usize = 56;
const USER_TIME: usize = 0;
const SYSTEM_TIME: usize = 1;
const INSTRUCTIONS: usize = 29;
const CYCLES: usize = 30;
const P_INSTRUCTIONS: usize = 38;
const P_CYCLES: usize = 39;

/// A span of the machine's ticks as time: `rusage_info` gives CPU time in the units of
/// `mach_absolute_time`, which are nanoseconds on Intel and 125/3 of one on Apple silicon.
fn ticks(n: u64) -> Duration {
    let (numer, denom) = *TIMEBASE.get_or_init(timebase);
    let nanos = u128::from(n) * u128::from(numer) / u128::from(denom.max(1));
    Duration::from_nanos(u64::try_from(nanos).unwrap_or(u64::MAX))
}

static TIMEBASE: OnceLock<(u32, u32)> = OnceLock::new();

#[allow(
    deprecated,
    reason = "libc's own declaration, which mach2 only repeats"
)]
fn timebase() -> (u32, u32) {
    let mut info = libc::mach_timebase_info { numer: 0, denom: 0 };
    // SAFETY: `mach_timebase_info` writes the two fields of the structure it is given.
    let status = unsafe { libc::mach_timebase_info(&raw mut info) };
    if status == 0 && info.denom != 0 {
        (info.numer, info.denom)
    } else {
        (1, 1)
    }
}
