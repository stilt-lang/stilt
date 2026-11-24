//! The machine the comparisons ran on, and how busy it was, as the system reports them.

use std::process::Command;

/// The machine: its processor, cores, memory and system.
#[derive(Debug)]
pub(crate) struct Machine {
    pub(crate) processor: String,
    pub(crate) cores: String,
    /// Its memory, in bytes.
    pub(crate) memory: u64,
    pub(crate) system: String,
}

/// The machine this runs on.
pub(crate) fn describe() -> Machine {
    if cfg!(target_os = "macos") {
        let sysctl = |name: &str| output("sysctl", &["-n", name]);
        let performance = sysctl("hw.perflevel0.physicalcpu");
        let efficiency = sysctl("hw.perflevel1.physicalcpu");
        let cores = if efficiency.is_empty() {
            format!("{} cores", sysctl("hw.physicalcpu"))
        } else {
            format!("{performance} performance and {efficiency} efficiency cores")
        };
        Machine {
            processor: sysctl("machdep.cpu.brand_string"),
            cores,
            memory: sysctl("hw.memsize").parse().unwrap_or(0),
            system: format!("macOS {}", output("sw_vers", &["-productVersion"])),
        }
    } else {
        let info = std::fs::read_to_string("/proc/cpuinfo").unwrap_or_default();
        let processor = info
            .lines()
            .find_map(|l| l.strip_prefix("model name"))
            .map(|l| l.trim_start_matches([' ', '\t', ':']).to_owned())
            .unwrap_or_default();
        let memory = std::fs::read_to_string("/proc/meminfo")
            .unwrap_or_default()
            .lines()
            .find_map(|l| l.strip_prefix("MemTotal:"))
            .and_then(|l| l.trim().trim_end_matches(" kB").parse::<u64>().ok())
            .map_or(0, |kb| kb * 1024);
        let cores = std::thread::available_parallelism().map_or(0, std::num::NonZero::get);
        Machine {
            processor,
            cores: format!("{cores} cores"),
            memory,
            system: output("uname", &["-sr"]),
        }
    }
}

/// The system's load averages over the last 1, 5 and 15 minutes.
pub(crate) fn load() -> String {
    let text = if cfg!(target_os = "macos") {
        output("sysctl", &["-n", "vm.loadavg"])
    } else {
        std::fs::read_to_string("/proc/loadavg").unwrap_or_default()
    };
    text.trim_matches(['{', '}', ' ', '\n'])
        .split_whitespace()
        .take(3)
        .collect::<Vec<_>>()
        .join(", ")
}

/// The date and time now, in UTC.
pub(crate) fn now() -> String {
    output("date", &["-u", "+%Y-%m-%d %H:%M UTC"])
}

/// What `program` prints, trimmed, in the C locale, so that numbers have decimal points; empty
/// when it can't run.
fn output(program: &str, args: &[&str]) -> String {
    Command::new(program)
        .args(args)
        .env("LC_ALL", "C")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned())
        .unwrap_or_default()
}
