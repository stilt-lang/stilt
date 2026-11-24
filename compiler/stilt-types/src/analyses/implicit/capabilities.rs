//! The natives of `std` that have a capability (facts.capability-natives). Every other function has
//! the capabilities of what it names (facts.capabilities), which the fixed points find.

use stilt_hir::hir::{Capabilities, Capability};

use super::Key;

/// The capabilities of the native function `key`: `console` for `print`, `eprint` and the
/// console functions of `std.io`, `fs` for every native of `std.fs`, `clock` for `std.clock`'s,
/// `env` for `std.cli`'s, `rand` for `std.random.entropy`, `spawn` for `std.task.spawn`, which
/// reaches it through `async` (tasks.implicit-effects-and-capabilities), and for `Scope.spawn`
/// (tasks.implicit-effects-and-capabilities), `exec` for every native of `std.process` and `net`
/// for every native of `std.net`. `exit` has none (facts.io-and-capabilities).
pub(super) fn native(key: &Key) -> Capabilities {
    if let Key::Member(owner, name) = key
        && crate::analyses::demands::is_scope(owner)
        && &**name == "spawn"
    {
        return Capabilities::one(Capability::Spawn);
    }
    let Key::Function(item) = key else {
        return Capabilities::default();
    };
    let found = match (&*item.home, &*item.name) {
        ("std.prelude", "print" | "eprint")
        | ("std.io", "read_line" | "poll_line" | "read_all" | "write" | "ewrite" | "flush") => {
            Capability::Console
        }
        ("std.fs", _) => Capability::Fs,
        ("std.clock", "unix_ms" | "monotonic_ns" | "sleep_ms") => Capability::Clock,
        ("std.cli", "args" | "env") => Capability::Env,
        ("std.random", "entropy") => Capability::Rand,
        ("std.task", "spawn") => Capability::Spawn,
        ("std.process", _) => Capability::Exec,
        ("std.net", _) => Capability::Net,
        _ => return Capabilities::default(),
    };
    Capabilities::one(found)
}
