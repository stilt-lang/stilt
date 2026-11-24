//! The targets `stilt build` writes executables for: aarch64 macOS, x86-64 and aarch64 Linux,
//! and WebAssembly, from any host (goals targets and cross-compilation).

use std::fmt;

/// A target of `stilt build`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Target {
    /// aarch64 macOS, whose executables link the system's `libSystem` dynamically, as every
    /// macOS executable must.
    Aarch64Macos,
    /// x86-64 Linux, whose executables are static, linked with musl, so that they run on any
    /// distribution.
    X86_64Linux,
    /// aarch64 Linux, whose executables are static too, linked with musl.
    Aarch64Linux,
    /// WebAssembly, whose executables are WASI preview 1 commands, which Cranelift doesn't
    /// write, so that every build for it goes through C (wasm.target).
    Wasm32Wasip1,
}

impl Target {
    /// Every target, in the order `stilt build --help` lists them.
    pub const ALL: [Self; 4] = [
        Self::Aarch64Macos,
        Self::X86_64Linux,
        Self::Aarch64Linux,
        Self::Wasm32Wasip1,
    ];

    /// The name `--target` takes.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Aarch64Macos => "aarch64-macos",
            Self::X86_64Linux => "x86_64-linux",
            Self::Aarch64Linux => "aarch64-linux",
            Self::Wasm32Wasip1 => "wasm32-wasip1",
        }
    }

    /// The target of `name`, if it is one.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|t| t.name() == name)
    }

    /// The target triple of Cranelift and Rust, whose runtime library is built for it.
    #[must_use]
    pub const fn triple(self) -> &'static str {
        match self {
            Self::Aarch64Macos => "aarch64-apple-darwin",
            Self::X86_64Linux => "x86_64-unknown-linux-musl",
            Self::Aarch64Linux => "aarch64-unknown-linux-musl",
            Self::Wasm32Wasip1 => "wasm32-wasip1",
        }
    }

    /// Whether Cranelift writes the target's debug builds; every build of one it doesn't write
    /// goes through C.
    #[must_use]
    pub const fn cranelift(self) -> bool {
        !matches!(self, Self::Wasm32Wasip1)
    }

    /// Whether its executables load shared libraries when they start, as aarch64 macOS's do: an
    /// x86-64 Linux executable is static, and a WebAssembly module loads none (c.loading-libraries,
    /// ).
    #[must_use]
    pub const fn loads_libraries(self) -> bool {
        matches!(self, Self::Aarch64Macos)
    }

    /// The host, if it is a target.
    #[must_use]
    pub const fn host() -> Option<Self> {
        if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
            Some(Self::Aarch64Macos)
        } else if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
            Some(Self::X86_64Linux)
        } else if cfg!(all(target_arch = "aarch64", target_os = "linux")) {
            Some(Self::Aarch64Linux)
        } else {
            None
        }
    }
}

impl fmt::Display for Target {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

#[cfg(test)]
mod tests {
    use super::Target;

    #[test]
    fn each_target_is_found_by_its_name() {
        for target in Target::ALL {
            assert_eq!(Target::from_name(target.name()), Some(target));
        }
        assert_eq!(Target::from_name("riscv64-linux"), None);
    }
}
