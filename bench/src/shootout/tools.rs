//! How each language checks, builds and runs its version of the project, with its caches under
//! the version's own directory, so that a clean step starts from none: `stilt check` and
//! `stilt build`, whose engine holds the program between commands; `cargo check` and
//! `cargo build`; `go build`, which is also Go's check, since Go has no command that only checks;
//! `dune build @check` and `dune build`, rooted at the version's directory; and `swift build`,
//! also Swift's check.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

use super::Language;

/// The tools that build the versions.
#[derive(Debug, clap::Args)]
pub(crate) struct Tools {
    /// The `stilt` that checks and builds the Stilt version.
    #[arg(long, default_value = "target/release/stilt")]
    stilt: PathBuf,
    /// The `cargo` that checks and builds the Rust version.
    #[arg(long, default_value = "cargo")]
    cargo: PathBuf,
    /// The `go` that builds the Go version.
    #[arg(long, default_value = "go")]
    go: PathBuf,
    /// The `dune` that checks and builds the OCaml version, beside the OCaml compilers it runs.
    #[arg(long, default_value = "dune")]
    dune: PathBuf,
    /// The `swift` that builds the Swift version.
    #[arg(long, default_value = "swift")]
    swift: PathBuf,
}

/// What a step runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Step {
    Check,
    Build,
}

impl Tools {
    /// The tool of `language`: a path made absolute, since each command runs in its
    /// version's directory, or a name that the `PATH` finds.
    fn tool(&self, language: Language) -> PathBuf {
        let tool = match language {
            Language::Stilt => &self.stilt,
            Language::Rust => &self.cargo,
            Language::Go => &self.go,
            Language::OCaml => &self.dune,
            Language::Swift => &self.swift,
        };
        if tool.components().count() > 1 {
            std::path::absolute(tool).unwrap_or_else(|_| tool.clone())
        } else {
            tool.clone()
        }
    }

    /// The command of `step` on the version in `dir`.
    pub(crate) fn command(&self, language: Language, step: Step, dir: &Path) -> Command {
        let mut command = Command::new(self.tool(language));
        command.current_dir(dir);
        let args: &[&str] = match (language, step) {
            (Language::Stilt, Step::Check) => &["check", "."],
            (Language::Stilt | Language::Go, _) => &["build", "-o", "program", "."],
            (Language::Rust, Step::Check) => &["check", "--quiet"],
            (Language::Rust | Language::Swift, _) => &["build", "--quiet"],
            (Language::OCaml, Step::Check) => &["build", "--root", ".", "@check"],
            (Language::OCaml, Step::Build) => &["build", "--root", ".", "./main.exe"],
        };
        command.args(args);
        self.environment(language, &mut command, dir);
        command
    }

    /// Each tool keeps what it caches under `dir`, and Go its settings too.
    fn environment(&self, language: Language, command: &mut Command, dir: &Path) {
        match language {
            Language::Stilt => {
                command.env("STILT_HOME", dir.join(".stilt-home"));
            }
            Language::Rust => {
                command.env("CARGO_TARGET_DIR", dir.join("target"));
            }
            Language::Go => go_environment(command, dir),
            // dune finds the OCaml compilers beside itself.
            Language::OCaml => {
                let dune = self.tool(Language::OCaml);
                if let Some(bin) = dune.parent().filter(|p| !p.as_os_str().is_empty()) {
                    let path = std::env::var_os("PATH").unwrap_or_default();
                    let mut paths = vec![bin.to_path_buf()];
                    paths.extend(std::env::split_paths(&path));
                    if let Ok(joined) = std::env::join_paths(paths) {
                        command.env("PATH", joined);
                    }
                }
            }
            Language::Swift => {}
        }
    }

    /// The executable that a build of the version in `dir` writes.
    pub(crate) fn executable(language: Language, dir: &Path) -> PathBuf {
        match language {
            Language::Stilt | Language::Go => dir.join("program"),
            Language::Rust => dir.join("target").join("debug").join("shoot"),
            Language::OCaml => dir.join("_build").join("default").join("main.exe"),
            Language::Swift => dir.join(".build").join("debug").join("shoot"),
        }
    }

    /// Removes what the tool of `language` cached for the version in `dir`, and stops the
    /// engine that holds the Stilt version. Go's cache holds what it compiled of Go's own
    /// library too, which every other language ships compiled, so a clean Go cache is one that
    /// holds only that: a copy of the cache that building a program of the packages `main` uses
    /// leaves.
    pub(crate) fn clean(&self, language: Language, dir: &Path) {
        if language == Language::Stilt {
            let _ = Command::new(self.tool(Language::Stilt))
                .args(["engine", "--stop", "."])
                .current_dir(dir)
                .env("STILT_HOME", dir.join(".stilt-home"))
                .output();
        }
        for cache in [
            ".stilt-home",
            "target",
            ".go-cache",
            "_build",
            ".build",
            "program",
        ] {
            let path = dir.join(cache);
            let _ = std::fs::remove_dir_all(&path);
            let _ = std::fs::remove_file(&path);
        }
        if language == Language::Go {
            let library = self.go_library(dir);
            let _ = copy_tree(&library, &dir.join(".go-cache"));
        }
    }

    /// The cache that Go's library leaves, made beside the version's directory once.
    fn go_library(&self, dir: &Path) -> PathBuf {
        let library = dir.with_file_name("go-library");
        if !library.join("cache").is_dir() {
            let program = library.join("program");
            let _ = std::fs::create_dir_all(&program);
            let _ = std::fs::write(program.join("go.mod"), "module library\n\ngo 1.22\n");
            let _ = std::fs::write(
                program.join("main.go"),
                "package main\n\nimport (\n\t\"fmt\"\n\t\"os\"\n\t\"time\"\n)\n\nfunc main() {\n\tfmt.Println(len(os.Args), time.Millisecond)\n}\n",
            );
            let mut command = Command::new(self.tool(Language::Go));
            command
                .args(["build", "-o", "program", "."])
                .current_dir(&program);
            go_environment(&mut command, &library);
            let _ = command.output();
            let _ = std::fs::rename(library.join(".go-cache"), library.join("cache"));
        }
        library.join("cache")
    }

    /// The command that runs `stilt run` on the Stilt version in `dir`, with `watch`.
    pub(crate) fn hot_run(&self, dir: &Path) -> Command {
        let mut command = Command::new(self.tool(Language::Stilt));
        command
            .args(["run", ".", "watch"])
            .current_dir(dir)
            .env("STILT_HOME", dir.join(".stilt-home"));
        command
    }

    /// The tool's version, or why it can't run.
    pub(crate) fn version(&self, language: Language) -> Result<String, String> {
        let arg: &[&str] = match language {
            Language::Go => &["version"],
            _ => &["--version"],
        };
        let output = Command::new(self.tool(language))
            .args(arg)
            .output()
            .map_err(|e| format!("cannot run {}: {e}", self.tool(language).display()))?;
        let text = String::from_utf8_lossy(if output.stdout.is_empty() {
            &output.stderr
        } else {
            &output.stdout
        })
        .into_owned();
        let line = text
            .lines()
            .find(|l| !l.trim().is_empty())
            .unwrap_or("")
            .trim();
        Ok(match language {
            Language::OCaml => format!("dune {line}"),
            Language::Swift => line
                .find("Swift version")
                .map_or(line, |i| &line[i..])
                .to_owned(),
            _ => line.to_owned(),
        })
    }

    /// How a step runs, as the report shows it.
    pub(crate) fn line(&self, language: Language, step: Step) -> String {
        let command = self.command(language, step, Path::new("."));
        let tool = Path::new(command.get_program())
            .file_name()
            .map_or_else(OsString::new, ToOwned::to_owned);
        std::iter::once(tool)
            .chain(command.get_args().map(ToOwned::to_owned))
            .map(|a| a.to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join(" ")
    }
}

/// Go keeps its cache and its modules under `dir`, reads no settings of the user's, and takes
/// no newer toolchain than its own.
fn go_environment(command: &mut Command, dir: &Path) {
    command
        .env("GOCACHE", dir.join(".go-cache"))
        .env("GOPATH", dir.join(".go-path"))
        .env("GOENV", "off")
        .env("GOTOOLCHAIN", "local")
        .env("GOFLAGS", "");
}

/// Copies the directory `from` to `to`, which doesn't exist.
fn copy_tree(from: &Path, to: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(to)?;
    for entry in std::fs::read_dir(from)? {
        let entry = entry?;
        let target = to.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            copy_tree(&entry.path(), &target)?;
        } else {
            std::fs::copy(entry.path(), target)?;
        }
    }
    Ok(())
}
