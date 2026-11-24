//! The languages of the comparisons, and the toolchain that builds each one's programs with its
//! release flags: its compiler, the version it reports and the flags it is given.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The stack of a program's main thread, where its language lets the build choose it: 512 MiB,
/// the most the arm64 linker gives a macOS executable's main thread, which cfold's recursion a
/// million calls deep needs. Java gets as much for its threads, and Koka's builds set their own.
const STACK: &str = "0x20000000";

/// A language that the comparisons run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Language {
    Stilt,
    Rust,
    Koka,
    OCaml,
    Haskell,
    Swift,
    Java,
    Go,
    /// jq, which a tool written in Stilt races rather than a program of a language.
    Jq,
    /// jaq, another implementation of jq's language.
    Jaq,
}

impl Language {
    /// Every language, in the order of the report's columns.
    pub(crate) const ALL: [Language; 10] = [
        Language::Stilt,
        Language::Rust,
        Language::Koka,
        Language::OCaml,
        Language::Haskell,
        Language::Swift,
        Language::Java,
        Language::Go,
        Language::Jq,
        Language::Jaq,
    ];

    pub(crate) fn name(self) -> &'static str {
        match self {
            Language::Stilt => "Stilt",
            Language::Rust => "Rust",
            Language::Koka => "Koka",
            Language::OCaml => "OCaml",
            Language::Haskell => "Haskell",
            Language::Swift => "Swift",
            Language::Java => "Java",
            Language::Go => "Go",
            Language::Jq => "jq",
            Language::Jaq => "jaq",
        }
    }

    /// The name of a program's source file in the language, or none for a tool, which is run
    /// as it is.
    pub(crate) fn source(self) -> Option<&'static str> {
        Some(match self {
            Language::Stilt => "main.lt",
            Language::Rust => "main.rs",
            Language::Koka => "main.kk",
            Language::OCaml => "main.ml",
            Language::Haskell => "Main.hs",
            Language::Swift => "main.swift",
            Language::Java => "Main.java",
            Language::Go => "main.go",
            Language::Jq | Language::Jaq => return None,
        })
    }

    /// The language named `name`, in any case.
    pub(crate) fn named(name: &str) -> Option<Language> {
        Language::ALL
            .into_iter()
            .find(|l| l.name().eq_ignore_ascii_case(name))
    }
}

/// The tools that build the programs.
#[derive(Debug, clap::Args)]
pub(crate) struct Tools {
    /// The `stilt` that builds the Stilt programs.
    #[arg(long, default_value = "target/release/stilt")]
    stilt: PathBuf,
    /// The `rustc` that builds the Rust programs.
    #[arg(long, default_value = "rustc")]
    rustc: PathBuf,
    /// The `koka` that builds the Koka programs.
    #[arg(long, default_value = "koka")]
    koka: PathBuf,
    /// The `ocamlopt` that builds the OCaml programs.
    #[arg(long, default_value = "ocamlopt")]
    ocamlopt: PathBuf,
    /// The `ghc` that builds the Haskell programs.
    #[arg(long, default_value = "ghc")]
    ghc: PathBuf,
    /// The `swiftc` that builds the Swift programs.
    #[arg(long, default_value = "swiftc")]
    swiftc: PathBuf,
    /// The `javac` that builds the Java programs.
    #[arg(long, default_value = "javac")]
    javac: PathBuf,
    /// The `java` that runs them.
    #[arg(long, default_value = "java")]
    java: PathBuf,
    /// The `go` that builds the Go programs.
    #[arg(long, default_value = "go")]
    go: PathBuf,
    /// The `cargo` that builds the Rust programs that use Rayon, with the `rustc` above.
    #[arg(long, default_value = "cargo")]
    cargo: PathBuf,
    /// The `jq` that `examples/pick` races.
    #[arg(long, default_value = "jq")]
    jq: PathBuf,
    /// The `jaq` that `examples/pick` races.
    #[arg(long, default_value = "jaq")]
    jaq: PathBuf,
}

/// A language's toolchain, found and asked its version.
#[derive(Debug)]
pub(crate) struct Toolchain {
    pub(crate) language: Language,
    pub(crate) version: String,
    tool: PathBuf,
    /// The flags its compiler gets before the source, the output and the paths of a build.
    flags: Vec<String>,
    /// The command that runs a program, before the program, for a language whose programs an
    /// executable of its own runs.
    runner: Vec<OsString>,
    /// Where builds keep what they cache, and Go its settings.
    out: PathBuf,
    /// The `cargo` that builds a Rust program of a Cargo package.
    cargo: PathBuf,
}

impl Toolchain {
    /// How a program is built, as the report shows it.
    pub(crate) fn build_line(&self) -> String {
        let tool = self.tool.file_name().map_or_else(
            || self.tool.display().to_string(),
            |n| n.to_string_lossy().into_owned(),
        );
        std::iter::once(tool)
            .chain(self.flags.iter().cloned())
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// How a program is run, for a language whose programs aren't executables of their own.
    pub(crate) fn run_line(&self) -> Option<String> {
        (self.language == Language::Java).then(|| "java -Xss512m -cp . Main".to_owned())
    }

    /// Builds `source` in the empty directory `dir`, and gives the command that runs it.
    pub(crate) fn build(&self, source: &Path, dir: &Path) -> Result<Vec<OsString>, String> {
        if matches!(self.language, Language::Jq | Language::Jaq) {
            return Ok(vec![self.tool.clone().into()]);
        }
        let exe = dir.join("program");
        let mut command = self.command();
        command.args(&self.flags).current_dir(dir);
        match self.language {
            Language::Haskell => {
                command.arg("-outputdir").arg(dir);
            }
            Language::Swift => {
                command
                    .arg("-module-cache-path")
                    .arg(self.out.join("swift-modules"));
            }
            // Koka names a module by its path from the directory it runs in, so it runs in
            // the program's, as Go does.
            Language::Koka => {
                command.arg(format!("--builddir={}", dir.join("build").display()));
            }
            Language::Stilt | Language::Rust | Language::Go | Language::Jq | Language::Jaq => {}
            // ocamlopt writes its intermediate files beside the source, so it builds a copy.
            Language::OCaml => {
                std::fs::copy(source, dir.join("main.ml"))
                    .map_err(|e| format!("cannot copy {}: {e}", source.display()))?;
            }
            Language::Java => {
                command.arg("-d").arg(dir).arg(source);
            }
        }
        match self.language {
            Language::Koka | Language::Go => {
                command.arg("-o").arg(&exe).args(source.file_name());
                command.current_dir(source.parent().unwrap_or(dir));
            }
            Language::OCaml => {
                command.arg("-o").arg(&exe).arg("main.ml");
            }
            Language::Java => {}
            _ => {
                command.arg("-o").arg(&exe).arg(source);
            }
        }
        finish(&mut command, source)?;
        let mut run = self.runner.clone();
        if self.language == Language::Java {
            run.extend(["-cp".into(), dir.into(), "Main".into()]);
        } else {
            run.push(exe.into());
        }
        Ok(run)
    }

    /// Builds the binary `bin` of the Cargo package `manifest` with its release profile and
    /// this toolchain's `rustc`, copies it into the empty directory `dir`, and gives the command
    /// that runs it.
    pub(crate) fn build_cargo(
        &self,
        manifest: &Path,
        bin: &str,
        dir: &Path,
    ) -> Result<Vec<OsString>, String> {
        let target = self.out.join("cargo");
        let mut command = Command::new(&self.cargo);
        command
            .env("RUSTC", &self.tool)
            .args(["build", "--release", "--quiet", "--locked", "--bin", bin])
            .arg("--manifest-path")
            .arg(manifest)
            .arg("--target-dir")
            .arg(&target);
        finish(&mut command, manifest)?;
        let exe = dir.join("program");
        std::fs::copy(target.join("release").join(bin), &exe)
            .map_err(|e| format!("cannot copy the {bin} that Cargo built: {e}"))?;
        Ok(vec![exe.into()])
    }

    /// A command of the toolchain's compiler, with its environment.
    fn command(&self) -> Command {
        let mut command = Command::new(&self.tool);
        match self.language {
            Language::Stilt => {
                command.env("STILT_HOME", self.out.join("stilt-home"));
            }
            // Go keeps its cache, its modules and what it records of its use under a home of
            // its own, never the user's, and takes no newer toolchain than this one.
            Language::Go => {
                command
                    .env("HOME", self.out.join("go-home"))
                    .env("GOENV", "off")
                    .env("GOTOOLCHAIN", "local")
                    .env("GOFLAGS", "")
                    .env("GOCACHE", self.out.join("go-cache"))
                    .env("GOPATH", self.out.join("go-path"));
            }
            _ => {}
        }
        command
    }
}

fn finish(command: &mut Command, source: &Path) -> Result<(), String> {
    let output = command
        .output()
        .map_err(|e| format!("cannot build {}: {e}", source.display()))?;
    if output.status.success() {
        Ok(())
    } else {
        Err(format!(
            "cannot build {}:\n{}{}",
            source.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    }
}

/// The toolchains of the languages of `wanted` that `tools` finds, and the reason each other
/// language is left out.
pub(crate) fn find(
    tools: &Tools,
    wanted: &[Language],
    out: &Path,
) -> (Vec<Toolchain>, Vec<(Language, String)>) {
    let (mut found, mut missing) = (Vec::new(), Vec::new());
    for &language in wanted {
        match toolchain(tools, language, out) {
            Ok(t) => found.push(t),
            Err(why) => missing.push((language, why)),
        }
    }
    (found, missing)
}

fn toolchain(tools: &Tools, language: Language, out: &Path) -> Result<Toolchain, String> {
    let macos = cfg!(target_os = "macos");
    let (tool, mut flags, runner): (&PathBuf, Vec<String>, Vec<OsString>) = match language {
        Language::Stilt => (&tools.stilt, strings(&["build", "--release"]), vec![]),
        Language::Rust => {
            let mut flags = strings(&["--edition", "2024", "-C", "opt-level=3"]);
            if macos {
                flags.extend(["-C".to_owned(), format!("link-arg=-Wl,-stack_size,{STACK}")]);
            }
            (&tools.rustc, flags, vec![])
        }
        Language::Koka => (&tools.koka, strings(&["-O2", "--stack=512M"]), vec![]),
        Language::OCaml => (&tools.ocamlopt, vec![], vec![]),
        Language::Haskell => (&tools.ghc, strings(&["-O2"]), vec![]),
        Language::Swift => {
            let mut flags = strings(&["-O", "-wmo"]);
            if macos {
                flags.extend(strings(&["-Xlinker", "-stack_size", "-Xlinker", STACK]));
            }
            (&tools.swiftc, flags, vec![])
        }
        Language::Java => {
            let runner = vec![located(&tools.java).into(), "-Xss512m".into()];
            (&tools.javac, vec![], runner)
        }
        Language::Go => (&tools.go, vec![], vec![]),
        Language::Jq => (&tools.jq, vec![], vec![]),
        Language::Jaq => (&tools.jaq, vec![], vec![]),
    };
    let mut toolchain = Toolchain {
        language,
        version: String::new(),
        tool: located(tool),
        flags: Vec::new(),
        runner,
        out: out.to_owned(),
        cargo: tools.cargo.clone(),
    };
    toolchain.version = version(&toolchain, tools)?;
    if language == Language::OCaml
        && first_line(toolchain.command().args(["-config-var", "flambda"]))? == "true"
    {
        flags.push("-O3".to_owned());
        toolchain.version.push_str(", with flambda");
    }
    if language == Language::Go {
        flags.insert(0, "build".to_owned());
    }
    toolchain.flags = flags;
    Ok(toolchain)
}

/// `tool`, made absolute if it names a directory, since builds run in directories of their own;
/// a bare name is looked for on the path.
fn located(tool: &Path) -> PathBuf {
    if tool.components().count() > 1 {
        std::path::absolute(tool).unwrap_or_else(|_| tool.to_owned())
    } else {
        tool.to_owned()
    }
}

fn strings(words: &[&str]) -> Vec<String> {
    words.iter().map(|&w| w.to_owned()).collect()
}

/// The version that a toolchain reports, as the report shows it.
fn version(t: &Toolchain, tools: &Tools) -> Result<String, String> {
    let line = match t.language {
        Language::OCaml => format!("OCaml {}", first_line(t.command().arg("-version"))?),
        Language::Java => first_line(Command::new(&tools.java).arg("--version"))?,
        Language::Go => first_line(t.command().arg("version"))?,
        _ => first_line(t.command().arg("--version"))?,
    };
    Ok(match t.language {
        Language::Koka => line.split(',').next().unwrap_or(&line).to_owned(),
        Language::Haskell => line
            .rsplit(' ')
            .next()
            .map_or(line.clone(), |v| format!("GHC {v}")),
        Language::Swift => line
            .find("Apple Swift")
            .or_else(|| line.find("Swift version"))
            .map_or(line.clone(), |i| line[i..].to_owned()),
        Language::Go => line.trim_start_matches("go version ").to_owned(),
        _ => line,
    })
}

/// The first line that `command` prints, on stdout or else on stderr.
fn first_line(command: &mut Command) -> Result<String, String> {
    let output = command.output().map_err(|e| {
        format!(
            "cannot run {}: {e}",
            command.get_program().to_string_lossy()
        )
    })?;
    if !output.status.success() {
        return Err(format!(
            "{} failed: {}",
            command.get_program().to_string_lossy(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let text = if output.stdout.is_empty() {
        output.stderr
    } else {
        output.stdout
    };
    Ok(String::from_utf8_lossy(&text)
        .lines()
        .next()
        .unwrap_or("")
        .trim()
        .to_owned())
}
