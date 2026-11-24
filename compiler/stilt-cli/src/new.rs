//! `stilt new`: a package in a directory of its own, with its manifest, a module, a test and a
//! README, which checks, runs and tests as it is.

use std::path::Path;

use crate::report::Report;

/// What `stilt new PATH [--lib]` writes, as a report: the files of a package named for the
/// directory's last component, which must not exist or be empty.
pub(crate) fn command(path: &Path, lib: bool) -> Report {
    let Some(name) = path.file_name().map(|n| n.to_string_lossy().into_owned()) else {
        return Report::refuse(&format!("{} names no directory", path.display()));
    };
    if !stilt_pkg::manifest::is_package_name(&name) {
        return Report::refuse(&format!(
            "`{name}` can't name a package: a package's name is a lowercase identifier, such \
             as `report` or `csv_tools`, and not `main`, `std` or a reserved word"
        ));
    }
    if std::fs::read_dir(path).is_ok_and(|mut d| d.next().is_some()) {
        return Report::refuse(&format!(
            "{} already exists and isn't empty",
            path.display()
        ));
    }
    let edition = stilt_pkg::edition::newest().name;
    let files = [
        (
            "stilt.toml",
            format!("[package]\nname = \"{name}\"\nedition = \"{edition}\"\n"),
        ),
        ("src/main.lt", if lib { library() } else { program(&name) }),
        ("README.md", readme(&name, lib)),
    ];
    for (file, text) in &files {
        let at = path.join(file);
        let written = at
            .parent()
            .map_or(Ok(()), std::fs::create_dir_all)
            .and_then(|()| std::fs::write(&at, text));
        if let Err(e) = written {
            return Report::refuse(&format!("cannot write {}: {e}", at.display()));
        }
    }
    let what = if lib { "library" } else { "program" };
    Report {
        stdout: format!(
            "Created the {what} `{name}` in {}.\n\nNext:\n  cd {}\n  stilt {}\n",
            path.display(),
            path.display(),
            if lib { "test" } else { "run" }
        ),
        ..Report::default()
    }
}

fn program(name: &str) -> String {
    format!(
        "/// The greeting this program prints.\n\
         fn greeting(who: str) -> str {{ \"Hello, {{who}}!\" }}\n\n\
         fn main() / io {{\n  print(greeting(\"{name}\"))\n}}\n\n\
         test \"greets by name\" {{\n  assert greeting(\"you\") == \"Hello, you!\"\n}}\n"
    )
}

fn library() -> String {
    "/// The sum of `xs`.\n\
     /// ex: total([1, 2, 3]) == 6\n\
     pub fn total(xs: List<i64>) -> i64 {\n  var sum = 0\n  for x in xs { sum += x }\n  sum\n}\n\n\
     test \"an empty list sums to zero\" {\n  assert total([]) == 0\n}\n"
        .to_owned()
}

/// The README, whose `show` names a function, since a module's skeleton shows no facts
/// (facts.visibility).
fn readme(name: &str, lib: bool) -> String {
    let (run, function) = if lib {
        (
            "stilt test     # run the tests and the doc examples",
            "total",
        )
    } else {
        (
            "stilt run      # run the program\nstilt test     # run its tests",
            "greeting",
        )
    };
    format!(
        "# {name}\n\n```sh\nstilt check    # report errors and warnings\n{run}\n\
         stilt show main.{function}  # what the compiler infers about `{function}`\n```\n"
    )
}
