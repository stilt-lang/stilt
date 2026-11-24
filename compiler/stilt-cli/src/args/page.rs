//! The documentation's page of `stilt`'s commands, `docs/commands.md`, written from the command
//! line's own help, so that it says what `stilt help` prints. A test checks that it is current, and
//! `cargo test -p stilt-cli --bin stilt -- --ignored --exact args::page::write` writes it.

use std::fmt::Write;

use clap::CommandFactory;

use super::Args;

const PAGE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/commands.md");

/// The page: a table of the commands, then each command's help.
fn page() -> String {
    let mut stilt = Args::command();
    stilt.build();
    let names: Vec<String> = stilt
        .get_subcommands()
        .filter(|c| !c.is_hide_set() && c.get_name() != "help")
        .map(|c| c.get_name().to_owned())
        .collect();
    let mut out = String::from(
        "# The command line\n\nThe commands of `stilt`, the compiler and the tools around it. This \
         page is written from `stilt`'s own help, so each command's section is what `stilt help \
         COMMAND` prints; a test of `compiler/stilt-cli` checks that it is current.\n\n\
         | Command | Does |\n| --- | --- |\n",
    );
    for name in &names {
        let about = stilt
            .find_subcommand(name)
            .and_then(|c| c.get_about())
            .map(ToString::to_string)
            .unwrap_or_default();
        let _ = writeln!(
            out,
            "| [`{name}`](#stilt-{name}) | {} |",
            about.trim_end_matches('.')
        );
    }
    let _ = write!(out, "\n```text\n{}```\n", plain(&stilt.render_long_help()));
    for name in &names {
        let command = stilt.find_subcommand_mut(name).expect("a listed command");
        let help = plain(&command.render_long_help());
        let _ = write!(out, "\n## stilt {name}\n\n```text\n{help}```\n");
    }
    out
}

/// The help's text without styles, each line without the spaces at its end.
fn plain(help: &clap::builder::StyledStr) -> String {
    help.to_string()
        .lines()
        .fold(String::new(), |mut out, line| {
            let _ = writeln!(out, "{}", line.trim_end());
            out
        })
}

#[test]
fn the_commands_page_is_current() {
    let written = std::fs::read_to_string(PAGE).unwrap_or_default();
    assert!(
        written == page(),
        "docs/commands.md is not what `stilt help` prints; run `cargo test -p stilt-cli --bin \
         stilt -- --ignored --exact args::page::write`"
    );
}

#[test]
#[ignore = "it writes docs/commands.md: cargo test -p stilt-cli --bin stilt -- --ignored --exact args::page::write"]
fn write() {
    std::fs::write(PAGE, page()).expect("docs/commands.md is written");
}
