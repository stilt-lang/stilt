//! What a shell and `man` read of `stilt`'s commands, written from the same definitions as its
//! help: the completions of a shell, and a manual page per command. The release archive holds
//! both, under `share/`.

use std::path::Path;
use std::process::ExitCode;

use clap::CommandFactory as _;

use super::Args;

/// Prints the completions of `stilt` for `shell` on stdout.
pub(crate) fn completions(shell: clap_complete::Shell) -> ExitCode {
    let mut command = Args::command();
    clap_complete::generate(shell, &mut command, "stilt", &mut std::io::stdout());
    ExitCode::SUCCESS
}

/// Writes `stilt.1` and a page per visible command, as `stilt-check.1`, into `dir`.
pub(crate) fn manual(dir: &Path) -> ExitCode {
    match write_pages(dir) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("stilt: {}: {e}", dir.display());
            ExitCode::from(crate::NOT_A_PROGRAM)
        }
    }
}

fn write_pages(dir: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(dir)?;
    let command = Args::command();
    page(dir, "stilt", command.clone())?;
    for sub in command.get_subcommands().filter(|c| !c.is_hide_set()) {
        let name = format!("stilt-{}", sub.get_name());
        page(dir, &name, sub.clone().name(name.clone()))?;
    }
    Ok(())
}

fn page(dir: &Path, name: &str, command: clap::Command) -> std::io::Result<()> {
    let mut out = Vec::new();
    clap_mangen::Man::new(command).render(&mut out)?;
    std::fs::write(dir.join(format!("{name}.1")), out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_visible_command_has_a_page_and_completions_name_them() {
        let dir = std::env::temp_dir().join(format!("stilt-manual-{}", std::process::id()));
        write_pages(&dir).unwrap();
        let page = std::fs::read_to_string(dir.join("stilt-check.1")).unwrap();
        assert!(page.contains("stilt\\-check"), "{page}");
        assert!(dir.join("stilt.1").exists());
        assert!(!dir.join("stilt-engine.1").exists());
        std::fs::remove_dir_all(&dir).unwrap();
        let mut out = Vec::new();
        let mut command = Args::command();
        clap_complete::generate(clap_complete::Shell::Zsh, &mut command, "stilt", &mut out);
        let script = String::from_utf8(out).unwrap();
        assert!(script.contains("migrate"));
    }
}
