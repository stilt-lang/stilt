//! Zed's extension for Stilt. Zed reads the language, its grammar and its queries from the
//! extension's files; this code gives Zed the command of its language server, `stilt lsp`,
//! which it finds on the `PATH` of the project's shell.

use zed_extension_api::{self as zed, Command, LanguageServerId, Result, Worktree};

/// What Zed asks of the extension. It holds nothing, since the server is the `stilt` the user
/// installed.
#[derive(Debug)]
struct Stilt;

impl zed::Extension for Stilt {
    fn new() -> Self {
        Stilt
    }

    fn language_server_command(
        &mut self,
        _language_server_id: &LanguageServerId,
        worktree: &Worktree,
    ) -> Result<Command> {
        let command = worktree.which("stilt").ok_or_else(|| {
            "`stilt` isn't on the PATH of this project's shell, so `stilt lsp` can't start: \
             install Stilt, and add the folder holding `stilt`, `~/.stilt/bin` for its \
             installer, to the PATH"
                .to_string()
        })?;
        Ok(Command {
            command,
            args: vec!["lsp".to_string()],
            env: worktree.shell_env(),
        })
    }
}

zed::register_extension!(Stilt);
