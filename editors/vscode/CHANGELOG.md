# Changes

## Unreleased

- `stilt` is found in `$STILT_HOME/bin`, `~/.stilt/bin`, the `PATH`, the directories of Homebrew and Nix, and the `PATH` of your login shell, so the language server starts when VS Code was opened from the Dock or a desktop menu, whose `PATH` lacks `~/.stilt/bin`. Before, it failed with `spawn stilt ENOENT`, once for each program.
- Without Stilt, one notification offers **Install Stilt**, which runs `install.sh` in a notification that shows its progress, **Locate…**, and **Don't Ask Again**. The server starts once the install ends, with no reload. A `stilt` older than the extension needs is offered **Update**.
- The language status shows the version of `stilt` and the server's state, and **Manage** opens a menu: install or update, check for updates, restart, turn the servers off, logs, locate `stilt`, settings, the walkthrough, and **Report an Issue**.
- **Stilt: New Project…** runs `stilt new` and opens the package; **Stilt: Get Started** opens a walkthrough, which never opens by itself.
- New settings: `stilt.env`, `stilt.server.enable`, `stilt.installPrompt`, `stilt.codeLens.run`, `stilt.codeLens.debug` and `stilt.run.arguments`. `stilt.path` is empty by default, which means the extension looks by itself, and accepts `~`, `${userHome}`, `${workspaceFolder}` and `${env:NAME}`.
- A server that can't start says so once, with the reason, instead of `undefined`.

## 2027.1.0

The first release, with the compiler of the same version:

- highlighting of Stilt, and of the code blocks of Markdown that name it;
- the language server, `stilt lsp`: diagnostics as you type, each function's inferred facts beside it with the lines that cause them, hovers that explain every keyword and diagnostic code, completion, renames, formatting and code actions;
- running and debugging a program, and running its tests, from the editor.
