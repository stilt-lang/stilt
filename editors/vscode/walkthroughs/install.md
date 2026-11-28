# Install Stilt

**Install Stilt** runs the project's installer, which downloads the latest release, checks its signature, and puts `stilt` in `~/.stilt/bin`. Nothing runs with administrator rights, and the language server starts as soon as it ends, with no reload.

The same, from a terminal:

```sh
curl -sSf https://raw.githubusercontent.com/stilt-lang/stilt/main/install.sh | sh
```

With Homebrew, `brew install stilt-lang/stilt/stilt`.

The extension finds `stilt` in `$STILT_HOME/bin`, `~/.stilt/bin`, the `PATH`, the directories of Homebrew and Nix, and the `PATH` of your login shell. To run another one, such as a build of Stilt's repository, set `stilt.path`, or use **Locate stilt**.

The language status, `{}` beside **Stilt** in the status bar, shows the version in use and the server's state. Click it for the rest: restart, logs, updates.
