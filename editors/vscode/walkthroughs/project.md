# Start a program

**New Project** asks for a program or a library, a directory and a name, runs `stilt new`, and opens the package:

```text
hello/
  stilt.toml      the manifest: the package's name and edition
  README.md
  src/main.lt     main, and a test
```

A program is the nearest directory above a file that holds a `stilt.toml` or a `main.lt`, so a workspace may hold several, and each gets a language server of its own.
