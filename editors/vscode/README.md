# Stilt for Visual Studio Code

Highlighting for `.lt` files, and Stilt's language server, `stilt lsp`, for each program whose files are open. A program is the nearest directory above a file that holds a `stilt.toml` or a `main.lt`, within the file's workspace folder, so a workspace may hold several, such as this repository's `examples/`, and each gets a server of its own. A file outside every program gets highlighting alone.

Each server answers with its program's engine, which the command line shares (goal `one-engine`): what the editor shows is what `stilt check` reports, buffers that aren't saved included, and `stilt test` and `stilt show` read those buffers too.

## Requirements

- **`stilt`**, on the `PATH` or where `stilt.path` names it. When it can't start, the extension says so, and offers to locate it.
- **To debug**, [LLDB DAP](https://marketplace.visualstudio.com/items?itemName=llvm-vs-code-extensions.lldb-dap) or [CodeLLDB](https://marketplace.visualstudio.com/items?itemName=vadimcn.vscode-lldb).
- **To check `stilt.toml`**, an extension that reads TOML schemas, such as [Even Better TOML](https://marketplace.visualstudio.com/items?itemName=tamasfe.even-better-toml).

## Features

### Writing

- **Diagnostics** of every file as you type, each with its code. The code links to its explanation, which `stilt show CODE` prints, and **Explain E0311** in the quick fixes opens it beside the editor. A diagnostic's fixes are quick fixes, its only fix the preferred one, which **Auto Fix** applies, and `source.fixAll.stilt` applies every fix of a file at once, as `"editor.codeActionsOnSave": { "source.fixAll.stilt": "explicit" }` does on save. Its notes, such as the template of a macro whose expansion has the error, are related information. A hole shows as information, a stale doc as deprecated, and commented-out code or an unreachable arm faded.
- **Completion** of the variables in scope with their types, the module's, the prelude's and the imports' items with their signatures and docs, a value's fields and methods after `.`, a type's variants, a module's `pub` items, modules after `use`, and the keywords that may stand there. A function completes as a call, with a placeholder for each parameter, then opens its signature; a variant completes with one for each payload, and a keyword such as `match`, `for` or `test` with its construct. It works in unfinished code, such as a `.` at the end of a line, and inside a macro use's groups, also while the macro fails on them.
- **Signature help** for calls and method calls, with the parameter being written.
- **Formatting** with `stilt fmt`'s formatter, which has no options, on save by default. A file with a syntax error is left as it is.
- **Rename** across every file of the program. The standard library's names and keywords can't be renamed.

### Reading

- **Hover.** A variable's inferred type, written as it is bound, as `var total: i64`; a field's type; a type's definition; a function's header with its inferred facts, its doc in Markdown and its examples as code; a macro use's expansion. Over a keyword, an effect, a limit or a primitive type, the form it is written in, what it means and the record that defines it, so every word of the language explains itself where it is written.
- **Inlay hints.** The inferred type of each `let`, `var` and closure parameter that writes none, and each function's inferred facts before its body, as `stilt show` writes them, such as `[consumes globals, panic, alloc, div]`. Hover over a fact to read what it means and every line that causes it, each a link to its line, and Cmd- or Ctrl-click the fact to go to the first.
- **Causes.** What the line that holds the cursor does that causes its function's facts, at the line's end, as `stilt show` writes it, such as `// an interpolated string allocates`. `stilt.inlayHints.causes` shows them at every such line, or nowhere.
- **Semantic highlighting**, from the program as checking resolved it: keywords, those that direct control apart; contextual keywords only where they act as keywords; effects, built-in and declared; types, traits, type parameters and row variables; functions, methods and macros; parameters and locals, mutable ones underlined; constants, fields, variants and modules; fragments and splices; doc comments, their examples' code, and their code in backticks; and a string's escapes, interpolation braces and format specs. The grammar colors a file the same way before the server answers, so colors don't change when it does.
- **Highlights** of a name in its file, the places that bind or assign it apart from those that read it.
- **Navigation**: go to definition, declaration and type definition, find references, the file's outline with each impl's members nested, the program's symbols, folding and selection ranges.
- **Stilt in Markdown**: the code of a ```` ```stilt ```` block of a Markdown file is highlighted as Stilt, as in the guide, `docs/guide/` of Stilt's repository.

### Showing

Each opens a read-only document beside the editor, which stays current as you type.

| Command | What it shows |
| --- | --- |
| **Stilt: Show Function with Its Facts** | `stilt show` of the function at the cursor: its inferred types and facts written in, each line followed by what it does that causes them |
| **Stilt: Show Function with Its Macros Expanded** | The same, with `--expanded`: each macro use replaced by its expansion |
| **Stilt: Show Release Report of Function** | `stilt show --release`: the instantiations the function is compiled for, the calls left on dictionaries, the reference counts and copies its code performs, and the checks proved and kept |
| **Stilt: Show Module's Skeleton** | The module's signatures and doc summaries, with its tier |
| **Stilt: Explain Diagnostic Code…** | A code's explanation, as Markdown: what it means, where it is reported, the record that defines it, its tier and the phase that checks it |

The status bar shows, beside the language's name, the state of the active file's language server, and its module with the module's tier, either of which can be pinned.

### Testing

The Test Explorer and the editor's gutter list each `test "name"`, each doc example, `/// ex:`, and each property, `/// prop:`, of each file of each program. A run runs `stilt test --json` in each program it covers, which reuses the results of tests whose code is unchanged, and reports each result where it is written. A failure shows why it failed, as `stilt test` writes it, with a comparison's two sides as a diff, and a property's shrunk counterexample with its case and seed. A program with errors runs no test, and each of its tests shows its first error. A continuous run runs again on each save.

### Running and debugging

- **Stilt: Run Program**, the **Run** above `main`, and the run button of the editor's title run `stilt run` on the active file's program in a terminal, where it reads its standard input and takes each edit in while it runs.
- **Stilt: Debug Program**, the **Debug** above `main`, and F5 in a Stilt file build the program with `stilt build`, whose executables carry DWARF debug information, and run it under LLDB DAP or CodeLLDB, with the breakpoints set in its files; with neither installed, it offers to install LLDB DAP. A `launch.json` may name a program of its own, its arguments, and the directory it runs in, `cwd`, which is the program's by default:

  ```json
  { "type": "stilt", "request": "launch", "name": "Debug calc", "program": "${workspaceFolder}/examples/calc", "args": [] }
  ```

- **Tasks.** **Tasks: Run Task** lists `check`, `build`, `test`, `run` and `fmt` for each program, and a `tasks.json` may name one, as `{ "type": "stilt", "command": "build", "args": ["--release"] }`. The problem matchers `$stilt`, `$stilt-warnings` and `$stilt-tests` read their diagnostics and failures into the Problems view.

### Manifests

`stilt.toml` is checked against its schema, of [packages.manifest](../../reference/04-programs.md#packages.manifest) and [facts.capability-grants](../../reference/15-facts.md#facts.capability-grants), by a TOML extension: a hover over a key says what it holds, completion offers the effects a dependency `may` be granted, and a key or a value the manifest can't hold is underlined as it is written. The explorer nests `docs.lock` and `default.profile` under it, and a program of one file's `NAME.profile` under its `NAME.lt`.

## Commands

| Command | What it does |
| --- | --- |
| **Stilt: Run Program** | Runs the active file's program in a terminal |
| **Stilt: Debug Program** | Builds the active file's program and debugs it |
| **Stilt: Show Function with Its Facts**, **…with Its Macros Expanded**, **Release Report of Function**, **Module's Skeleton** | Show what `stilt show` prints, as above. The editor's context menu holds them under **Stilt** |
| **Stilt: Explain Diagnostic Code…** | Opens a code's explanation, that of the diagnostic at the cursor by default |
| **Stilt: Open Program's Manifest** | Opens the active file's program's `stilt.toml` |
| **Stilt: Restart Language Servers** | Restarts every server, after a rebuild of `stilt` for example. The language status runs it too |
| **Stilt: Show Logs** | Shows the **Stilt** output, where the extension and the servers log |

## Settings

| Setting | Default | What it does |
| --- | --- | --- |
| `stilt.path` | `stilt` | The `stilt` binary that runs the servers, the commands, the tasks, the tests and the builds of the debugger, such as `target/release/stilt` of a build of this repository |
| `stilt.inlayHints.types` | `true` | Shows the inferred types of bindings |
| `stilt.inlayHints.facts` | `true` | Shows the inferred facts of functions |
| `stilt.inlayHints.causes` | `cursorLine` | Where to show what a line does that causes facts: `cursorLine`, `everyLine` or `off` |
| `stilt.codeLens.enable` | `true` | Shows **Run** and **Debug** above `main` |
| `stilt.debug.engine` | `auto` | The debugger: `lldb-dap`, `codelldb`, or `auto`, LLDB DAP when it is installed and CodeLLDB otherwise |
| `stilt.trace.server` | `off` | Writes the messages between the editor and the servers to the **Stilt** output: `messages` or `verbose` |

In Stilt files, the extension sets the editor to what `stilt fmt` writes: two spaces a level, a final newline and no trailing blanks, and it formats on save. Word-based suggestions are off, since completion knows every name in scope.

## Colors

Each semantic token falls back on a TextMate scope that themes color, the same scope the grammar gives the same text. Stilt adds the token types `boolean`, `selfKeyword`, `effect`, `rowVariable`, `fragment`, `escapeSequence`, `interpolation` and `formatSpecifier`, and the modifiers `controlFlow` and `mutable`, beside the protocol's own.

| Token | Scope | What it is |
| --- | --- | --- |
| `keyword` | `keyword.other.stilt` | A keyword that declares, binds or annotates, as `fn`, `let` or `without` |
| `keyword.controlFlow` | `keyword.control.stilt` | A keyword that directs control, as `if`, `match`, `return`, `try`, `raise` or `resume` |
| `boolean`, `selfKeyword` | `constant.language.boolean.stilt`, `variable.language.self.stilt` | `true` and `false`; `self` and `Self` |
| `effect.defaultLibrary` | `support.type.effect.stilt` | A built-in effect or limit: `io`, `raise` and `async` in a row, and `panic`, `overflow`, `alloc`, `div`, `copy`, `locks` and the capabilities after `without` |
| `effect` | `entity.name.type.effect.stilt` | An effect a program declares |
| `type`, `type.defaultLibrary` | `entity.name.type.stilt`, `support.type.primitive.stilt` | A type; a primitive type |
| `interface`, `typeParameter`, `rowVariable` | `entity.name.type.trait.stilt`, `entity.name.type.parameter.stilt`, `entity.name.type.parameter.row.stilt` | A trait; a type parameter; a row variable |
| `function`, `method`, `macro` | `entity.name.function.stilt`, `entity.name.function.method.stilt`, `entity.name.function.macro.stilt` | A function, a method, a macro |
| `parameter`, `variable`, `variable.readonly`, `fragment` | `variable.parameter.stilt`, `variable.other.stilt`, `variable.other.constant.stilt`, `variable.other.fragment.stilt` | A parameter, a local, a constant, a fragment or a splice |
| `property`, `enumMember`, `namespace` | `variable.other.property.stilt`, `variable.other.enummember.stilt`, `entity.name.namespace.stilt` | A field or a tuple's element, a variant, a module |
| `escapeSequence`, `interpolation`, `formatSpecifier` | `constant.character.escape.stilt`, `punctuation.section.embedded.stilt`, `storage.type.format.stilt` | A string's escape, the braces of its interpolation, and an interpolation's format spec |
| `*.mutable` | `markup.underline` | A `var`'s binding or an `inout` parameter, underlined |

A theme or the settings can color Stilt's tokens apart. This gives built-in effects a color of their own and keeps mutable bindings without an underline:

```json
"editor.semanticTokenColorCustomizations": {
  "rules": {
    "effect.defaultLibrary:stilt": { "foreground": "#C586C0", "italic": true },
    "*.mutable:stilt": { "underline": false }
  }
}
```

## Workspace trust

In a workspace you don't trust, the language server runs the `stilt` that your user settings name, never one a workspace's settings name, and no program, test or build runs.

## Files

| File | Contents |
| --- | --- |
| `syntaxes/stilt.tmLanguage.template.json` | The template of `stilt.tmLanguage.json`, which `just grammar-generate` writes from it with the words and tokens of the Reference ([`tools/grammar/README.md`](../../tools/grammar/README.md#words-and-tokens)) |
| `syntaxes/stilt.tmLanguage.json` | The grammar, which colors a file before the server answers, as its tokens do: the lexical structure of [lexical.tokens](../../reference/02-lexical.md#lexical.tokens), its keywords, those that direct control apart, contextual keywords and reserved words, the rows and limits of `reference/03-syntax.md`, effects and handlers ([handlers.declaring-effect](../../reference/12-effects.md#handlers.declaring-effect)), variants, as an expression names a type only before a struct literal, a function of its own or its type arguments ([types.no-type-arguments](../../reference/07-types.md#types.no-type-arguments); [declarations.no-aliases](../../reference/10-declarations.md#declarations.no-aliases)), `syntax` declarations, macro uses and fragments ([macros.uses](../../reference/16-meta.md#macros.uses)), `macro` declarations, `meta use`, quotes, and their splices and spreads ([macros.splices](../../reference/16-meta.md#macros.splices) and [macros.spreads](../../reference/16-meta.md#macros.spreads)), value parameters ([generics.value-parameters](../../reference/07-types.md#generics.value-parameters)), packs ([variadics.packs](../../reference/07-types.md#variadics.packs)), `comptime` ([meta.staging-annotations](../../reference/16-meta.md#meta.staging-annotations)), bound tests ([meta.bound-tests](../../reference/16-meta.md#meta.bound-tests)), and the code of `/// ex:` and `/// prop:` lines |
| `syntaxes/stilt.markdown.tmLanguage.json` | The grammar of Stilt code blocks in Markdown files |
| `language-configuration.json` | Comments, brackets, indentation, and `///` continued on a new line |
| `schemas/stilt.toml.json` | The schema of `stilt.toml` ([packages.manifest](../../reference/04-programs.md#packages.manifest), [packages.package-table](../../reference/04-programs.md#packages.package-table) and [packages.dependencies](../../reference/04-programs.md#packages.dependencies); [facts.capability-grants](../../reference/15-facts.md#facts.capability-grants)) |
| `src/extension.js` | Starts the extension, and wires the modules below |
| `src/programs.js` | Finds programs and runs a language client for each, restarting one that fails |
| `src/middleware.js` | The hints the settings switch off, and the links of diagnostic codes |
| `src/status.js` | The language status: the server's state, the module and its tier |
| `src/show.js` | The documents of `stilt show`, the explanations of diagnostics, and their quick fixes |
| `src/causes.js` | The causes of facts at the cursor's line |
| `src/tests.js` | The Test Explorer's tests and their runs |
| `src/tasks.js` | The tasks, and **Run Program** |
| `src/debug.js` | The debug type `stilt`, which builds a program and runs it under LLDB |
| `src/lenses.js` | **Run** and **Debug** above `main` |
| `package.json` | The manifest: the languages and grammars, the token types and the scopes each falls back on, the settings and their defaults, the commands and menus, the tasks and problem matchers, the debugger and the schema |

## Developing

From this folder, with Node.js:

```sh
npm install
npm run check      # type-checks src/ against the editor's API
npm run package    # writes stilt-0.1.0.vsix
code --install-extension stilt-0.1.0.vsix
```

A change to the grammar is made in `syntaxes/stilt.tmLanguage.template.json`, and `just grammar-generate`, from the repository's root, writes `stilt.tmLanguage.json` from it. To try a change without installing it, start the editor on a workspace with `code --extensionDevelopmentPath=$PWD WORKSPACE`, and run **Developer: Reload Window** after each change.
