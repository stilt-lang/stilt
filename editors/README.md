# Editors

The extensions that bring Stilt to editors. Each highlights `.lt` files and runs the language server, `stilt lsp` (goal `one-engine`), which answers with the engine of the program the editor opened, so the editor shows what `stilt check`, `stilt show` and `stilt test` give.

| Folder | Editor |
| --- | --- |
| [`vscode/`](vscode/) | Visual Studio Code: the language server's diagnostics, completion, hovers that explain every keyword and effect, navigation, formatting, inferred types and facts with the lines that cause them, and semantic highlighting that the grammar matches before the server answers; the views of `stilt show` and the explanations of diagnostics; the Test Explorer's tests; running and debugging programs; tasks; and the schema of `stilt.toml` |
| [`tree-sitter/`](tree-sitter/) | The grammar for tree-sitter, which Neovim, Helix, Zed and other editors read, generated from the Reference |
| [`zed/`](zed/) | Zed: the language server's diagnostics, completion, hovers, navigation, formatting, semantic tokens and inlay hints, the inferred facts among them; highlighting, brackets, indentation and an outline by the tree-sitter grammar |

## Other editors

Any editor with a client of the Language Server Protocol runs `stilt lsp` as VS Code does, and gets its diagnostics, completion, hovers, navigation, formatting, semantic highlighting and inlay hints, the inferred facts among them where the editor shows inlay hints, and code lenses where it shows them: one above each test and doc example that runs `stilt test`, one above `main` that runs `stilt run`, and each result beside its lens until a file changes, a failure with why, `main` with its exit status and its last line of output. A program's root is the nearest directory that holds a `stilt.toml` or a `main.lt`. The tree-sitter grammar and its queries in [`tree-sitter/`](tree-sitter/) highlight `.lt` files in editors that read tree-sitter.

**Neovim** 0.11 or later, in `init.lua`:

```lua
vim.filetype.add({ extension = { lt = "stilt" } })
vim.lsp.config("stilt", {
  cmd = { "stilt", "lsp" },
  filetypes = { "stilt" },
  root_markers = { "stilt.toml", "main.lt" },
})
vim.lsp.enable("stilt")
vim.lsp.inlay_hint.enable(true)
vim.api.nvim_create_autocmd({ "LspAttach", "InsertLeave", "BufWritePost" }, {
  pattern = "*.lt",
  callback = function(event) vim.lsp.codelens.refresh({ bufnr = event.buf }) end,
})
vim.keymap.set("n", "<leader>cl", vim.lsp.codelens.run)
```

`<leader>cl` runs the lens of the cursor's line, and again while its job runs, which stops it; choosing a result shows all of it.

Neovim colors a file from the server's semantic tokens. For tree-sitter's highlighting too, register the grammar with nvim-treesitter's `parsers` table, with `url` this repository, `location = "editors/tree-sitter"` and `files = { "src/parser.c", "src/scanner.c" }`, and copy `tree-sitter/queries/highlights.scm` to `queries/stilt/` in your configuration.

**Helix**, in `languages.toml`, then `hx --grammar fetch` and `hx --grammar build`, and copy `tree-sitter/queries/highlights.scm` to `runtime/queries/stilt/` in Helix's configuration directory:

```toml
[language-server.stilt]
command = "stilt"
args = ["lsp"]

[[language]]
name = "stilt"
scope = "source.stilt"
file-types = ["lt"]
roots = ["main.lt", "stilt.toml"]
comment-token = "//"
indent = { tab-width = 2, unit = "  " }
language-servers = ["stilt"]

[[grammar]]
name = "stilt"
source = { git = "https://github.com/stilt-lang/stilt", rev = "main", subpath = "editors/tree-sitter" }
```

**Emacs** 29 or later, with Eglot, which comes with it and shows no code lenses:

```elisp
(define-derived-mode stilt-mode prog-mode "Stilt"
  "Major mode for Stilt, whose colors and more come from `stilt lsp'."
  (setq-local comment-start "// "))
(add-to-list 'auto-mode-alist '("\\.lt\\'" . stilt-mode))
(with-eval-after-load 'eglot
  (add-to-list 'eglot-server-programs '(stilt-mode "stilt" "lsp")))
(add-hook 'stilt-mode-hook #'eglot-ensure)
```

**Zed** reads the extension of [`zed/`](zed/): run `zed: install dev extension` from its command palette and choose that folder, and turn on its inlay hints in its settings to see the facts.
