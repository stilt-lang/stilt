# Make it yours

| Setting | What it does |
| --- | --- |
| `stilt.path` | The `stilt` to run, found by itself when empty |
| `stilt.inlayHints.types`, `.facts`, `.causes` | Which inferred types, facts and causes show |
| `stilt.codeLens.run`, `.debug` | Which lenses show above `main` |
| `stilt.run.arguments` | The arguments of a run |
| `stilt.server.enable` | Turns the language server off, keeping the highlighting |

To keep Stilt files from formatting on save:

```json
"[stilt]": { "editor.formatOnSave": false }
```
