# /// script
# requires-python = ">=3.11"
# ///
"""The lines of each crate that the tests ran, from the summary that `cargo llvm-cov report
--json --summary-only` writes, as the Markdown table that `just covered` prints.

A file that more than one binary compiles, as a crate's library compiled into its tests and into
`stilt`, appears once for each; its lines are counted once, from the binary that ran most of
them.
"""

import json
import sys
from collections import defaultdict
from pathlib import Path


def crate(path: str) -> str:
    """The crate a file of the repository belongs to: `compiler/NAME` or `tools/NAME`, or its
    top directory."""
    parts = Path(path).parts
    return "/".join(parts[:2]) if parts[0] in ("compiler", "tools") else parts[0]


def main() -> None:
    root = Path.cwd().resolve()
    files: dict[str, tuple[int, int, int, int]] = {}
    for export in json.loads(Path(sys.argv[1]).read_text())["data"]:
        for f in export["files"]:
            path = Path(f["filename"]).resolve()
            if not path.is_relative_to(root):
                continue
            s = f["summary"]
            counts = (
                s["lines"]["count"],
                s["lines"]["covered"],
                s["functions"]["count"],
                s["functions"]["covered"],
            )
            name = str(path.relative_to(root))
            if name not in files or counts[1] > files[name][1]:
                files[name] = counts
    crates: dict[str, list[int]] = defaultdict(lambda: [0, 0, 0, 0])
    for name, counts in files.items():
        for i, n in enumerate(counts):
            crates[crate(name)][i] += n
    print("| Crate | Lines | Lines run | Functions run |")
    print("| --- | ---: | ---: | ---: |")
    for name, (lines, run, functions, called) in sorted(crates.items(), key=lambda c: -c[1][0]):
        print(f"| `{name}` | {lines} | {100 * run / lines:.1f}% | {100 * called / max(functions, 1):.1f}% |")
    compiler = [c for n, c in crates.items() if n.startswith("compiler/")]
    lines, run = sum(c[0] for c in compiler), sum(c[1] for c in compiler)
    print(f"| The compiler's crates | {lines} | {100 * run / lines:.1f}% | |")


if __name__ == "__main__":
    main()
