# /// script
# requires-python = ">=3.11"
# dependencies = ["llguidance==1.9.1"]
# ///
"""Convert a grammar in GBNF to the Lark-like format of llguidance, with llguidance's own
converter, so that `stilt-grammar check` can read it: no Rust crate reads GBNF.

Usage:
    uv run tools/grammar/gbnf_to_lark.py STILT.GBNF OUT.LARK
"""

import sys
from pathlib import Path

from llguidance.gbnf_to_lark import gbnf_to_lark  # type: ignore[import]


def main() -> None:
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    source, target = Path(sys.argv[1]), Path(sys.argv[2])
    target.write_text(gbnf_to_lark(source.read_text()))


if __name__ == "__main__":
    main()
