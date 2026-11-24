# /// script
# requires-python = ">=3.11"
# dependencies = ["tiktoken"]
# ///
"""Check that every diagnostic of the snapshot programs is short (goal short-messages): its
message and the texts of its labels make fewer than 40 tokens together, on every tokenizer of
the basket.

Usage:
    uv run tests/diagnostics/tokens.py STILT

STILT is the compiler's binary. Exits with status 1 if a diagnostic is too long.
"""

import json
import subprocess
import sys
from pathlib import Path

import tiktoken  # type: ignore[import]

HERE = Path(__file__).resolve().parent
ENCODINGS = ("o200k_base", "cl100k_base")
LIMIT = 40


def programs() -> list[Path]:
    found = []
    # `_pending/` holds drafts only while a change is reviewed; git keeps no empty directory.
    for directory in (d for d in (HERE, HERE / "_pending") if d.is_dir()):
        for path in sorted(directory.iterdir()):
            if path.name.startswith(("_", ".")) or path.suffix == ".repos":
                continue
            if path.is_dir() or path.suffix == ".lt":
                found.append(path)
    return found


def short_form(diagnostic: dict) -> str:
    labels = [label["text"] for label in diagnostic["labels"] if label["text"]]
    return " ".join([diagnostic["message"], *labels])


def main() -> int:
    stilt = sys.argv[1]
    encoders = {name: tiktoken.get_encoding(name) for name in ENCODINGS}
    too_long = 0
    for program in programs():
        output = subprocess.run(
            [stilt, "check", "--json", str(program)], capture_output=True, check=False
        )
        for diagnostic in json.loads(output.stdout)["diagnostics"]:
            text = short_form(diagnostic)
            counts = {name: len(e.encode(text)) for name, e in encoders.items()}
            if max(counts.values()) >= LIMIT:
                too_long += 1
                print(f"ERROR {program.name}: {counts} tokens: {text}")
    print(f"{len(programs())} programs, {too_long} with a diagnostic of {LIMIT} tokens or more")
    return 1 if too_long else 0


if __name__ == "__main__":
    sys.exit(main())
