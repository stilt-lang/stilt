# /// script
# requires-python = ">=3.11"
# dependencies = ["tiktoken"]
# ///
"""Count the tokens in each version of the orders program.

Usage:
    uv run measure.py          # print the token table
    uv run measure.py --check  # also check that the runnable versions agree

`/// ex:` lines are excluded from the Stilt counts because they are tests,
and the other versions carry no tests. `--check` needs `python3`, `node` (22.6
or later) and `rustc` on PATH.
"""

import subprocess
import sys
import tempfile
from pathlib import Path

import tiktoken  # type: ignore[import]

HERE = Path(__file__).resolve().parent
PROGRAMS = HERE / "programs"
INPUTS = HERE / "inputs"
ENCODINGS = ("o200k_base", "cl100k_base")

VERSIONS = [
    ("Stilt", "orders.lt"),
    ("Stilt without the six constructs", "orders.plain.lt"),
    ("Python", "orders.py"),
    ("TypeScript", "orders.ts"),
    ("Rust", "orders.rs"),
    ("Stilt, one line per declaration", "orders.packed.txt"),
    ("Stilt skeleton view", "orders.skeleton.txt"),
]


def source_text(path: Path) -> str:
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    if path.suffix == ".lt":
        lines = [line for line in lines if not line.lstrip().startswith("/// ex:")]
    return "".join(lines)


def print_token_table() -> None:
    encoders = {name: tiktoken.get_encoding(name) for name in ENCODINGS}
    print(f"| Version | {' | '.join(ENCODINGS)} |")
    print(f"| --- |{' --- |' * len(ENCODINGS)}")
    for label, file_name in VERSIONS:
        text = source_text(PROGRAMS / file_name)
        counts = " | ".join(str(len(encoders[name].encode(text))) for name in ENCODINGS)
        print(f"| {label} | {counts} |")


def run(command: list[str]) -> tuple[str, str, int]:
    result = subprocess.run(command, capture_output=True, text=True, check=False)
    return result.stdout, result.stderr, result.returncode


def check_outputs() -> bool:
    with tempfile.TemporaryDirectory() as build_dir:
        binary = Path(build_dir) / "orders"
        subprocess.run(
            ["rustc", "--edition", "2024", "-O", "-o", str(binary), str(PROGRAMS / "orders.rs")],
            check=True,
        )
        commands = {
            "Python": ["python3", str(PROGRAMS / "orders.py")],
            "TypeScript": ["node", "--experimental-strip-types", "--no-warnings",
                           str(PROGRAMS / "orders.ts")],
            "Rust": [str(binary)],
        }
        cases = [[str(path)] for path in sorted(INPUTS.glob("*.csv"))]
        cases += [[], [str(INPUTS / "does_not_exist.csv")]]
        agree = True
        for args in cases:
            outcomes = {name: run(command + args) for name, command in commands.items()}
            if len(set(outcomes.values())) != 1:
                agree = False
                print(f"DISAGREE on {args}:")
                for name, outcome in outcomes.items():
                    print(f"  {name}: {outcome!r}")
        return agree


def main() -> int:
    print_token_table()
    if "--check" in sys.argv[1:]:
        if not check_outputs():
            return 1
        print("\nAll runnable versions produce identical stdout, stderr and exit status.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
