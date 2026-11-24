#!/usr/bin/env python3
"""Collects the release notes from the change files in changes/.

With no argument, prints the notes of the release that VERSION names. `--check` only checks that
every change file is well formed, and `--remove` deletes them, once the release is published.
"""  # noqa: EXE001

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHANGES = ROOT / "changes"
HEADINGS = {
    "language": "Language",
    "library": "Standard library",
    "tools": "Compiler and tools",
    "fix": "Fixes",
    "docs": "Documentation",
}
KEYS = {"kind", "rfc"}


def change_files():
    return sorted(p for p in CHANGES.glob("*.md") if p.name != "README.md")


def parse(path):
    """Returns (header, text) of a change file, or raises ValueError with what is wrong."""
    head, _, text = path.read_text().partition("\n\n")
    header = {}
    for line in head.splitlines():
        key, sep, value = line.partition(":")
        if not sep or key.strip() not in KEYS or not value.strip():
            raise ValueError(f"the header line {line!r} is not `kind: …` or `rfc: …`")
        if key.strip() in header:
            raise ValueError(f"the header names {key.strip()} twice")
        header[key.strip()] = value.strip()
    if header.get("kind") not in HEADINGS:
        raise ValueError(f"kind must be one of {', '.join(HEADINGS)}")
    if "rfc" in header and not header["rfc"].isdigit():
        raise ValueError("rfc must be the RFC's number")
    if not text.strip():
        raise ValueError("there is no text after the header")
    return header, text.strip()


def collect():
    """Returns {kind: [entry]} and the list of errors."""
    entries = {kind: [] for kind in HEADINGS}
    errors = []
    for path in change_files():
        try:
            header, text = parse(path)
        except ValueError as error:
            errors.append(f"{path.relative_to(ROOT)}: {error}")
            continue
        if "rfc" in header:
            text += f" (RFC {int(header['rfc']):04d})"
        entries[header["kind"]].append(text)
    return entries, errors


def render(entries, version):
    lines = [f"# Stilt {version}", ""]
    for kind, heading in HEADINGS.items():
        if not entries[kind]:
            continue
        lines += [f"## {heading}", ""]
        for text in entries[kind]:
            first, *rest = text.splitlines()
            lines.append(f"- {first}")
            lines += [f"  {line}" if line else "" for line in rest]
        lines.append("")
    return "\n".join(lines)


def main():
    assert __doc__ is not None
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="only check the files")
    mode.add_argument("--remove", action="store_true", help="delete the files")
    args = parser.parse_args()
    if args.remove:
        for path in change_files():
            path.unlink()
        return 0
    entries, errors = collect()
    for error in errors:
        print(f"ERROR {error}", file=sys.stderr)
    if errors:
        return 1
    if args.check:
        return 0
    if not any(entries.values()):
        print("ERROR changes/ holds no change file", file=sys.stderr)
        return 1
    print(render(entries, (ROOT / "VERSION").read_text().strip()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
