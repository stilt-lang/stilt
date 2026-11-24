#!/usr/bin/env python3
"""Write the Modules and Theorems tables of `formal/README.md` from the proof map.

`tables.py MAP README` reads `map.json`, which `just proof-map` writes from the compiled model,
and replaces the text between `<!-- modules -->` and `<!-- /modules -->`, and between
`<!-- theorems -->` and `<!-- /theorems -->`, with a table of each module, its doc's first
sentence and the paragraphs its declarations cite, and tables of the checks of
`Program.Accepted` and of the promises of `Program.Promises`, each promise with the lemmas
`soundness` gives it from. `--check` fails, writing nothing, when the README isn't
what the map gives, so the tables can't drift from the model's doc comments.
"""

import json
import re
import sys
from pathlib import Path


def sentence(doc: str) -> str:
    """The first sentence of a doc's first paragraph, its heading left out, on one line."""
    paras = [p for p in re.split(r"\n\s*\n", doc or "") if p.strip() and not p.lstrip().startswith("#")]
    if not paras:
        heading = (doc or "").strip().lstrip("#").strip()
        return heading.splitlines()[0] if heading else ""
    text = " ".join(paras[0].split())
    end = re.search(r"(?<!e\.g)(?<!i\.e)\.(\s|$)", text)
    return text[: end.start() + 1] if end else text


def chapter_of(chapters: list) -> dict:
    """Each paragraph's chapter file, by its ID."""
    return {p["id"] if isinstance(p, dict) else p: c["file"] for c in chapters for p in c["paragraphs"]}


def link(pid: str, files: dict) -> str:
    file = files.get(pid)
    return f"[{pid}](../reference/{Path(file).name}#{pid})" if file else f"`{pid}`"


def modules(m: dict, files: dict) -> list[str]:
    cited: dict[str, list[str]] = {}
    for d in m["decls"]:
        for pid in d["c"]:
            seen = cited.setdefault(d["m"], [])
            if pid not in seen:
                seen.append(pid)
    rows = ["| Module | Contents | Records |", "| --- | --- | --- |"]
    for mod in sorted(m["modules"], key=lambda x: x["n"]):
        records = ", ".join(link(p, files) for p in cited.get(mod["n"], []))
        rows.append(f"| [`Stilt.{mod['n']}`]({Path(mod['f']).relative_to('formal')}) | {sentence(mod['d'])} | {records} |")
    return rows


def one_line(doc: str) -> str:
    return " ".join((doc or "").split())


def theorems(m: dict) -> list[str]:
    """The checks of `Program.Accepted`, then the promises of `Program.Promises`, each with the
    lemmas that the proof of `soundness` gives it from."""
    decls = m["decls"]
    rows = ["| Check of `Program.Accepted` | What it asks |", "| --- | --- |"]
    rows += [f"| `{a['n']}` | {one_line(a['d'])} |" for a in m["accepted"]]
    rows += ["", "| Promise of `Program.Promises` | What every run keeps | From |", "| --- | --- | --- |"]
    for p in m["promises"]:
        lemmas = ", ".join(f"`{decls[i]['n']}`" for i in p["from"] if decls[i]["k"] == "theorem") or "its own proof"
        rows.append(f"| `{p['n']}` | {one_line(p['d'])} | {lemmas} |")
    return rows


def replace(text: str, tag: str, rows: list[str]) -> str:
    pattern = re.compile(rf"(<!-- {tag} -->\n)(?:.*?\n)?(<!-- /{tag} -->)", re.S)
    if not pattern.search(text):
        sys.exit(f"ERROR formal/README.md has no <!-- {tag} --> section")
    return pattern.sub(lambda g: g.group(1) + "\n".join(rows) + "\n" + g.group(2), text)


def main() -> None:
    args = [a for a in sys.argv[1:] if a != "--check"]
    m = json.loads(Path(args[0]).read_text())
    readme = Path(args[1])
    old = readme.read_text()
    files = chapter_of(m["chapters"])
    new = replace(replace(old, "modules", modules(m, files)), "theorems", theorems(m))
    if "--check" in sys.argv:
        if new != old:
            sys.exit("ERROR formal/README.md's tables aren't what the proof map gives: run `just proof-map`")
    elif new != old:
        readme.write_text(new)


if __name__ == "__main__":
    main()
