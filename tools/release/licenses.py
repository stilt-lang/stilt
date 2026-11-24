#!/usr/bin/env python3
"""Write `THIRD-PARTY-LICENSES`, the notices of everything a release's archive holds that Stilt
didn't write, and of what the programs it builds link.

`licenses.py OUT` lists the toolchain's parts that come from elsewhere, each with its licence and
what holds it, then the crates that `stilt` and its runtime library are built from, as
`cargo metadata` resolves them for the normal dependencies of `stilt-cli` and `stilt-runtime`
(the crates `sbom.py` lists), each with its licence, and then each distinct licence text those
crates ship, once, with the crates that ship it. It reads the checkout and the crates' sources
that cargo has fetched, so the same commit gives the same file.
"""

import json
import subprocess
import sys
from pathlib import Path

ROOTS = ("stilt-cli", "stilt-runtime")
NOTICES = ("LICENSE", "LICENCE", "COPYING", "NOTICE", "COPYRIGHT", "UNLICENSE")

# The parts of the toolchain that come from elsewhere: what each is, its licence, and where it
# ends up. Each built program links its target's runtime library, which holds Rust's standard
# library and the runtime's crates below.
PARTS = (
    ("rust-lld and libLLVM", "The linker of release and debug builds, from Rust's toolchain",
     "Apache-2.0 WITH LLVM-exception", "the toolchain"),
    ("clang", "The C compiler of release builds, fetched the first time one runs, as LLVM releases it",
     "Apache-2.0 WITH LLVM-exception", "the toolchain, once fetched"),
    ("musl", "The C library of Linux programs: libc.a, crt1.o, crti.o and crtn.o",
     "MIT", "every program built for Linux, linked statically"),
    ("LLVM's libunwind, crtbegin.o and crtend.o", "Unwinding and startup for Linux programs",
     "Apache-2.0 WITH LLVM-exception", "every program built for Linux, linked statically"),
    ("wasi-libc", "The C library of WebAssembly programs",
     "Apache-2.0 WITH LLVM-exception OR Apache-2.0 OR MIT", "every WebAssembly program"),
    ("compiler-rt's builtins", "libclang_rt.builtins.a, the arithmetic helpers of WebAssembly programs",
     "Apache-2.0 WITH LLVM-exception", "every WebAssembly program"),
    ("Binaryen", "wasm-opt, the optimizer of WebAssembly release builds",
     "Apache-2.0", "the toolchain"),
    ("Rust's standard library", "The library `stilt` and each target's runtime library are built on",
     "MIT OR Apache-2.0", "`stilt`, and every program, linked statically"),
)

def crates(repo: Path) -> list[dict]:
    """The crates from elsewhere reachable from the roots through normal dependencies, each once."""
    meta = json.loads(
        subprocess.run(
            ["cargo", "metadata", "--format-version", "1", "--locked"],
            cwd=repo, check=True, capture_output=True, text=True,
        ).stdout
    )
    packages = {p["id"]: p for p in meta["packages"]}
    nodes = {n["id"]: n for n in meta["resolve"]["nodes"]}
    todo = [i for i, p in packages.items() if p["name"] in ROOTS and p["source"] is None]
    seen: dict[str, dict] = {}
    while todo:
        pid = todo.pop()
        if pid in seen:
            continue
        seen[pid] = packages[pid]
        for dep in nodes[pid]["deps"]:
            if any(k["kind"] is None for k in dep["dep_kinds"]):
                todo.append(dep["pkg"])
    ours = [p for p in seen.values() if p["source"] is not None]
    return sorted(ours, key=lambda p: (p["name"], p["version"]))


def notices(package: dict) -> list[str]:
    """The texts of the licence and notice files at the root of a crate's source."""
    root = Path(package["manifest_path"]).parent
    files = sorted(
        f for f in root.iterdir()
        if f.is_file() and f.name.upper().startswith(NOTICES)
    )
    return [f.read_text(errors="replace").strip() for f in files]


def main() -> None:
    out = Path(sys.argv[1])
    repo = Path(__file__).resolve().parents[2]
    lines = [
        "THIRD-PARTY LICENSES",
        "",
        "Stilt is licensed under the MIT license or the Apache License 2.0, at your option",
        "(LICENSE-MIT, LICENSE-APACHE). This file gives the licences of what this archive holds",
        "that Stilt didn't write, and of what the programs it builds link. Beside it, rust/ holds",
        "the notices that Rust's toolchain ships: COPYRIGHT-library.html for its standard library",
        "and musl, and licenses/ for the licence texts named here, LLVM's exception among them.",
        "Where a part offers a choice of licences, Stilt takes it under the first.",
        "",
        "== The toolchain's parts ==",
        "",
    ]
    for name, what, licence, where in PARTS:
        lines += [f"{name}: {what}.", f"    Licence: {licence}. In: {where}.", ""]
    found = crates(repo)
    lines += ["== The crates of `stilt` and of the runtime library ==", ""]
    lines += [f"{p['name']} {p['version']}: {p.get('license') or 'see its notice below'}" for p in found]
    texts: dict[str, list[str]] = {}
    for p in found:
        for text in notices(p):
            texts.setdefault(text, []).append(f"{p['name']} {p['version']}")
    lines += ["", "== The crates' licence and notice files ==", ""]
    for text, users in sorted(texts.items(), key=lambda t: t[1][0]):
        lines += [f"-- {', '.join(users)} --", "", text, ""]
    out.write_text("\n".join(lines).rstrip() + "\n")


if __name__ == "__main__":
    main()
