#!/usr/bin/env python3
"""Write the software bill of materials of a release, `stilt.spdx.json`, in SPDX 2.3's JSON form.

`sbom.py VERSION OUT` lists what the release's archives hold: the crates that `stilt` and its
runtime library are built from, as `cargo metadata` resolves them for the normal dependencies of
`stilt-cli` and `stilt-runtime`, each with its version, licence, source and the SHA-256 that
`Cargo.lock` records; and the archives that a release build fetches, as
`compiler/stilt-cli/src/release/toolchains.txt` and `wasm.txt` pin them, each with its URL and
SHA-256. It reads nothing but the checkout and `cargo metadata`, so the same commit gives the
same document but for its creation time, which is the commit's.
"""

import json
import subprocess
import sys
from pathlib import Path

ROOTS = ("stilt-cli", "stilt-runtime")
PINS = ("compiler/stilt-cli/src/release/toolchains.txt", "compiler/stilt-cli/src/release/wasm.txt")


def spdx_id(name: str, version: str) -> str:
    """An SPDX identifier made of the characters SPDX allows."""
    safe = "".join(c if c.isalnum() or c in ".-" else "-" for c in f"{name}-{version}")
    return f"SPDXRef-{safe}"


def crates(repo: Path) -> list[dict]:
    """The crates reachable from the roots through normal dependencies, each once."""
    meta = json.loads(
        subprocess.run(
            ["cargo", "metadata", "--format-version", "1", "--locked"],
            cwd=repo, check=True, capture_output=True, text=True,
        ).stdout
    )
    packages = {p["id"]: p for p in meta["packages"]}
    nodes = {n["id"]: n for n in meta["resolve"]["nodes"]}
    lock = {}
    for block in (repo / "Cargo.lock").read_text().split("[[package]]")[1:]:
        fields = dict(
            (k.strip(), v.strip().strip('"'))
            for k, _, v in (line.partition("=") for line in block.strip().splitlines())
            if v
        )
        lock[(fields.get("name"), fields.get("version"))] = fields.get("checksum")
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
    out = []
    for p in sorted(seen.values(), key=lambda p: (p["name"], p["version"])):
        entry = {
            "SPDXID": spdx_id(p["name"], p["version"]),
            "name": p["name"],
            "versionInfo": p["version"],
            "downloadLocation": "NOASSERTION" if p["source"] else "https://github.com/stilt-lang/stilt",
            "licenseConcluded": "NOASSERTION",
            "licenseDeclared": p.get("license") or "NOASSERTION",
            "copyrightText": "NOASSERTION",
            "filesAnalyzed": False,
        }
        if p["source"] and p["source"].startswith("registry+"):
            entry["downloadLocation"] = (
                f"https://crates.io/api/v1/crates/{p['name']}/{p['version']}/download"
            )
            entry["externalRefs"] = [{
                "referenceCategory": "PACKAGE-MANAGER",
                "referenceType": "purl",
                "referenceLocator": f"pkg:cargo/{p['name']}@{p['version']}",
            }]
        checksum = lock.get((p["name"], p["version"]))
        if checksum:
            entry["checksums"] = [{"algorithm": "SHA256", "checksumValue": checksum}]
        out.append(entry)
    return out


def pinned(repo: Path) -> list[dict]:
    """The archives that release builds fetch, as the pin files give them."""
    out = []
    for pins in PINS:
        for line in (repo / pins).read_text().splitlines():
            if not line.strip() or line.startswith("#"):
                continue
            words = line.split()
            name, host, url, sha = (
                ("clang", *words) if len(words) == 3 else tuple(words)
            )
            out.append({
                "SPDXID": spdx_id(f"{name}-{host}", sha[:12]),
                "name": f"{name} ({host})",
                "downloadLocation": url,
                "checksums": [{"algorithm": "SHA256", "checksumValue": sha}],
                "licenseConcluded": "NOASSERTION",
                "licenseDeclared": "NOASSERTION",
                "copyrightText": "NOASSERTION",
                "filesAnalyzed": False,
            })
    return out


def main() -> None:
    version, out = sys.argv[1], Path(sys.argv[2])
    repo = Path(__file__).resolve().parents[2]
    created = subprocess.run(
        ["git", "log", "-1", "--format=%cI"], cwd=repo, check=True, capture_output=True, text=True,
    ).stdout.strip()
    stilt = {
        "SPDXID": "SPDXRef-stilt",
        "name": "stilt",
        "versionInfo": version,
        "downloadLocation": "https://github.com/stilt-lang/stilt",
        "licenseConcluded": "MIT OR Apache-2.0",
        "licenseDeclared": "MIT OR Apache-2.0",
        "copyrightText": "NOASSERTION",
        "filesAnalyzed": False,
    }
    parts = crates(repo) + pinned(repo)
    document = {
        "spdxVersion": "SPDX-2.3",
        "dataLicense": "CC0-1.0",
        "SPDXID": "SPDXRef-DOCUMENT",
        "name": f"stilt-{version}",
        "documentNamespace": f"https://github.com/stilt-lang/stilt/releases/tag/{version}/sbom",
        "creationInfo": {"created": created.replace("+00:00", "Z"), "creators": ["Tool: tools/release/sbom.py"]},
        "packages": [stilt] + parts,
        "relationships": [
            {"spdxElementId": "SPDXRef-DOCUMENT", "relationshipType": "DESCRIBES", "relatedSpdxElement": "SPDXRef-stilt"}
        ] + [
            {"spdxElementId": "SPDXRef-stilt", "relationshipType": "CONTAINS", "relatedSpdxElement": p["SPDXID"]}
            for p in parts
        ],
    }
    out.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
