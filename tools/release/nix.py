#!/usr/bin/env python3
"""Writes the Nix expression of a release, `stilt.nix`, from its SHA256SUMS.

The expression unpacks the archive of the machine's host, as install.sh does, into the store,
with `bin/stilt` linked to it; on Linux, autoPatchelfHook points the executables at the store's
C library. The release workflow writes it beside the archives:

    uv run tools/release/nix.py SHA256SUMS > stilt.nix

`nix-env -f stilt.nix -i` or `nix profile install --file stilt.nix` installs it, and
`pkgs.callPackage ./stilt.nix { }` gives the package. `--base-url` names where the archives are
instead of the release, as a test that installs archives of its own does with a file:// URL.
"""  # noqa: EXE001

import argparse
import sys
from pathlib import Path

from homebrew import REPOSITORY, ROOT, digests

# Nix's names for each host, and the archive that `just dist` writes for it.
HOSTS = {
    "aarch64-darwin": "aarch64-macos",
    "x86_64-linux": "x86_64-linux",
    "aarch64-linux": "aarch64-linux",
}

EXPRESSION = """\
# Stilt {version}, written by tools/release/nix.py from the release's SHA256SUMS.
# `nix-env -f stilt.nix -i` or `nix profile install --file stilt.nix` installs it, and
# `pkgs.callPackage ./stilt.nix {{ }}` gives the package.
{{ pkgs ? import <nixpkgs> {{ }} }}:

let
  inherit (pkgs) lib stdenv;
  archives = {{
{archives}  }};
  system = stdenv.hostPlatform.system;
  archive = archives.${{system}} or (throw "Stilt has no toolchain for ${{system}}");
in
stdenv.mkDerivation {{
  pname = "stilt";
  version = "{version}";

  src = pkgs.fetchurl {{
    url = "{base}/stilt-${{archive.host}}.tar.gz";
    sha256 = archive.sha256;
  }};

  # The linker and the executables are built for a C library at the usual paths.
  nativeBuildInputs = lib.optionals stdenv.hostPlatform.isLinux [ pkgs.autoPatchelfHook ];
  buildInputs = lib.optionals stdenv.hostPlatform.isLinux [ pkgs.zlib stdenv.cc.cc.lib ];
  # The runtime libraries keep their DWARF, which debuggers read in the programs they link.
  dontStrip = true;
  dontConfigure = true;
  dontBuild = true;

  # `stilt` finds its toolchain beside itself, through the link.
  installPhase = ''
    runHook preInstall
    mkdir -p $out/libexec/stilt $out/bin
    cp -R . $out/libexec/stilt/
    ln -s $out/libexec/stilt/bin/stilt $out/bin/stilt
    mkdir -p $out/share
    cp -R share/. $out/share/
    runHook postInstall
  '';

  meta = {{
    description = "Compiled language whose compiler infers what code costs and shows it";
    homepage = "{repository}";
    license = with lib.licenses; [ mit asl20 ];
    sourceProvenance = [ lib.sourceTypes.binaryNativeCode ];
    platforms = builtins.attrNames archives;
    mainProgram = "stilt";
  }};
}}
"""

ARCHIVE = '    {system} = {{ host = "{host}"; sha256 = "{digest}"; }};\n'


def expression(version, sums, base):
    """The expression's text, or raises ValueError when SHA256SUMS lacks a host's archive."""
    found = digests(sums)
    archives = []
    for system, host in HOSTS.items():
        archive = f"stilt-{host}.tar.gz"
        if archive not in found:
            raise ValueError(f"SHA256SUMS has no {archive}")
        archives.append(ARCHIVE.format(system=system, host=host, digest=found[archive]))
    return EXPRESSION.format(
        version=version,
        repository=REPOSITORY,
        base=base.rstrip("/"),
        archives="".join(archives),
    )


def main():
    assert __doc__ is not None
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("sums", type=Path, help="the release's SHA256SUMS")
    parser.add_argument("--version", help="the release's version; VERSION's by default")
    parser.add_argument("--base-url", help="the archives' URL; the release's by default")
    args = parser.parse_args()
    version = args.version or (ROOT / "VERSION").read_text().strip()
    base = args.base_url or f"{REPOSITORY}/releases/download/{version}"
    try:
        sys.stdout.write(expression(version, args.sums.read_text(), base))
    except ValueError as error:
        sys.exit(f"nix.py: {error}")


if __name__ == "__main__":
    main()
