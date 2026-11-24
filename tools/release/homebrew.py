#!/usr/bin/env python3
"""Writes the Homebrew formula of a release, `stilt.rb`, from its SHA256SUMS.

The formula installs the archive of the machine's host, as install.sh does, and its test runs
`stilt new`, `check` and `run` on a fresh package. The release workflow writes it beside the
archives; the tap's repository, homebrew-stilt, takes it as `Formula/stilt.rb`.

    uv run tools/release/homebrew.py SHA256SUMS > stilt.rb
"""  # noqa: EXE001

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPOSITORY = "https://github.com/stilt-lang/stilt"
# Homebrew's names for each host, and the archive that `just dist` writes for it.
HOSTS = {
    ("macos", "arm"): "aarch64-macos",
    ("linux", "intel"): "x86_64-linux",
    ("linux", "arm"): "aarch64-linux",
}

FORMULA = """\
# The formula of Stilt {version}, written by tools/release/homebrew.py from the release's
# SHA256SUMS.
class Stilt < Formula
  desc "Compiled language whose compiler infers what code costs and shows it"
  homepage "{repository}"
  version "{version}"
  license any_of: ["MIT", "Apache-2.0"]

{blocks}
  def install
    libexec.install Dir["*"]
    bin.install_symlink libexec/"bin/stilt"
    man1.install Dir[libexec/"share/man/man1/*.1"]
    bash_completion.install libexec/"share/bash-completion/completions/stilt"
    zsh_completion.install libexec/"share/zsh/site-functions/_stilt"
    fish_completion.install libexec/"share/fish/vendor_completions.d/stilt.fish"
  end

  test do
    system bin/"stilt", "new", "hello"
    cd "hello" do
      system bin/"stilt", "check"
      assert_match "Hello", shell_output("#{{bin}}/stilt run")
    end
  end
end
"""

BLOCK = """\
  on_{os} do
    on_{cpu} do
      url "{repository}/releases/download/{version}/{archive}"
      sha256 "{digest}"
    end
  end
"""


def digests(sums):
    """The digest of each archive that a SHA256SUMS file lists, by file name."""
    found = {}
    for line in sums.splitlines():
        if not line.strip():
            continue
        digest, _, name = line.partition("  ")
        if len(digest) != 64 or not name:
            raise ValueError(f"not a line of SHA256SUMS: {line!r}")
        found[name.strip().lstrip("*")] = digest
    return found


def formula(version, sums):
    """The formula's text, or raises ValueError when SHA256SUMS lacks a host's archive."""
    found = digests(sums)
    blocks = []
    for (os, cpu), host in HOSTS.items():
        archive = f"stilt-{host}.tar.gz"
        if archive not in found:
            raise ValueError(f"SHA256SUMS has no {archive}")
        blocks.append(
            BLOCK.format(
                os=os,
                cpu=cpu,
                repository=REPOSITORY,
                version=version,
                archive=archive,
                digest=found[archive],
            )
        )
    return FORMULA.format(version=version, repository=REPOSITORY, blocks="\n".join(blocks))


def main():
    assert __doc__ is not None
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("sums", type=Path, help="the release's SHA256SUMS")
    parser.add_argument("--version", help="the release's version; VERSION's by default")
    args = parser.parse_args()
    version = args.version or (ROOT / "VERSION").read_text().strip()
    try:
        sys.stdout.write(formula(version, args.sums.read_text()))
    except ValueError as error:
        sys.exit(f"homebrew.py: {error}")


if __name__ == "__main__":
    main()
