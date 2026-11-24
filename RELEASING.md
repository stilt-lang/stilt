# Releasing

A release is a version tag on `main`. The dictator ([GOVERNANCE.md](GOVERNANCE.md)) chooses the version and pushes the tag; the [release workflow](.github/workflows/release.yml) does the rest. Versions are calendar versions, `YYYY.M.PATCH`, as in `2027.1.0`; `VERSION` holds the current one.

## Checklist

Before tagging:

- [ ] Every pull request that changes what a user sees has its file in [`changes/`](changes/), and `uv run tools/release/notes.py` prints notes that read well. Edit the files, not the output.
- [ ] `VERSION` holds the version to release, and the workspace's `Cargo.toml` and `editors/vscode/package.json` have the same version (`just lint` checks them).
- [ ] `just ci` passes on `main` on a dedicated machine with `STILT_DEDICATED=1`, and the latest nightly run is green: the million generated programs, the matrix, the sanitizers and the debuggers.
- [ ] `just coverage` reports every paragraph of the Reference cited and every registered code tested or checked elsewhere; the report goes with the release.
- [ ] `just covered` reports the lines and functions of each crate that the tests and the suites run, in `target/covered/README.md`; the table goes with the release, beside the report of `just coverage`.
- [ ] `just dist` builds and installs this host's archive, and a release build from a fresh install works.
- [ ] The guide, the Reference and the design documents say what the release does; `docs/` was updated with every change to a paragraph.
- [ ] Each RFC implemented in this release has its status updated in the [RFC repository](https://github.com/stilt-lang/stilt-rfcs) to `stable`, with this version.
- [ ] The repository secrets that the workflow reads are set (below), and `release_key` in `install.sh` is the signing key's public key, which the workflow checks.

Tag:

```sh
git tag -s 2027.1.0 -m "Stilt 2027.1.0"
git push origin 2027.1.0
```

The workflow checks, and stops if one fails: the tag is the content of `VERSION`; the tag is on `main`; the checks named `CI passed` succeeded on the tagged commit; the change files are well formed and there is at least one; the extension's version is the tag's. Then it builds each host's toolchain with `just dist`, writes `SHA256SUMS`, signs it, publishes a release with the archives, `install.sh`, the checksums, the notes, the Homebrew formula `stilt.rb` and the Nix expression `stilt.nix`, and publishes the extension on the Visual Studio Marketplace and on Open VSX.

After it succeeds:

- [ ] `curl -sSf https://raw.githubusercontent.com/stilt-lang/stilt/main/install.sh | sh` installs the release on a clean machine of each host, and `stilt new`, `check`, `run`, `test` and `build` work with nothing else installed.
- [ ] `nix profile install --file stilt.nix`, with the release's `stilt.nix`, which `tools/release/nix.py` writes from `SHA256SUMS`, installs it on a machine of each host with Nix, and `stilt new`, `run`, `test` and `build` work.
- [ ] Copy the release's `stilt.rb`, which `tools/release/homebrew.py` writes from `SHA256SUMS`, to `Formula/stilt.rb` in the tap, `homebrew-stilt`, so `brew install stilt-lang/stilt/stilt` installs it.
- [ ] Set the grammar's `rev` in `editors/zed/extension.toml` to the tagged commit and its `version` to the release's, commit that to `main`, and publish Zed's extension from that commit: in [zed-industries/extensions](https://github.com/zed-industries/extensions), point the submodule `extensions/stilt` at it and give the entry `stilt` of `extensions.toml` `path = "editors/zed"` and that version.
- [ ] `uv run tools/release/notes.py --remove`, and commit the removal: the next release's notes start empty.
- [ ] Announce it.

## Repository secrets

| Secret | Used for |
| --- | --- |
| `RELEASE_SIGNING_KEY` | The private OpenSSH Ed25519 key, without a passphrase, that signs `SHA256SUMS` as `SHA256SUMS.sig` |
| `VSCE_PAT` | A personal access token of the Visual Studio Marketplace publisher, to publish the extension |
| `OVSX_PAT` | A token of Open VSX, to publish the extension there |

The publishing jobs run in the `release` environment, which can require the dictator's approval before they start.

## The signing key

Each release's `SHA256SUMS` is signed with an Ed25519 key that OpenSSH makes, so the installer checks it with the `ssh-keygen` that macOS and Linux come with. Make the key once, on a machine of your own:

```sh
ssh-keygen -t ed25519 -N '' -C stilt-release -f stilt-release
```

Store `stilt-release` as the secret `RELEASE_SIGNING_KEY`, keep a copy offline, and write the first two words of `stilt-release.pub` as `release_key` in `install.sh`, the default of `${STILT_RELEASE_KEY:-"…"}`. A new key is a change to `install.sh` too, so the installers of older commits refuse releases signed by it. Anyone can check a release by hand:

```sh
printf 'stilt-release %s\n' "$(sed -n 's/^release_key=.*:-"\(.*\)"}$/\1/p' install.sh)" > allowed_signers
ssh-keygen -Y verify -f allowed_signers -I stilt-release -n stilt-release -s SHA256SUMS.sig < SHA256SUMS
```

Each release attaches its software bill of materials, `stilt.sbom.spdx.json`, in SPDX 2.3, which `tools/release/sbom.py` writes: the crates of `stilt` and its runtime with their licences and the digests of `Cargo.lock`, and the archives that release builds fetch with theirs.
