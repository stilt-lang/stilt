#!/bin/sh
# Installs Stilt's toolchain: `stilt`, and beside it the linker and the runtime libraries that
# its builds use. It downloads the archive of this machine's host and the release's SHA256SUMS,
# checks SHA256SUMS's signature against the release key written below, with OpenSSH's
# `ssh-keygen -Y verify`, and the archive against its digest there, and unpacks it into
# $STILT_HOME, ~/.stilt unless set, as $STILT_HOME/VERSION, with $STILT_HOME/bin/stilt linked
# to it. Release builds fetch clang themselves, the first time.
#
#   curl -sSf https://raw.githubusercontent.com/stilt-lang/stilt/main/install.sh | sh
#   curl -sSf https://raw.githubusercontent.com/stilt-lang/stilt/main/install.sh | sh -s -- --version 2027.1.0
#
# STILT_DIST, a URL or a directory, says where the archives are: the repository's releases,
# unless set, or the directory that `just dist` writes them into, which STILT_RELEASE_KEY then
# names the key of, since `just dist` signs with a key of its own.

set -eu

dist=${STILT_DIST:-https://github.com/stilt-lang/stilt/releases}
home=${STILT_HOME:-$HOME/.stilt}
version=latest
# The public key that signs every release's SHA256SUMS, written here when the key is made
# (RELEASING.md). The release workflow publishes nothing unless it is the signing key's, so an
# archive or a digest changed where the releases are served is refused.
release_key=${STILT_RELEASE_KEY:-"ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIIGrPaIueji+ePOGwwLKiBbiED2oB19u3FSaQy4sC/GK"}

say() { printf 'stilt: %s\n' "$1" >&2; }
fail() { say "$1"; exit 1; }

while [ $# -gt 0 ]; do
    case $1 in
        --version) [ $# -ge 2 ] || fail "--version needs a version, as 2027.1.0"; version=$2; shift 2 ;;
        *) fail "unknown option $1; the options are --version VERSION" ;;
    esac
done

case "$(uname -s)-$(uname -m)" in
    Darwin-arm64) host=aarch64-macos ;;
    Linux-x86_64) host=x86_64-linux ;;
    Linux-aarch64 | Linux-arm64) host=aarch64-linux ;;
    *) fail "no toolchain is built for $(uname -s) on $(uname -m) yet; aarch64 macOS and x86-64 and aarch64 Linux have one" ;;
esac

# Fetches `$1` of the distribution into the file `$2`.
fetch() {
    case $dist in
        http://* | https://*)
            if [ "$version" = latest ]; then url=$dist/latest/download/$1; else url=$dist/download/$version/$1; fi
            if command -v curl > /dev/null; then
                curl -sSfL --proto '=https' --tlsv1.2 -o "$2" "$url" || fail "can't download $url"
            elif command -v wget > /dev/null; then
                wget -q --https-only -O "$2" "$url" || fail "can't download $url"
            else
                fail "downloading needs curl or wget"
            fi
            ;;
        *) cp "$dist/$1" "$2" 2> /dev/null || fail "no $1 in $dist" ;;
    esac
}

digest() {
    if command -v sha256sum > /dev/null; then sha256sum "$1" | cut -d ' ' -f 1
    else shasum -a 256 "$1" | cut -d ' ' -f 1
    fi
}

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
archive=stilt-$host.tar.gz
[ -n "$release_key" ] || fail "this installer holds no release key; nothing was installed"
command -v ssh-keygen > /dev/null     || fail "checking the release's signature needs OpenSSH's ssh-keygen, as the package openssh-client gives"
fetch SHA256SUMS "$work/SHA256SUMS"
fetch SHA256SUMS.sig "$work/SHA256SUMS.sig"
printf 'stilt-release %s\n' "$release_key" > "$work/allowed_signers"
ssh-keygen -Y verify -f "$work/allowed_signers" -I stilt-release -n stilt-release \
    -s "$work/SHA256SUMS.sig" < "$work/SHA256SUMS" > /dev/null 2>&1 \
    || fail "SHA256SUMS isn't signed by the release key; nothing was installed"
want=$(awk -v f="$archive" '$2 == f || $2 == "*" f { print $1 }' "$work/SHA256SUMS")
[ -n "$want" ] || fail "SHA256SUMS has no digest of $archive; nothing was installed"
fetch "$archive" "$work/$archive"
[ "$(digest "$work/$archive")" = "$want" ] || fail "$archive doesn't match its SHA-256 digest; nothing was installed"

mkdir -p "$work/unpacked"
tar -xzf "$work/$archive" -C "$work/unpacked"
unpacked=$(ls "$work/unpacked")
[ -x "$work/unpacked/$unpacked/bin/stilt" ] || fail "$archive holds no bin/stilt"
installed=${unpacked#stilt-}
installed=${installed%-"$host"}

mkdir -p "$home/bin"
rm -rf "${home:?}/$installed"
mv "$work/unpacked/$unpacked" "$home/$installed"
ln -sfn "../$installed/bin/stilt" "$home/bin/stilt"
# The manual pages and the shells' completions, at stable paths beside bin.
ln -sfn "$installed/share" "$home/share"
say "installed $("$home/bin/stilt" --version) in $home/$installed"
say "manual pages are in $home/share/man and completions in $home/share; or run: stilt completions zsh"

case ":$PATH:" in
    *":$home/bin:"*) ;;
    *) say "add $home/bin to your PATH, as with: export PATH=\"$home/bin:\$PATH\"" ;;
esac
