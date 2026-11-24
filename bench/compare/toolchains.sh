#!/usr/bin/env bash
# Downloads the toolchains of the comparisons that a machine's package manager doesn't give, Go's
# and Koka's, from their official release archives into target/toolchains/, checking each archive
# against its SHA-256, and installs nothing anywhere else. A toolchain already there is kept, and
# one that can't be downloaded is left out, with a note, so the comparisons leave its language
# out. Prints the options of `stilt-bench compare` that name the toolchains it has.
set -euo pipefail

go_version=1.27.4
koka_version=3.2.9
dir=target/toolchains

case "$(uname -s)-$(uname -m)" in
    Darwin-arm64)
        go_os=darwin-arm64 koka_os=macos-arm64
        go_sum=91a44a2b8a716600ad94a4f143e156116620db8828086a6e3602291be9bd0bb4
        koka_sum=b71fe2237b5f6b11116e296497b9756136a6d2a2514dcbf022aa9f620f04c088
        ;;
    Linux-x86_64)
        go_os=linux-amd64 koka_os=linux-x64
        go_sum=7226736c2339719cda28fbf3a54d71aa63bcefe376e98cef00034268dab24840
        koka_sum=310459831a7c6fa6a0cd8e0e02d6b5b3b36441d5e7ce24168bda016cd2e95eee
        ;;
    Linux-aarch64)
        go_os=linux-arm64 koka_os=linux-arm64
        go_sum=3392582988a273a87ab5043ee1b2c9c17a2c3c00580bf9326c47a2e0aaaeac92
        koka_sum=0cb2c033f57afad475d637fe4c016ff5ba2f5ba3cfa364a89d9c410fbfd5dcd6
        ;;
    *)
        echo "note: Go and Koka publish no release for this machine" >&2
        exit 0
        ;;
esac

sha256() {
    if command -v sha256sum > /dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi \
        | cut -d ' ' -f 1
}

# Unpacks the archive at URL, whose SHA-256 is SUM, into DEST, without its first STRIP levels.
fetch() {
    local name=$1 url=$2 sum=$3 dest=$4 strip=$5
    [ -d "$dest" ] && return 0
    local archive
    archive="$dir/archives/$(basename "$url")"
    mkdir -p "$dir/archives"
    if ! curl -fsSL -o "$archive.part" "$url"; then
        echo "note: cannot download $name from $url, so the comparisons leave it out" >&2
        rm -f "$archive.part"
        return 0
    fi
    if [ "$(sha256 "$archive.part")" != "$sum" ]; then
        echo "ERROR $url: its SHA-256 isn't $sum" >&2
        rm -f "$archive.part"
        exit 1
    fi
    mv "$archive.part" "$archive"
    rm -rf "$dest.part"
    mkdir -p "$dest.part"
    tar -xzf "$archive" -C "$dest.part" --strip-components "$strip"
    mv "$dest.part" "$dest"
}

fetch Go "https://go.dev/dl/go$go_version.$go_os.tar.gz" "$go_sum" "$dir/go-$go_version" 1
fetch Koka "https://github.com/koka-lang/koka/releases/download/v$koka_version/koka-v$koka_version-$koka_os.tar.gz" \
    "$koka_sum" "$dir/koka-$koka_version" 0
if [ -x "$dir/go-$go_version/bin/go" ]; then
    printf -- '--go %s ' "$dir/go-$go_version/bin/go"
fi
if [ -x "$dir/koka-$koka_version/bin/koka" ]; then
    printf -- '--koka %s ' "$dir/koka-$koka_version/bin/koka"
fi
