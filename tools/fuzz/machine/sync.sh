#!/usr/bin/env bash
# Every few minutes (stilt-fuzz-sync.timer): on a new commit of main, rebuild and restart the
# workers on it. The first build takes about an hour on two vCPUs; later ones minutes.
set -euo pipefail
. "$(dirname "$0")/env.sh"
exec 9> "$STATE/sync.lock"; flock -n 9 || exit 0
[ -d "$SRC/.git" ] || git clone -q "$REPO_URL" "$SRC"
git -C "$SRC" fetch -q origin main
new=$(git -C "$SRC" rev-parse origin/main)
[ "$new" = "$(cat "$STATE/built" 2> /dev/null || true)" ] && exit 0
echo "building $new"
systemctl --user stop stilt-fuzz-differential stilt-fuzz-targets || true
git -C "$SRC" checkout -q --force --detach "$new"
cd "$SRC"
[ -d _opam ] || opam switch create . 5.5.2 --deps-only --with-test --yes
opam exec --switch=. -- dune build @install
cargo build --release -p stilt-cli -p stilt-test
CARGO_TARGET_DIR=target/fuzz cargo +nightly fuzz build --fuzz-dir tools/fuzz -O -s none
rm -rf "$FUZZ/work/interpreter-cache"   # answers of the old interpreter
echo "$new" > "$STATE/built"
systemctl --user start stilt-fuzz-differential stilt-fuzz-targets
echo "running $new"
