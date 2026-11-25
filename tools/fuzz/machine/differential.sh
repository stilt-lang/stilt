#!/usr/bin/env bash
# Worker 1: generated programs, run by the debug back end and their tests compared with the
# reference interpreter's, a thousand at a time from consecutive seeds (CI and the nightly use
# seeds from 1, so the machine starts at 10,000,001). A failing batch becomes a finding that
# its seed and the commit reproduce.
set -uo pipefail
. "$(dirname "$0")/env.sh"
cd "$SRC"
gen=_build/install/default/bin/stilt-gen
ref=_build/install/default/bin/stilt-ref
mkdir -p "$FUZZ/work"
while true; do
    seed=$(cat "$STATE/seed" 2> /dev/null || echo 10000001)
    out=$FUZZ/work/programs logs=$FUZZ/work/logs
    rm -rf "$out" "$logs"
    "$gen" csmith --seed "$seed" --count 1000 --bundle 10 --out "$out" > /dev/null
    if ! target/release/stilt-test --impl target/release/stilt --diff "$ref" --tests \
        --cache "$FUZZ/work/interpreter-cache" --logs "$logs" "$out" > "$FUZZ/work/report" 2>&1; then
        f=$FINDINGS/differential-$seed
        mkdir -p "$f"
        cp "$FUZZ/work/report" "$f/report"
        cp -r "$logs" "$f/logs" 2> /dev/null || true
        printf 'kind=differential\nseed=%s\ncount=1000\ncommit=%s\n' "$seed" "$(cat "$STATE/built")" > "$f/finding"
    fi
    echo $((seed + 1000)) > "$STATE/seed"
    echo "$(date -u +%FT%TZ) differential $seed 1000" >> "$STATE/progress"
done
