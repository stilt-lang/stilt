#!/usr/bin/env bash
# Worker 2: the cargo fuzz targets in turn, an hour each, their corpora kept across builds.
# The conformance suite and the examples seed parse, format and check (tools/fuzz/README.md).
set -uo pipefail
. "$(dirname "$0")/env.sh"
cd "$SRC"
while true; do
    for t in parse format check lsp pack; do
        mkdir -p "$CORPUS/$t" "$FUZZ/work/artifacts/$t"
        seeds=()
        case $t in parse | format | check) seeds=(conformance examples) ;; esac
        flags=(-O -s none); [ "$t" = lsp ] && flags+=(-a)
        CARGO_TARGET_DIR=target/fuzz timeout 4000 cargo +nightly fuzz run --fuzz-dir tools/fuzz \
            "${flags[@]}" "$t" "$CORPUS/$t" "${seeds[@]}" -- -max_total_time=3600 \
            -rss_limit_mb=1500 -timeout=20 -artifact_prefix="$FUZZ/work/artifacts/$t/" \
            > "$FUZZ/work/$t.log" 2>&1
        for a in "$FUZZ/work/artifacts/$t"/*; do
            [ -f "$a" ] || continue
            f=$FINDINGS/$t-$(basename "$a")
            mkdir -p "$f"
            mv "$a" "$f/input"
            tail -60 "$FUZZ/work/$t.log" > "$f/report"
            printf 'kind=%s\ncommit=%s\n' "$t" "$(cat "$STATE/built")" > "$f/finding"
        done
        execs=$(grep -o 'stat::number_of_executed_units: *[0-9]*' "$FUZZ/work/$t.log" | grep -o '[0-9]*$' | tail -1)
        echo "$(date -u +%FT%TZ) $t ${execs:-0}" >> "$STATE/progress"
    done
done
