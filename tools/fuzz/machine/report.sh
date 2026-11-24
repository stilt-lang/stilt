#!/usr/bin/env bash
# Hourly (stilt-fuzz-report.timer): each new finding becomes an issue labelled `fuzz`, or a
# comment on the open issue with the same signature (the kind, and where it panicked or what
# the runner reported first); and the pinned issue "Fuzzing status" is rewritten. It needs a
# token that may write issues on the repository alone, in ~/fuzz/token; without one, findings
# wait in ~/fuzz/findings.
set -euo pipefail
. "$(dirname "$0")/env.sh"
[ -s "$FUZZ/token" ] || { echo "no token: $(ls "$FINDINGS" | wc -l) findings wait"; exit 0; }
api() { curl -fsS -H "Authorization: Bearer $(cat "$FUZZ/token")" \
    -H "Accept: application/vnd.github+json" "https://api.github.com/repos/$REPO/$1" "${@:2}"; }
for f in "$FINDINGS"/*/; do
    [ -f "$f/finding" ] || continue
    . "$f/finding"
    where=$(grep -m1 -oE "panicked at [^ ]+|deadly signal|timeout|out-of-memory|FAIL[^ ]* [^ ]+" "$f/report" || echo failure)
    signature="$kind: $where"
    body=$(mktemp)
    {
        echo "Found by the fuzzing machine on commit $commit."
        echo
        if [ "$kind" = differential ]; then
            echo "Reproduce: \`stilt-gen csmith --seed $seed --count $count --bundle 10 --out programs\`, then \`just differential\`'s runner on \`programs\`."
        else
            echo "Reproduce: save the input below as \`input\`, then \`cargo +nightly fuzz run --fuzz-dir tools/fuzz -O -s none $kind input\`."
            echo; echo '```'; base64 -w 76 < "$f/input" | head -200; echo '```'
        fi
        echo; echo '<details><summary>Report</summary>'; echo; echo '```'; tail -40 "$f/report"; echo '```'; echo '</details>'
    } > "$body"
    open=$(api "issues?labels=fuzz&state=open&per_page=100" | jq -r --arg s "$signature" '.[] | select(.title == $s) | .number' | head -1)
    if [ -n "$open" ]; then
        jq -Rs '{body: .}' < "$body" | api "issues/$open/comments" -X POST --data @- > /dev/null
    else
        jq -Rs --arg t "$signature" '{title: $t, body: ., labels: ["fuzz"]}' < "$body" | api issues -X POST --data @- > /dev/null
    fi
    rm -f "$body"
    mkdir -p "$FUZZ/reported"; mv "$f" "$FUZZ/reported/"
done
# The status issue.
since=$(date -u -d '-1 hour' +%FT%TZ)
programs=$(awk -v s="$since" '$1 >= s && $2 == "differential" { n += $4 } END { print n + 0 }' "$STATE/progress" 2> /dev/null || echo 0)
execs=$(awk -v s="$since" '$1 >= s && $2 != "differential" { n += $3 } END { print n + 0 }' "$STATE/progress" 2> /dev/null || echo 0)
corpus=$(find "$CORPUS" -type f | wc -l)
findings=$(api "issues?labels=fuzz&state=open&per_page=100" | jq length)
status="Rewritten every hour by the fuzzing machine.

| | |
| --- | --- |
| Commit fuzzed | $(cat "$STATE/built" 2> /dev/null) |
| Generated programs, last hour | $programs |
| Fuzz target executions, last hour | $execs |
| Corpus inputs | $corpus |
| Open findings (label \`fuzz\`) | $findings |
| Updated | $(date -u '+%F %H:%M UTC') |"
number=$(api "issues?state=open&per_page=100" | jq -r '.[] | select(.title == "Fuzzing status") | .number' | head -1)
if [ -n "$number" ]; then
    jq -n --arg b "$status" '{body: $b}' | api "issues/$number" -X PATCH --data @- > /dev/null
else
    jq -n --arg b "$status" '{title: "Fuzzing status", body: $b}' | api issues -X POST --data @- > /dev/null
fi
