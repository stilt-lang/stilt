#!/usr/bin/env bash
# The Lean model's executable semantics as the conformance runner drives it (formal/Stilt/Run):
# `run` writes the program as the model's calculus writes it, with the reference interpreter's
# `model`, then runs it in `stilt-model`. A program the calculus can't write, and a run the
# model declines, end with status 77 after a line that says why, which `just formal` gives the
# runner as the status by which an implementation declines a program. No crash ends with 77: an
# exception in the export ends with Cmdliner's 125, which fails the test. Every other command goes
# to the reference interpreter. A panic's report names neither its message nor its place, so a
# run that panics in a test that checks them is declined too.
set -uo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
reference="$root/_build/install/default/bin/stilt-ref"
if [ "${1:-}" != run ]; then
    exec "$reference" "$@"
fi
shift
program=$1
shift
if [ $# -gt 0 ]; then
    echo "stilt-model: declined: a program's arguments, which the model doesn't give" >&2
    exit 77
fi
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
"$reference" model "$program" > "$dir/program.json" || exit $?
# The model evaluates by rewriting values, far slower than either implementation: a run that
# needs more than 60 s of processor time is declined, not failed. `just formal` gives each test
# 90 s. The longest run, std/random.lt's, needs 7 s on a fast machine, and took more than 20 on a
# hosted runner shared with others.
(ulimit -t 60 && exec "$root/formal/.lake/build/bin/stilt-model" "$dir/program.json") \
    > "$dir/out" 2> "$dir/err"
status=$?
if [ $status -gt 128 ]; then
    echo "stilt-model: declined: a run that needs more than the model's 60 s of processor time" >&2
    exit 77
fi
# The calculus keeps neither a panic's message nor its place, so its report names neither: a
# test that checks the whole of stderr declines the run, as the implementation of part of the
# language would. `just formal` asks no `panic-at` of the model (the runner's `--locations absent`).
source=$program
[ -d "$source" ] && source="$source/main.lt"
if grep -q '^panic: ' "$dir/err" && grep -qE '^//~ stderr:' "$source" 2> /dev/null; then
    echo "stilt-model: declined: a panic whose report the test checks, which the model can't tell" >&2
    exit 77
fi
# A program with errors ends with status 2 after its diagnostics, which only the
# implementations write (program.programs-with-errors).
if grep -q '"erroneous":true' "$dir/program.json" && grep -q '^//~ stderr:' "$source" 2> /dev/null; then
    echo "stilt-model: declined: the diagnostics of a program with errors, which the model doesn't write" >&2
    exit 77
fi
cat "$dir/out"
cat "$dir/err" >&2
exit $status
