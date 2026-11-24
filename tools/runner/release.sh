#!/usr/bin/env bash
# The compiler as the conformance runner drives it, but with `run` replaced by
# `stilt build --release` and a run of the executable it writes, so that the suite tests the
# release build (builds.same-meaning). Every other command goes to the compiler as it is, and so
# does the run of a program with errors or holes, which a release build refuses
# (builds.what-it-refuses) and `run` runs all the same (program.programs-with-errors;
# declarations.running-holes). `--stilt PATH` names another build of the compiler than the debug
# one.
set -uo pipefail
repo="$(cd "$(dirname "$0")/../.." && pwd)"
stilt=$repo/target/bin/stilt
if [ "${1:-}" = --stilt ]; then
    stilt=$2
    shift 2
fi
if [ "${1:-}" != run ]; then
    exec "$stilt" "$@"
fi
shift
program=$1
shift
if ! report=$("$stilt" check --json "$program" 2> /dev/null < /dev/null) \
    || [[ "$report" == *'"W0300"'* ]]; then
    exec "$stilt" run "$program" "$@"
fi
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
# The build mustn't take the program's input. Its objects are kept in the checkout's cache,
# since the runner's environment has no home (conformance.environment), so a run after the first
# compiles only the C that changed.
STILT_HOME=$repo/target/stilt-home "$stilt" build --release -o "$dir/program" "$program" \
    < /dev/null || exit $?
"$dir/program" "$@"
