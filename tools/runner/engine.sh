#!/usr/bin/env bash
# The compiler as the conformance runner drives it, with the commands on a program of a
# directory answered by the engine that the first of them starts (goal one-engine): each
# command stops the program's engine after it, failing when none answered. `test` asks the
# engine of every program, a program of one file included, which must answer. `run` goes through
# an engine too: run by `stilt run`, which the engine gives the program's code, when
# engine-run.sh is the implementation; and otherwise replaced by `stilt build`, through an
# engine, and a run of the executable it writes, as in built.sh, but for the run of a program
# with errors, which `build` refuses and which goes to the compiler as it is. A program of one
# file has no engine but for `test`. Every other command goes to the compiler as it is.
set -uo pipefail
stilt="$(cd "$(dirname "$0")/../.." && pwd)/target/bin/stilt"
# Stops the engine of the program PATH, which must have answered when PATH is a directory or
# the command is `test`.
stop() {
    if { [ -d "$1" ] || [ "$command" = test ]; } && ! "$stilt" engine --stop "$1" 2> /dev/null; then
        echo "stilt: no engine answered" >&2
        exit 99
    fi
}
# Runs `stilt ARGS` on the program PATH, and stops its engine.
engine() {
    local program=$1
    shift
    "$stilt" "$@"
    local status=$?
    stop "$program"
    return $status
}
command=${1:-}
case $command in
check | test)
    engine "${@: -1}" "$@"
    exit $?
    ;;
run) ;;
*) exec "$stilt" "$@" ;;
esac
program=$2
if [ "${STILT_RUN_BY:-build}" = run ]; then
    engine "$program" "$@"
    exit $?
fi
shift 2
if ! "$stilt" check "$program" > /dev/null 2>&1; then
    engine "$program" run "$program" "$@"
    exit $?
fi
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
engine "$program" build -o "$dir/program" "$program" || exit $?
"$dir/program" "$@"
