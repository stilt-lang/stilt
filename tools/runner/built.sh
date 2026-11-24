#!/usr/bin/env bash
# The compiler as the conformance runner drives it, but with `run` replaced by `stilt build`
# and a run of the executable it writes, so that the suite tests the built program rather than
# the JIT. Every other command goes to the compiler as it is, and so does the run of a program
# with errors, which `build` refuses and `run` runs all the same (program.programs-with-errors).
set -uo pipefail
stilt="$(cd "$(dirname "$0")/../.." && pwd)/target/bin/stilt"
if [ "${1:-}" != run ]; then
    exec "$stilt" "$@"
fi
shift
program=$1
shift
if ! "$stilt" check "$program" > /dev/null 2>&1; then
    exec "$stilt" run "$program" "$@"
fi
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
"$stilt" build -o "$dir/program" "$program" || exit $?
"$dir/program" "$@"
