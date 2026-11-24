#!/usr/bin/env bash
# The compiler that `just covered` built with coverage instrumentation, as the conformance runner
# drives it: each process writes its profile beside the build, since the runner passes its
# commands no environment but `PATH` (conformance.environment). With `--release` first, as
# `covered-release.sh` passes it, it runs as `release.sh` does, building each test with
# `stilt build --release`.
set -uo pipefail
repo="$(cd "$(dirname "$0")/../.." && pwd)"
export LLVM_PROFILE_FILE="$repo/target/covered/stilt-%p-%10m.profraw"
stilt="$repo/target/covered/debug/stilt"
if [ "${1:-}" = --release ]; then
    shift
    exec "$repo/tools/runner/release.sh" --stilt "$stilt" "$@"
fi
exec "$stilt" "$@"
