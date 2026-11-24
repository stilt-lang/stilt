#!/usr/bin/env bash
# The compiler as the conformance runner drives it, for one cell of the matrix of hosts and
# targets (goals targets and cross-compilation): `cross.sh CONTAINER HOST TARGET BUILD COMMAND...`
# replaces `run` with `stilt build --target TARGET` on HOST, `macos` or `linux`, with
# `--release` when BUILD is `release` (builds.release-builds), and a run of the executable on the
# target's machine. Every other command goes to HOST's compiler as it is, and so does the run of a
# program with errors, which `build` refuses and `run` runs all the same
# (program.programs-with-errors), or of one with a hole, which a release build refuses
# (builds.what-it-refuses).
#
# This machine is the Mac. CONTAINER is an x86-64 Linux container that `just cross` starts,
# which mounts the repository at the same path and runs the executables built for x86-64 Linux,
# and the compiler built for it; STILT_ARM_MACHINE names the aarch64 Linux machine, which runs
# those built for aarch64 Linux natively. With STILT_CROSS_HOST set, the Linux host is that container
# instead, the Linux machine of the host's architecture, which runs the compiler that
# STILT_CROSS_COMPILER names. A module built for wasm32-wasip1 runs on this machine under the
# wasmtime that STILT_WASMTIME names, the reference runtime, with 4 MiB of stack for its code,
# the test's directory, the working one, and /tmp granted, and the environment it is given
# (wasm.limits and wasm.conformance-runs), killed after 30 seconds; CONTAINER is then unused.
set -uo pipefail
container=$1 host=$2 target=$3 build=$4
shift 4
repo="$(cd "$(dirname "$0")/../.." && pwd)"

host_container=${STILT_CROSS_HOST:-$container}
compiler=${STILT_CROSS_COMPILER:-$repo/target/cross/x86_64-unknown-linux-musl/debug/stilt}

# Runs a command in a container, in the current directory, on this script's input. Docker can
# lose the end of an input that it forwards, which leaves a program that reads to the end
# waiting until the runner kills it, so the input goes to a file that the command reads there.
in_container() {
    local name=$1 input status
    shift
    mkdir -p "$repo/target/cross-run"
    input=$(mktemp "$repo/target/cross-run/input.XXXXXX")
    cat > "$input"
    docker exec -w "$PWD" "$name" sh -c 'exec "$@" < "$0"' "$input" "$@"
    status=$?
    rm -f "$input"
    return $status
}

# Runs a command on the x86-64 Linux machine, in the current directory.
linux() {
    in_container "$container" "$@"
}

stilt() {
    if [ "$host" = linux ]; then
        in_container "$host_container" "$compiler" "$@"
    else
        "$repo/target/bin/stilt" "$@"
    fi
}

if [ "${1:-}" != run ]; then
    stilt "$@"
    exit $?
fi
shift
program=$1
shift
if ! report=$(stilt check --json "$program" 2> /dev/null < /dev/null) \
    || { [ "$build" = release ] && [[ "$report" == *'"W0300"'* ]]; }; then
    stilt run "$program" "$@"
    exit $?
fi
mkdir -p "$repo/target/cross-run"
dir=$(mktemp -d "$repo/target/cross-run/build.XXXXXX")
trap 'rm -rf "$dir"' EXIT
# The build mustn't take the program's input. A release build's objects are kept in the
# checkout's cache, since the runner's environment has no home (conformance.environment).
release=
if [ "$build" = release ]; then release=--release; fi
STILT_HOME=$repo/target/stilt-home stilt build $release --target "$target" \
    -o "$dir/program" "$program" < /dev/null || exit $?
if [ "$target" = x86_64-linux ]; then
    linux "$dir/program" "$@"
elif [ "$target" = aarch64-linux ]; then
    in_container "$STILT_ARM_MACHINE" "$dir/program" "$@"
elif [ "$target" = wasm32-wasip1 ]; then
    "$STILT_WASMTIME" run -W max-wasm-stack=4194304 -W timeout=30s -S inherit-env=y \
        --dir . --dir /tmp "$dir/program" "$@"
else
    "$dir/program" "$@"
fi
