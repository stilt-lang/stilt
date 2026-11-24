#!/usr/bin/env bash
# Starts the Linux machine of `just sanitizers` and `just debuggers`: a container of the image
# that this directory's Dockerfile builds, which mounts the repository and the build directory
# that `target` links to at their own paths and may trace processes, as debuggers do. Prints the
# container's name; the caller removes it.
set -euo pipefail
if ! docker info > /dev/null 2>&1; then
    echo "ERROR the Linux machine needs Docker, which isn't running" >&2
    exit 1
fi
repo="$(cd "$(dirname "$0")/../.." && pwd -P)"
mkdir -p "$repo/target"
build="$(cd "$repo/target" && pwd -P)"
docker build -q -t stilt-linux "$repo/tools/linux" > /dev/null
name=stilt-linux-$$-$RANDOM
docker run -d --rm --name "$name" --cap-add=SYS_PTRACE --security-opt seccomp=unconfined \
    -v "$repo:$repo" -v "$build:$build" -w "$repo" -v stilt-linux-cargo:/usr/local/cargo/registry \
    stilt-linux sleep infinity > /dev/null
echo "$name"
