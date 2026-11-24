#!/usr/bin/env bash
# `covered.sh` building each test with `stilt build --release`, for the runner's `--impl`.
exec "$(dirname "$0")/covered.sh" --release "$@"
