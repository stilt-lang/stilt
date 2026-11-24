#!/usr/bin/env bash
# engine.sh, with each run test run by `stilt run`, which the engine started for the test's
# program gives the program's code (goal one-engine), rather than built.
STILT_RUN_BY=run exec "$(dirname "$0")/engine.sh" "$@"
