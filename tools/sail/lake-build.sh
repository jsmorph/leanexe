#!/bin/sh
# Usage: lake-build.sh PROJECT [TARGET]
# Resolves the dependencies of the Lake project that Sail's Lean back end wrote, whose manifest
# lists none, and builds TARGET (default: the default targets) with the toolchain that its
# lean-toolchain names.
set -eu
cd "$1"
shift
lake update
lake build "$@"
