#!/bin/sh
# Usage: lean-file.sh REPO_COPY FILE
# Elaborates FILE with `lake env lean` in REPO_COPY, after elaborate.sh has built the libraries
# that FILE imports.
set -eu
cd "$1"
lake env lean --tstack=400000 "$2"
