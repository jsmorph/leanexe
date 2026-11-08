#!/bin/sh
# Installs Sail 0.20.3, with its Lean back end, in an opam switch of the user's opam root.
# Needs opam and the Debian packages build-essential, libgmp-dev, z3, and pkg-config.
set -eu
: "${OPAMROOT:=$HOME/.opam}"
: "${OPAMJOBS:=6}"
switch="${SAIL_SWITCH:-sail-0.20.3}"
export OPAMROOT OPAMJOBS OPAMYES=1
if [ ! -d "$OPAMROOT" ]; then
  opam init --bare --no-setup
fi
if ! opam switch list --short | grep -qx "$switch"; then
  opam switch create "$switch" ocaml-base-compiler.5.4.1
fi
opam install --switch "$switch" sail.0.20.3
opam exec --switch "$switch" -- sail --version
