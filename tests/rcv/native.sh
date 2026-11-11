#!/bin/sh
# Builds build/rcv/native/rcv-tabulate-c, the Oakland tabulator translated to C and compiled with
# CompCert, which reads a canonical ballot file and writes its report (Demos/Rcv/tabulate.c), or,
# with the argument maine, build/rcv/maine/native/rcv-maine-c from the Maine module.
# native-verified build writes the C text of the translation of
# Demos.Rcv.TabulateProgram.compiled.module or Demos.Rcv.Maine.TabulateProgram.compiled.module and
# its export tables, has clightgen read the C text back, compares that Clight with the
# translation, and compiles the text with ccomp only when they match.  ccomp then links the object
# with the export tables, Demos/Rcv/tabulate.c, and tools/native-host.c compiled with
# -Dmain=host_main.  CCOMP, CLIGHTGEN, and CCOMP_STDLIB are as for tests/native/verified.sh.
# Usage: tests/rcv/native.sh [maine]
set -eu
cd "$(dirname "$0")/../.."
case "${1:-}" in
  "")
    lib=Demos.Rcv.Tabulate
    module=Demos.Rcv.TabulateProgram.compiled.module
    name=rcvTabulate
    out=build/rcv/native
    program=rcv-tabulate-c
    ;;
  maine)
    lib=Demos.Rcv.Maine.Tabulate
    module=Demos.Rcv.Maine.TabulateProgram.compiled.module
    name=rcvMaine
    out=build/rcv/maine/native
    program=rcv-maine-c
    ;;
  *)
    echo "usage: tests/rcv/native.sh [maine]" >&2
    exit 2
    ;;
esac
ccomp=${CCOMP:-ccomp}
clightgen=${CLIGHTGEN:-clightgen}
set --
if [ -n "${CCOMP_STDLIB:-}" ]; then
  set -- -stdlib "$CCOMP_STDLIB"
fi
tools/leanrun --timeout 2h lake --log-level error build native-verified "$lib"
rm -rf "$out"
mkdir -p "$out"
CLIGHTGEN=$clightgen CCOMP=$ccomp tools/leanrun --timeout 30m lake env \
  .lake/build/bin/native-verified build "$lib" "$module" "$name" "$out"
"$ccomp" "$@" -I tools -Dmain=host_main -c tools/native-host.c -o "$out/host.o"
"$ccomp" "$@" -I tools "-DPROGRAM=\"$program\"" -o "$out/$program" "$out/$name.o" \
  "$out/${name}_glue.c" Demos/Rcv/tabulate.c "$out/host.o"
echo "native.sh: wrote $out/$program"
