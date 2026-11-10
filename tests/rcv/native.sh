#!/bin/sh
# Builds build/rcv/native/rcv-tabulate-c, the tabulator translated to C and compiled with CompCert,
# which reads a canonical ballot file and writes its report (Demos/Rcv/tabulate.c).
# native-verified build writes the C text of the translation of
# Demos.Rcv.TabulateProgram.compiled.module and its export tables, has clightgen read the C text
# back, compares that Clight with the translation, and compiles the text with ccomp only when they
# match.  ccomp then links the object with the export tables, Demos/Rcv/tabulate.c, and
# tools/native-host.c compiled with -Dmain=host_main.  CCOMP, CLIGHTGEN, and CCOMP_STDLIB are as
# for tests/native/verified.sh.
# Usage: tests/rcv/native.sh
set -eu
cd "$(dirname "$0")/../.."
ccomp=${CCOMP:-ccomp}
clightgen=${CLIGHTGEN:-clightgen}
set --
if [ -n "${CCOMP_STDLIB:-}" ]; then
  set -- -stdlib "$CCOMP_STDLIB"
fi
out=build/rcv/native
tools/leanrun --timeout 2h lake --log-level error build native-verified Demos.Rcv.Tabulate
rm -rf "$out"
mkdir -p "$out"
CLIGHTGEN=$clightgen CCOMP=$ccomp tools/leanrun --timeout 30m lake env \
  .lake/build/bin/native-verified build Demos.Rcv.Tabulate \
  Demos.Rcv.TabulateProgram.compiled.module rcvTabulate "$out"
"$ccomp" "$@" -I tools -Dmain=host_main -c tools/native-host.c -o "$out/host.o"
"$ccomp" "$@" -I tools -o "$out/rcv-tabulate-c" "$out/rcvTabulate.o" "$out/rcvTabulate_glue.c" \
  Demos/Rcv/tabulate.c "$out/host.o"
echo "native.sh: wrote $out/rcv-tabulate-c"
