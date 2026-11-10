/* The tabulator translated to C.  `rcv-tabulate-c FILE` reads the canonical ballot file FILE,
   calls the export `tabulate` of the translation of `Demos.Rcv.TabulateProgram.compiled.module`,
   compiled with CompCert, and writes the report to standard output.  tests/rcv/native.sh links it
   with the translation, its export tables, and tools/native-host.c compiled with
   -Dmain=host_main.  The host's `bytes-file:` argument places the file's bytes in a block that
   the module's `alloc` returns, as the Wasmtime host does, and `host_invoke` reads `lx_status`
   after the call, so a trap ends the program with status 2 and the trap's message on standard
   error.  A wrong number of arguments, a file that cannot be read, a report outside memory, or a
   failed write ends it with status 1. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "native-host.h"
#include "native-call.h"

typedef unsigned long long u64;

int main(int argc, char **argv) {
  const lx_export *e;
  u64 args[2];
  u64 results[2];
  u64 size;
  char *spec;
  size_t n;
  if (argc != 2) {
    fprintf(stderr, "usage: rcv-tabulate-c FILE\n");
    return 1;
  }
  n = strlen(argv[1]);
  spec = malloc(n + 12);
  if (spec == NULL) {
    fprintf(stderr, "rcv-tabulate-c: out of memory\n");
    return 1;
  }
  memcpy(spec, "bytes-file:", 11);
  memcpy(spec + 11, argv[1], n + 1);
  host_start();
  e = host_get_export("tabulate");
  host_place_args(e, "tabulate", "bytes", 1, &spec, args);
  free(spec);
  host_invoke(e, args, results);
  size = (u64)lx_pages * 65536;
  if (results[0] > size || results[1] > size - results[0]) {
    fprintf(stderr, "rcv-tabulate-c: the report lies outside memory\n");
    return 1;
  }
  if (fwrite((unsigned char *)lx_mem + results[0], 1, (size_t)results[1], stdout) !=
          (size_t)results[1] ||
      fflush(stdout) != 0) {
    perror("rcv-tabulate-c: stdout");
    return 1;
  }
  return 0;
}
