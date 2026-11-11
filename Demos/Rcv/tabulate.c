/* The tabulator translated to C.  `rcv-tabulate-c FILE` and `rcv-maine-c FILE` read the canonical
   ballot file FILE, call the export `tabulate` of the translation that they are linked with,
   compiled with CompCert, and write the report to standard output.  tests/rcv/native.sh links
   this file with the translation of `Demos.Rcv.TabulateProgram.compiled.module` into
   rcv-tabulate-c, and with the argument maine, with PROGRAM defined as "rcv-maine-c", with the
   translation of `Demos.Rcv.Maine.TabulateProgram.compiled.module` into rcv-maine-c.  Each links
   the translation's export tables and tools/native-host.c compiled with -Dmain=host_main, and
   PROGRAM names the executable in its messages.  The host's `bytes-file:` argument places the
   file's bytes in a block that the module's `alloc` returns, as the Wasmtime host does, and
   `host_invoke` reads `lx_status` after the call, so a trap ends the program with status 2 and
   the trap's message on standard error.  A wrong number of arguments, a file that cannot be read,
   a report outside memory, or a failed write ends it with status 1. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "native-host.h"
#include "native-call.h"

#ifndef PROGRAM
#define PROGRAM "rcv-tabulate-c"
#endif

typedef unsigned long long u64;

int main(int argc, char **argv) {
  const lx_export *e;
  u64 args[2];
  u64 results[2];
  u64 size;
  char *spec;
  size_t n;
  if (argc != 2) {
    fprintf(stderr, "usage: " PROGRAM " FILE\n");
    return 1;
  }
  n = strlen(argv[1]);
  spec = malloc(n + 12);
  if (spec == NULL) {
    fprintf(stderr, PROGRAM ": out of memory\n");
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
    fprintf(stderr, PROGRAM ": the report lies outside memory\n");
    return 1;
  }
  if (fwrite((unsigned char *)lx_mem + results[0], 1, (size_t)results[1], stdout) !=
          (size_t)results[1] ||
      fflush(stdout) != 0) {
    perror(PROGRAM ": stdout");
    return 1;
  }
  return 0;
}
