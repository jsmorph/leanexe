/* The command `bench` of the host of a translated module, for tests/native/bench.sh, which links
   this file with its translation, its glue, and tools/native-host.c compiled with
   -Dmain=host_main.  `bench SECONDS MAX FUNC RESULT [ARG...]`, which tools/wasmtime-host.c also
   takes, calls the export once to warm up, and then repeatedly until SECONDS have passed or MAX
   timed calls have run.  Before each call it places the arguments again, since a call may
   consume them, and it times only the call, with CLOCK_MONOTONIC.  It prints the results of the
   last call as `call` does, then `bench N NS`, the number of timed calls and their total time in
   nanoseconds.  Every other command goes to the main of tools/native-host.c. */

/* For clock_gettime and CLOCK_MONOTONIC. */
#define _POSIX_C_SOURCE 199309L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "native-host.h"
#include "native-call.h"

typedef unsigned long long u64;

int host_main(int argc, char **argv);

static u64 now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (u64)t.tv_sec * 1000000000ULL + (u64)t.tv_nsec;
}

static void bench_export(const char *seconds, const char *max, const char *func_name,
                         const char *result_kind, int argc, char **argv) {
  const lx_export *e = host_get_export(func_name);
  u64 args[256];
  u64 results[128];
  u64 limit = (u64)(atof(seconds) * 1e9), most = host_parse_u64(max);
  u64 start, count = 0, total = 0, before, after;
  size_t nresults = host_place_args(e, func_name, result_kind, argc, argv, args);
  host_invoke(e, args, results);
  start = now_ns();
  while (count < most && now_ns() - start < limit) {
    host_place_args(e, func_name, result_kind, argc, argv, args);
    before = now_ns();
    host_invoke(e, args, results);
    after = now_ns();
    total += after - before;
    count++;
  }
  host_print_results(result_kind, results, nresults);
  printf("bench %llu %llu\n", count, total);
}

int main(int argc, char **argv) {
  if (argc < 2 || strcmp(argv[1], "bench") != 0) {
    return host_main(argc, argv);
  }
  if (argc < 6) {
    fprintf(stderr, "usage: HOST call|call-stats FUNC RESULT [ARG...]\n"
                    "       HOST bench SECONDS MAX FUNC RESULT [ARG...]\n");
    exit(2);
  }
  host_start();
  bench_export(argv[2], argv[3], argv[4], argv[5], argc - 6, argv + 6);
  return 0;
}
