/* The functions of tools/native-host.c that tools/native-bench.c calls.  A file that includes
   this header includes tools/native-host.h first. */

#include <stddef.h>

/* Calls lx_init, then the export `reset` when the module has it, and exits with status 1 when
   lx_init traps. */
void host_start(void);

/* The export named `name`, or exit with status 1 when the module has none. */
const lx_export *host_get_export(const char *name);

/* Places the arguments `argv` of a call of `e` into `args` and returns the number of results
   that `result_kind` describes, after checking both against the type of `e`. */
size_t host_place_args(const lx_export *e, const char *func_name, const char *result_kind,
                       int argc, char **argv, unsigned long long *args);

/* Calls `e` and exits with status 2 after a trap. */
void host_invoke(const lx_export *e, const unsigned long long *args, unsigned long long *results);

/* Prints the results of a call as `result_kind` describes them. */
void host_print_results(const char *result_kind, const unsigned long long *results,
                        size_t nresults);

/* The decimal number `text`, or exit with status 1 when it is not one. */
unsigned long long host_parse_u64(const char *text);
