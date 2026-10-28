/* The interface between tools/native-host.c and a translated module.  The module's C text
   defines the lx_ globals, lx_init, and its functions; its glue, which native-verified writes,
   defines the tables of its exported functions and globals. */

/* An exported function: its name, one letter per parameter and per result (i for unsigned
   int, l for unsigned long long, f for float, d for double), and a function that calls it with
   the arguments `args` and stores its results in `results`, each as the bits of its value. */
typedef struct {
  const char *name;
  const char *params;
  const char *results;
  void (*call)(const unsigned long long *args, unsigned long long *results);
} lx_export;

/* An exported global, an unsigned long long. */
typedef struct {
  const char *name;
  unsigned long long *value;
} lx_global_export;

extern const lx_export lx_exports[];
extern const int lx_export_count;
extern const lx_global_export lx_global_exports[];
extern const int lx_global_export_count;

extern unsigned int lx_status;
extern unsigned int lx_pages;
extern unsigned long long lx_mem[];
void lx_init(void);
