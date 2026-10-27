/* The parts of <stdlib.h> that tools/native-host.c uses, for its build without libc. */
#include <stddef.h>
void exit(int status);
void *malloc(size_t n);
void *calloc(size_t n, size_t size);
void free(void *p);
unsigned long long strtoull(const char *s, char **end, int base);
