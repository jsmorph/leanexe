/* The parts of <string.h> that tools/native-host.c uses, for its build without libc. */
#include <stddef.h>
size_t strlen(const char *s);
int strcmp(const char *a, const char *b);
int strncmp(const char *a, const char *b, size_t n);
char *strchr(const char *s, int c);
void *memcpy(void *dst, const void *src, size_t n);
