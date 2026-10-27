/* The parts of <stdio.h> that tools/native-host.c uses, for its build without libc. */
#include <stddef.h>
typedef struct lx_file FILE;
extern FILE *stdout;
extern FILE *stderr;
#define SEEK_SET 0
#define SEEK_END 2
int printf(const char *format, ...);
int fprintf(FILE *file, const char *format, ...);
void perror(const char *s);
FILE *fopen(const char *path, const char *mode);
int fclose(FILE *file);
int fseek(FILE *file, long offset, int whence);
long ftell(FILE *file);
size_t fread(void *p, size_t size, size_t n, FILE *file);
size_t fwrite(const void *p, size_t size, size_t n, FILE *file);
