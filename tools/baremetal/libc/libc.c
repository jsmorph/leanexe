/* The C library functions that tools/native-host.c uses, for its build without libc on QEMU's
   virt machine (docs/native-bare-metal.md, milestone B1).  Standard output goes to the UART
   through lx_out, and standard error too, with each line prefixed by "E:".  printf and fprintf
   know the conversions %s, %llu, %02x, and %d that the host uses.  malloc rounds each request up
   to a multiple of 16 bytes and takes it from a static arena of 16 MiB, and free does nothing,
   since each QEMU process runs one case.  fopen fails, so the host's file arguments are not
   available.  exit reports through the startup code's lx_exit.  main reads the command line
   from a block that QEMU's generic loader places at LX_ARGS: the number of arguments in
   decimal, then each argument, each ending with a zero byte, and calls the host's main, renamed
   host_main. */

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LX_ARGS 0x7F000000ULL

extern volatile unsigned int lx_out;
void lx_exit(int status);
int host_main(int argc, char **argv);

struct lx_file { int fd; int bol; };
static FILE out_file = {1, 1};
static FILE err_file = {2, 1};
FILE *stdout = &out_file;
FILE *stderr = &err_file;

static void put(FILE *f, char c) {
  if (f->fd == 2 && f->bol) { lx_out = 'E'; lx_out = ':'; }
  lx_out = (unsigned char) c;
  f->bol = c == '\n';
}

static void put_str(FILE *f, const char *s) { while (*s) put(f, *s++); }

static void put_dec(FILE *f, unsigned long long v) {
  char buf[24];
  int n = 0;
  do { buf[n++] = (char) ('0' + v % 10); v /= 10; } while (v != 0);
  while (n > 0) put(f, buf[--n]);
}

static int vformat(FILE *f, const char *fmt, va_list ap) {
  for (; *fmt; fmt++) {
    if (*fmt != '%') { put(f, *fmt); continue; }
    fmt++;
    if (*fmt == 's') {
      put_str(f, va_arg(ap, const char *));
    } else if (fmt[0] == 'l' && fmt[1] == 'l' && fmt[2] == 'u') {
      put_dec(f, va_arg(ap, unsigned long long));
      fmt += 2;
    } else if (fmt[0] == '0' && fmt[1] == '2' && fmt[2] == 'x') {
      unsigned int v = (unsigned int) va_arg(ap, int);
      put(f, "0123456789abcdef"[(v >> 4) & 15]);
      put(f, "0123456789abcdef"[v & 15]);
      fmt += 2;
    } else if (*fmt == 'd') {
      int v = va_arg(ap, int);
      if (v < 0) { put(f, '-'); put_dec(f, (unsigned long long) (-(long long) v)); }
      else put_dec(f, (unsigned long long) v);
    } else {
      put_str(f, "<bad format>");
    }
  }
  return 0;
}

int printf(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vformat(stdout, fmt, ap);
  va_end(ap);
  return 0;
}

int fprintf(FILE *f, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vformat(f, fmt, ap);
  va_end(ap);
  return 0;
}

void perror(const char *s) { put_str(stderr, s); put_str(stderr, ": error\n"); }
FILE *fopen(const char *path, const char *mode) { (void) path; (void) mode; return NULL; }
int fclose(FILE *f) { (void) f; return -1; }
int fseek(FILE *f, long o, int w) { (void) f; (void) o; (void) w; return -1; }
long ftell(FILE *f) { (void) f; return -1; }
size_t fread(void *p, size_t s, size_t n, FILE *f) { (void) p; (void) s; (void) n; (void) f; return 0; }
size_t fwrite(const void *p, size_t s, size_t n, FILE *f) { (void) p; (void) s; (void) n; (void) f; return 0; }

void exit(int status) { lx_exit(status); }

static unsigned long long arena[2097152];
static unsigned long long arena_used;

void *malloc(size_t n) {
  unsigned long long words = (n + 15) / 8 & ~1ULL;
  void *p;
  if (arena_used + words > sizeof arena / 8) { put_str(stderr, "out of memory\n"); lx_exit(1); }
  p = &arena[arena_used];
  arena_used += words;
  return p;
}

void *calloc(size_t n, size_t size) {
  unsigned char *p = malloc(n * size);
  size_t i;
  for (i = 0; i < n * size; i++) p[i] = 0;
  return p;
}

void free(void *p) { (void) p; }

unsigned long long strtoull(const char *s, char **end, int base) {
  unsigned long long v = 0;
  const char *c = s;
  (void) base;
  while (*c >= '0' && *c <= '9') { v = v * 10 + (unsigned long long) (*c - '0'); c++; }
  if (end) *end = (char *) c;
  return v;
}

size_t strlen(const char *s) { size_t n = 0; while (s[n]) n++; return n; }

int strcmp(const char *a, const char *b) {
  while (*a && *a == *b) { a++; b++; }
  return (unsigned char) *a - (unsigned char) *b;
}

int strncmp(const char *a, const char *b, size_t n) {
  for (; n > 0; n--, a++, b++) {
    if (*a != *b || *a == 0) return (unsigned char) *a - (unsigned char) *b;
  }
  return 0;
}

char *strchr(const char *s, int c) {
  for (;; s++) {
    if (*s == (char) c) return (char *) s;
    if (*s == 0) return NULL;
  }
}

void *memcpy(void *dst, const void *src, size_t n) {
  unsigned char *d = dst;
  const unsigned char *s = src;
  while (n-- > 0) *d++ = *s++;
  return dst;
}

int main(void) {
  char *p = (char *) LX_ARGS;
  char *argv[300];
  int argc, i;
  argc = (int) strtoull(p, NULL, 10);
  p += strlen(p) + 1;
  if (argc < 1 || argc > 299) { put_str(stderr, "bad argument block\n"); return 1; }
  for (i = 0; i < argc; i++) { argv[i] = p; p += strlen(p) + 1; }
  argv[argc] = NULL;
  return host_main(argc, argv);
}
