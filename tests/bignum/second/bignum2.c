/*
 * Runs the C translation of the second iteration's module, the program of the theorems of
 * Native.lean, compiled with CompCert, on the cases of check.mjs's cases.txt, one per line: the
 * case's kind and its arguments separated by '|', a natural as its limbs separated by ',', an
 * integer as its sign word, ':', and its limbs, and a text as its words.
 *
 * A case natMul calls lxf_natMulKara, and lxf_natMulKaraWith at the threshold 16, intMul calls
 * lxf_intMulKara, and read calls lxf_intOfTextDC and lxf_natOfTextDC on the same text, and
 * lxf_natOfTextDCWith with the threshold 48 and the bound 16 on the base elements; the host
 * requires the entry with parameters to return the words of the export.  The host calls lx_init once, allocates each array through
 * the module's alloc and writes its length word and words, as the theorems' premises require of
 * the store, calls the export, prints its result in the format of check.mjs's module.txt from the
 * returned word or the result globals, and releases every argument and result through the module's
 * release, so the store is ready for the next call.  It exits with status 1 when a call traps.
 * No theorem covers this file.  Usage: bignum2 < cases.txt
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern unsigned int lx_status;
extern unsigned long long lx_mem[];
extern unsigned long long lx_r0_l, lx_r1_l, lx_r2_l;
void lx_init(void);
unsigned long long lxf_alloc(unsigned long long bytes);
void lxf_release(unsigned long long p);
unsigned long long lxf_natMulKara(unsigned long long u, unsigned long long v);
unsigned long long lxf_natMulKaraWith(unsigned long long t, unsigned long long u, unsigned long long v);
void lxf_natOfTextDCWith(unsigned long long t, unsigned long long e, unsigned long long s);
void lxf_intMulKara(unsigned long long n1, unsigned long long m1, unsigned long long n2,
                    unsigned long long m2);
void lxf_natOfTextDC(unsigned long long s);
void lxf_intOfTextDC(unsigned long long s);

static unsigned char *bytes(void) { return (unsigned char *)lx_mem; }

static void store(unsigned long long a, unsigned long long w) {
  int i;
  for (i = 0; i < 8; i++) bytes()[a + i] = (unsigned char)(w >> (8 * i));
}

static unsigned long long load(unsigned long long a) {
  unsigned long long w = 0;
  int i;
  for (i = 7; i >= 0; i--) w = (w << 8) | bytes()[a + i];
  return w;
}

static void check(void) {
  if (lx_status != 0) {
    fprintf(stderr, "bignum2: a call trapped with code %u\n", lx_status);
    exit(1);
  }
}

#define MAXW (1 << 20)
static char line[1 << 24];
static char *fields[8];
static unsigned long long words[MAXW];
static unsigned long long owned[8];
static int nowned;

/* The array of the words of the text s, separated by ',', placed in lx_mem. */
static unsigned long long array(char *f) {
  unsigned long long n = 0, p, k;
  char *s = f, *end;
  for (;;) {
    unsigned long long w = strtoull(s, &end, 10);
    if (end == s) break;
    if (n == MAXW) {
      fprintf(stderr, "bignum2: more than %d words\n", MAXW);
      exit(1);
    }
    words[n++] = w;
    s = end;
    if (*s == ',') s++;
  }
  p = lxf_alloc(8 + 8 * n);
  check();
  store(p, n);
  for (k = 0; k < n; k++) store(p + 8 + 8 * k, words[k]);
  owned[nowned++] = p;
  return p;
}

/* Whether the arrays at p and q hold the same words. */
static int same(unsigned long long p, unsigned long long q) {
  unsigned long long n = load(p), k;
  if (n != load(q)) return 0;
  for (k = 0; k < n; k++)
    if (load(p + 8 + 8 * k) != load(q + 8 + 8 * k)) return 0;
  return 1;
}

static void differ(const char *what) {
  fprintf(stderr, "bignum2: %s differs from the export\n", what);
  exit(1);
}

/* Prints the array at p as [a,b,...] and releases it. */
static void put(unsigned long long p) {
  unsigned long long n = load(p), k;
  putchar('[');
  for (k = 0; k < n; k++) printf(k ? ",%llu" : "%llu", load(p + 8 + 8 * k));
  putchar(']');
  lxf_release(p);
}

int main(void) {
  unsigned long long count = 0;
  lx_init();
  while (fgets(line, sizeof line, stdin)) {
    int nf = 0, k;
    char *s = line, *op;
    line[strcspn(line, "\n")] = 0;
    for (;;) {
      fields[nf++] = s;
      s = strchr(s, '|');
      if (!s || nf == 8) break;
      *s++ = 0;
    }
    op = fields[0];
    nowned = 0;
    if (!strcmp(op, "natMul")) {
      unsigned long long u = array(fields[1]), v = array(fields[2]);
      unsigned long long r = lxf_natMulKara(u, v), r16;
      check();
      r16 = lxf_natMulKaraWith(16, u, v);
      check();
      if (!same(r, r16)) differ("natMulKaraWith");
      lxf_release(r16);
      put(r);
    } else if (!strcmp(op, "intMul")) {
      char *c1 = strchr(fields[1], ':'), *c2 = strchr(fields[2], ':');
      unsigned long long n1, m1, n2, m2;
      *c1 = 0; *c2 = 0;
      n1 = strtoull(fields[1], NULL, 10); m1 = array(c1 + 1);
      n2 = strtoull(fields[2], NULL, 10); m2 = array(c2 + 1);
      lxf_intMulKara(n1, m1, n2, m2);
      check();
      printf("%llu:", lx_r0_l);
      put(lx_r1_l);
    } else if (!strcmp(op, "read")) {
      unsigned long long a = array(fields[1]);
      lxf_intOfTextDC(a);
      check();
      printf("%llu:%llu:", lx_r0_l, lx_r1_l);
      put(lx_r2_l);
      putchar(';');
      lxf_natOfTextDC(a);
      check();
      {
        unsigned long long f = lx_r0_l, m = lx_r1_l;
        lxf_natOfTextDCWith(48, 16, a);
        check();
        if (lx_r0_l != f || !same(m, lx_r1_l)) differ("natOfTextDCWith");
        lxf_release(lx_r1_l);
        printf("%llu:", f);
        put(m);
      }
    } else {
      fprintf(stderr, "bignum2: unknown case %s\n", op);
      return 1;
    }
    putchar('\n');
    for (k = 0; k < nowned; k++) lxf_release(owned[k]);
    count++;
  }
  fprintf(stderr, "bignum2: %llu calls\n", count);
  return 0;
}
