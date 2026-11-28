/*
 * Runs the C translation of the third iteration's module, the program of the theorems of
 * Native.lean, compiled with CompCert, on the cases of check.mjs's cases.txt, one per line: the
 * case's kind and its arguments separated by '|', a natural as its limbs separated by ',', and an
 * integer as its sign word, ':', and its limbs.
 *
 * A case natDiv calls lxf_natDivModCheckedBZ, and lxf_natDivModCheckedBZWith at the thresholds 16
 * for the product, 4 for the base case, and 2 for the top level, which take the recursive path on
 * every divisor of at least two limbs and every dividend at least two limbs longer; intDiv calls
 * lxf_intTDivModCheckedBZ and lxf_intEDivModCheckedBZ; print calls lxf_natToTextDC, and
 * lxf_natToTextDCWith at the thresholds 16 and 4, the leaf level 1, and the printer's threshold 0,
 * on the natural, and lxf_intToTextDC on the integer with the same limbs, negative when it is not
 * zero.  The host requires each entry with parameters to return the words of its export.  The
 * host calls lx_init once, allocates each array through the module's alloc and writes its length
 * word and words, as the theorems' premises require of the store, calls the export, prints its
 * result in the format of check.mjs's module.txt from the returned word or the result globals, and
 * releases every argument and result through the module's release, so the store is ready for the
 * next call.  It exits with status 1 when a call traps.  No theorem covers this file.
 * Usage: bignum3 < cases.txt
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern unsigned int lx_status;
extern unsigned long long lx_mem[];
extern unsigned long long lx_r0_l, lx_r1_l, lx_r2_l, lx_r3_l, lx_r4_l;
void lx_init(void);
unsigned long long lxf_alloc(unsigned long long bytes);
void lxf_release(unsigned long long p);
void lxf_natDivModCheckedBZWith(unsigned long long t, unsigned long long T, unsigned long long D,
                                unsigned long long u, unsigned long long v);
void lxf_natDivModCheckedBZ(unsigned long long u, unsigned long long v);
void lxf_intTDivModCheckedBZ(unsigned long long n1, unsigned long long m1, unsigned long long n2,
                             unsigned long long m2);
void lxf_intEDivModCheckedBZ(unsigned long long n1, unsigned long long m1, unsigned long long n2,
                             unsigned long long m2);
unsigned long long lxf_natToTextDCWith(unsigned long long t, unsigned long long T,
                                       unsigned long long L, unsigned long long P,
                                       unsigned long long u);
unsigned long long lxf_natToTextDC(unsigned long long u);
unsigned long long lxf_intToTextDC(unsigned long long n, unsigned long long m);

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
    fprintf(stderr, "bignum3: a call trapped with code %u\n", lx_status);
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
      fprintf(stderr, "bignum3: more than %d words\n", MAXW);
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
  fprintf(stderr, "bignum3: %s differs from the export\n", what);
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

/* An integer argument "sign:limbs": the sign word, and the limbs placed in lx_mem. */
static void integer(char *f, unsigned long long *n, unsigned long long *m) {
  char *c = strchr(f, ':');
  *c = 0;
  *n = strtoull(f, NULL, 10);
  *m = array(c + 1);
}

/* Prints the five results of an integer division, status:sign:[q]:sign:[r], and releases them. */
static void putDiv(void) {
  unsigned long long s = lx_r0_l, qn = lx_r1_l, q = lx_r2_l, rn = lx_r3_l, r = lx_r4_l;
  printf("%llu:%llu:", s, qn);
  put(q);
  printf(":%llu:", rn);
  put(r);
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
    if (!strcmp(op, "natDiv")) {
      unsigned long long u = array(fields[1]), v = array(fields[2]);
      unsigned long long st, q, r;
      lxf_natDivModCheckedBZ(u, v);
      check();
      st = lx_r0_l; q = lx_r1_l; r = lx_r2_l;
      lxf_natDivModCheckedBZWith(16, 4, 2, u, v);
      check();
      if (lx_r0_l != st || !same(q, lx_r1_l) || !same(r, lx_r2_l)) differ("natDivModCheckedBZWith");
      lxf_release(lx_r1_l);
      lxf_release(lx_r2_l);
      printf("%llu:", st);
      put(q);
      putchar(':');
      put(r);
    } else if (!strcmp(op, "intDiv")) {
      unsigned long long n1, m1, n2, m2;
      integer(fields[1], &n1, &m1);
      integer(fields[2], &n2, &m2);
      lxf_intTDivModCheckedBZ(n1, m1, n2, m2);
      check();
      putDiv();
      putchar(';');
      lxf_intEDivModCheckedBZ(n1, m1, n2, m2);
      check();
      putDiv();
    } else if (!strcmp(op, "print")) {
      unsigned long long u = array(fields[1]);
      unsigned long long t = lxf_natToTextDC(u), tw, tn;
      check();
      tw = lxf_natToTextDCWith(16, 4, 1, 0, u);
      check();
      if (!same(t, tw)) differ("natToTextDCWith");
      lxf_release(tw);
      put(t);
      putchar(';');
      tn = lxf_intToTextDC(load(u) != 0, u);
      check();
      put(tn);
    } else {
      fprintf(stderr, "bignum3: unknown case %s\n", op);
      return 1;
    }
    putchar('\n');
    for (k = 0; k < nowned; k++) lxf_release(owned[k]);
    count++;
  }
  fprintf(stderr, "bignum3: %llu calls\n", count);
  return 0;
}
