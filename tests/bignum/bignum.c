/*
 * Runs the C translation of the bignum module, the program of the theorems of Native.lean,
 * compiled with CompCert, on the calls of check.mjs's calls.txt, one per line: the export's name
 * and its arguments separated by '|', a natural as its limbs and a text as its words, separated
 * by ',', and an integer as its sign word followed by its limbs.
 *
 * The host calls lx_init once, allocates each array through the module's alloc and writes its
 * length word and words, as the theorems' premises require of the store, calls the export, prints
 * its result in the format of check.mjs's module.txt from the returned word or the result globals,
 * and releases every argument and result through the module's release, so the store is ready for
 * the next call.  It exits with status 1 when a call traps.  No theorem covers this file.
 * Usage: bignum < calls.txt
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
unsigned long long lxf_natTrim(unsigned long long u);
unsigned long long lxf_natCmp(unsigned long long u, unsigned long long v);
unsigned long long lxf_natAdd(unsigned long long u, unsigned long long v);
void lxf_natSub(unsigned long long u, unsigned long long v);
unsigned long long lxf_natMul(unsigned long long u, unsigned long long v);
void lxf_natDivModChecked(unsigned long long u, unsigned long long v);
void lxf_intNeg(unsigned long long n, unsigned long long m);
unsigned long long lxf_intCmp(unsigned long long n1, unsigned long long m1, unsigned long long n2,
                              unsigned long long m2);
void lxf_intAdd(unsigned long long, unsigned long long, unsigned long long, unsigned long long);
void lxf_intSub(unsigned long long, unsigned long long, unsigned long long, unsigned long long);
void lxf_intMul(unsigned long long, unsigned long long, unsigned long long, unsigned long long);
void lxf_intTDivModChecked(unsigned long long, unsigned long long, unsigned long long,
                           unsigned long long);
void lxf_intEDivModChecked(unsigned long long, unsigned long long, unsigned long long,
                           unsigned long long);
unsigned long long lxf_intToText(unsigned long long n, unsigned long long m);
void lxf_intOfText(unsigned long long s);
void lxf_textNeg(unsigned long long s);
void lxf_textCmp(unsigned long long s, unsigned long long t);
void lxf_textAdd(unsigned long long s, unsigned long long t);
void lxf_textSub(unsigned long long s, unsigned long long t);
void lxf_textMul(unsigned long long s, unsigned long long t);
void lxf_textTDiv(unsigned long long s, unsigned long long t);
void lxf_textTMod(unsigned long long s, unsigned long long t);
void lxf_textEDiv(unsigned long long s, unsigned long long t);
void lxf_textEMod(unsigned long long s, unsigned long long t);

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
    fprintf(stderr, "bignum: a call trapped with code %u\n", lx_status);
    exit(1);
  }
}

#define MAXW (1 << 20)
static char line[1 << 24];
static char *fields[8];
static unsigned long long words[MAXW];
static unsigned long long owned[8];
static int nowned;

/* The array of the words of field f in lx_mem. */
static unsigned long long array(char *f) {
  unsigned long long n = 0, p, k;
  char *s = f, *end;
  for (;;) {
    unsigned long long w = strtoull(s, &end, 10);
    if (end == s) break;
    if (n == MAXW) {
      fprintf(stderr, "bignum: more than %d words\n", MAXW);
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

static unsigned long long word(char *f) { return strtoull(f, NULL, 10); }

/* Prints the array at p as [a,b,...] and releases it. */
static void put(unsigned long long p) {
  unsigned long long n = load(p), k;
  putchar('[');
  for (k = 0; k < n; k++) printf(k ? ",%llu" : "%llu", load(p + 8 + 8 * k));
  putchar(']');
  lxf_release(p);
}

static void rec(unsigned long long n, unsigned long long p) {
  printf("%llu:", n);
  put(p);
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
#define NAT2 unsigned long long u = array(fields[1]), v = array(fields[2])
#define INT2 unsigned long long n1 = word(fields[1]), m1 = array(fields[2]), \
    n2 = word(fields[3]), m2 = array(fields[4])
#define TXT2 unsigned long long a = array(fields[1]), b = array(fields[2])
    if (!strcmp(op, "natTrim")) { unsigned long long u = array(fields[1]); unsigned long long r = lxf_natTrim(u); check(); put(r); }
    else if (!strcmp(op, "natCmp")) { NAT2; unsigned long long r = lxf_natCmp(u, v); check(); printf("%llu", r); }
    else if (!strcmp(op, "natAdd")) { NAT2; unsigned long long r = lxf_natAdd(u, v); check(); put(r); }
    else if (!strcmp(op, "natSub")) { NAT2; lxf_natSub(u, v); check(); printf("%llu;", lx_r0_l); put(lx_r1_l); }
    else if (!strcmp(op, "natMul")) { NAT2; unsigned long long r = lxf_natMul(u, v); check(); put(r); }
    else if (!strcmp(op, "natDivMod")) {
      NAT2; unsigned long long q, r; lxf_natDivModChecked(u, v); check();
      q = lx_r1_l; r = lx_r2_l; printf("%llu;", lx_r0_l); put(q); putchar(';'); put(r);
    }
    else if (!strcmp(op, "intNeg")) {
      unsigned long long n = word(fields[1]), m = array(fields[2]); lxf_intNeg(n, m); check();
      rec(lx_r0_l, lx_r1_l);
    }
    else if (!strcmp(op, "intCmp")) { INT2; unsigned long long r = lxf_intCmp(n1, m1, n2, m2); check(); printf("%llu", r); }
    else if (!strcmp(op, "intAdd")) { INT2; lxf_intAdd(n1, m1, n2, m2); check(); rec(lx_r0_l, lx_r1_l); }
    else if (!strcmp(op, "intSub")) { INT2; lxf_intSub(n1, m1, n2, m2); check(); rec(lx_r0_l, lx_r1_l); }
    else if (!strcmp(op, "intMul")) { INT2; lxf_intMul(n1, m1, n2, m2); check(); rec(lx_r0_l, lx_r1_l); }
    else if (!strcmp(op, "intTDivModChecked") || !strcmp(op, "intEDivModChecked")) {
      INT2; unsigned long long st, qn, qp, rn, rp;
      if (op[3] == 'T') lxf_intTDivModChecked(n1, m1, n2, m2); else lxf_intEDivModChecked(n1, m1, n2, m2);
      check();
      st = lx_r0_l; qn = lx_r1_l; qp = lx_r2_l; rn = lx_r3_l; rp = lx_r4_l;
      printf("%llu;", st); rec(qn, qp); putchar(';'); rec(rn, rp);
    }
    else if (!strcmp(op, "intToText")) {
      unsigned long long n = word(fields[1]), m = array(fields[2]); unsigned long long r = lxf_intToText(n, m);
      check(); put(r);
    }
    else if (!strcmp(op, "intOfText")) {
      unsigned long long a = array(fields[1]); lxf_intOfText(a); check();
      printf("%llu;", lx_r0_l); rec(lx_r1_l, lx_r2_l);
    }
    else if (!strcmp(op, "textNeg")) { unsigned long long a = array(fields[1]); lxf_textNeg(a); check(); printf("%llu;", lx_r0_l); put(lx_r1_l); }
    else if (!strcmp(op, "textCmp")) { TXT2; lxf_textCmp(a, b); check(); printf("%llu;%llu", lx_r0_l, lx_r1_l); }
    else if (!strncmp(op, "text", 4)) {
      TXT2;
      if (!strcmp(op, "textAdd")) lxf_textAdd(a, b);
      else if (!strcmp(op, "textSub")) lxf_textSub(a, b);
      else if (!strcmp(op, "textMul")) lxf_textMul(a, b);
      else if (!strcmp(op, "textTDiv")) lxf_textTDiv(a, b);
      else if (!strcmp(op, "textTMod")) lxf_textTMod(a, b);
      else if (!strcmp(op, "textEDiv")) lxf_textEDiv(a, b);
      else if (!strcmp(op, "textEMod")) lxf_textEMod(a, b);
      else { fprintf(stderr, "bignum: unknown export %s\n", op); return 1; }
      check(); printf("%llu;", lx_r0_l); put(lx_r1_l);
    } else {
      fprintf(stderr, "bignum: unknown export %s\n", op);
      return 1;
    }
    putchar('\n');
    for (k = 0; k < nowned; k++) lxf_release(owned[k]);
    count++;
  }
  fprintf(stderr, "bignum: %llu calls\n", count);
  return 0;
}
