/* Usage: fpemu VECTORS
   Runs the floating-point functions of the arm-v9.4-a model, as Sail's C back end compiles them
   (build.sh), on the vectors of the file VECTORS.  A line of VECTORS is FORM CLASS A B TALOS
   MODEL, with FORM one of fadd fsub fmul fdiv fsqrt ucvtf and A, B, TALOS, and MODEL 64-bit words
   in hexadecimal or MODEL "-".  For each line, fpemu sets up the state as model_init does, with
   FeatureImpl's entries for FEAT_AA64EL0 and FEAT_AA64EL1 set, as Vectors.lean does; computes
   FPAdd(A, B), FPSub(A, B), FPMul(A, B), FPDiv(A, B), FPSqrt(A), or FixedToFP(A) (unsigned,
   fbits 0, rounding TIEEVEN) at 64 bits under FPCR 0x02000000; and prints the line followed by
   the result in hexadecimal.

   Sail's C library computes reals as GMP rationals, exactly except in sqrt_real (sail.c), which
   returns an exact root when the numerator and denominator of its argument x are squares and
   otherwise stops Newton's iteration n = (p + x/p)/2 when |p - n| < c, with c = 10^-30 for
   x >= 1 and c = x * 10^-30 for x < 1, and returns n.  Each iterate n satisfies n >= sqrt(x) and
   n - sqrt(x) = (p - sqrt(x))^2 / 2p < |p - n|, so the result r satisfies
   0 <= r - sqrt(x) < c.  FPRound rounds r as it would sqrt(x) when no rounding boundary of
   binary64, a midpoint between adjacent doubles, lies within c of sqrt(x); the square root of a
   positive double lies in the range of normal doubles, so the overflow and subnormal boundaries
   do not apply.  For FPSqrt, fpemu prints three more fields: "none" when the operand is a NaN, a zero, an
   infinity, or negative, the cases in which FPSqrt does not call sqrt_real, followed by "- -";
   otherwise "resolved" or "unresolved", as the distance from sqrt(A) to the nearest midpoint is
   at least c or not, followed by lower bounds of that distance as a multiple of c and of half
   an ulp of sqrt(A).  The distance comes from GMP's integer square root with 128 bits below the
   half ulp.

   The slice cuts AArch64_FPTrappedException and AArch32_FPTrappedException, and the back end's
   model_main calls the model's main, which the slice lacks; fpemu defines the three to exit
   with a message, since FPCR 0x02000000 enables no trap and fpemu does not call model_main. */

#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <gmp.h>

#include "armv9fp.h"

/* The back end declares these in its header in C++ mode only. */
void model_init(void);
void model_fini(void);

static void fail(const char *msg, unsigned long line)
{
  fprintf(stderr, "fpemu: line %lu: %s\n", line, msg);
  exit(EXIT_FAILURE);
}

unit zAArch64_FPTrappedException(bool is_ase, uint64_t exceptions)
{
  fprintf(stderr, "fpemu: AArch64_FPTrappedException(%d, 0x%02" PRIx64 ") called\n", is_ase,
          exceptions);
  exit(EXIT_FAILURE);
}

unit zAArch32_FPTrappedException(uint64_t exceptions)
{
  fprintf(stderr, "fpemu: AArch32_FPTrappedException(0x%02" PRIx64 ") called\n", exceptions);
  exit(EXIT_FAILURE);
}

unit zmain(unit u)
{
  (void)u;
  fprintf(stderr, "fpemu: the model's main is not in the slice\n");
  exit(EXIT_FAILURE);
}

static void configure(unsigned long line)
{
  static const enum zFeature features[] = {zFEAT_AA64EL0, zFEAT_AA64EL1};
  model_init();
  for (size_t i = 0; i < sizeof features / sizeof features[0]; i++) {
    int64_t k = znum_of_Feature(features[i]);
    if (k < 0 || (uint64_t)k >= zFeatureImpl.len)
      fail("num_of_Feature out of FeatureImpl's bounds", line);
    zFeatureImpl.data[k] = true;
    if (!zIsFeatureImplemented(features[i]))
      fail("IsFeatureImplemented is false after the update", line);
  }
}

static sbits word(uint64_t x)
{
  sbits r = {64, x};
  return r;
}

static uint64_t result(sbits r, unsigned long line)
{
  if (have_exception)
    fail("the model threw an exception", line);
  if (r.len != 64)
    fail("the result is not 64 bits", line);
  return r.bits;
}

static uint64_t compute(const char *form, uint64_t a, uint64_t b, unsigned long line)
{
  const struct zFPCRType fpcr = {UINT64_C(0x02000000)};
  if (strcmp(form, "fadd") == 0)
    return result(zFPAdd(word(a), word(b), fpcr), line);
  if (strcmp(form, "fsub") == 0)
    return result(zFPSub(word(a), word(b), fpcr), line);
  if (strcmp(form, "fmul") == 0)
    return result(zFPMul(word(a), word(b), fpcr), line);
  if (strcmp(form, "fdiv") == 0)
    return result(zFPDiv(word(a), word(b), fpcr), line);
  if (strcmp(form, "fsqrt") == 0)
    return result(zFPSqrt(word(a), fpcr), line);
  if (strcmp(form, "ucvtf") == 0) {
    sail_int fbits;
    CREATE(sail_int)(&fbits);
    CONVERT_OF(sail_int, mach_int)(&fbits, 0);
    sbits r = zFixedToFP(word(a), fbits, true, fpcr, zFPRounding_TIEEVEN, 64);
    KILL(sail_int)(&fbits);
    return result(r, line);
  }
  fail("unknown form", line);
  return 0;
}

static long floor_half(long b)
{
  return b >= 0 ? b / 2 : -((1 - b) / 2);
}

/* Multiplies q by 2^k for an integer k of either sign. */
static void scale2(mpq_t q, long k)
{
  if (k >= 0)
    mpq_mul_2exp(q, q, (mp_bitcnt_t)k);
  else
    mpq_div_2exp(q, q, (mp_bitcnt_t)-k);
}

/* For a positive finite double a of value v = m * 2^e, scales sqrt(v) by 2^F to
   S in [2^(G+53), 2^(G+54)), where an ulp is 2^(G+1) and the midpoint between the doubles
   Q * 2^(G+1) and (Q+1) * 2^(G+1) is Q * 2^(G+1) + 2^G, computes T = floor(S) and a lower bound
   D of the distance from S to the nearest midpoint, and prints D / (c * 2^F) and D / 2^G. */
static void margin(uint64_t a, unsigned long line)
{
  const long G = 128;
  uint64_t ex = (a >> 52) & 0x7ff;
  uint64_t fr = a & ((UINT64_C(1) << 52) - 1);
  uint64_t m = ex ? fr | (UINT64_C(1) << 52) : fr;
  long e = ex ? (long)ex - 1075 : -1074;
  long b = 63 - __builtin_clzll(m) + e;
  long q = floor_half(b);
  long F = G + 53 - q;
  if (e + 2 * F < 0)
    fail("margin: negative scale", line);
  mpz_t n, t, rem, k, mid, d, d2;
  mpz_inits(n, t, rem, k, mid, d, d2, NULL);
  mpz_set_ui(n, m);
  mpz_mul_2exp(n, n, (mp_bitcnt_t)(e + 2 * F));
  mpz_sqrtrem(t, rem, n);
  bool exact = mpz_sgn(rem) == 0;
  mpz_fdiv_q_2exp(k, t, (mp_bitcnt_t)(G + 1));
  if (mpz_sizeinbase(k, 2) != 53)
    fail("margin: significand out of range", line);
  mpz_mul_2exp(mid, k, (mp_bitcnt_t)(G + 1));
  mpz_setbit(mid, (mp_bitcnt_t)G);
  if (mpz_cmp(t, mid) >= 0) {
    mpz_sub(d, t, mid);
  } else {
    mpz_sub(d, mid, t);
    if (!exact)
      mpz_sub_ui(d, d, 1);
  }
  if (mpz_scan1(k, 0) == 52) {
    /* The midpoint below the binade, 2^(G+53) - 2^(G-1). */
    mpz_set_ui(d2, 0);
    mpz_setbit(d2, (mp_bitcnt_t)(G + 53));
    mpz_set_ui(mid, 0);
    mpz_setbit(mid, (mp_bitcnt_t)(G - 1));
    mpz_sub(d2, d2, mid);
    mpz_sub(d2, t, d2);
    if (mpz_cmp(d2, d) < 0)
      mpz_set(d, d2);
  }
  mpq_t ratio, half;
  mpq_inits(ratio, half, NULL);
  mpz_ui_pow_ui(k, 10, 30);
  mpz_mul(k, k, d);
  mpq_set_z(ratio, k);
  scale2(ratio, -F);
  if (b < 0) {
    mpq_t mq;
    mpq_init(mq);
    mpq_set_ui(mq, m, 1);
    mpq_div(ratio, ratio, mq);
    scale2(ratio, -e);
    mpq_clear(mq);
  }
  mpq_set_z(half, d);
  scale2(half, -G);
  printf(" %s %.6e %.6e", mpq_cmp_ui(ratio, 1, 1) >= 0 ? "resolved" : "unresolved",
         mpq_get_d(ratio), mpq_get_d(half));
  mpq_clears(ratio, half, NULL);
  mpz_clears(n, t, rem, k, mid, d, d2, NULL);
}

static bool reaches_sqrt(uint64_t a)
{
  uint64_t ex = (a >> 52) & 0x7ff;
  return (a >> 63) == 0 && ex != 0x7ff && (a << 1) != 0;
}

int main(int argc, char *argv[])
{
  if (argc != 2) {
    fprintf(stderr, "usage: fpemu VECTORS\n");
    return 2;
  }
  FILE *f = fopen(argv[1], "r");
  if (f == NULL) {
    perror(argv[1]);
    return 1;
  }
  char buf[256];
  unsigned long line = 0;
  while (fgets(buf, sizeof buf, f) != NULL) {
    line++;
    size_t len = strlen(buf);
    if (len == 0 || buf[len - 1] != '\n')
      fail("line too long or unterminated", line);
    buf[len - 1] = '\0';
    char form[16], cls[64], talos[32], model[32];
    uint64_t a, b;
    if (sscanf(buf, "%15s %63s %" SCNx64 " %" SCNx64 " %31s %31s", form, cls, &a, &b, talos,
               model) != 6)
      fail("malformed line", line);
    configure(line);
    uint64_t r = compute(form, a, b, line);
    model_fini();
    printf("%s %016" PRIx64, buf, r);
    if (strcmp(form, "fsqrt") == 0) {
      if (reaches_sqrt(a))
        margin(a, line);
      else
        printf(" none - -");
    }
    putchar('\n');
  }
  if (ferror(f)) {
    perror(argv[1]);
    return 1;
  }
  fclose(f);
  if (fflush(stdout) != 0 || ferror(stdout)) {
    perror("stdout");
    return 1;
  }
  return 0;
}
