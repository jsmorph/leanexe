/* A program in the form of the translator's output, with a main that writes nine words in
   hexadecimal through lx_out, a volatile global at the UART's data register, and returns 42.
   The words are a recursion of depth 900 and its status, the same recursion past the depth limit
   of 1,000 and its status 1, the bits and the truncation of a sum of square roots computed
   through __builtin_fsqrt with the canonical-NaN test through lx_pun, an in-bounds update of
   lx_mem, and an out-of-bounds update with its status 2. */

unsigned int lx_status = 0U;
unsigned long long lx_g0 = 4096ULL;
unsigned int lx_pages = 16U;
unsigned long long lx_mem[33554432];
unsigned long long lx_pun[1];
extern volatile unsigned int lx_out;

unsigned long long lxf_depth(unsigned long long d, unsigned long long n) {
  unsigned long long r;
  if (d >= 1000ULL) { lx_status = 1U; return 0ULL; }
  if (n == 0ULL) return 0ULL;
  r = lxf_depth(d + 1ULL, n - 1ULL);
  if (lx_status != 0U) return 0ULL;
  return r + 1ULL;
}

double lxf_sqrtsum(unsigned long long n) {
  double s, t;
  unsigned long long i;
  s = 0.0;
  i = 0ULL;
  for (;;) {
    if (!(i < n)) break;
    t = __builtin_fsqrt((double) i);
    if (t != t) { *(unsigned long long *) lx_pun = 0x7FF8000000000000ULL; t = *(double *) lx_pun; }
    s = s + t;
    i = i + 1ULL;
  }
  return s;
}

unsigned long long lxf_touch(unsigned long long a) {
  if (a + 8ULL > (unsigned long long) lx_pages * 65536ULL) { lx_status = 2U; return 0ULL; }
  lx_mem[a >> 3ULL] = lx_mem[a >> 3ULL] + 1ULL;
  ((unsigned char *) lx_mem)[a + 3ULL] = (unsigned char) 7U;
  return lx_mem[a >> 3ULL];
}

void emit_word(unsigned long long w) {
  int k;
  for (k = 60; k >= 0; k = k - 4) {
    lx_out = (unsigned int) "0123456789abcdef"[(w >> k) & 15ULL];
  }
  lx_out = 10U;
}

int main(void) {
  double s;
  emit_word(lxf_depth(0ULL, 900ULL));
  emit_word(lx_status);
  lx_status = 0U;
  emit_word(lxf_depth(0ULL, 2000ULL));
  emit_word(lx_status);
  lx_status = 0U;
  s = lxf_sqrtsum(1000ULL);
  *(double *) lx_pun = s;
  emit_word(*(unsigned long long *) lx_pun);
  emit_word((unsigned long long) s);
  emit_word(lxf_touch(4096ULL));
  emit_word(lxf_touch(16ULL * 65536ULL));
  emit_word(lx_status);
  return 42;
}
