/* The printer of the co-simulation of the Cortex-M7 model (tests/TestSupport/M7/Cosim.lean),
   outside every proof.  The harness's main calls cosim_print after its cases.  For each case it
   writes one line: "C", the case's number, the instruction's two halfwords, its address, the
   window's address, r0 to r12, SP, LR, and APSR before the instruction, the window's 64 bytes
   before it, the same registers after it followed by the number of the landing word, and the
   window's bytes after it, every number in hexadecimal.  It writes through lx_putc of the board's
   board.S. */

extern void lx_putc(unsigned int c);
extern const unsigned int cosim_count;
extern unsigned int *const cosim_in[];
extern unsigned int *const cosim_out[];
extern unsigned char *const cosim_inwin[];
extern const unsigned short *const cosim_test[];
extern unsigned char cosim_win[];

static const char digits[] = "0123456789abcdef";

static void out(char c) { lx_putc((unsigned char) c); }

static void hex(unsigned int v) {
  char buf[8];
  int n = 0;
  do { buf[n++] = digits[v & 15U]; v >>= 4; } while (v != 0U);
  out(' ');
  while (n > 0) out(buf[--n]);
}

static void bytes(const unsigned char *b) {
  int i;
  out(' ');
  for (i = 0; i < 64; i++) {
    out(digits[b[i] >> 4]);
    out(digits[b[i] & 15U]);
  }
}

int cosim_print(void) {
  unsigned int k;
  int i;
  for (k = 0; k < cosim_count; k++) {
    const unsigned short *t =
      (const unsigned short *) ((unsigned int) cosim_test[k] & ~1U);
    unsigned int *in = cosim_in[k], *o = cosim_out[k];
    out('C');
    hex(k);
    hex(t[0]);
    hex(t[1]);
    hex((unsigned int) t);
    hex((unsigned int) cosim_win);
    for (i = 0; i < 16; i++) hex(in[i]);
    bytes(cosim_inwin[k]);
    for (i = 0; i < 17; i++) hex(o[i]);
    bytes((const unsigned char *) (o + 17));
    out('\n');
  }
  return 0;
}
