/* The printer of the co-simulation of the AArch64 model (tests/TestSupport/A64/Cosim.lean),
   outside every proof.  The harness's main calls cosim_print after its cases.  For each case it
   writes one line: "C", the case's number, the instruction's word, its address, the window's
   address, the 31 registers, the stack pointer, and NZCV before the instruction, the window's 64
   bytes before it, the same registers after it followed by the number of the landing word, the
   window's bytes after it, and the 32 floating-point registers before and after it, every number
   in hexadecimal. */

extern volatile unsigned int lx_out;
extern const unsigned long long cosim_count;
extern unsigned long long *const cosim_in[];
extern unsigned long long *const cosim_out[];
extern unsigned char *const cosim_inwin[];

static const char digits[] = "0123456789abcdef";

static void out(char c) { lx_out = (unsigned char) c; }

static void hex(unsigned long long v) {
  char buf[16];
  int n = 0;
  do { buf[n++] = digits[v & 15]; v >>= 4; } while (v != 0);
  out(' ');
  while (n > 0) out(buf[--n]);
}

static void bytes(const unsigned char *b) {
  int i;
  out(' ');
  for (i = 0; i < 64; i++) {
    out(digits[b[i] >> 4]);
    out(digits[b[i] & 15]);
  }
}

int cosim_print(void) {
  unsigned long long k;
  int i;
  for (k = 0; k < cosim_count; k++) {
    unsigned long long *in = cosim_in[k], *o = cosim_out[k];
    out('C');
    hex(k);
    hex(*(const unsigned int *) o[34]);
    hex(o[34]);
    hex(o[35]);
    for (i = 0; i < 33; i++) hex(in[i]);
    bytes(cosim_inwin[k]);
    for (i = 0; i < 34; i++) hex(o[i]);
    bytes((const unsigned char *) (o + 36));
    for (i = 0; i < 32; i++) hex(in[33 + i]);
    for (i = 0; i < 32; i++) hex(o[44 + i]);
    out('\n');
  }
  return 0;
}
