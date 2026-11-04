/* The reports of the Cortex-M7 startup code, through the UART, outside every proof.
   lx_report_exit writes "R:exit", the status, and the stack's high-water mark in bytes, the part
   of the stack whose fill pattern changed.  lx_report_fault writes "R:fault", the exception
   number, CFSR, HFSR, MMFAR, BFAR, and the stacked return address, and returns 255, the exit
   status.  The code computes with 32-bit integers only, so that it calls none of CompCert's
   run-time functions. */

extern volatile unsigned int lx_out;
extern unsigned int __stack_bottom[];
extern unsigned int __stack_top[];

static void out(char c) { lx_out = (unsigned char) c; }

static void outs(const char *s) { while (*s) out(*s++); }

static void outdec(unsigned int v) {
  char buf[12];
  int n = 0;
  do { buf[n++] = (char) ('0' + v % 10U); v /= 10U; } while (v != 0U);
  while (n > 0) out(buf[--n]);
}

static void outhex(unsigned int v) {
  int i;
  outs("0x");
  for (i = 28; i >= 0; i -= 4) out("0123456789abcdef"[(v >> i) & 15U]);
}

unsigned int lx_report_exit(int r) {
  unsigned int *p = __stack_bottom;
  while (p < __stack_top && *p == 0x5354414bU) p++;
  outs("R:exit ");
  outdec((unsigned int) r);
  outs(" stack ");
  outdec((unsigned int) ((char *) __stack_top - (char *) p));
  outs("\n");
  return (unsigned int) r;
}

unsigned int lx_report_fault(unsigned int n, unsigned int cfsr, unsigned int hfsr,
                             unsigned int mmfar, unsigned int bfar, unsigned int pc) {
  outs("R:fault ");
  outdec(n);
  outs(" cfsr ");
  outhex(cfsr);
  outs(" hfsr ");
  outhex(hfsr);
  outs(" mmfar ");
  outhex(mmfar);
  outs(" bfar ");
  outhex(bfar);
  outs(" pc ");
  outhex(pc);
  outs("\n");
  return 255U;
}
