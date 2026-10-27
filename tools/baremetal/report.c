/* The reports of the startup code, through the UART, outside every proof.  lx_report_exit
   writes "R:exit", the status, the exception level at entry, and the stack's high-water mark in
   bytes, the part of the stack whose fill pattern changed.  lx_report_exception writes
   "R:exception", the vector's index, ESR_EL1, ELR_EL1, and FAR_EL1, and returns 255, the exit
   status. */

extern volatile unsigned int lx_uart_dr;
extern unsigned long long __stack_bottom[];
extern unsigned long long __stack_top[];

static void out(char c) { lx_uart_dr = (unsigned char) c; }

static void outs(const char *s) { while (*s) out(*s++); }

static void outdec(unsigned long long v) {
  char buf[24];
  int n = 0;
  do { buf[n++] = (char) ('0' + v % 10); v /= 10; } while (v != 0);
  while (n > 0) out(buf[--n]);
}

static void outhex(unsigned long long v) {
  int i;
  outs("0x");
  for (i = 60; i >= 0; i -= 4) out("0123456789abcdef"[(v >> i) & 15]);
}

unsigned int lx_report_exit(int r, unsigned long long el) {
  unsigned long long *p = __stack_bottom;
  while (p < __stack_top && *p == 0x5354414b5354414bULL) p++;
  outs("R:exit ");
  outdec((unsigned int) r);
  outs(" el ");
  outdec(el);
  outs(" stack ");
  outdec((unsigned long long) ((char *) __stack_top - (char *) p));
  outs("\n");
  return (unsigned int) r;
}

unsigned int lx_report_exception(unsigned long long n, unsigned long long esr,
                                 unsigned long long elr, unsigned long long far) {
  outs("R:exception ");
  outdec(n);
  outs(" esr ");
  outhex(esr);
  outs(" elr ");
  outhex(elr);
  outs(" far ");
  outhex(far);
  outs("\n");
  return 255U;
}
