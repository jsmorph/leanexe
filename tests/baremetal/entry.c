/* Writes the exception level, DAIF, and SCTLR_EL1 that the startup code recorded at entry, one
   hexadecimal word per line. */
extern volatile unsigned int lx_uart_dr;
extern unsigned long long lx_boot_el[3];
static void hex(unsigned long long v) {
  int i;
  for (i = 60; i >= 0; i -= 4) lx_uart_dr = "0123456789abcdef"[(v >> i) & 15];
  lx_uart_dr = '\n';
}
int main(void) { hex(lx_boot_el[0]); hex(lx_boot_el[1]); hex(lx_boot_el[2]); return 0; }
