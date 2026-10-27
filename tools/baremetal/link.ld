/* The layout of a CompCert program on QEMU's virt machine for AArch64.  RAM starts at
   0x40000000, where QEMU places the device tree for a bare-metal guest, so the image starts 1 MiB
   higher.  An exception stack of 4 KiB and the stack of STACK_SIZE bytes, which the linker's
   --defsym sets, follow .bss.  lx_uart_dr is the data register of the PL011 UART that QEMU 8.2.2's
   device tree gives. */
ENTRY(_start)
SECTIONS
{
  . = 0x40100000;
  .text : { KEEP(*(.text.boot)) *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
  .data : { *(.data .data.*) }
  .bss (NOLOAD) : {
    . = ALIGN(16);
    __bss_start = .;
    *(.bss .bss.*) *(COMMON)
    . = ALIGN(16);
    __bss_end = .;
  }
  . = ALIGN(4096);
  __exc_stack_bottom = .;
  . += 0x1000;
  __exc_stack_top = .;
  __stack_bottom = .;
  . += STACK_SIZE;
  __stack_top = .;
  lx_uart_dr = 0x09000000;
}
