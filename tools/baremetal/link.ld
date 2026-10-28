/* The layout of a CompCert program on QEMU's virt machine for AArch64.  RAM starts at
   0x40000000, where QEMU places the device tree for a bare-metal guest, so the image starts 1 MiB
   higher.  Code and read-only data form one segment, readable and executable, and data and .bss
   another, readable and writable.  An exception stack of 4 KiB and the stack of STACK_SIZE bytes,
   which the linker's --defsym sets, follow .bss.  lx_out is the data register of the PL011 UART
   that QEMU 8.2.2's device tree gives.  lx_in is the start of the 16 MiB of RAM into which
   QEMU's generic loader places a program's input, above the stack. */
ENTRY(_start)
PHDRS
{
  text PT_LOAD FLAGS(5);
  data PT_LOAD FLAGS(6);
}
SECTIONS
{
  . = 0x40100000;
  .text : { KEEP(*(.text.boot)) *(.text .text.*) } :text
  .rodata : { *(.rodata .rodata.*) } :text
  .eh_frame : { *(.eh_frame) } :text
  . = ALIGN(4096);
  .data : { *(.data .data.*) } :data
  .got : { *(.got .got.plt) } :data
  .bss (NOLOAD) : {
    . = ALIGN(16);
    __bss_start = .;
    *(.bss .bss.*) *(COMMON)
    . = ALIGN(16);
    __bss_end = .;
  } :data
  . = ALIGN(4096);
  __exc_stack_bottom = .;
  . += 0x1000;
  __exc_stack_top = .;
  __stack_bottom = .;
  . += STACK_SIZE;
  __stack_top = .;
  lx_out = 0x09000000;
  lx_in = 0x70000000;
  ASSERT(__stack_top <= lx_in, "the stack overlaps lx_in")
}
