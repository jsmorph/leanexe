/* The layout of a CompCert program on QEMU's virt machine for AArch64.  RAM is the 1 GiB from
   0x40000000, where QEMU places the device tree for a bare-metal guest, so the image starts 1 MiB
   higher.  Code and read-only data form one segment, readable and executable, and data and .bss
   another, readable and writable.  The five translation tables of the startup code follow .bss,
   then an exception stack of 4 KiB, a guard page of 4 KiB that the tables leave unmapped, and
   the stack of STACK_SIZE bytes, which the linker's --defsym sets.  lx_out is the data register
   of the PL011 UART that QEMU 8.2.2's device tree gives.  lx_in is the start of the 16 MiB of
   RAM into which QEMU's generic loader places a program's input, above the stack. */
ENTRY(_start)
PHDRS
{
  text PT_LOAD FLAGS(5);
  data PT_LOAD FLAGS(6);
}
SECTIONS
{
  __ram_start = 0x40000000;
  __ram_end = 0x80000000;
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
  __tables = .;
  . += 0x5000;
  __exc_stack_bottom = .;
  . += 0x1000;
  __exc_stack_top = .;
  __stack_guard = .;
  . += 0x1000;
  __stack_bottom = .;
  . += STACK_SIZE;
  __stack_top = .;
  lx_out = 0x09000000;
  lx_in = 0x70000000;
  ASSERT(__stack_top <= lx_in, "the stack overlaps lx_in")
  ASSERT(lx_in + 0x1000000 <= __ram_end, "lx_in extends past RAM")
  ASSERT(__ram_start % 0x40000000 == 0 && __ram_end - __ram_start == 0x40000000,
    "RAM is not one aligned GiB, the extent of the tables' level 2 table for RAM")
  ASSERT(__ram_end <= 0x100000000 && lx_out < 0x100000000,
    "an address lies outside the tables' 32-bit range")
  ASSERT(lx_out / 0x40000000 != __ram_start / 0x40000000,
    "lx_out lies in the GiB of RAM")
}
