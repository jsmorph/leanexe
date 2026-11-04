/* The layout of a CompCert program on QEMU's mps2-an500, a Cortex-M7.  The addresses are those of
   Arm's Application Note AN500, DAI 0500B, Table 3-1 (pages 3-5 and 3-6) and Table 3-3 (page 3-8),
   and of QEMU 8.2.2's model (hw/arm/mps2.c, lines 165 to 216, 291 to 293, and 520).  CODE is ZBT
   SSRAM1, 4 MiB at 0, mirrored at 0x00400000.  SRAM is ZBT SSRAM2 and SSRAM3, 4 MiB at 0x20000000,
   mirrored at 0x20400000.  PSRAM is 16 MiB at 0x60000000.  The Armv7-M default memory map makes the
   Code, SRAM, and RAM regions that hold them Normal memory, and the Peripheral region of the UART
   Device memory (Armv7-M Architecture Reference Manual, DDI 0403E.e, Table B3-1, page B3-592).  The
   vector table, code, read-only data, and the load image of .data lie in CODE, where QEMU's ELF
   loader places each segment at its physical address (include/hw/elf_ops.h, line 499), and the
   startup code copies .data to its address in SRAM.  SRAM holds .data, .bss, the exception stack of
   4 KiB, the guard of 4 KiB that MPU region 0 denies, aligned to its size as MPU_RBAR requires
   (section B3.5.8, page B3-639), and the stack of STACK_SIZE bytes, which the linker's --defsym
   sets.  The sections after .data are loaded at their own addresses, so that the zeros that QEMU's
   loader writes for them fall in SRAM.  lx_out is the data register of the CMSDK UART0 (Cortex-M
   System Design Kit TRM, DDI 0479D, Table 4-7, page 4-9).  lx_in is the start of PSRAM, into which
   QEMU's generic loader places a program's input. */
ENTRY(_start)
MEMORY
{
  CODE (rx) : ORIGIN = 0x00000000, LENGTH = 0x400000
  SRAM (rw) : ORIGIN = 0x20000000, LENGTH = 0x400000
}
SECTIONS
{
  .text : {
    KEEP(*(.vectors))
    *(.text.boot)
    *(.text .text.*)
    *(.rodata .rodata.*)
  } >CODE
  .eh_frame : { *(.eh_frame) } >CODE
  .ARM.exidx : { *(.ARM.exidx .ARM.exidx.*) } >CODE
  .data : ALIGN(8) {
    __data_start = .;
    *(.data .data.*)
    . = ALIGN(8);
    __data_end = .;
  } >SRAM AT>CODE
  __data_load = LOADADDR(.data);
  .bss (NOLOAD) : ALIGN(8) {
    __bss_start = .;
    *(.bss .bss.*) *(COMMON)
    . = ALIGN(8);
    __bss_end = .;
  } >SRAM AT>SRAM
  .stack (NOLOAD) : ALIGN(8) {
    __exc_stack_bottom = .;
    . += 0x1000;
    __exc_stack_top = .;
    . = ALIGN(0x1000);
    __stack_guard = .;
    . += 0x1000;
    __stack_bottom = .;
    . += STACK_SIZE;
    __stack_top = .;
  } >SRAM AT>SRAM
  lx_out = 0x40004000;
  lx_in = 0x60000000;
  ASSERT(__vectors == 0, "the vector table does not start at 0, the reset value of VTOR")
  ASSERT(__data_load % 4 == 0, "the load image of .data is not word-aligned")
  ASSERT(STACK_SIZE % 8 == 0, "STACK_SIZE is not a multiple of 8")
  ASSERT(__stack_guard % 0x1000 == 0 && __stack_bottom - __stack_guard == 0x1000,
    "the guard is not the 4 KiB region at a 4 KiB boundary that GUARD_RASR in start.S gives")
}
