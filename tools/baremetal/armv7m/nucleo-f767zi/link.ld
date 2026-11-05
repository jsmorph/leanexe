/* The layout of a CompCert program on the NUCLEO-F767ZI's STM32F767ZI, a Cortex-M7.  The
   addresses are those of ST's device header stm32f767xx.h.  FLASH is the 2 MiB of flash at
   0x08000000 on the AXIM interface (FLASH_BASE to FLASH_END), and DTCM is the 128 KiB of RAM at
   0x20000000 that the processor reaches through its data TCM interface (RAMDTCM_BASE).  The
   program leaves SRAM1 and SRAM2, at 0x20020000 to 0x2007FFFF, unused.  The Armv7-M default
   memory map makes the Code and SRAM regions that hold them Normal memory and the Peripheral
   region Device memory (Armv7-M Architecture Reference Manual, DDI 0403E.e, Table B3-1, page
   B3-592).  The vector table, code, read-only data, and the load image of .data lie in FLASH, and
   the startup code copies .data to its address in DTCM.  DTCM holds .data, .bss, the exception
   stack of 4 KiB, the guard of 4 KiB that MPU region 0 denies, aligned to its size as MPU_RBAR
   requires (section B3.5.8, page B3-639), and the stack of STACK_SIZE bytes, 32 KiB unless the
   linker's --defsym sets it.  The sections after .data have no contents and are loaded at their
   own addresses, so that the image's program headers name flash only for the code and the load
   image of .data, and a binary made from its sections with contents holds flash only.  lx_reg
   is the array of the 32-bit registers of the APB1 devices from 0x40000000 (APB1PERIPH_BASE), in
   which USART3, at 0x40004800 (USART3_BASE), has USART_ISR at index 0x1207, USART_RDR at index
   0x1209, and USART_TDR at index 0x120A (USART_TypeDef). */
ENTRY(_start)
MEMORY
{
  FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 0x200000
  DTCM (rw) : ORIGIN = 0x20000000, LENGTH = 0x20000
}
STACK_SIZE = DEFINED(STACK_SIZE) ? STACK_SIZE : 0x8000;
SECTIONS
{
  .text : {
    KEEP(*(.vectors))
    *(.text.boot)
    *(.text .text.*)
    *(.rodata .rodata.*)
  } >FLASH
  .eh_frame : { *(.eh_frame) } >FLASH
  .ARM.exidx : { *(.ARM.exidx .ARM.exidx.*) } >FLASH
  .data : ALIGN(8) {
    __data_start = .;
    *(.data .data.*)
    . = ALIGN(8);
    __data_end = .;
  } >DTCM AT>FLASH
  __data_load = LOADADDR(.data);
  .bss (NOLOAD) : ALIGN(8) {
    __bss_start = .;
    *(.bss .bss.*) *(COMMON)
    . = ALIGN(8);
    __bss_end = .;
  } >DTCM AT>DTCM
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
  } >DTCM AT>DTCM
  lx_reg = 0x40000000;
  ASSERT(__vectors == 0x08000000, "the vector table does not start at 0x08000000")
  ASSERT(__data_load % 4 == 0, "the load image of .data is not word-aligned")
  ASSERT(STACK_SIZE % 8 == 0, "STACK_SIZE is not a multiple of 8")
  ASSERT(__stack_guard % 0x1000 == 0 && __stack_bottom - __stack_guard == 0x1000,
    "the guard is not the 4 KiB region at a 4 KiB boundary that GUARD_RASR in start.S gives")
}
