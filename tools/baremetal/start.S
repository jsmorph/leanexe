/* The startup code of a CompCert program on QEMU's virt machine for AArch64, outside every
   proof (docs/native-bare-metal.md).  It masks interrupts, requires exception level 1, records
   the exception level and the DAIF and SCTLR_EL1 that it found at entry in lx_boot_el, installs
   the exception vectors, turns the MMU and the caches on, enables floating point, sets the stack,
   fills the stack with a pattern for the high-water mark, clears .bss, and calls main.  After
   main returns, or after a call of lx_exit, it reports through lx_report_exit and exits with the
   status through semihosting, or, when PSCI_EXIT is defined, turns the machine off through PSCI
   SYSTEM_OFF, so that only the report gives the status.  At another exception level it reports
   the level and exits with status 254, and an exception reports its registers and exits with
   status 255.  lx_stack_mark and lx_stack_used measure the stack of one call for the test of the
   stack bound.  Defining NO_FPEN leaves floating point disabled, defining UNALIGNED_TEST adds an
   unaligned 8-byte load before main, and defining GUARD_TEST adds a store to the guard page below
   the stack.  The first two reproduce results of the design's experiments.

   The translation tables map RAM, from __ram_start to __ram_end, as Normal Inner and Outer
   Write-Back memory, Inner Shareable, and the 4 KiB page of lx_out as Device-nGnRnE memory, and
   leave the guard page below the stack and every other address unmapped.  The startup code
   writes them with the MMU off, as Device-nGnRnE accesses, and the table walks are
   Non-cacheable, so that the walks read what those writes stored.  The five tables at __tables
   are a level 1 table, a level 2 and a level 3 table for the UART's page, a level 2 table for
   RAM in blocks of 2 MiB, and a level 3 table for the 2 MiB that hold the guard page.  The stack
   fill and the clearing of .bss come after the MMU is on, as Cacheable writes. */

#define PATTERN 0x5354414b5354414b
#define TABLE 3
#define DEVICE_PAGE ((1 << 54) | (1 << 53) | (1 << 10) | 3)
#define RAM_BLOCK ((1 << 54) | (1 << 10) | (3 << 8) | (1 << 2) | 1)
#define RAM_PAGE ((1 << 54) | (1 << 10) | (3 << 8) | (1 << 2) | 3)
#define MAIR 0xff00
#define TCR ((2 << 30) | (1 << 23) | (32 << 16) | 32)
#define SCTLR_SET ((1 << 12) | (1 << 2) | 1)
#define SCTLR_CLEAR ((1 << 19) | (1 << 1))
#define SYSTEM_OFF 0x84000008

        .section .text.boot, "ax"
        .global _start
_start:
        mrs     x20, DAIF
        msr     daifset, #0xf
        mrs     x19, CurrentEL
        lsr     x19, x19, #2
        and     x19, x19, #3
        cmp     x19, #1
        b.ne    wrong_level
        mrs     x21, SCTLR_EL1
        ldr     x0, =vectors
        msr     VBAR_EL1, x0
        isb
        ldr     x0, =__tables
        add     x1, x0, #0x5000
1:      stp     xzr, xzr, [x0], #16
        cmp     x0, x1
        b.lo    1b
        ldr     x0, =__tables
        add     x1, x0, #0x1000
        add     x2, x0, #0x2000
        add     x3, x0, #0x3000
        add     x4, x0, #0x4000
        ldr     x6, =lx_out
        ubfx    x7, x6, #30, #2
        orr     x5, x1, #TABLE
        str     x5, [x0, x7, lsl #3]
        ubfx    x7, x6, #21, #9
        orr     x5, x2, #TABLE
        str     x5, [x1, x7, lsl #3]
        ubfx    x7, x6, #12, #9
        and     x6, x6, #~0xfff
        ldr     x5, =DEVICE_PAGE
        orr     x5, x6, x5
        str     x5, [x2, x7, lsl #3]
        ldr     x6, =__ram_start
        ubfx    x7, x6, #30, #2
        orr     x5, x3, #TABLE
        str     x5, [x0, x7, lsl #3]
        ldr     x5, =RAM_BLOCK
        orr     x5, x6, x5
        mov     x7, #0
2:      str     x5, [x3, x7, lsl #3]
        add     x5, x5, #0x200000
        add     x7, x7, #1
        cmp     x7, #512
        b.lo    2b
        ldr     x6, =__stack_guard
        ubfx    x7, x6, #21, #9
        orr     x5, x4, #TABLE
        str     x5, [x3, x7, lsl #3]
        and     x8, x6, #~0x1fffff
        ldr     x5, =RAM_PAGE
        orr     x5, x8, x5
        mov     x7, #0
3:      str     x5, [x4, x7, lsl #3]
        add     x5, x5, #0x1000
        add     x7, x7, #1
        cmp     x7, #512
        b.lo    3b
        ubfx    x7, x6, #12, #9
        str     xzr, [x4, x7, lsl #3]
        ldr     x1, =MAIR
        msr     MAIR_EL1, x1
        ldr     x1, =TCR
        msr     TCR_EL1, x1
        msr     TTBR0_EL1, x0
        dsb     sy
        isb
        tlbi    vmalle1
        dsb     nsh
        isb
        ldr     x1, =SCTLR_SET
        orr     x0, x21, x1
        ldr     x1, =SCTLR_CLEAR
        bic     x0, x0, x1
        msr     SCTLR_EL1, x0
        isb
#ifndef NO_FPEN
        mov     x0, #(3 << 20)
        msr     CPACR_EL1, x0
#endif
        isb
        ldr     x0, =__stack_top
        mov     sp, x0
        ldr     x0, =__stack_bottom
        ldr     x1, =__stack_top
        ldr     x2, =PATTERN
4:      cmp     x0, x1
        b.hs    5f
        str     x2, [x0], #8
        b       4b
5:      ldr     x0, =__bss_start
        ldr     x1, =__bss_end
6:      cmp     x0, x1
        b.hs    15f
        stp     xzr, xzr, [x0], #16
        b       6b
15:
#ifdef UNALIGNED_TEST
        ldr     x1, =__bss_start
        add     x1, x1, #3
        ldr     x0, [x1]
#endif
#ifdef GUARD_TEST
        ldr     x1, =__stack_bottom
        str     xzr, [x1, #-8]
#endif
        ldr     x0, =lx_boot_el
        str     x19, [x0]
        str     x20, [x0, #8]
        str     x21, [x0, #16]
        bl      main
        .global lx_exit
lx_exit:
        ldr     x2, =lx_stack_low
        ldr     x2, [x2]
        cbz     x2, 16f
        str     xzr, [x2]
16:     ldr     x1, =lx_boot_el
        ldr     x1, [x1]
        bl      lx_report_exit
exit:
#ifdef PSCI_EXIT
        dsb     sy
        ldr     x0, =SYSTEM_OFF
        hvc     #0
#else
        ldr     x1, =exit_block
        ldr     x2, =0x20026
        str     x2, [x1]
        mov     w0, w0
        str     x0, [x1, #8]
        mov     w0, #0x18
        hlt     #0xf000
#endif
17:     wfe
        b       17b

        .balign 2048
vectors:
        .irp    n, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
        .balign 128
        mov     x0, #\n
        b       exception
        .endr

wrong_level:
        ldr     x1, =__exc_stack_top
        mov     sp, x1
        mov     x0, x19
        bl      lx_report_level
        b       exit

exception:
        ldr     x1, =__exc_stack_top
        mov     sp, x1
        mrs     x1, ESR_EL1
        mrs     x2, ELR_EL1
        mrs     x3, FAR_EL1
        bl      lx_report_exception
        b       exit

/* lx_stack_mark records the lowest word of the stack whose pattern has changed in lx_stack_low,
   unless a lower one is recorded, records the caller's stack pointer in lx_mark_sp, and fills
   the stack below it with the pattern again.  lx_stack_used returns the bytes below lx_mark_sp
   whose pattern has changed since.  Neither uses the stack, so between them a call's high-water
   mark is the callee's alone.  lx_exit marks the word at lx_stack_low, so that the report of the
   whole stack's high-water mark covers what the fills erased. */
        .text
        .global lx_stack_mark
lx_stack_mark:
        ldr     x1, =__stack_bottom
        mov     x0, sp
        ldr     x2, =PATTERN
7:      cmp     x1, x0
        b.hs    8f
        ldr     x3, [x1]
        cmp     x3, x2
        b.ne    8f
        add     x1, x1, #8
        b       7b
8:      ldr     x3, =lx_stack_low
        ldr     x4, [x3]
        cbz     x4, 9f
        cmp     x1, x4
        b.hs    10f
9:      cmp     x1, x0
        b.hs    10f
        str     x1, [x3]
10:     ldr     x3, =lx_mark_sp
        str     x0, [x3]
        ldr     x1, =__stack_bottom
11:     cmp     x1, x0
        b.hs    12f
        str     x2, [x1], #8
        b       11b
12:     ret

        .global lx_stack_used
lx_stack_used:
        ldr     x1, =__stack_bottom
        ldr     x0, =lx_mark_sp
        ldr     x0, [x0]
        ldr     x2, =PATTERN
13:     cmp     x1, x0
        b.hs    14f
        ldr     x3, [x1]
        cmp     x3, x2
        b.ne    14f
        add     x1, x1, #8
        b       13b
14:     sub     x0, x0, x1
        ret

        .bss
        .balign 16
exit_block:
        .skip   16
        .global lx_boot_el
lx_boot_el:
        .skip   24
        .balign 8
lx_stack_low:
        .skip   8
lx_mark_sp:
        .skip   8
