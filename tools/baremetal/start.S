/* The startup code of a CompCert program on QEMU's virt machine for AArch64, outside every
   proof (docs/native-bare-metal.md).  It masks interrupts, requires exception level 1, records
   the exception level and the DAIF and SCTLR_EL1 that it found at entry in lx_boot_el, installs
   the exception vectors, enables floating point, sets the stack, fills the stack with a pattern
   for the high-water mark, clears .bss, and calls main.  After main returns, or after a call of
   lx_exit, it reports through lx_report_exit and exits through semihosting with the status.  At
   another exception level it reports the level and exits with status 254, and an exception
   reports its registers and exits with status 255.  lx_stack_mark and lx_stack_used measure the
   stack of one call for the test of the stack bound.  Defining NO_FPEN leaves floating point
   disabled, and defining UNALIGNED_TEST adds an unaligned 8-byte load before main.  Both
   reproduce results of the design's experiments. */

#define PATTERN 0x5354414b5354414b

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
        ldr     x0, =vectors
        msr     VBAR_EL1, x0
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
1:      cmp     x0, x1
        b.hs    2f
        str     x2, [x0], #8
        b       1b
2:      ldr     x0, =__bss_start
        ldr     x1, =__bss_end
3:      cmp     x0, x1
        b.hs    4f
        stp     xzr, xzr, [x0], #16
        b       3b
4:
#ifdef UNALIGNED_TEST
        ldr     x1, =__bss_start
        add     x1, x1, #3
        ldr     x0, [x1]
#endif
        ldr     x0, =lx_boot_el
        str     x19, [x0]
        str     x20, [x0, #8]
        mrs     x1, SCTLR_EL1
        str     x1, [x0, #16]
        bl      main
        .global lx_exit
lx_exit:
        ldr     x2, =lx_stack_low
        ldr     x2, [x2]
        cbz     x2, 6f
        str     xzr, [x2]
6:      ldr     x1, =lx_boot_el
        ldr     x1, [x1]
        bl      lx_report_exit
exit:
        ldr     x1, =exit_block
        ldr     x2, =0x20026
        str     x2, [x1]
        mov     w0, w0
        str     x0, [x1, #8]
        mov     w0, #0x18
        hlt     #0xf000
5:      wfe
        b       5b

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
