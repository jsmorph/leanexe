/* The startup code of a CompCert program on a Cortex-M7, outside every proof.  The board's
   directory, tools/baremetal/armv7m/BOARD, holds link.ld, the board's memory layout, and board.S,
   which defines the vector table __vectors, whose first two words are the initial main stack
   pointer, __exc_stack_top, and the reset entry _start, and whose other words send every
   exception to fault; board_init, which sets up the board's devices; board_exit, which ends the
   program with the status in r0; and lx_putc, which writes the byte in r0 to the board's UART for
   the reports of report.c.

   _start runs in privileged Thread mode on the main stack.  It sets VTOR to the table and enables
   MemManage, BusFault, and UsageFault in SHCSR, so that each such fault is taken as itself rather
   than escalated to HardFault.  It clears CCR.UNALIGN_TRP, so that loads and stores of single
   registers support unaligned addresses (Armv7-M Architecture Reference Manual, DDI 0403E.e,
   sections A3.2.1 and B3.2.8, pages A3-65 and B3-604), and leaves the cache enables CCR.DC and
   CCR.IC at their reset value 0 (Cortex-M7 TRM, DDI 0489F, Table 3-1, page 3-3), since the caches
   need invalidation before they are enabled (section 4.1.3, page 4-3).  It enables the
   floating-point unit by giving CP10 and CP11 full access in CPACR (section B3.2.20, page
   B3-614).  It calls board_init, copies .data from its load address to RAM, clears .bss, and
   fills the stack with a pattern for the high-water mark.  It then makes MPU region 0 the guard
   below the stack, 4 KiB at __stack_guard with no access and execute-never, and enables the MPU
   with the default memory map as the background for privileged accesses (sections B3.5.6 to
   B3.5.9, pages B3-637 to B3-642), so that an access to the guard takes a MemManage fault.
   Finally it sets the process stack pointer to __stack_top, selects it with CONTROL.SPSEL
   (section B1.4.4, page B1-519), and calls main.  The program runs on the process stack and every
   exception handler on the main stack, so that a handler runs after an overflow of the program's
   stack.  No interrupt is enabled.  PRIMASK stays 0, since setting it raises the execution
   priority to 0, that of the faults, which would then escalate to HardFault (section B1.5.4,
   pages B1-528 and B1-529).

   After main returns, or after a call of lx_exit, the code selects the main stack again at
   __exc_stack_top, reports through lx_report_exit, and ends through board_exit.  An exception
   enters fault, which reads the exception number, CFSR, HFSR, MMFAR, BFAR, and the stacked return
   address, or 0 after a stacking error, when the frame is incomplete.  It then moves to the top
   of the main stack, reports through lx_report_fault, and ends through board_exit with status
   255.  Defining NO_FPEN leaves the floating-point unit disabled, GUARD_TEST adds a store to the
   word below the stack, UNALIGNED_TEST an unaligned word load, and UNALIGNED_LDRD_TEST an
   unaligned LDRD, each before main. */

#define SCB_VTOR 0xe000ed08
#define SCB_CCR 0xe000ed14
#define SCB_SHCSR 0xe000ed24
#define SCB_CFSR 0xe000ed28
#define SCB_HFSR 0xe000ed2c
#define SCB_MMFAR 0xe000ed34
#define SCB_BFAR 0xe000ed38
#define SCB_CPACR 0xe000ed88
#define MPU_RNR 0xe000ed98
#define SHCSR_FAULTS ((1 << 18) | (1 << 17) | (1 << 16))
#define CCR_UNALIGN_TRP (1 << 3)
#define CPACR_CP10_CP11 (0xf << 20)
#define CFSR_STACKING ((1 << 12) | (1 << 4))
#define GUARD_RASR ((1 << 28) | (11 << 1) | 1)
#define MPU_ENABLE ((1 << 2) | 1)
#define PATTERN 0x5354414b

        .syntax unified
        .arch   armv7e-m
        .fpu    fpv5-d16
        .eabi_attribute Tag_ABI_VFP_args, 1
        .thumb

        .section .text.boot, "ax"
        .global _start
        .type   _start, %function
        .thumb_func
_start:
        ldr     r0, =SCB_VTOR
        ldr     r1, =__vectors
        str     r1, [r0]
        ldr     r0, =SCB_SHCSR
        ldr     r1, [r0]
        orr     r1, r1, #SHCSR_FAULTS
        str     r1, [r0]
        ldr     r0, =SCB_CCR
        ldr     r1, [r0]
        bic     r1, r1, #CCR_UNALIGN_TRP
        str     r1, [r0]
#ifndef NO_FPEN
        ldr     r0, =SCB_CPACR
        ldr     r1, [r0]
        orr     r1, r1, #CPACR_CP10_CP11
        str     r1, [r0]
#endif
        dsb
        isb
        bl      board_init
        ldr     r0, =__data_load
        ldr     r1, =__data_start
        ldr     r2, =__data_end
1:      cmp     r1, r2
        bhs     2f
        ldr     r3, [r0], #4
        str     r3, [r1], #4
        b       1b
2:      ldr     r1, =__bss_start
        ldr     r2, =__bss_end
        movs    r3, #0
3:      cmp     r1, r2
        bhs     4f
        str     r3, [r1], #4
        b       3b
4:      ldr     r1, =__stack_bottom
        ldr     r2, =__stack_top
        ldr     r3, =PATTERN
5:      cmp     r1, r2
        bhs     6f
        str     r3, [r1], #4
        b       5b
6:      ldr     r0, =MPU_RNR
        movs    r1, #0
        str     r1, [r0]
        ldr     r1, =__stack_guard
        str     r1, [r0, #4]
        ldr     r1, =GUARD_RASR
        str     r1, [r0, #8]
        movs    r1, #MPU_ENABLE
        str     r1, [r0, #-4]
        dsb
        isb
        ldr     r0, =__stack_top
        msr     PSP, r0
        movs    r0, #2
        msr     CONTROL, r0
        isb
#ifdef GUARD_TEST
        ldr     r1, =__stack_bottom
        movs    r0, #0
        str     r0, [r1, #-4]
#endif
#ifdef UNALIGNED_TEST
        ldr     r1, =__bss_start
        ldr     r0, [r1, #1]
#endif
#ifdef UNALIGNED_LDRD_TEST
        ldr     r1, =__bss_start
        adds    r1, r1, #1
        ldrd    r2, r3, [r1]
#endif
        bl      main

        .global lx_exit
        .type   lx_exit, %function
        .thumb_func
lx_exit:
        mrs     r1, CONTROL
        bic     r1, r1, #2
        msr     CONTROL, r1
        isb
        ldr     r1, =__exc_stack_top
        mov     sp, r1
        bl      lx_report_exit
        b       board_exit

        .global fault
        .type   fault, %function
        .thumb_func
fault:
        mrs     r0, IPSR
        ldr     r1, =SCB_CFSR
        ldr     r1, [r1]
        movs    r5, #0
        ldr     r2, =CFSR_STACKING
        tst     r1, r2
        bne     9f
        tst     lr, #4
        bne     8f
        mrs     r2, MSP
        ldr     r5, [r2, #24]
        b       9f
8:      mrs     r2, PSP
        ldr     r5, [r2, #24]
9:      ldr     r2, =SCB_HFSR
        ldr     r2, [r2]
        ldr     r3, =SCB_MMFAR
        ldr     r3, [r3]
        ldr     r4, =SCB_BFAR
        ldr     r4, [r4]
        ldr     r6, =__exc_stack_top
        mov     sp, r6
        sub     sp, sp, #8
        str     r4, [sp]
        str     r5, [sp, #4]
        bl      lx_report_fault
        b       board_exit
        .ltorg

        .section .note.GNU-stack, "", %progbits
