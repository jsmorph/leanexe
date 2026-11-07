/* The board code of QEMU's mps2-an500, a Cortex-M7, for tools/baremetal/armv7m/start.S, outside
   every proof.  The vector table at address 0 has the 16 system entries and the 32 interrupts
   that QEMU gives the AN500 (hw/arm/mps2.c, line 234).  QEMU reads its first two words at reset
   from VTOR, whose reset value is 0 (QEMU 8.2.2, target/arm/cpu.c, lines 429 to 457, and
   hw/arm/armv7m.c, line 547).

   board_init starts CMSDK Timer0 at lx_timer counting down from its maximum reload value, so that
   a read of its VALUE register is a clock (Cortex-M System Design Kit TRM, DDI 0479D, Table 3-1).
   It sets the baud divider of the CMSDK UART0, whose registers begin at lx_uart, to 16, the
   minimum (Table 4-7, page 4-9), and sets its transmitter and receiver enables, without which
   QEMU's model sends no byte and takes none (hw/char/cmsdk-apb-uart.c, lines 115 to 124, 194 to
   203, and 249 to 260).  Defining NO_UART leaves the transmitter and receiver disabled.

   board_exit exits through the semihosting call SYS_EXIT_EXTENDED, 0x20, whose parameter block
   holds ADP_Stopped_ApplicationExit and the status (Arm semihosting specification).  QEMU takes
   BKPT 0xab as a semihosting call on M-profile (target/arm/tcg/translate.c, lines 6391 to 6401)
   and exits with that status (semihosting/arm-compat-semi.c, lines 725 to 757).  lx_putc stores
   the byte in UART0's data register, lx_out, without reading the status register. */

#define UART_CTRL 8
#define UART_BAUDDIV 16
#define UART_TX_RX_EN 3
#define TIMER_CTRL 0
#define TIMER_VALUE 4
#define TIMER_RELOAD 8
#define TIMER_ENABLE 1
#define SYS_EXIT_EXTENDED 0x20
#define ADP_Stopped_ApplicationExit 0x20026

        .syntax unified
        .arch   armv7e-m
        .thumb

        .section .vectors, "a"
        .global __vectors
__vectors:
        .word   __exc_stack_top
        .word   _start
        .rept   46
        .word   fault
        .endr

        .text
        .global board_init
        .type   board_init, %function
        .thumb_func
board_init:
        ldr     r0, =lx_timer
        mvn     r1, #0
        str     r1, [r0, #TIMER_RELOAD]
        str     r1, [r0, #TIMER_VALUE]
        movs    r1, #TIMER_ENABLE
        str     r1, [r0, #TIMER_CTRL]
#ifndef NO_UART
        ldr     r0, =lx_uart
        movs    r1, #16
        str     r1, [r0, #UART_BAUDDIV]
        movs    r1, #UART_TX_RX_EN
        str     r1, [r0, #UART_CTRL]
#endif
        bx      lr

        .global board_exit
        .type   board_exit, %function
        .thumb_func
board_exit:
        ldr     r1, =exit_block
        ldr     r2, =ADP_Stopped_ApplicationExit
        str     r2, [r1]
        str     r0, [r1, #4]
        movs    r0, #SYS_EXIT_EXTENDED
        bkpt    0xab
1:      wfi
        b       1b

        .global lx_putc
        .type   lx_putc, %function
        .thumb_func
lx_putc:
        ldr     r1, =lx_out
        str     r0, [r1]
        bx      lr
        .ltorg

        .bss
        .balign 4
exit_block:
        .skip   8

        .section .note.GNU-stack, "", %progbits
