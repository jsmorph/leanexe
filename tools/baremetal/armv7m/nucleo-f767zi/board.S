/* The board code of the NUCLEO-F767ZI, whose STM32F767ZI has a Cortex-M7 with a double-precision
   FPU, for tools/baremetal/armv7m/start.S, outside every proof.  No run on a board has tested it.
   The addresses and bits come from ST's device header stm32f767xx.h (repository
   STMicroelectronics/cmsis-device-f7), the size of the vector table from ST's startup_stm32f767xx.s
   in the same repository, the alternate function of PD8 and PD9 from ST's pin data (repository
   STMicroelectronics/STM32_open_pin_data, mcu/STM32F767ZITx.xml and
   mcu/IP/GPIO-STM32F76x_gpio_v1_0_Modes.xml), and the clock after reset from ST's
   system_stm32f7xx.c (repository STMicroelectronics/cmsis-device-f7).  The encodings of the clock
   selection, the pin settings, the character format, the baud divider, and the boot address come
   from ST's drivers (repository STMicroelectronics/stm32f7xx-hal-driver: RCC_USART3CLKSOURCE_HSI
   in stm32f7xx_hal_rcc_ex.h, the LL_GPIO_ constants in stm32f7xx_ll_gpio.h, the LL_USART_
   constants and __LL_USART_DIV_SAMPLING16 in stm32f7xx_ll_usart.h, and OB_BOOTADDR_ITCM_FLASH and
   OB_BOOTADDR_AXIM_FLASH in stm32f7xx_hal_flash_ex.h).  The settings of USART3 and its pins follow
   ST's example USART_Communication_Rx_IT for the board (repository STMicroelectronics/STM32CubeF7,
   Projects/STM32F767ZI-Nucleo/Examples_LL/USART), which also states that USART3 on PD8 and PD9
   reaches the ST-LINK's virtual COM port in the board's default configuration.

   The vector table has the 16 system entries and the 110 interrupts of the STM32F767, 0 to 109, 126
   words at 0x08000000, the start of flash on the AXIM interface.  With BOOT0 low the processor
   boots from the address that the option byte BOOT_ADD0 names.  Its value 0x0080 names
   0x00200000, the same flash on the ITCM interface, and 0x2000 names 0x08000000, and with either
   value the processor reads the table's first two words at reset.  start.S then sets VTOR to
   0x08000000.

   The processor leaves reset running from HSI, the internal oscillator of 16 MHz, and board_init
   keeps that clock, the bus prescalers, and the flash latency.  board_init selects HSI as the clock
   of USART3 in RCC_DCKCFGR2.USART3SEL, bits 5 and 4, and enables the clocks of GPIOD
   (RCC_AHB1ENR.GPIODEN, bit 3) and USART3 (RCC_APB1ENR.USART3EN, bit 18), reading each register
   back after the write, as ST's HAL does, before it uses the device.  It gives PD8 and PD9 the
   example's settings, high speed in GPIOD_OSPEEDR, push-pull in GPIOD_OTYPER, pull-up in
   GPIOD_PUPDR, and alternate function 7 in GPIOD_AFRH, and then selects the alternate function
   mode in GPIOD_MODER, which connects the pins to USART3_TX and USART3_RX.  It clears
   USART_CR2.STOP, for one stop bit, and sets USART_BRR to 3,333, (16,000,000 + 2,400) / 4,800
   rounded down, for 4,800.5 baud.  It then writes USART_CR1 with UE, RE, and TE set and every
   other bit clear, for 8 data bits, no parity, and 16 times oversampling.  USART_CR3 keeps its
   reset value, which the example states to be no hardware flow control.

   USART3 holds one received byte and the program polls, so the program must read each byte before
   the next one arrives.  A byte takes two windows of the program: one whose status read shows RXNE
   and requests the read of USART_RDR, and one that takes the byte.  In QEMU a window of the energy
   controller's program executes at most 4,477 instructions, other than the window that runs the
   gateway after the last byte of a record, and a byte at 4,800 baud lasts 33,333 cycles at 16 MHz,
   3.7 times the instructions of two such windows.  Defining NO_UART leaves UE, RE, and TE clear.

   board_exit waits for interrupts forever, since without a debugger no host takes a semihosting
   call.  lx_putc waits until USART_ISR.TXE, bit 7, is set and then writes the byte to USART_TDR. */

#define RCC_AHB1ENR 0x40023830
#define RCC_APB1ENR 0x40023840
#define RCC_DCKCFGR2 0x40023890
#define RCC_DCKCFGR2_USART3SEL (3 << 4)
#define RCC_DCKCFGR2_USART3SEL_HSI (2 << 4)
#define RCC_AHB1ENR_GPIODEN (1 << 3)
#define RCC_APB1ENR_USART3EN (1 << 18)
#define GPIOD 0x40020c00
#define GPIO_MODER 0x00
#define GPIO_OTYPER 0x04
#define GPIO_OSPEEDR 0x08
#define GPIO_PUPDR 0x0c
#define GPIO_AFRH 0x24
#define PD8_PD9_MODE (0xf << 16)
#define PD8_PD9_MODE_AF (0xa << 16)
#define PD8_PD9_OTYPE (3 << 8)
#define PD8_PD9_SPEED (0xf << 16)
#define PD8_PD9_SPEED_HIGH (0xa << 16)
#define PD8_PD9_PULL (0xf << 16)
#define PD8_PD9_PULL_UP (0x5 << 16)
#define PD8_PD9_AF 0xff
#define PD8_PD9_AF7 0x77
#define USART3 0x40004800
#define USART_CR1 0x00
#define USART_CR2 0x04
#define USART_BRR 0x0c
#define USART_ISR 0x1c
#define USART_TDR 0x28
#define USART_CR1_UE_RE_TE ((1 << 3) | (1 << 2) | 1)
#define USART_CR2_STOP (3 << 12)
#define USART_ISR_TXE (1 << 7)
#define USART_BRR_4800 3333

        .syntax unified
        .arch   armv7e-m
        .thumb

        .section .vectors, "a"
        .global __vectors
__vectors:
        .word   __exc_stack_top
        .word   _start
        .rept   124
        .word   fault
        .endr

        .text
        .global board_init
        .type   board_init, %function
        .thumb_func
board_init:
        ldr     r0, =RCC_DCKCFGR2
        ldr     r1, [r0]
        bic     r1, r1, #RCC_DCKCFGR2_USART3SEL
        orr     r1, r1, #RCC_DCKCFGR2_USART3SEL_HSI
        str     r1, [r0]
        ldr     r0, =RCC_AHB1ENR
        ldr     r1, [r0]
        orr     r1, r1, #RCC_AHB1ENR_GPIODEN
        str     r1, [r0]
        ldr     r1, [r0]
        ldr     r0, =RCC_APB1ENR
        ldr     r1, [r0]
        orr     r1, r1, #RCC_APB1ENR_USART3EN
        str     r1, [r0]
        ldr     r1, [r0]
        dsb
        ldr     r0, =GPIOD
        ldr     r1, [r0, #GPIO_OSPEEDR]
        bic     r1, r1, #PD8_PD9_SPEED
        orr     r1, r1, #PD8_PD9_SPEED_HIGH
        str     r1, [r0, #GPIO_OSPEEDR]
        ldr     r1, [r0, #GPIO_OTYPER]
        bic     r1, r1, #PD8_PD9_OTYPE
        str     r1, [r0, #GPIO_OTYPER]
        ldr     r1, [r0, #GPIO_PUPDR]
        bic     r1, r1, #PD8_PD9_PULL
        orr     r1, r1, #PD8_PD9_PULL_UP
        str     r1, [r0, #GPIO_PUPDR]
        ldr     r1, [r0, #GPIO_AFRH]
        bic     r1, r1, #PD8_PD9_AF
        orr     r1, r1, #PD8_PD9_AF7
        str     r1, [r0, #GPIO_AFRH]
        ldr     r1, [r0, #GPIO_MODER]
        bic     r1, r1, #PD8_PD9_MODE
        orr     r1, r1, #PD8_PD9_MODE_AF
        str     r1, [r0, #GPIO_MODER]
        ldr     r0, =USART3
        ldr     r1, [r0, #USART_CR2]
        bic     r1, r1, #USART_CR2_STOP
        str     r1, [r0, #USART_CR2]
        movw    r1, #USART_BRR_4800
        str     r1, [r0, #USART_BRR]
#ifndef NO_UART
        movs    r1, #USART_CR1_UE_RE_TE
        str     r1, [r0, #USART_CR1]
#endif
        bx      lr

        .global board_exit
        .type   board_exit, %function
        .thumb_func
board_exit:
1:      wfi
        b       1b

        .global lx_putc
        .type   lx_putc, %function
        .thumb_func
lx_putc:
        ldr     r1, =USART3
1:      ldr     r2, [r1, #USART_ISR]
        tst     r2, #USART_ISR_TXE
        beq     1b
        str     r0, [r1, #USART_TDR]
        bx      lr
        .ltorg

        .section .note.GNU-stack, "", %progbits
