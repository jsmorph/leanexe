/* The board code of the NUCLEO-F767ZI, whose STM32F767ZI has a Cortex-M7 with a double-precision
   FPU, for tools/baremetal/armv7m/start.S, outside every proof.  No run on a board has tested it.
   The addresses and bits come from ST's device header stm32f767xx.h (repository
   STMicroelectronics/cmsis-device-f7), the size of the vector table from ST's
   startup_stm32f767xx.s in the same repository, the alternate function of PD8 and PD9 from ST's
   pin data (repository STMicroelectronics/STM32_open_pin_data, mcu/STM32F767ZITx.xml and
   mcu/IP/GPIO-STM32F76x_gpio_v1_0_Modes.xml), the clock after reset from ST's
   system_stm32f7xx.c (repository STMicroelectronics/cmsis-device-f7), and the encodings of the
   clock selection and boot address from ST's HAL (repository
   STMicroelectronics/stm32f7xx-hal-driver: RCC_USART3CLKSOURCE_HSI in stm32f7xx_hal_rcc_ex.h and
   OB_BOOTADDR_ITCM_FLASH in stm32f7xx_hal_flash_ex.h).

   The vector table has the 16 system entries and the 110 interrupts of the STM32F767, 0 to 109,
   126 words at 0x08000000, the start of flash on the AXIM interface.  With BOOT0 low the
   processor boots from the address that the option byte BOOT_ADD0 names.  The image requires its
   value 0x0080, which names 0x00200000, the same flash on the ITCM interface, so that the
   processor reads the table's first two words there at reset.  start.S then sets VTOR to
   0x08000000.

   The processor leaves reset running from HSI, the internal oscillator of 16 MHz, and board_init
   keeps that clock, the bus prescalers, and the flash latency.  board_init selects HSI as the
   clock of USART3 in RCC_DCKCFGR2.USART3SEL, bits 5 and 4, and enables the clocks of GPIOD
   (RCC_AHB1ENR.GPIODEN, bit 3) and USART3 (RCC_APB1ENR.USART3EN, bit 18), reading each register
   back after the write, as ST's HAL does, before it uses the device.  It selects alternate
   function 7 for PD8 and PD9 in GPIOD_AFRH and then the alternate function mode in GPIOD_MODER,
   which connects them to USART3_TX and USART3_RX.  The NUCLEO-F767ZI connects those pins to the
   virtual COM port of its ST-LINK.  board_init sets USART_BRR to 1667, for 16 MHz / 1667 = 9,598
   baud, 0.02% below 9,600, and keeps the reset values of the other fields of USART_CR1 and
   USART_CR2: 8 data bits, no parity, one stop bit, and 16 times oversampling.  It then sets UE,
   RE, and TE in USART_CR1.  In QEMU a window of the energy controller's program executes at most
   4,477 instructions, other than the window that runs the gateway after the last byte of a
   record, and a byte at 9,600 baud lasts 16,667 cycles at 16 MHz, 3.7 times as many.

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
#define GPIO_AFRH 0x24
#define PD8_PD9_MODE (0xf << 16)
#define PD8_PD9_MODE_AF (0xa << 16)
#define PD8_PD9_AF 0xff
#define PD8_PD9_AF7 0x77
#define USART3 0x40004800
#define USART_CR1 0x00
#define USART_BRR 0x0c
#define USART_ISR 0x1c
#define USART_TDR 0x28
#define USART_CR1_UE_RE_TE ((1 << 3) | (1 << 2) | 1)
#define USART_ISR_TXE (1 << 7)
#define USART_BRR_9600 1667

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
        ldr     r1, [r0, #GPIO_AFRH]
        bic     r1, r1, #PD8_PD9_AF
        orr     r1, r1, #PD8_PD9_AF7
        str     r1, [r0, #GPIO_AFRH]
        ldr     r1, [r0, #GPIO_MODER]
        bic     r1, r1, #PD8_PD9_MODE
        orr     r1, r1, #PD8_PD9_MODE_AF
        str     r1, [r0, #GPIO_MODER]
        ldr     r0, =USART3
        movw    r1, #USART_BRR_9600
        str     r1, [r0, #USART_BRR]
        movs    r1, #USART_CR1_UE_RE_TE
        str     r1, [r0, #USART_CR1]
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
