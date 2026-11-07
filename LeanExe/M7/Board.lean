import LeanExe.M7.Boot
import LeanExe.M7.Init
import LeanExe.M7.Setup

/-!
The NUCLEO-F767ZI's STM32F767ZI for the Cortex-M7 back end: its memories and devices, the
layout of an image in its flash, and the initialization of `board_init` in
`tools/baremetal/armv7m/nucleo-f767zi/board.S`, as accesses that Lean writes into the image.

The flash of 2 MiB lies at `0x08000000` on the AXIM interface and at `0x00200000` on the ITCM
interface, and DTCM's 128 KiB at `0x20000000` (RM0410 Rev 4, section 2.2.2, Figure 2, and section
2.3).  `st-flash write` puts an image's bytes at `0x08000000`, so the code map holds them from both
addresses.  With BOOT0 low, the processor reads the vector table at reset from the address that
the option byte BOOT_ADD0 names, and this board's BOOT_ADD0, 0x0080, names `0x00200000` (RM0410
Rev 4, section 2.5 and Table 2; OPTCR1 reads `0x00400080`).  The image's table therefore lies at
`0x00200000`, and its reset entry names the initialization there, so the program runs from the
ITCM alias.  SP starts at the top of DTCM, and the stack's limit is DTCM's base.  A program whose
functions access linear memory or globals keeps the module's store in the generator's area from
`areaHeader`, DTCM's base, below the stack, whose limit is then the area's end `areaEnd`, and its
image runs the setup of `LeanExe/M7/Setup.lean` before the initialization.

`platform` names DTCM as Normal memory and the 65,536 words from `0x40000000` that requests address
as devices; RCC at `0x40023800`, GPIOD at `0x40020C00`, and USART3 at `0x40004800` lie among them
(ST's `stm32f767xx.h`).  Every other address, flash among them, stops the model on a load or a
store, so the program never changes its code.

`init` performs `board_init`'s accesses in its order.  It selects HSI as USART3's clock in
`RCC_DCKCFGR2.USART3SEL`, bits 5 and 4, enables the clocks of GPIOD (`RCC_AHB1ENR.GPIODEN`, bit 3)
and USART3 (`RCC_APB1ENR.USART3EN`, bit 18), each read back after its write, and completes the
accesses with `DSB SY`.  It gives PD8 and PD9 high speed, push-pull, pull-up, and alternate
function 7, and then the alternate function mode, clears `USART_CR2.STOP` for one stop bit,
writes 3,333 to `USART_BRR` for 4,800 baud from HSI's 16 MHz, and writes `USART_CR1` with UE, RE,
and TE set.  Each read-modify-write clears and sets the bits that `board.S` clears and sets.
-/

namespace LeanExe.M7.Nucleo

/-- DTCM as Normal memory, and the 65,536 device words from `0x40000000`. -/
def platform : Platform :=
  { normal := fun b => decide (0x20000000 ≤ b.toNat ∧ b.toNat < 0x20020000)
    device := fun a => decide (0x40000000 ≤ a.toNat ∧ a.toNat < 0x40040000) }

/-- The device window of the requests, `lx_reg` of the C path's programs on this board. -/
def devBase : UInt32 := 0x40000000

/-- The flash on the AXIM interface, where `st-flash` writes an image. -/
def flashAxim : UInt32 := 0x08000000

/-- The flash on the ITCM interface, where BOOT_ADD0 places the vector table. -/
def flashItcm : UInt32 := 0x00200000

/-- The stack's limit, DTCM's base. -/
def stackLimit : UInt32 := 0x20000000

/-- The initial SP, the top of DTCM. -/
def stackTop : UInt32 := 0x20020000

def rccAhb1enr : UInt32 := 0x40023830
def rccApb1enr : UInt32 := 0x40023840
def rccDckcfgr2 : UInt32 := 0x40023890
def gpiodModer : UInt32 := 0x40020C00
def gpiodOtyper : UInt32 := 0x40020C04
def gpiodOspeedr : UInt32 := 0x40020C08
def gpiodPupdr : UInt32 := 0x40020C0C
def gpiodAfrh : UInt32 := 0x40020C24
def usartCr1 : UInt32 := 0x40004800
def usartCr2 : UInt32 := 0x40004804
def usartBrr : UInt32 := 0x4000480C
def usartIsr : UInt32 := 0x4000481C
def usartRdr : UInt32 := 0x40004824
def usartTdr : UInt32 := 0x40004828

/-- The accesses of `board_init`, in its order. -/
def init : List InitOp :=
  [.rmw rccDckcfgr2 0x30 0x20,
    .rmw rccAhb1enr 0 0x8, .read rccAhb1enr,
    .rmw rccApb1enr 0 0x40000, .read rccApb1enr,
    .dsb,
    .rmw gpiodOspeedr 0xF0000 0xA0000,
    .rmw gpiodOtyper 0x300 0,
    .rmw gpiodPupdr 0xF0000 0x50000,
    .rmw gpiodAfrh 0xFF 0x77,
    .rmw gpiodModer 0xF0000 0xA0000,
    .rmw usartCr2 0x3000 0,
    .write usartBrr 3333,
    .write usartCr1 0xD]

/-- The image's layout: the vector table of the 16 system entries and the 110 interrupts of the
STM32F767 at the ITCM alias, SP at the top of DTCM, and the initialization. -/
def boot : Boot := { org := flashItcm, entries := 126, sp := stackTop, init := initCode init }

/-- The image's instructions from the self-loop on for step `k` of `m` from the state `s0`. -/
def program (m : Wasm.Module) (k : Nat) (s0 : List UInt64) : GenM (List Instr) :=
  bootProgram boot m k s0 stackLimit devBase

/-- The bytes of the image. -/
def image (m : Wasm.Module) (k : Nat) (s0 : List UInt64) : GenM (List UInt8) := do
  return bootBytes boot (← program m k s0)

/-- The address of the loop's head of `main` for the initial state `s0`. -/
def loopHead (s0 : List UInt64) : UInt32 := after boot.base (mainStart s0)

/-- The layout of an image whose area holds the store of `m`: the setup of the generator's area
before the initialization. -/
def areaBoot (m : Wasm.Module) : Boot := boot.setup (setupCode areaHeader areaPages m)

end LeanExe.M7.Nucleo
