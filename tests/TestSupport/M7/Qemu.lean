import LeanExe.M7.Boot
import TestSupport.Bare.Req

/-!
The echo of `cmsdkTick` through the Cortex-M7 back end on QEMU's `mps2-an500`, an emulated
Cortex-M7.  QEMU 8.2.2 loads a raw image given with `-kernel` at address 0, in ZBT SSRAM1
(`hw/arm/armv7m.c`, `armv7m_load_kernel`, and `hw/arm/mps2.c`), and at reset its Cortex-M7 reads
the vector table from `VTOR`, whose reset value on this board is 0 (`target/arm/cpu.c`, lines 429
to 457, `hw/arm/armv7m.c`, line 547, and `hw/arm/mps2.c`, line 234).  The image holds the table
of the 16 system entries and the 32 interrupts of QEMU's AN500, the self-loop, UART0's
initialization, and the program that the generator places after it.

`platform` names the memories and devices of the board that the program uses: ZBT SSRAM2 and
SSRAM3, 4 MiB at `0x20000000`, as Normal memory, and the 65,536 words of the APB devices from
`0x40000000`, among them CMSDK UART0 at `0x40004000` (Arm DAI 0500B, Tables 3-1 and 3-3, and
`docs/native-bare-metal.md`).  SP starts at the top of SSRAM2 and SSRAM3, and the stack's limit is
their base.  The initialization sets UART0's `BAUDDIV`, index `0x1004`, to 16, the minimum, and
its `CTRL`, index `0x1002`, to 3, the transmitter and receiver enables, without which QEMU's model
sends no byte and takes none (`hw/char/cmsdk-apb-uart.c`, lines 115 to 124, 194 to 203, and 249
to 260), as `board_init` of `tools/baremetal/armv7m/mps2-an500/board.S` does.
-/

namespace TestSupport.M7.Qemu

open LeanExe.M7 TestSupport.Bare

/-- SSRAM2 and SSRAM3 as Normal memory, and the APB devices' 65,536 words from `0x40000000`. -/
def platform : Platform :=
  { normal := fun b => decide (0x20000000 ≤ b.toNat ∧ b.toNat < 0x20400000)
    device := fun a => decide (0x40000000 ≤ a.toNat ∧ a.toNat < 0x40040000) }

/-- The device window of the requests: `lx_reg` of the C path's programs on this board. -/
def devBase : UInt32 := 0x40000000

/-- The stack's limit, the base of SSRAM2 and SSRAM3. -/
def stackLimit : UInt32 := 0x20000000

/-- The initial SP, the top of SSRAM2 and SSRAM3. -/
def stackTop : UInt32 := 0x20400000

/-- UART0's initialization: r1 to UART0's base, `BAUDDIV` to 16, and `CTRL` to 3. -/
def init : List Instr :=
  [.movwOf 1 0x4000, .movtOf 1 0x4000, .movImm 0 16, .str 0 1 16, .movImm 0 3, .str 0 1 8]

/-- The device accesses of the initialization. -/
def initTrace : List Access := [.write 0x40004010 16, .write 0x40004008 3]

/-- The image's layout: the vector table of 48 words at 0, SP at the top of SSRAM2 and SSRAM3,
and UART0's initialization. -/
def boot : Boot := { org := 0, entries := 48, sp := stackTop, init := init }

/-- The echo's instructions from the self-loop on: the step `cmsdkTick`, function 5 of
`reqCompiled.module`, from the state 3. -/
def echoProgram : GenM (List Instr) :=
  bootProgram boot reqCompiled.module 5 [3] stackLimit devBase

/-- The bytes of the echo's image. -/
def echoImage : GenM (List UInt8) := do
  return bootBytes boot (← echoProgram)

/-- The address of the loop's head of `main`. -/
def loopHead : UInt32 := after boot.base (mainStart [3])

end TestSupport.M7.Qemu
