import LeanExe.M7.Board

/-!
The diagnostic image of the NUCLEO-F767ZI's debug state at reset, which `m7-windows diag` writes,
`tests/baremetal/m7-board.sh diag` runs, and no theorem covers.  At its reset entry, before the
board's initialization, the image reads DHCSR, DEMCR, DFSR, `FP_CTRL`, `DWT_CTRL`, `ITM_TCR`,
`DBGMCU_CR`, `DBGMCU_APB1_FZ`, `DBGMCU_APB2_FZ`, and `RCC_CSR`, and stores them in that order in
a record at DTCM's base after a magic word and the number of starts.  DDI 0403E.e section C1.6.5
makes reads of the DWT and the ITM UNKNOWN while DEMCR.TRCENA is 0, so the image sets TRCENA for
its reads of `DWT_CTRL` and `ITM_TCR` and then writes back the DEMCR that it read.  It sets RMVF in
`RCC_CSR`, so that the next start reads the flags of its own reset only, and counts the start:
DTCM keeps its contents over a system reset, and the count restarts from 1 when the magic word is
absent.  The board's initialization follows, and then a loop that, for each byte that USART3
receives, sends the record's 48 bytes, each word's low byte first.  `tests/baremetal/uart_diag.py`
plays the far end.
-/

namespace TestSupport.M7.Diag

open LeanExe.M7 LeanExe.M7.Nucleo

def record : UInt32 := 0x20000000
def magic : UInt32 := 0xD1A6C0DE

/-- DHCSR, with DEMCR 12 bytes above it. -/
def dhcsr : UInt32 := 0xE000EDF0
def dfsr : UInt32 := 0xE000ED30
def fpCtrl : UInt32 := 0xE0002000
def dwtCtrl : UInt32 := 0xE0001000
def itmTcr : UInt32 := 0xE0000E80
/-- `DBGMCU_CR`, with `DBGMCU_APB1_FZ` and `DBGMCU_APB2_FZ` 4 and 8 bytes above it. -/
def dbgmcuCr : UInt32 := 0xE0042004
def rccCsr : UInt32 := 0x40023874

/-- The reads at the reset entry into words 2 to 11 of the record, whose address r7 holds, with
DEMCR's value kept in r2 for its restore, then RMVF, and then the count in word 1. -/
def captureCode : List Instr :=
  movWord 7 record ++
  movWord 0 dhcsr ++ [.ldr 1 0 0, .str 1 7 8, .ldr 2 0 12, .str 2 7 12] ++
  movWord 3 dfsr ++ [.ldr 1 3 0, .str 1 7 16] ++
  movWord 3 fpCtrl ++ [.ldr 1 3 0, .str 1 7 20] ++
  movWord 4 0x01000000 ++ [.orrReg 0 4 2 4, .str 4 0 12] ++
  movWord 3 dwtCtrl ++ [.ldr 1 3 0, .str 1 7 24] ++
  movWord 3 itmTcr ++ [.ldr 1 3 0, .str 1 7 28] ++
  [.str 2 0 12] ++
  movWord 3 dbgmcuCr ++
    [.ldr 1 3 0, .str 1 7 32, .ldr 1 3 4, .str 1 7 36, .ldr 1 3 8, .str 1 7 40] ++
  movWord 3 rccCsr ++ [.ldr 1 3 0, .str 1 7 44] ++
  movWord 4 0x01000000 ++ [.orrReg 0 1 1 4, .str 1 3 0] ++
  [.ldr 1 7 0] ++ movWord 2 magic ++
  [.cmpReg 1 2, Instr.bcondTo 0 12, .movImm 3 0, .str 3 7 4, .str 2 7 0,
    .ldr 3 7 4, .movImm 1 1, Instr.addLsl 0 3 3 1 0, .str 3 7 4]

/-- The loop after the initialization, with `USART_ISR`'s address in r0, the record's in r6, and
the byte's index in r5: a wait for RXNE, the read of `USART_RDR`, and for each of the 48 bytes a
wait for TXE and the write of the byte to `USART_TDR`. -/
def loopCode : List Instr :=
  movWord 0 usartIsr ++ movWord 6 record ++
  [.ldr 1 0 0, .andImm 1 1 32, .cmpImm 1 0, Instr.bcondTo 0 (-16),
    .ldr 1 0 8, .movImm 5 0,
    .ldr 1 0 0, .andImm 1 1 128, .cmpImm 1 0, Instr.bcondTo 0 (-16),
    Instr.lsrBy 2 5 2, Instr.addLsl 0 3 6 2 2, .ldr 3 3 0, .andImm 4 5 3, Instr.lslBy 4 4 3,
    .lsrReg 3 3 4, .andImm 3 3 255, .str 3 0 12,
    .movImm 1 1, Instr.addLsl 0 5 5 1 0, .cmpImm 5 48, Instr.bcondTo 1 (-64),
    Instr.bTo (-92)]

/-- The board's layout with the reads before the initialization. -/
def diagBoot : Boot :=
  { org := flashItcm, entries := 126, sp := stackTop, init := captureCode ++ initCode init }

/-- The bytes of the image. -/
def diagImage : List UInt8 := bootBytes diagBoot (Instr.bTo (-4) :: diagBoot.init ++ loopCode)

end TestSupport.M7.Diag
