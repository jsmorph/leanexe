import LeanExe.M7.Board
import TestSupport.M7.Nucleo
import TestSupport.Bare.Programs

/-!
The test of the setup of `LeanExe/M7/Setup.lean` on the NUCLEO-F767ZI: an image whose setup writes
the area of a module with a nonzero data prefix, CRC-32's table, before the board's
initialization and the echo of `usart3Tick`.  `crcArea` compiles CRC-32 by the table as
`TestSupport.Bare.crcCompiled` does, with one page of memory, so that its area of 69,632 bytes
lies at DTCM's base below the stack.  `areaEcho` gives the image's instructions from the layout
`areaBoot` of `crcArea.module` and the echo's program, whose stack's limit is the area's end.
`m7-windows area-board` writes the image and the area's bytes as the setup leaves them,
`areaPrefixBytes` of the module followed by zeros, which `m7-board.sh area-read` compares with
DTCM read back over SWD after a reset.
-/

namespace TestSupport.M7.Area

open LeanExe.M7 LeanExe.M7.Nucleo TestSupport.Bare

verified_compile (pages := 1) (cap := 1) crcArea := [Library.Hashing.Crc.updateWith,
  Library.Hashing.Crc.crcWith, crcMsg, crcCheck]

/-- The image's instructions from the self-loop on: the setup of the area of `crcArea.module`, the
board's initialization, and the echo's program with the stack's limit at the area's end. -/
def areaEcho : GenM (List Instr) :=
  bootProgram (areaBoot crcArea.module 1) reqCompiled.module 9 [3] (areaLimit 1) devBase

/-- The bytes of the image. -/
def areaEchoImage : GenM (List UInt8) := do
  return bootBytes (areaBoot crcArea.module 1) (← areaEcho)

/-- The area's bytes as the setup leaves them: the prefix and zeros. -/
def areaExpected : List UInt8 :=
  LeanExe.areaPrefixBytes crcArea.module ++
    List.replicate (LeanExe.areaSize 1 - LeanExe.areaPrefix crcArea.module) 0

/-- The address of the board's initialization, after the setup. -/
def areaInit : UInt32 := after boot.reset (setupCode areaBase 1 crcArea.module).length

end TestSupport.M7.Area
