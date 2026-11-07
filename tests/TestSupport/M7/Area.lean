import LeanExe.M7.Board
import TestSupport.M7.Nucleo
import TestSupport.M7.Crc

/-!
The test of the setup of `LeanExe/M7/Setup.lean` on the NUCLEO-F767ZI: an image whose setup writes
the area of the CRC-32 step's module `crcStepCompiled.module` of `tests/TestSupport/M7/Crc.lean`,
whose memory of one page holds CRC-32's table, before the board's initialization and the echo of
`usart3Tick`.  `areaEcho` gives the image's instructions from the layout `areaBoot` of that module
and the echo's program, whose stack's limit is the area's end.  `m7-windows area-board` writes the
image and the area's bytes as the setup leaves them, `areaPrefixBytes` of the module followed by
zeros, which `m7-board.sh area-read` compares with DTCM read back over SWD after a reset.
-/

namespace TestSupport.M7.Area

open LeanExe.M7 LeanExe.M7.Nucleo TestSupport.Bare TestSupport.M7.Crc

/-- The image's instructions from the self-loop on: the setup of the area of the CRC-32 step's
module, the board's initialization, and the echo's program with the stack's limit at the area's
end. -/
def areaEcho : GenM (List Instr) :=
  bootProgram (areaBoot crcStepCompiled.module) reqCompiled.module 9 [3] areaEnd devBase

/-- The bytes of the image. -/
def areaEchoImage : GenM (List UInt8) := do
  return bootBytes (areaBoot crcStepCompiled.module) (← areaEcho)

/-- The area's bytes as the setup leaves them: the prefix and zeros. -/
def areaExpected : List UInt8 :=
  LeanExe.areaPrefixBytes crcStepCompiled.module ++
    List.replicate (LeanExe.areaSize areaPages - LeanExe.areaPrefix crcStepCompiled.module) 0

/-- The address of the board's initialization, after the setup. -/
def areaInit : UInt32 :=
  after boot.reset (setupCode areaHeader areaPages crcStepCompiled.module).length

end TestSupport.M7.Area
