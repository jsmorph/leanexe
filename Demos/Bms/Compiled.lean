import Demos.Bms.Program
import Verified.Reflect.Command
import Verified.Call

/-!
The BMS step of `Demos/Bms/Program.lean` compiled by the verified compiler.  `bmsCompiled.module`
exports `bmsTickUsart3`, the step for USART3, and `bmsTick`, the step for UART0 of `mps2-an500`,
and `bmsDelim` and `bmsPoll`, the two functions that the steps' dispatch calls.  The generated
`implements` theorem of each step states that the module's function computes the Lean step from
every store without a trap, which the Cortex-M7 back end's step theorems of
`tests/TestSupport/M7/BmsStep.lean` take.
-/

namespace Demos.Bms.Program

open LeanExe.Native (readReq writeReq)
open LeanExe.Requests
open Library.Hashing.Crc.Bitwise (crc32Reg crc32Word)

set_option maxRecDepth 100000 in
verified_compile (pages := 1) (cap := 1) bmsCompiled := [readReq, writeReq, zero40, push40,
  unshift40, first40, last40, decByte, decPos, dec8, decAll, decodeWords, encByte, encPos, enc8,
  encAll, encStart, encFinish, crc32Reg, crc32Word, decodeRec, recCrc, bias16, bias32, bitW,
  cellOutW, tempOutW, sensorW, overVW, underVW, overTW, underTW, chgOverW, disOverW, chgOutW,
  chgTempW, sumW, auxW, contentW, permitOf, failW, goodW, acceptW, startW, pcCondW, rule4W,
  rule5W, nextW, ageW, updW, answerSrc, segKind, bmsDelim, bmsPoll, bmsTickUsart3, bmsTick]

end Demos.Bms.Program
