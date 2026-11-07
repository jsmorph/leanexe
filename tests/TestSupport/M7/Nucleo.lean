import LeanExe.M7.Board
import TestSupport.Bare.Req

/-!
The echo of `usart3Tick` through the Cortex-M7 back end on the NUCLEO-F767ZI: the image of
`LeanExe/M7/Board.lean` for the step `usart3Tick`, function 9 of `reqCompiled.module`, from the
state 3, the state from which `uart_echo.py` drives the C path's echo.  `m7-windows board` writes
its bytes to `echo.bin`, which `st-flash` writes to the board's flash at `0x08000000`.
-/

namespace TestSupport.M7.Nucleo

open LeanExe.M7 LeanExe.M7.Nucleo TestSupport.Bare

/-- The echo's instructions from the self-loop on. -/
def echoProgram : GenM (List Instr) := program reqCompiled.module 9 [3]

/-- The bytes of the echo's image. -/
def echoImage : GenM (List UInt8) := image reqCompiled.module 9 [3]

/-- The address of the loop's head of the echo's `main`. -/
def echoHead : UInt32 := loopHead [3]

end TestSupport.M7.Nucleo
