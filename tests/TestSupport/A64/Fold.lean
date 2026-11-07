import Verified.Examples.Fold
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare

/-!
The theorem of the bare-metal program for AArch64 of Fold's recursion of depth 1000, in the form
`ProgramRuns`, for every room and cap: `main` calls entry 13 of
`Verified.Examples.Fold.compiled.module`, `recursive`, on 1000.  The machine writes the eight bytes
of `recursive 1000` to the UART and returns 0, or it reaches the exit word with the status 1 of
`unreachable`, which the guard of the call depth reaches, or the status 4 of an overflow of the
stack.
-/

namespace TestSupport.A64.Fold

open LeanExe.A64 Verified.Examples.Fold

theorem runs (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 13 [1000] room cap .word
      (LeanExe.Native.encodeWord (recursive 1000)) fun c => c = 1 ∨ c = 4 :=
  program_runs_implements compiled.recursive.implements 1000 compiled.initial.1 (fun _ => trivial)
    writes_word

end TestSupport.A64.Fold
