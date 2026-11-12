import Verified.Wasi.ReadCost
import Verified.Wasi.SysForm
import LeanExe.Wasi.Semantics

/-! The heap that a `sys` command allocates.  A flat call allocates the buffer of its output, and a
reported call allocates one block after its reporter returns, whose size follows from the
reporter's reply in the trace. -/

namespace Verified.Wasi

open LeanExe.Wasi

/-- The capacity of a flat call's output: the argument word of its `output` parameter. -/
def flatCapacity : List Param → List UInt64 → Option UInt64
  | [], _ => none
  | .output :: _, values => some (values.headD 0)
  | param :: params, values =>
    if param.takesArg then flatCapacity params values.tail else flatCapacity params values

/-- The bytes of the block of a reported call whose reporter returned the reply in `trace`: the
shown region and the hidden region after it at the next multiple of 4. -/
def reportedBlock : List Event → Option UInt64
  | .sys _ _ (.returned errno outputs) :: _ =>
    let sizes : Reply := ⟨errno, outputs⟩
    if errno = 0 ∧ sizes.word 1 + 4 * sizes.word 0 + 3 < 4294967296 then
      some (sizes.word 1 + 4 * sizes.word 0 + 3)
    else none
  | _ => none

def sysCost : SysForm → LeanExe.Wasi.Call → List UInt64 → List Event → Nat
  | .flat .., call, values, _ =>
    match flatCapacity call.params values with
    | some capacity => readCost capacity
    | none => 0
  | .reported, _, _, trace =>
    match reportedBlock trace with
    | some size => Bytes.allocationCost size.toNat
    | none => 0

end Verified.Wasi
