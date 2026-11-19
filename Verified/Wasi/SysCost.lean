import Verified.Bytes.Allocation
import Verified.Wasi.SysForm
import LeanExe.Wasi.Semantics

/-! The heap that a `sys` command allocates.  A reported call allocates one block after its
reporter returns, whose size follows from the reporter's reply in the trace.  The other forms
allocate nothing: a fill writes into the buffer that the command takes, and a record call and a
`poll` call place their regions in the call area.  `flatCapacity` and `flatCapacityWith` give the
length of the output of a call's lowered words. -/

namespace Verified.Wasi

open LeanExe.Wasi

/-- The capacity of a flat call's output: the argument word of its `output` parameter. -/
def flatCapacity : List Param → List UInt64 → Option UInt64
  | [], _ => none
  | .output :: _, values => some (values.headD 0)
  | param :: params, values =>
    if param.takesArg then flatCapacity params values.tail else flatCapacity params values

/-- The capacity of a flat call's output, from the words of its word variables, when `inputs`
holds an input for each `input` parameter.  An `input` parameter with no input left takes a word,
as in `flatCapacity`, so that `flatCapacityWith params values []` is `flatCapacity params values`.
-/
def flatCapacityWith : List Param → List UInt64 → List LeanExe.Bytes → Option UInt64
  | [], _, _ => none
  | .output :: _, values, _ => some (values.headD 0)
  | .input :: params, values, _ :: inputs => flatCapacityWith params values inputs
  | param :: params, values, inputs =>
    if param.takesArg then flatCapacityWith params values.tail inputs
    else flatCapacityWith params values inputs

theorem flatCapacityWith_nil : ∀ (params : List Param) (values : List UInt64),
    flatCapacityWith params values [] = flatCapacity params values
  | [], _ => rfl
  | param :: params, values => by
    cases param <;> simp only [flatCapacityWith, flatCapacity, flatCapacityWith_nil params]

/-- The bytes of the block of a reported call whose reporter returned the reply in `trace`: the
shown region and the hidden region after it at the next multiple of 4. -/
def reportedBlock : List Event → Option UInt64
  | .sys _ _ (.returned errno outputs) :: _ =>
    let sizes : Reply := ⟨errno, outputs⟩
    if errno = 0 ∧ sizes.word 1 + 4 * sizes.word 0 + 3 < 4294967296 then
      some (sizes.word 1 + 4 * sizes.word 0 + 3)
    else none
  | _ => none

/-- The heap that the call of a `sys` command allocates, from the trace of its run. -/
def sysCost : SysForm → LeanExe.Wasi.Call → List Event → Nat
  | .reported, _, trace =>
    match reportedBlock trace with
    | some size => Bytes.allocationCost size.toNat
    | none => 0
  | .flat .., _, _ | .record _, _, _ | .iovecRead, _, _ | .iovecWrite, _, _ | .poll, _, _ => 0

end Verified.Wasi
