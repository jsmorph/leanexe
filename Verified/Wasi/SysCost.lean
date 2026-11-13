import Verified.Wasi.ReadCost
import Verified.Wasi.SysForm
import LeanExe.Wasi.Semantics

/-! The heap that a `sys` command allocates.  A flat call allocates the buffer of its output, a
reported call allocates one block after its reporter returns, whose size follows from the
reporter's reply in the trace, and a record call allocates the block of its record. -/

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

/-- The bytes of the block of a record call: the record's size and `align - 1` bytes in which to
align it. -/
def recordBlock (params : List Param) : Nat :=
  match recordOf params with
  | some (size, align, _) => size + align - 1
  | none => 0

def sysCost : SysForm → LeanExe.Wasi.Call → List UInt64 → List Event → Nat
  | .flat .., call, values, _ =>
    match flatCapacity call.params values with
    | some capacity => readCost capacity
    | none => 0
  | .reported, _, _, trace =>
    match reportedBlock trace with
    | some size => Bytes.allocationCost size.toNat
    | none => 0
  | .record _, call, _, _ => Bytes.allocationCost (recordBlock call.params)

/-- The heap that a `sys` command allocates, with the bytes of its input variables. -/
def sysCostWith : SysForm → LeanExe.Wasi.Call → List UInt64 → List LeanExe.Bytes → List Event → Nat
  | .flat .., call, values, inputs, _ =>
    match flatCapacityWith call.params values inputs with
    | some capacity => readCost capacity
    | none => 0
  | .reported, call, values, _, trace => sysCost .reported call values trace
  | .record _, call, _, _, _ => Bytes.allocationCost (recordBlock call.params)

theorem sysCostWith_nil (form : SysForm) (call : LeanExe.Wasi.Call) (values : List UInt64) :
    sysCostWith form call values [] = sysCost form call values := by
  funext trace
  cases form with
  | flat words bytes => simp only [sysCostWith, sysCost, flatCapacityWith_nil]
  | reported => rfl
  | record => rfl

end Verified.Wasi
