import Project.ProofKit.I64Frame
import Project.ProofKit.LocalPrefix

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit

def KernelState (params saved : List Value) (savedCount ownerSlot copiedSlot : Nat)
    (outputPtr : UInt64) (outputSize : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 193 ∧ frame.values = [] ∧
  I64Values frame.locals ∧ frame.locals.take savedCount = saved ∧
  frame.locals[ownerSlot]? = some (.i64 outputPtr) ∧
  frame.locals[ownerSlot + 1]? = some (.i64 outputPtr) ∧
  frame.locals[ownerSlot + 2]? = some (.i64 (UInt64.ofNat outputSize)) ∧
  frame.locals[copiedSlot]? = some (.i64 outputPtr) ∧
  frame.locals[copiedSlot + 1]? = some (.i64 outputPtr) ∧
  frame.locals[copiedSlot + 2]? = some (.i64 (UInt64.ofNat outputSize))

end Project.Gpt2QuantizedCached.CachedBlock
