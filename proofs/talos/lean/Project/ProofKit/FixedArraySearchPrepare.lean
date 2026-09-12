import Project.ProofKit.FixedArraySearchFrame
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.FixedArrayCapacity

namespace Project.ProofKit.FixedArraySearch
open Wasm

theorem resultFrame_before (params saved tail : List Wasm.Value)
    (need previous current capacity next result : UInt64) (index : Nat) (value : UInt64)
    (hLower : params.length ≤ index) (hUpper : index < params.length + saved.length) :
    FixedArrayFold.resultFrame (frame params saved tail need previous current capacity next result)
      index value =
      frame params (saved.set (index - params.length) (.i64 value)) tail
        need previous current capacity next result := by
  have hIndex : index - params.length < saved.length := by omega
  apply Frame.ext
  · rfl
  · exact List.set_append_left (index - params.length) (.i64 value) hIndex
  · rfl

theorem capacityFrame_need (params saved tail : List Wasm.Value)
    (need previous current capacity next result value : UInt64) :
    FixedArrayCapacity.capacityFrame (frame params saved tail need previous current capacity next result)
      (params.length + saved.length) value =
      frame params saved tail value previous current capacity next result := by
  apply Frame.ext
  · rfl
  · simp [FixedArrayCapacity.capacityFrame, frame]
  · rfl

#print axioms resultFrame_before
#print axioms capacityFrame_need

end Project.ProofKit.FixedArraySearch
