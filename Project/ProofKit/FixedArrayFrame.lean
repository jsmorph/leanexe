import Project.ProofKit.FixedArrayFold

namespace Project.ProofKit.FixedArrayFold
open Wasm

theorem resultFrame_get_ne (frame : Locals) (resultLocal readLocal : Nat) (value : UInt64)
    (hResultLocal : frame.params.length ≤ resultLocal) (hNe : readLocal ≠ resultLocal) :
    (resultFrame frame resultLocal value).get readLocal = frame.get readLocal := by
  by_cases hParam : readLocal < frame.params.length
  · simp [resultFrame, Locals.get, hParam]
  · by_cases hValid : readLocal < frame.params.length + frame.locals.length
    · have hIndexNe : readLocal - frame.params.length ≠ resultLocal - frame.params.length := by omega
      simp [resultFrame, Locals.get, hParam, hValid, Ne.symm hIndexNe]
    · simp [resultFrame, Locals.get, hParam, hValid]

#print axioms resultFrame_get_ne

end Project.ProofKit.FixedArrayFold
