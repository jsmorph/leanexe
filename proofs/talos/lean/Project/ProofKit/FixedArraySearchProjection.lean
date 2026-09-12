import Project.ProofKit.FixedArraySearchFrame

namespace Project.ProofKit.FixedArraySearch
open Wasm

theorem frame_get_before (params saved tail : List Wasm.Value)
    (need previous current capacity next result : UInt64) (index : Nat)
    (hIndex : index < params.length + saved.length) :
    (frame params saved tail need previous current capacity next result).get index =
      ({ params := params, locals := saved, values := [] } : Locals).get index := by
  by_cases hParam : index < params.length
  · simp [frame, Locals.get, hParam]
  · have hSaved : index - params.length < saved.length := by omega
    simp [frame, Locals.get, hParam, hIndex, List.getElem?_append, hSaved]
    omega

#print axioms frame_get_before

end Project.ProofKit.FixedArraySearch
