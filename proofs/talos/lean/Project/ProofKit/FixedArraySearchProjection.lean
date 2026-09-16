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

theorem frame_get_outside (params saved tail : List Wasm.Value)
    (need previous current capacity next result need' previous' current' capacity' next' result' : UInt64)
    (index : Nat) (hOutside : index < params.length + saved.length ∨
      params.length + saved.length + 6 ≤ index) :
    (frame params saved tail need' previous' current' capacity' next' result').get index =
      (frame params saved tail need previous current capacity next result).get index := by
  rcases hOutside with hBefore | hAfter
  · rw [frame_get_before _ _ _ _ _ _ _ _ _ index hBefore,
      frame_get_before _ _ _ _ _ _ _ _ _ index hBefore]
  · have hParam : ¬index < params.length := by omega
    have hSaved : ¬index - params.length < saved.length := by omega
    have hWindow : ¬index - params.length - saved.length < 6 := by omega
    simp only [frame, Locals.get, hParam, ite_false, List.length_append,
      List.length_cons, List.length_nil, List.getElem?_append, Nat.reduceAdd, hSaved, hWindow]

#print axioms frame_get_outside

end Project.ProofKit.FixedArraySearch
