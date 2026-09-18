import Project.ProofKit.I64Frame

namespace Project.ProofKit
open Wasm

theorem Frame.local_of_take_eq {before after : Locals} {count index : Nat}
    (hPrefix : after.locals.take count = before.locals.take count) (hIndex : index < count) :
    after.locals[index]? = before.locals[index]? := by
  have h := congrArg (fun values => values[index]?) hPrefix
  simpa only [List.getElem?_take_of_lt hIndex] using h

theorem Frame.get_of_take_eq {before after : Locals} {count index : Nat}
    (hParams : after.params = before.params)
    (hPrefix : after.locals.take count = before.locals.take count)
    (hBefore : count ≤ before.locals.length) (hAfter : count ≤ after.locals.length)
    (hIndex : index < before.params.length + count) :
    after.get index = before.get index := by
  unfold Locals.get
  rw [hParams]
  by_cases hParam : index < before.params.length
  · simp only [hParam, ite_true]
  · have hLocal : index - before.params.length < count := by omega
    simp only [hParam, ite_false,
      show index < before.params.length + before.locals.length by omega,
      show index < before.params.length + after.locals.length by omega, ite_true]
    exact local_of_take_eq hPrefix hLocal

#print axioms Frame.local_of_take_eq
#print axioms Frame.get_of_take_eq

end Project.ProofKit
