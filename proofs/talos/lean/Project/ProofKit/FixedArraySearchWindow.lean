import Project.ProofKit.FixedArraySearchFrame

namespace Project.ProofKit.FixedArraySearch
open Wasm

theorem frame_eq_of_gets (base : Locals) (offset : Nat)
    (need previous current capacity next result : UInt64)
    (hBound : offset + 6 ≤ base.locals.length) (hValues : base.values = [])
    (hGets : ∀ i : Nat, i < 6 → base.get (base.params.length + offset + i) =
      [.i64 need, .i64 previous, .i64 current, .i64 capacity, .i64 next, .i64 result][i]?) :
    base = frame base.params (base.locals.take offset) (base.locals.drop (offset + 6))
      need previous current capacity next result := by
  let words : List Wasm.Value :=
    [.i64 need, .i64 previous, .i64 current, .i64 capacity, .i64 next, .i64 result]
  have hSlice : (base.locals.drop offset).take 6 = words := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 6
    · rw [List.getElem?_take_of_lt hi, List.getElem?_drop]
      have hNotParam : ¬base.params.length + offset + i < base.params.length := by omega
      have hValid : base.params.length + offset + i < base.params.length + base.locals.length := by omega
      simpa only [Locals.get, hNotParam, hValid, ite_false, ite_true,
        show base.params.length + offset + i - base.params.length = offset + i by omega] using hGets i hi
    · have hTakeBound := List.length_take_le 6 (base.locals.drop offset)
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none
        (by simp only [words, List.length_cons, List.length_nil]; omega)]
  have hRest : base.locals.drop offset = words ++ base.locals.drop (offset + 6) := by
    simpa only [hSlice, List.drop_drop, Nat.add_comm 6 offset] using
      (List.take_append_drop 6 (base.locals.drop offset)).symm
  apply Project.ProofKit.Frame.ext
  · rfl
  · change base.locals = base.locals.take offset ++ (words ++ base.locals.drop (offset + 6))
    rw [← hRest]
    exact (List.take_append_drop offset base.locals).symm
  · exact hValues

#print axioms frame_eq_of_gets

end Project.ProofKit.FixedArraySearch
