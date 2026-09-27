import Project.Beck.ExecutionWordWindow
import Project.Beck.ExecutionWordSet

namespace Project.Beck.Execution

open Wasm Project.ProofKit

theorem locals_window_eq (locals window : List Value) (offset : Nat)
    (reads : ∀ i < window.length, locals[offset + i]? = window[i]?) :
    locals = locals.take offset ++ window ++ locals.drop (offset + window.length) := by
  have slice : (locals.drop offset).take window.length = window := by
    apply List.ext_getElem?
    intro i
    by_cases inside : i < window.length
    · rw [List.getElem?_take_of_lt inside, List.getElem?_drop, reads i inside]
    · rw [List.getElem?_eq_none (by have := List.length_take_le window.length (locals.drop offset); omega),
        List.getElem?_eq_none (by omega)]
  calc
    locals = locals.take offset ++ locals.drop offset := (List.take_append_drop offset locals).symm
    _ = locals.take offset ++ ((locals.drop offset).take window.length ++ (locals.drop offset).drop window.length) :=
      congrArg (locals.take offset ++ ·) (List.take_append_drop window.length (locals.drop offset)).symm
    _ = _ := by rw [slice, List.drop_drop]; simp only [List.append_assoc]

theorem WordLocals.setFrame {locals : List Value} (typed : WordLocals locals) (params : List Value)
    (offset : Nat) (bound : offset + 15 ≤ locals.length) (ptr value : UInt64) (index length : Nat)
    (sourceRead : locals[offset]? = some (.i64 ptr))
    (indexRead : locals[offset + 1]? = some (.i64 index.toUInt64))
    (lengthRead : locals[offset + 2]? = some (.i64 length.toUInt64))
    (countRead : locals[offset + 3]? = some (.i64 length.toUInt64))
    (valueRead : locals[offset + 6]? = some (.i64 value)) :
    ∃ target counter padding1 padding2 need previous current capacity afterNode result : UInt64,
      ({ params := params, locals := locals } : Locals) =
        wordSetFrame params (locals.take offset) (locals.drop (offset + 15)) ptr index length target counter value padding1 padding2
          need previous current capacity afterNode result := by
  obtain ⟨target, read4⟩ := typed.read (offset + 4) (by omega)
  obtain ⟨counter, read5⟩ := typed.read (offset + 5) (by omega)
  obtain ⟨padding1, read7⟩ := typed.read (offset + 7) (by omega)
  obtain ⟨padding2, read8⟩ := typed.read (offset + 8) (by omega)
  obtain ⟨need, read9⟩ := typed.read (offset + 9) (by omega)
  obtain ⟨previous, read10⟩ := typed.read (offset + 10) (by omega)
  obtain ⟨current, read11⟩ := typed.read (offset + 11) (by omega)
  obtain ⟨capacity, read12⟩ := typed.read (offset + 12) (by omega)
  obtain ⟨afterNode, read13⟩ := typed.read (offset + 13) (by omega)
  obtain ⟨result, read14⟩ := typed.read (offset + 14) (by omega)
  refine ⟨target, counter, padding1, padding2, need, previous, current, capacity, afterNode, result, ?_⟩
  apply Frame.ext <;> try rfl
  have split := locals_window_eq locals
    [.i64 ptr, .i64 index.toUInt64, .i64 length.toUInt64, .i64 length.toUInt64,
      .i64 target, .i64 counter, .i64 value, .i64 padding1, .i64 padding2, .i64 need, .i64 previous,
      .i64 current, .i64 capacity, .i64 afterNode, .i64 result] offset (by
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i <;> simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ,
        sourceRead, indexRead, lengthRead, countRead, valueRead, read4, read5, read7, read8, read9, read10, read11, read12, read13, read14])
  simpa only [wordSetFrame, FixedArraySearch.frame, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.append_assoc, List.cons_append, List.nil_append] using split

end Project.Beck.Execution
