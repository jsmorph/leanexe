import Project.ProofKit.FixedArraySearchFrame

namespace Project.ProofKit
open Wasm

def I64Values (values : List Wasm.Value) : Prop :=
  ∀ value ∈ values, ∃ word : UInt64, value = .i64 word

theorem I64Values.set {values : List Wasm.Value} (h : I64Values values) (index : Nat) (word : UInt64) :
    I64Values (values.set index (.i64 word)) := by
  intro value hValue
  rcases List.mem_or_eq_of_mem_set hValue with hValue | rfl
  · exact h value hValue
  · exact ⟨word, rfl⟩

theorem I64Values.replicate (count : Nat) (word : UInt64) :
    I64Values (List.replicate count (.i64 word)) := by
  intro value hValue
  exact ⟨word, (List.mem_replicate.mp hValue).2⟩

theorem I64Values.take {values : List Wasm.Value} (h : I64Values values) (count : Nat) :
    I64Values (values.take count) := fun value hValue => h value (List.mem_of_mem_take hValue)

theorem I64Values.drop {values : List Wasm.Value} (h : I64Values values) (count : Nat) :
    I64Values (values.drop count) := fun value hValue => h value (List.mem_of_mem_drop hValue)

theorem I64Values.append {left right : List Wasm.Value} (hLeft : I64Values left) (hRight : I64Values right) :
    I64Values (left ++ right) := by
  intro value hValue
  rcases List.mem_append.mp hValue with hValue | hValue
  · exact hLeft value hValue
  · exact hRight value hValue

theorem I64Values.cons {values : List Wasm.Value} (h : I64Values values) (word : UInt64) :
    I64Values (.i64 word :: values) := by
  intro value hValue
  rcases List.mem_cons.mp hValue with rfl | hValue
  · exact ⟨word, rfl⟩
  · exact h value hValue

theorem I64Values.nil : I64Values [] := by simp [I64Values]

theorem I64Values.block6 {values : List Wasm.Value} (h : I64Values values)
    (start : Nat) (hBound : start + 6 ≤ values.length) :
    ∃ a b c d e f : UInt64,
      values = values.take start ++ [.i64 a, .i64 b, .i64 c, .i64 d, .i64 e, .i64 f] ++
        values.drop (start + 6) := by
  have h0 : start < values.length := by omega
  have h1 : start + 1 < values.length := by omega
  have h2 : start + 2 < values.length := by omega
  have h3 : start + 3 < values.length := by omega
  have h4 : start + 4 < values.length := by omega
  have h5 : start + 5 < values.length := by omega
  obtain ⟨a, ha⟩ := h _ (List.getElem_mem h0)
  obtain ⟨b, hb⟩ := h _ (List.getElem_mem h1)
  obtain ⟨c, hc⟩ := h _ (List.getElem_mem h2)
  obtain ⟨d, hd⟩ := h _ (List.getElem_mem h3)
  obtain ⟨e, he⟩ := h _ (List.getElem_mem h4)
  obtain ⟨f, hf⟩ := h _ (List.getElem_mem h5)
  refine ⟨a, b, c, d, e, f, ?_⟩
  have hDrop : values.drop start = [.i64 a, .i64 b, .i64 c, .i64 d, .i64 e, .i64 f] ++
      values.drop (start + 6) := by
    rw [List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [List.drop_eq_getElem_cons h2]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [List.drop_eq_getElem_cons h3]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [List.drop_eq_getElem_cons h4]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [List.drop_eq_getElem_cons h5]
    simp only [Nat.add_assoc, Nat.reduceAdd, ha, hb, hc, hd, he, hf,
      List.cons_append, List.nil_append]
  simpa only [hDrop, List.append_assoc] using (List.take_append_drop start values).symm

theorem Frame.exists_allocator {frame : Locals} (hValues : frame.values = [])
    (hTyped : I64Values frame.locals) (start : Nat) (need : UInt64)
    (hBound : start + 6 ≤ frame.locals.length)
    (hNeed : frame.get (frame.params.length + start) = some (.i64 need)) :
    ∃ previous current capacity next result : UInt64,
      frame = FixedArraySearch.frame frame.params (frame.locals.take start)
        (frame.locals.drop (start + 6)) need previous current capacity next result := by
  obtain ⟨a, b, c, d, e, f, hLocals⟩ := hTyped.block6 start hBound
  have hStart : (frame.locals.take start).length = start := by simp; omega
  have hA : a = need := by
    have h := hNeed
    simp only [Locals.get, Nat.not_lt.mpr (Nat.le_add_right _ _), ite_false, Nat.add_sub_cancel_left] at h
    rw [hLocals] at h
    simpa [List.getElem?_append, hStart, List.append_assoc] using h
  subst a
  exact ⟨b, c, d, e, f, Frame.ext _ _ rfl (by simpa [FixedArraySearch.frame, List.append_assoc] using hLocals) hValues⟩

#print axioms I64Values.block6
#print axioms Frame.exists_allocator

end Project.ProofKit
