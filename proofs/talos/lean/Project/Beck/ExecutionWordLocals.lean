import Project.Beck.ExecutionScalar

namespace Project.Beck.Execution

open Wasm

def WordLocals (locals : List Value) : Prop := ∀ value ∈ locals, ∃ word : UInt64, value = .i64 word

theorem WordLocals.nil : WordLocals [] := by simp [WordLocals]

theorem WordLocals.cons {locals : List Value} (typed : WordLocals locals) (word : UInt64) :
    WordLocals (.i64 word :: locals) := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨word, rfl⟩
  · exact typed value member

theorem WordLocals.replicate (count : Nat) (word : UInt64) : WordLocals (List.replicate count (.i64 word)) := by
  intro value member
  exact ⟨word, (List.mem_replicate.mp member).2⟩

theorem WordLocals.set {locals : List Value} (typed : WordLocals locals) (index : Nat) (word : UInt64) :
    WordLocals (locals.set index (.i64 word)) := by
  intro value member
  rcases List.mem_or_eq_of_mem_set member with old | equal
  · exact typed value old
  · exact ⟨word, equal⟩

theorem WordLocals.append {first second : List Value} (left : WordLocals first) (right : WordLocals second) :
    WordLocals (first ++ second) := by
  intro value member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact left value leftMember
  · exact right value rightMember

theorem WordLocals.take {locals : List Value} (typed : WordLocals locals) (count : Nat) : WordLocals (locals.take count) :=
  fun value member => typed value (List.mem_of_mem_take member)

theorem WordLocals.drop {locals : List Value} (typed : WordLocals locals) (count : Nat) : WordLocals (locals.drop count) :=
  fun value member => typed value (List.mem_of_mem_drop member)

theorem WordLocals.read {locals : List Value} (typed : WordLocals locals) (index : Nat) (bound : index < locals.length) :
    ∃ word : UInt64, locals[index]? = some (.i64 word) := by
  obtain ⟨word, equal⟩ := typed locals[index] (List.getElem_mem bound)
  exact ⟨word, by rw [List.getElem?_eq_getElem bound, equal]⟩

end Project.Beck.Execution
