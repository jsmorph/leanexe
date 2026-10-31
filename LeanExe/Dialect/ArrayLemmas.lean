/-! Lemmas about reads `xs[k]!` of arrays after `set!` and `push`, and about the words of a prefix
`xs.toList.take n`. -/

namespace LeanExe.Dialect

theorem get_set {α : Type} [Inhabited α] (c : Array α) (i : Nat) (v : α) (k : Nat)
    (hi : i < c.size) : (c.set! i v)[k]! = if k = i then v else c[k]! := by
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hk : k < c.size
  · rw [getElem!_pos _ k (by simpa using hk), Array.getElem_setIfInBounds hk, getElem!_pos c k hk]
    by_cases h : k = i <;> simp_all [eq_comm]
  · rw [getElem!_neg _ k (by simpa using hk), getElem!_neg c k hk]
    have : k ≠ i := by omega
    simp [this]

theorem get_toList {α : Type} [Inhabited α] (q : Array α) {p : Nat} (hp : p < q.size) :
    q[p]! = q.toList[p]'(by simpa using hp) := by
  rw [getElem!_pos q p hp]; simp

theorem push_get_lt {α : Type} [Inhabited α] (q : Array α) (x : α) {p : Nat} (hp : p < q.size) :
    (q.push x)[p]! = q[p]! := by
  rw [getElem!_pos _ p (by simp; omega), getElem!_pos q p hp, Array.getElem_push_lt]

theorem push_get_size {α : Type} [Inhabited α] (q : Array α) (x : α) :
    (q.push x)[q.size]! = x := by
  rw [getElem!_pos _ q.size (by simp), Array.getElem_push_eq]

theorem take_get_mem {α : Type} [Inhabited α] {q : Array α} {f : Nat} {x : α}
    (h : x ∈ q.toList.take f) : ∃ p, p < f ∧ p < q.size ∧ q[p]! = x := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_take, Array.length_toList] at hp
  refine ⟨p, by omega, by omega, ?_⟩
  rw [get_toList q (by omega)]
  simp

end LeanExe.Dialect
