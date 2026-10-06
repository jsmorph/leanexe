import Project.Smalltalk.Marking

namespace Project.Smalltalk.Collector
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.Marking Project.Smalltalk.Sweep

theorem collectReady_eq_finish {original : Array UInt64} {cap : Nat}
    (valid : Graph.Valid original cap) (phase : read original 0 ≠ 4) :
    collectReady original = finishCollection (marking original) (read original 14) (read original 11 + 1) := by
  have facts := marking_correct valid phase
  have ok : read (marking original) 0 ≠ 4 := by rw [facts.2.2 0 (by decide) (by decide)]; exact phase
  change (if read (marking original) 0 == 4 || read (marking original) 18 != 0 then
    fail (marking original) 3 else finishCollection (marking original) (read original 14) (read original 11 + 1)) = _
  simp [ok, facts.2.1]

theorem collect_eq_finish {original : Array UInt64} {cap : Nat}
    (valid : Graph.Valid original cap) (phase : read original 0 ≠ 4) :
    collect original = finishCollection (marking original) (read (marking original) 14) (read original 11 + 1) := by
  have facts := marking_correct valid phase
  simp only [collect, beq_iff_eq, phase, ite_false]
  rw [collectReady_eq_finish valid phase, facts.2.2 14 (by decide) (by decide)]

/-- The concrete collector preserves all reachable payloads and frees exactly
the unreachable handles. The rebuilt list is complete, distinct, and counted.
This theorem assumes a valid heap and a phase other than error. -/
theorem collect_correct {original : Array UInt64} {cap : Nat}
    (valid : Graph.Valid original cap) (phase : read original 0 ≠ 4) :
    Shape (collect original) cap ∧
    (∀ h, Reachable original h → ∀ k : UInt64, k.toNat < 8 → k ≠ 1 →
      field (collect original) h k = field original h k) ∧
    ∃ nodes, Project.Smalltalk.FreeList.Valid (collect original) cap nodes ∧
      (∀ h, Handle cap h → (h ∈ nodes ↔ ¬ Reachable original h)) ∧ nodes.Nodup := by
  have facts := marking_correct valid phase
  rw [collect_eq_finish valid phase]
  exact ⟨finishCollection_shape facts.1.1 _, sweep_correct valid facts.1 _⟩

theorem collect_register {original : Array UInt64} {cap : Nat} {r : UInt64}
    (valid : Graph.Valid original cap) (phase : read original 0 ≠ 4) (hr : r.toNat < 24)
    (notHead : r ≠ 8) (notCount : r ≠ 9) (notLast : r ≠ 10) (notStats : r ≠ 11) (notWork : r ≠ 18) :
    read (collect original) r = read original r := by
  have facts := marking_correct valid phase
  rw [collect_eq_finish valid phase,
    finishCollection_register facts.1.1 hr notHead notCount notLast notStats,
    facts.2.2 r hr notWork]

theorem collect_error_unchanged (s : Array UInt64) (error : read s 0 = 4) : collect s = s := by
  unfold collect
  rw [error]
  rfl

end Project.Smalltalk.Collector
