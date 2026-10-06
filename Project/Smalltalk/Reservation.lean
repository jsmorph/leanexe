import Project.Smalltalk.Heap

namespace Project.Smalltalk.Reservation
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.Collector Project.Smalltalk.CollectorPreservation

structure Effect (original t : Array UInt64) (cap : Nat) : Prop where
  heap : Heap.Valid t cap
  payload : ∀ h, Reachable original h → ∀ k : UInt64, k.toNat < 8 → k ≠ 1 →
    field t h k = field original h k
  registers : ∀ r : UInt64, r.toNat < 24 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 18 →
    read t r = read original r
  reachable : ∀ h, Reachable t h ↔ Reachable original h

theorem effect_refl {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap) : Effect s s cap :=
  ⟨valid, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ => Iff.rfl⟩

theorem effect_trans {s t u : Array UInt64} {cap : Nat}
    (left : Effect s t cap) (right : Effect t u cap) : Effect s u cap := by
  refine ⟨right.heap, ?_, ?_, ?_⟩
  · intro h reached k bound nonmark
    rw [right.payload h ((left.reachable h).mpr reached) k bound nonmark,
      left.payload h reached k bound nonmark]
  · intro r bound h8 h9 h10 h11 h18
    exact (right.registers r bound h8 h9 h10 h11 h18).trans (left.registers r bound h8 h9 h10 h11 h18)
  · intro h
    exact (right.reachable h).trans (left.reachable h)

theorem effect_phase {s t : Array UInt64} {cap : Nat} (effect : Effect s t cap) : read t 0 = read s 0 :=
  effect.registers 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem collect_effect {s : Array UInt64} {cap : Nat}
    (valid : Graph.Valid s cap) (phase : read s 0 ≠ 4) : Effect s (collect s) cap :=
  ⟨Heap.collect_valid valid phase, (collect_correct valid phase).2.1,
    fun _ bound h8 h9 h10 h11 h18 => collect_register valid phase bound h8 h9 h10 h11 h18,
    fun _ => collect_reachable valid phase⟩

theorem stress_effect {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (need : UInt64) : Effect s (stressCollection s need) cap := by
  unfold stressCollection
  split
  · exact collect_effect valid.1 phase
  · exact effect_refl valid

theorem space_effect {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (need : UInt64) : Effect s (spaceCollection s need) cap := by
  unfold spaceCollection
  split
  · exact collect_effect valid.1 phase
  · exact effect_refl valid

def prepared (s : Array UInt64) (need : UInt64) : Array UInt64 :=
  spaceCollection (stressCollection s need) need

theorem prepared_effect {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (need : UInt64) : Effect s (prepared s need) cap := by
  have first := stress_effect valid phase need
  have nonerror : read (stressCollection s need) 0 ≠ 4 := by rw [effect_phase first]; exact phase
  exact effect_trans first (space_effect first.heap nonerror need)

theorem reserve_eq {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (need : UInt64) :
    reserve s need = if read (prepared s need) 9 < need then fail (prepared s need) 9 else prepared s need := by
  have effect := prepared_effect valid phase need
  have nonerror : read (prepared s need) 0 ≠ 4 := by rw [effect_phase effect]; exact phase
  change (if read (prepared s need) 0 == 4 then prepared s need else
    if read (prepared s need) 9 < need then fail (prepared s need) 9 else prepared s need) = _
  rw [show (read (prepared s need) 0 == 4) = false from beq_eq_false_iff_ne.mpr nonerror]
  rfl

/-- Reservation preserves the typed heap, complete free list, and all original
reachable payloads. It either supplies the requested free cells with the
original phase, or reports out-of-memory error 9. -/
theorem reserve_correct {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (need : UInt64) :
    Heap.Valid (reserve s need) cap ∧
    (∀ h, Reachable s h → ∀ k : UInt64, k.toNat < 8 → k ≠ 1 →
      field (reserve s need) h k = field s h k) ∧
    (∀ h, Reachable (reserve s need) h ↔ Reachable s h) ∧
    ((read (reserve s need) 0 = read s 0 ∧ need ≤ read (reserve s need) 9) ∨
      (read (reserve s need) 0 = 4 ∧ read (reserve s need) 15 = 9)) := by
  have effect := prepared_effect valid phase need
  rw [reserve_eq valid phase]
  by_cases short : read (prepared s need) 9 < need
  · simp only [short, ite_true]
    refine ⟨Heap.fail_valid effect.heap 9, ?_, ?_, Or.inr ?_⟩
    · intro h reached k bound nonmark
      rw [Heap.fail_field effect.heap.1.1 (reachable_allocated valid.1 reached).1 bound,
        effect.payload h reached k bound nonmark]
    · intro h
      exact (Heap.fail_reachable effect.heap.1 9).trans (effect.reachable h)
    · rw [fail_read effect.heap.1.1, fail_read effect.heap.1.1]
      simp
  · simp only [short, ite_false]
    refine ⟨effect.heap, effect.payload, effect.reachable, Or.inl ⟨effect_phase effect, ?_⟩⟩
    simp only [UInt64.le_iff_toNat_le]
    rw [UInt64.lt_iff_toNat_lt] at short
    omega

theorem reserve_error_unchanged (s : Array UInt64) (need : UInt64) (error : read s 0 = 4) :
    reserve s need = s := by
  simp only [reserve, stressCollection, spaceCollection, error, bne_self_eq_false,
    Bool.false_and, Bool.false_eq_true, ite_false, BEq.rfl, ite_true]

theorem reserve_register {s : Array UInt64} {cap : Nat} {r : UInt64}
    (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4) (need : UInt64) (bound : r.toNat < 24)
    (h0 : r ≠ 0) (h15 : r ≠ 15) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10)
    (h11 : r ≠ 11) (h18 : r ≠ 18) : read (reserve s need) r = read s r := by
  have effect := prepared_effect valid phase need
  rw [reserve_eq valid phase]
  split
  · rw [fail_read effect.heap.1.1]
    simp only [h0, h15, ite_false]
    exact effect.registers r bound h8 h9 h10 h11 h18
  · exact effect.registers r bound h8 h9 h10 h11 h18

end Project.Smalltalk.Reservation
