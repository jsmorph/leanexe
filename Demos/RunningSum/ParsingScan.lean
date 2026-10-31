import Demos.RunningSum.Spec

namespace Demos.RunningSum

def parseScanStep (line : Array UInt64) (start i : UInt64)
    (state : UInt64 × Bool) : UInt64 × Bool :=
  if i < start then state
  else
    let byte := (line)[i.toNat]!
    let valid := state.2 && byte ≥ 48 && byte ≤ 57
    let first := if i == state.1 && byte == 48 then state.1 + 1 else state.1
    (first, valid)

def parseScan (line : Array UInt64) (start stop : UInt64) : UInt64 × Bool :=
  LeanExe.loop stop (start, true) (parseScanStep line start)

structure ScanInvariant (line : Array UInt64) (start cursor : Nat)
    (state : UInt64 × Bool) : Prop where
  start_le : start ≤ state.1.toNat
  first_le : state.1.toNat ≤ max start cursor
  zero_before : ∀ i, start ≤ i → i < state.1.toNat → (line)[i]! = 48
  nonzero : state.1.toNat < cursor → (line)[state.1.toNat]! ≠ 48
  valid_iff : state.2 = true ↔ ∀ i, start ≤ i → i < cursor →
    48 ≤ (line)[i]!.toNat ∧ (line)[i]!.toNat ≤ 57

theorem scanInvariant_step (line : Array UInt64) (start stop : UInt64)
    (k : Nat) (hk : k < stop.toNat)
    (state : UInt64 × Bool) (h : ScanInvariant line start.toNat k state) :
    ScanInvariant line start.toNat (k + 1)
      (parseScanStep line start (UInt64.ofNat k) state) := by
  have kNat : (UInt64.ofNat k).toNat = k :=
    UInt64.toNat_ofNat_of_lt' (lt_trans hk (UInt64.toNat_lt stop))
  by_cases before : k < start.toNat
  · have beforeWord : UInt64.ofNat k < start := by
      simpa only [UInt64.lt_iff_toNat_lt, kNat] using before
    rw [parseScanStep, ite_eq_left beforeWord]
    refine ⟨h.start_le, ?_, h.zero_before, ?_, ?_⟩
    · have := h.first_le
      omega
    · have := h.start_le
      omega
    · rw [h.valid_iff]
      constructor <;> intro _ i hi hj <;> omega
  · have active : ¬ UInt64.ofNat k < start := by
      simpa only [UInt64.lt_iff_toNat_lt, kNat] using before
    have first_le : state.1.toNat ≤ k := by
      have := h.first_le
      omega
    have nextValid :
        (state.2 && decide ((line)[k]! ≥ 48) && decide ((line)[k]! ≤ 57)) = true ↔
        ∀ i, start.toNat ≤ i → i < k + 1 →
          48 ≤ (line)[i]!.toNat ∧ (line)[i]!.toNat ≤ 57 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
        UInt64.reduceToNat, h.valid_iff]
      constructor
      · rintro ⟨⟨previous, lower⟩, upper⟩ i hi hj
        by_cases equal : i = k
        · simpa [equal] using And.intro lower upper
        · exact previous i hi (by omega)
      · intro all
        exact ⟨⟨fun i hi hj => all i hi (by omega), (all k (by omega) (by omega)).1⟩,
          (all k (by omega) (by omega)).2⟩
    rw [parseScanStep, ite_eq_right active]
    simp only [kNat]
    by_cases advance : UInt64.ofNat k == state.1 && (line)[k]! == 48
    · have pair : UInt64.ofNat k = state.1 ∧ (line)[k]! = 48 := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using advance
      have firstEq : state.1.toNat = k := by rw [← pair.1, kNat]
      have plusNat : (state.1 + 1).toNat = k + 1 := by
        rw [UInt64.toNat_add, firstEq]
        have := UInt64.toNat_lt stop
        simp only [UInt64.reduceToNat]
        omega
      simp only [advance, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_, nextValid⟩
      · simpa [plusNat] using (show start.toNat ≤ k + 1 by omega)
      · simp [plusNat]
      · intro i hi hj
        rw [plusNat] at hj
        by_cases previous : i < k
        · exact h.zero_before i hi (by omega)
        · have equal : i = k := by omega
          simpa [equal] using pair.2
      · simp [plusNat]
    · simp only [advance, Bool.false_eq_true, ↓reduceIte]
      refine ⟨h.start_le, ?_, h.zero_before, ?_, nextValid⟩
      · change state.1.toNat ≤ max start.toNat (k + 1)
        omega
      ·
        intro hj
        by_cases previous : state.1.toNat < k
        · exact h.nonzero previous
        · have equal : state.1.toNat = k := by omega
          intro zero
          apply advance
          simp [← equal, zero]

theorem parseScan_invariant (line : Array UInt64) (start stop : UInt64) :
    ScanInvariant line start.toNat stop.toNat (parseScan line start stop) := by
  apply LeanExe.Dialect.loop_induction
    (P := fun k state => ScanInvariant line start.toNat k state)
  · refine ⟨le_rfl, by simp, ?_, by simp, ?_⟩
    · intro i hi hj
      change i < start.toNat at hj
      omega
    · simp
  · intro k state hk h
    exact scanInvariant_step line start stop k hk state h

end Demos.RunningSum
