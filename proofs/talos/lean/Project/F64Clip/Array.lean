import Project.F64Clip.Bounds

namespace Project.F64Clip
open CodeLib.IEEE64 Project.ProofKit.F64Order

theorem accepted_iff (count : Nat) (bound : UInt64) (weights : Array UInt64) :
    accepted count bound weights = true ↔
      weights.size = count ∧ (Finite bound ∧ 0 ≤ value bound ∧ value bound ≤ 10) ∧
      ∀ (i : Nat) (hi : i < weights.size), Finite weights[i] := by
  simp only [accepted, Bool.and_eq_true, decide_eq_true_eq, validBound_iff,
    Array.all_eq_true, finiteBits_iff, and_assoc]

theorem prepare_rejected (count : Nat) (bound : UInt64) (weights : Array UInt64)
    (h : accepted count bound weights = false) : prepare count bound weights = #[] := by
  simp [prepare, h]

theorem prepare_success (count : Nat) (bound : UInt64) (weights : Array UInt64)
    (h : accepted count bound weights = true) :
    prepare count bound weights = weights.map (clip bound) := by
  simp [prepare, h]

theorem prepare_size (count : Nat) (bound : UInt64) (weights : Array UInt64)
    (h : accepted count bound weights = true) :
    (prepare count bound weights).size = count := by
  rw [prepare_success count bound weights h, Array.size_map]
  exact ((accepted_iff count bound weights).mp h).1

theorem prepare_getElem (count : Nat) (bound : UInt64) (weights : Array UInt64)
    (h : accepted count bound weights = true) (i : Nat) (hi : i < weights.size) :
    (prepare count bound weights)[i]! = clip bound weights[i]! := by
  rw [prepare_success count bound weights h]
  simp [hi]

theorem prepare_element (count : Nat) (bound : UInt64) (weights : Array UInt64)
    (h : accepted count bound weights = true) (i : Nat) (hi : i < weights.size) :
    Finite (prepare count bound weights)[i]! ∧
      |value (prepare count bound weights)[i]!| ≤ value bound ∧
      value (prepare count bound weights)[i]! =
        max (-value bound) (min (value bound) (value weights[i]!)) := by
  have hv := (accepted_iff count bound weights).mp h
  have hf : Finite weights[i]! := by simpa [hi] using hv.2.2 i hi
  rw [prepare_getElem count bound weights h i hi]
  have hc := clip_bounded bound weights[i]! hv.2.1.1 hv.2.1.2.1 hf
  exact ⟨hc.1, hc.2, clip_value bound weights[i]! hv.2.1.1 hv.2.1.2.1 hf⟩

theorem reject_nonfinite (count : Nat) (bound : UInt64) (weights : Array UInt64)
    (i : Nat) (hi : i < weights.size) (hf : ¬Finite weights[i]) :
    prepare count bound weights = #[] := by
  apply prepare_rejected
  apply Bool.eq_false_iff.mpr
  intro h
  exact hf (((accepted_iff count bound weights).mp h).2.2 i hi)

theorem prepare_idempotent (count : Nat) (bound : UInt64) (weights : Array UInt64)
    (h : accepted count bound weights = true) :
    prepare count bound (prepare count bound weights) = prepare count bound weights := by
  have hv := (accepted_iff count bound weights).mp h
  have hs := prepare_size count bound weights h
  have hf : ∀ (i : Nat) (hi : i < (prepare count bound weights).size),
      Finite (prepare count bound weights)[i] := by
    intro i hi
    have hiw : i < weights.size := by rw [hs] at hi; rw [hv.1]; exact hi
    simpa [hi] using (prepare_element count bound weights h i hiw).1
  have ha := (accepted_iff count bound (prepare count bound weights)).mpr ⟨hs, hv.2.1, hf⟩
  rw [prepare_success count bound (prepare count bound weights) ha]
  apply Array.ext
  · exact Array.size_map
  · intro i hi hj
    have hiw : i < weights.size := by simpa [hs, hv.1] using hj
    have hm := (prepare_element count bound weights h i hiw).2.1
    have hp := clip_preserves bound (prepare count bound weights)[i]! hv.2.1.1 hv.2.1.2.1
      (by simpa [hj] using hf i hj) hm
    simpa [hj] using hp

#print axioms accepted_iff
#print axioms prepare_element
#print axioms reject_nonfinite
#print axioms prepare_idempotent
end Project.F64Clip
