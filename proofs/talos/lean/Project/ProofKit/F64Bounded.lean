import Project.ProofKit.F64StrictOrder

namespace Project.ProofKit.F64Order
open CodeLib.IEEE64

theorem absBits_le_iff (a bound : UInt64) (hb : Finite bound) :
    absBits a ≤ absBits bound ↔ Finite a ∧ |value a| ≤ |value bound| := by
  constructor
  · intro h
    refine ⟨(finiteBits_iff _).mp ?_, abs_value_mono _ _ h⟩
    have hh := (finiteBits_iff bound).mpr hb
    simp only [finiteBits, decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at hh ⊢
    have ha := UInt64.le_iff_toNat_le.mp h
    omega
  · rintro ⟨_, h⟩
    by_contra hn
    have hh : absBits bound < absBits a := by
      rw [UInt64.lt_iff_toNat_lt]
      rw [UInt64.le_iff_toNat_le] at hn
      omega
    exact (not_lt_of_ge h) (abs_value_lt _ _ hh)

#print axioms absBits_le_iff
end Project.ProofKit.F64Order
