import LeanExe.ProofKit.F64NearestStep

namespace LeanExe.ProofKit.F64NearestEven
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder F64NearestStep

theorem nearest_adjacent (y : ℝ) (a b : UInt64) (ha : Nearest y a) (hb : Nearest y b) :
    a.toNat ≤ b.toNat + 1 ∧ b.toNat ≤ a.toNat + 1 := by
  have hlim : limit < 2 ^ 63 := by decide
  have directional (a b : UInt64) (ha : Nearest y a) (hb : Nearest y b) :
      a.toNat ≤ b.toNat + 1 := by
    by_contra hn
    let m := UInt64.ofNat (b.toNat + 1)
    have hm : m.toNat = b.toNat + 1 :=
      UInt64.toNat_ofNat_of_lt' (by
        change b.toNat + 1 < 2 ^ 64
        have haf := ha.1
        have hc : limit < 2 ^ 64 := by decide
        omega)
    have hmf : m.toNat < limit := by
      rw [hm]
      have haf := ha.1
      omega
    have hbm : value b < value m := value_strict (hmf.trans hlim) (by rw [hm]; omega)
    have hma : value m < value a := value_strict (ha.1.trans hlim) (by rw [hm]; omega)
    have hl := upper_midpoint _ _ y hbm (hb.2 m hmf)
    have hr := lower_midpoint _ _ y hma (ha.2 m hmf)
    linarith
  exact ⟨directional a b ha hb, directional b a hb ha⟩

theorem nearest_even_unique (y : ℝ) (a b : UInt64)
    (ha : NearestEven y a) (hb : NearestEven y b) : a = b := by
  have hadj := nearest_adjacent y a b ha.1 hb.1
  have hparity : a.toNat % 2 = b.toNat % 2 := le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)
  apply UInt64.toNat_inj.mp
  omega

noncomputable def roundNearestEven (y : ℝ) : UInt64 :=
  Classical.choose (exists_nearest_even y)

theorem roundNearestEven_spec (y : ℝ) : NearestEven y (roundNearestEven y) :=
  Classical.choose_spec (exists_nearest_even y)

theorem roundNearestEven_eq (y : ℝ) (w : UInt64) (hw : NearestEven y w) :
    roundNearestEven y = w :=
  nearest_even_unique y _ w (roundNearestEven_spec y) hw

#print axioms nearest_adjacent
#print axioms nearest_even_unique
#print axioms roundNearestEven_spec
#print axioms roundNearestEven_eq

end LeanExe.ProofKit.F64NearestEven
