import Project.ProofKit.F64Interval
import Project.ProofKit.F64OutwardAccumulation
import Project.ProofKit.F64MinmodSpec

namespace Project.ProofKit.F64Interval
open CodeLib.IEEE64

def Sound (result : Bounds) (x : ℝ) : Prop :=
  result.status = 0 ∧ Finite result.lower ∧ Finite result.upper ∧
    value result.lower ≤ x ∧ x ≤ value result.upper

theorem Sound.lower {a : Bounds} {x : ℝ} (h : Sound a x) :
    F64Outward.Sound false ⟨a.status, a.lower⟩ x :=
  ⟨h.1, h.2.1, h.2.2.2.1⟩

theorem Sound.upper {a : Bounds} {x : ℝ} (h : Sound a x) :
    F64Outward.Sound true ⟨a.status, a.upper⟩ x :=
  ⟨h.1, h.2.2.1, h.2.2.2.2⟩

theorem pack_accepted (lower upper : F64Outward.Checked)
    (h : (pack lower upper).status = 0) : lower.status = 0 ∧ upper.status = 0 := by
  unfold pack at h
  split at h
  · rename_i hc
    simpa using hc
  · simp [rejected] at h

theorem pack_sound (lower upper : F64Outward.Checked) (x : ℝ)
    (hl : F64Outward.Sound false lower x) (hu : F64Outward.Sound true upper x) :
    Sound (pack lower upper) x := by
  simp only [pack, hl.1, hu.1, beq_self_eq_true, Bool.and_self, ite_true]
  exact ⟨rfl, hl.2.1, hu.2.1, hl.2.2, hu.2.2⟩

theorem point_sound (word : UInt64) (h : Finite word) : Sound (point word) (value word) := by
  rw [point, ite_eq_left ((F64Order.finiteBits_iff word).mpr h)]
  exact ⟨rfl, h, h, le_rfl, le_rfl⟩

theorem add_sound (a b : Bounds) (x y : ℝ) (ha : Sound a x) (hb : Sound b y)
    (h : (add a b).status = 0) : Sound (add a b) (x + y) := by
  simp only [add, ha.1, hb.1, beq_self_eq_true, Bool.and_self, ite_true] at h ⊢
  have hp := pack_accepted _ _ h
  exact pack_sound _ _ _
    (F64Outward.add_sound false ⟨a.status, a.lower⟩ ⟨b.status, b.lower⟩ x y
      ha.lower hb.lower hp.1)
    (F64Outward.add_sound true ⟨a.status, a.upper⟩ ⟨b.status, b.upper⟩ x y
      ha.upper hb.upper hp.2)

theorem sub_sound (a b : Bounds) (x y : ℝ) (ha : Sound a x) (hb : Sound b y)
    (h : (sub a b).status = 0) : Sound (sub a b) (x - y) := by
  simp only [sub, ha.1, hb.1, beq_self_eq_true, Bool.and_self, ite_true] at h ⊢
  have hp := pack_accepted _ _ h
  exact pack_sound _ _ _
    (F64Outward.sub_sound false ⟨a.status, a.lower⟩ ⟨b.status, b.upper⟩ x y
      ha.lower hb.upper hp.1)
    (F64Outward.sub_sound true ⟨a.status, a.upper⟩ ⟨b.status, b.lower⟩ x y
      ha.upper hb.lower hp.2)

theorem scale_sound (a : Bounds) (word : UInt64) (x : ℝ) (ha : Sound a x)
    (h : (scale a word).status = 0) : Sound (scale a word) (x * value word) := by
  simp only [scale, ha.1, beq_self_eq_true, ite_true] at h ⊢
  split_ifs at h ⊢ with hs
  · have hp := pack_accepted _ _ h
    have hl := (F64Outward.mul_accepted false a.lower word hp.1).2.2
    have hu := (F64Outward.mul_accepted true a.upper word hp.2).2.2
    have hw := F64Minmod.value_nonnegative word hs
    exact pack_sound _ _ _
      ⟨hl.1, hl.2.1, hl.2.2.trans (mul_le_mul_of_nonneg_right ha.2.2.2.1 hw)⟩
      ⟨hu.1, hu.2.1, (mul_le_mul_of_nonneg_right ha.2.2.2.2 hw).trans hu.2.2⟩
  · have hp := pack_accepted _ _ h
    have hl := (F64Outward.mul_accepted false a.upper word hp.1).2.2
    have hu := (F64Outward.mul_accepted true a.lower word hp.2).2.2
    have hw := F64Minmod.value_nonpositive word hs
    exact pack_sound _ _ _
      ⟨hl.1, hl.2.1, hl.2.2.trans (mul_le_mul_of_nonpos_right ha.2.2.2.2 hw)⟩
      ⟨hu.1, hu.2.1, (mul_le_mul_of_nonpos_right ha.2.2.2.1 hw).trans hu.2.2⟩

theorem divPositive_sound (a : Bounds) (word : UInt64) (x : ℝ) (ha : Sound a x)
    (h : (divPositive a word).status = 0) :
    Sound (divPositive a word) (x / value word) := by
  simp only [divPositive, ha.1, beq_self_eq_true, Bool.true_and] at h ⊢
  split at h
  · rename_i hp
    rw [ite_eq_left hp]
    have hw := (F64Order.positiveBits_spec word hp).2
    have hs := pack_accepted _ _ h
    have hl := (F64Outward.div_accepted false a.lower word hs.1).2.2.2
    have hu := (F64Outward.div_accepted true a.upper word hs.2).2.2.2
    exact pack_sound _ _ _
      ⟨hl.1, hl.2.1, hl.2.2.trans (div_le_div_of_nonneg_right ha.2.2.2.1 hw.le)⟩
      ⟨hu.1, hu.2.1, (div_le_div_of_nonneg_right ha.2.2.2.2 hw.le).trans hu.2.2⟩
  · simp [rejected] at h

#print axioms point_sound
#print axioms add_sound
#print axioms sub_sound
#print axioms scale_sound
#print axioms divPositive_sound
end Project.ProofKit.F64Interval
