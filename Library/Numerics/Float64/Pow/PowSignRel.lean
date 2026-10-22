import Library.Numerics.Float64.Pow.PowNegate
import LeanExe.ProofKit.F64Bits

/-!
Negation through the operations of `Pow.powExp`.  `Rel x y` states that the word `x` is the
negation of `y`, that both are zeros, or that both are NaNs.  Sums, differences, and products with
one operand related keep the relation on all words, as do `Float` negation and `Float.ofBits` of a
negated word.  Related floats have the same absolute value and the same test against zero, and
opposite tests for being negative when they are neither zeros nor NaNs.
-/

namespace Library.Numerics.Float64.Pow.PowSignRel
open CodeLib.IEEE64 LeanExe.ProofKit PowNegate

set_option exponentiation.threshold 4096

/-- `x` is the negation of `y`, except that both may be zeros of any sign or NaNs. -/
def Rel (x y : UInt64) : Prop :=
  NegRel x y ∨ (Wasm.IEEE64.isNaN x = true ∧ Wasm.IEEE64.isNaN y = true)

theorem negate_rel (w : UInt64) : Rel (Wasm.IEEE64.negate w) w := Or.inl (Or.inl rfl)

theorem zero_rel (x y : UInt64) (hx : x.toNat % 2 ^ 63 = 0) (hy : y.toNat % 2 ^ 63 = 0) :
    Rel x y := Or.inl (Or.inr ⟨hx, hy⟩)

theorem nan_rel (x y : UInt64) (hx : Wasm.IEEE64.isNaN x = true)
    (hy : Wasm.IEEE64.isNaN y = true) : Rel x y := Or.inr ⟨hx, hy⟩

theorem canonical_nan : Wasm.IEEE64.isNaN Wasm.IEEE64.canonicalNaN = true := by decide

theorem zero_fields (w : UInt64) (h : w.toNat % 2 ^ 63 = 0) :
    Wasm.IEEE64.exponent w = 0 ∧ Wasm.IEEE64.fraction w = 0 := by
  have hT := w.toNat_lt
  constructor
  · show w.toNat / 2 ^ 52 % 2 ^ 11 = 0
    simp only [Nat.reducePow] at h hT ⊢
    omega
  · show w.toNat % 2 ^ 52 = 0
    simp only [Nat.reducePow] at h hT ⊢
    omega

theorem mag_zero (w : UInt64) :
    Wasm.IEEE64.scaledMagnitude w = 0 ↔ w.toNat % 2 ^ 63 = 0 := by
  have hT := w.toNat_lt
  unfold Wasm.IEEE64.scaledMagnitude Wasm.IEEE64.exponent Wasm.IEEE64.fraction
  simp only [beq_iff_eq]
  split_ifs with he
  · simp only [Nat.reducePow] at he hT ⊢
    omega
  · constructor
    · intro h
      exfalso
      have : 0 < (2 ^ 52 + w.toNat % 2 ^ 52) * 2 ^ (w.toNat / 2 ^ 52 % 2 ^ 11 - 1) := by
        positivity
      omega
    · intro h
      exfalso
      simp only [Nat.reducePow] at he hT h
      omega

theorem zero_not_nan (w : UInt64) (h : w.toNat % 2 ^ 63 = 0) :
    Wasm.IEEE64.isNaN w = false ∧ Wasm.IEEE64.isInfinite w = false := by
  obtain ⟨he, -⟩ := zero_fields w h
  simp [Wasm.IEEE64.isNaN, Wasm.IEEE64.isInfinite, he]

theorem nan_not_inf (w : UInt64) (h : Wasm.IEEE64.isNaN w = true) :
    Wasm.IEEE64.isInfinite w = false := by
  unfold Wasm.IEEE64.isNaN at h
  unfold Wasm.IEEE64.isInfinite
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  simp [h.2]

theorem inf_negate (w : UInt64) :
    Wasm.IEEE64.isInfinite (Wasm.IEEE64.negate w) = Wasm.IEEE64.isInfinite w := by
  obtain ⟨he, hf, -⟩ := F64Sign.fields_negate w
  simp only [Wasm.IEEE64.isInfinite, he, hf]

theorem mag_negate (w : UInt64) :
    Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate w) = Wasm.IEEE64.scaledMagnitude w := by
  obtain ⟨he, hf, -⟩ := F64Sign.fields_negate w
  simp only [Wasm.IEEE64.scaledMagnitude, he, hf]

theorem abs_negate (w : UInt64) :
    Wasm.IEEE64.abs (Wasm.IEEE64.negate w) = Wasm.IEEE64.abs w := by
  obtain ⟨he, hf, -⟩ := F64Sign.fields_negate w
  simp only [Wasm.IEEE64.abs, he, hf]

theorem nan_iff (x y : UInt64) (h : Rel x y) : Wasm.IEEE64.isNaN x = Wasm.IEEE64.isNaN y := by
  rcases h with (rfl | ⟨hx, hy⟩) | ⟨hx, hy⟩
  · exact F64Sign.isNaN_negate y
  · rw [(zero_not_nan x hx).1, (zero_not_nan y hy).1]
  · rw [hx, hy]

theorem inf_iff (x y : UInt64) (h : Rel x y) :
    Wasm.IEEE64.isInfinite x = Wasm.IEEE64.isInfinite y := by
  rcases h with (rfl | ⟨hx, hy⟩) | ⟨hx, hy⟩
  · exact inf_negate y
  · rw [(zero_not_nan x hx).2, (zero_not_nan y hy).2]
  · rw [nan_not_inf x hx, nan_not_inf y hy]

theorem mag_iff (x y : UInt64) (h : NegRel x y) :
    Wasm.IEEE64.scaledMagnitude x = Wasm.IEEE64.scaledMagnitude y := by
  rcases h with rfl | ⟨hx, hy⟩
  · exact mag_negate y
  · rw [(mag_zero x).mpr hx, (mag_zero y).mpr hy]

theorem negrel_of (x y : UInt64) (h : Rel x y) (hn : Wasm.IEEE64.isNaN y = false) :
    NegRel x y := by
  rcases h with h | ⟨-, hy⟩
  · exact h
  · rw [hy] at hn
    exact absurd hn (by decide)

theorem eq_negate (x y : UInt64) (h : Rel x y) (hn : Wasm.IEEE64.isNaN y = false)
    (hm : Wasm.IEEE64.scaledMagnitude y ≠ 0) : x = Wasm.IEEE64.negate y := by
  rcases negrel_of x y h hn with h | ⟨-, hy⟩
  · exact h
  · exact absurd ((mag_zero y).mpr hy) hm

theorem inf_mag (w : UInt64) (h : Wasm.IEEE64.isInfinite w = true) :
    Wasm.IEEE64.scaledMagnitude w ≠ 0 := by
  intro h0
  rw [(zero_not_nan w ((mag_zero w).mp h0)).2] at h
  exact absurd h (by decide)

theorem finite_of (w : UInt64) (hn : Wasm.IEEE64.isNaN w = false)
    (hi : ¬ Wasm.IEEE64.isInfinite w = true) : Finite w := by
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq]
  intro he
  apply hi
  unfold Wasm.IEEE64.isNaN at hn
  unfold Wasm.IEEE64.isInfinite
  rw [he] at hn ⊢
  by_cases hf : Wasm.IEEE64.fraction w = 0
  · simp [hf]
  · simp [hf] at hn

theorem negate_negate (w : UInt64) : Wasm.IEEE64.negate (Wasm.IEEE64.negate w) = w := by
  apply UInt64.toNat_inj.mp
  rw [F64SignedRounding.negate_toNat, (F64Sign.fields_negate w).2.2,
    F64SignedRounding.negate_toNat]
  have hT := w.toNat_lt
  cases hs : Wasm.IEEE64.sign w
  · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    omega
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    simp only [Wasm.IEEE64.sign, decide_eq_true_eq] at hs
    omega

theorem rel_symm (x y : UInt64) (h : Rel x y) : Rel y x := by
  rcases h with (rfl | ⟨hx, hy⟩) | ⟨hx, hy⟩
  · exact Or.inl (Or.inl (negate_negate y).symm)
  · exact zero_rel y x hy hx
  · exact nan_rel y x hy hx

theorem rel_negate (x y : UInt64) (h : Rel x y) :
    Rel (Wasm.IEEE64.negate x) (Wasm.IEEE64.negate y) := by
  rcases h with (rfl | ⟨hx, hy⟩) | ⟨hx, hy⟩
  · exact negate_rel _
  · exact zero_rel _ _ (by rw [F64SignedRounding.negate_magnitude]; exact hx)
      (by rw [F64SignedRounding.negate_magnitude]; exact hy)
  · exact nan_rel _ _ (by rw [F64Sign.isNaN_negate]; exact hx)
      (by rw [F64Sign.isNaN_negate]; exact hy)

theorem signMask_zero (b : Bool) : (Wasm.IEEE64.signMask b).toNat % 2 ^ 63 = 0 := by
  cases b <;> decide

/-- Sums of related words are related. -/
theorem add_total (a b a' b' : UInt64) (ha : Rel a' a) (hb : Rel b' b) :
    Rel (Wasm.IEEE64.add a' b') (Wasm.IEEE64.add a b) := by
  have hna := nan_iff _ _ ha
  have hnb := nan_iff _ _ hb
  have hia := inf_iff _ _ ha
  have hib := inf_iff _ _ hb
  by_cases hn : (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b) = true
  · have hn' : (Wasm.IEEE64.isNaN a' || Wasm.IEEE64.isNaN b') = true := by
      rw [hna, hnb]
      exact hn
    unfold Wasm.IEEE64.add
    rw [ite_eq_left hn, ite_eq_left hn']
    exact nan_rel _ _ canonical_nan canonical_nan
  have hn' : ¬ (Wasm.IEEE64.isNaN a' || Wasm.IEEE64.isNaN b') = true := by
    rw [hna, hnb]
    exact hn
  have hn0 : Wasm.IEEE64.isNaN a = false ∧ Wasm.IEEE64.isNaN b = false := by
    simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true] using hn
  obtain ⟨hna0, hnb0⟩ := hn0
  by_cases hfa : Wasm.IEEE64.isInfinite a = true
  · have ha' := eq_negate _ _ ha hna0 (inf_mag a hfa)
    have hfa' : Wasm.IEEE64.isInfinite a' = true := by
      rw [hia]
      exact hfa
    unfold Wasm.IEEE64.add
    rw [ite_eq_right hn, ite_eq_right hn', ite_eq_left hfa, ite_eq_left hfa']
    by_cases hfb : Wasm.IEEE64.isInfinite b = true
    · have hb' := eq_negate _ _ hb hnb0 (inf_mag b hfb)
      have hc : (Wasm.IEEE64.isInfinite b' && Wasm.IEEE64.sign a' != Wasm.IEEE64.sign b') =
          (Wasm.IEEE64.isInfinite b && Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
        rw [hib, ha', hb', (F64Sign.fields_negate a).2.2, (F64Sign.fields_negate b).2.2]
        cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl
      rw [hc]
      split_ifs
      · exact nan_rel _ _ canonical_nan canonical_nan
      · exact ha
    · have hfb' : ¬ Wasm.IEEE64.isInfinite b' = true := by
        rw [hib]
        exact hfb
      simp only [Bool.not_eq_true] at hfb hfb'
      simp only [hfb, hfb', Bool.false_and, Bool.false_eq_true, ite_false]
      exact ha
  · have hfa' : ¬ Wasm.IEEE64.isInfinite a' = true := by
      rw [hia]
      exact hfa
    by_cases hfb : Wasm.IEEE64.isInfinite b = true
    · have hfb' : Wasm.IEEE64.isInfinite b' = true := by
        rw [hib]
        exact hfb
      unfold Wasm.IEEE64.add
      rw [ite_eq_right hn, ite_eq_right hn', ite_eq_right hfa, ite_eq_right hfa',
        ite_eq_left hfb, ite_eq_left hfb']
      exact hb
    · have hfb' : ¬ Wasm.IEEE64.isInfinite b' = true := by
        rw [hib]
        exact hfb
      left
      exact add_rel a b a' b' (finite_of a hna0 hfa) (finite_of b hnb0 hfb)
        (finite_of a' (hna.trans hna0) hfa') (finite_of b' (hnb.trans hnb0) hfb')
        (negrel_sv a' a (negrel_of _ _ ha hna0)) (negrel_sv b' b (negrel_of _ _ hb hnb0))

/-- A product whose first operand is replaced by a related word is related. -/
theorem mul_left (a a' b : UInt64) (ha : Rel a' a) :
    Rel (Wasm.IEEE64.mul a' b) (Wasm.IEEE64.mul a b) := by
  have hna := nan_iff _ _ ha
  by_cases hn : (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b) = true
  · have hn' : (Wasm.IEEE64.isNaN a' || Wasm.IEEE64.isNaN b) = true := by
      rw [hna]
      exact hn
    unfold Wasm.IEEE64.mul
    rw [ite_eq_left hn, ite_eq_left hn']
    exact nan_rel _ _ canonical_nan canonical_nan
  have hn' : ¬ (Wasm.IEEE64.isNaN a' || Wasm.IEEE64.isNaN b) = true := by
    rw [hna]
    exact hn
  have hna0 : Wasm.IEEE64.isNaN a = false := by
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
    exact hn.1
  have hm := mag_iff _ _ (negrel_of _ _ ha hna0)
  have hia := inf_iff _ _ ha
  unfold Wasm.IEEE64.mul
  rw [ite_eq_right hn, ite_eq_right hn']
  simp only [hm, hia]
  by_cases hz : Wasm.IEEE64.scaledMagnitude a = 0
  · have hia0 : Wasm.IEEE64.isInfinite a = false := (zero_not_nan a ((mag_zero a).mp hz)).2
    simp only [hz, hia0, beq_self_eq_true, Bool.true_or, ite_true, Bool.false_eq_true,
      ite_false]
    split_ifs
    · exact nan_rel _ _ canonical_nan canonical_nan
    · exact zero_rel _ _ (signMask_zero _) (signMask_zero _)
  · have hs : Wasm.IEEE64.sign a' = !Wasm.IEEE64.sign a := by
      rw [eq_negate _ _ ha hna0 hz]
      exact (F64Sign.fields_negate a).2.2
    have hc : ((!Wasm.IEEE64.sign a) != Wasm.IEEE64.sign b) =
        !(Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
      cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl
    rw [hs, hc]
    generalize (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) = ng
    rw [infinity_not, signMask_not, roundDyadic_not]
    split_ifs <;> first
      | exact nan_rel _ _ canonical_nan canonical_nan
      | exact negate_rel _

/-- A product whose second operand is replaced by a related word is related. -/
theorem mul_right (a b b' : UInt64) (hb : Rel b' b) :
    Rel (Wasm.IEEE64.mul a b') (Wasm.IEEE64.mul a b) := by
  have hnb := nan_iff _ _ hb
  by_cases hn : (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b) = true
  · have hn' : (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b') = true := by
      rw [hnb]
      exact hn
    unfold Wasm.IEEE64.mul
    rw [ite_eq_left hn, ite_eq_left hn']
    exact nan_rel _ _ canonical_nan canonical_nan
  have hn' : ¬ (Wasm.IEEE64.isNaN a || Wasm.IEEE64.isNaN b') = true := by
    rw [hnb]
    exact hn
  have hnb0 : Wasm.IEEE64.isNaN b = false := by
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
    exact hn.2
  have hm := mag_iff _ _ (negrel_of _ _ hb hnb0)
  have hib := inf_iff _ _ hb
  unfold Wasm.IEEE64.mul
  rw [ite_eq_right hn, ite_eq_right hn']
  simp only [hm, hib]
  by_cases hz : Wasm.IEEE64.scaledMagnitude b = 0
  · have hib0 : Wasm.IEEE64.isInfinite b = false := (zero_not_nan b ((mag_zero b).mp hz)).2
    simp only [hz, hib0, beq_self_eq_true, Bool.or_true, ite_true, Bool.false_eq_true,
      ite_false]
    split_ifs
    · exact nan_rel _ _ canonical_nan canonical_nan
    · exact zero_rel _ _ (signMask_zero _) (signMask_zero _)
  · have hs : Wasm.IEEE64.sign b' = !Wasm.IEEE64.sign b := by
      rw [eq_negate _ _ hb hnb0 hz]
      exact (F64Sign.fields_negate b).2.2
    have hc : (Wasm.IEEE64.sign a != !Wasm.IEEE64.sign b) =
        !(Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
      cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl
    rw [hs, hc]
    generalize (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) = ng
    rw [infinity_not, signMask_not, roundDyadic_not]
    split_ifs <;> first
      | exact nan_rel _ _ canonical_nan canonical_nan
      | exact negate_rel _

theorem fadd {a b a' b' : Float} (ha : Rel a'.toBits a.toBits) (hb : Rel b'.toBits b.toBits) :
    Rel (a' + b').toBits (a + b).toBits := by
  rw [F64Bits.toBits_add, F64Bits.toBits_add]
  exact add_total _ _ _ _ ha hb

theorem fsub {a b a' b' : Float} (ha : Rel a'.toBits a.toBits) (hb : Rel b'.toBits b.toBits) :
    Rel (a' - b').toBits (a - b).toBits := by
  rw [F64Bits.toBits_sub, F64Bits.toBits_sub]
  exact add_total _ _ _ _ ha (rel_negate _ _ hb)

theorem fmul_left {a a' : Float} (b : Float) (ha : Rel a'.toBits a.toBits) :
    Rel (a' * b).toBits (a * b).toBits := by
  rw [F64Bits.toBits_mul, F64Bits.toBits_mul]
  exact mul_left _ _ _ ha

theorem fmul_right (a : Float) {b b' : Float} (hb : Rel b'.toBits b.toBits) :
    Rel (a * b').toBits (a * b).toBits := by
  rw [F64Bits.toBits_mul, F64Bits.toBits_mul]
  exact mul_right _ _ _ hb

theorem fneg (a : Float) : Rel (-a).toBits a.toBits := by
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero]
  split_ifs with h
  · exact nan_rel _ _ canonical_nan h
  · exact negate_rel _

theorem fofBits (w : UInt64) :
    Rel (Float.ofBits (Wasm.IEEE64.negate w)).toBits (Float.ofBits w).toBits := by
  rw [F64Bits.toBits_ofBits, F64Bits.toBits_ofBits, F64Sign.isNaN_negate]
  split_ifs
  · exact nan_rel _ _ canonical_nan canonical_nan
  · exact negate_rel _

theorem fabs {a a' : Float} (h : Rel a'.toBits a.toBits) : a'.abs = a.abs := by
  have hb : a'.abs.toBits = a.abs.toBits := by
    rw [F64Bits.toBits_abs, F64Bits.toBits_abs]
    rcases h with (h1 | ⟨h1, h2⟩) | ⟨h1, h2⟩
    · rw [h1, abs_negate]
    · obtain ⟨e1, f1⟩ := zero_fields _ h1
      obtain ⟨e2, f2⟩ := zero_fields _ h2
      simp only [Wasm.IEEE64.abs, e1, f1, e2, f2]
    · have c1 := F64Bits.toBits_canonical a'
      have c2 := F64Bits.toBits_canonical a
      rw [ite_eq_left h1] at c1
      rw [ite_eq_left h2] at c2
      rw [← c1, ← c2]
  rw [← F64Bits.ofBits_toBits a'.abs, hb, F64Bits.ofBits_toBits]

theorem zero_word : (0.0 : Float).toBits = 0 := rfl

theorem sv_zero : Wasm.IEEE64.scaledValue 0 = 0 := by decide

theorem fbeq_zero {a a' : Float} (h : Rel a'.toBits a.toBits) : (a' == 0.0) = (a == 0.0) := by
  rw [F64Bits.beq_eq, F64Bits.beq_eq, zero_word]
  unfold Wasm.IEEE64.eq
  rw [nan_iff _ _ h]
  by_cases hn : Wasm.IEEE64.isNaN a.toBits = true
  · simp [hn]
  · have hn' : Wasm.IEEE64.isNaN a.toBits = false := by simpa using hn
    rw [negrel_sv _ _ (negrel_of _ _ h hn')]
    simp only [hn', show Wasm.IEEE64.isNaN 0 = false by decide, Bool.or_false,
      Bool.false_eq_true, ite_false, sv_zero]
    by_cases hs : Wasm.IEEE64.scaledValue a.toBits = 0
    · simp [hs]
    · have : -Wasm.IEEE64.scaledValue a.toBits ≠ 0 := by omega
      simp [hs, this]

theorem flt_zero {a a' : Float} (h : Rel a'.toBits a.toBits)
    (hn : Wasm.IEEE64.isNaN a.toBits = false) (hz : Wasm.IEEE64.scaledMagnitude a.toBits ≠ 0) :
    a' < 0.0 ↔ ¬ a < 0.0 := by
  rw [F64Bits.lt_iff, F64Bits.lt_iff, zero_word]
  unfold Wasm.IEEE64.lt
  rw [nan_iff _ _ h, negrel_sv _ _ (negrel_of _ _ h hn)]
  simp only [hn, show Wasm.IEEE64.isNaN 0 = false by decide, Bool.or_false, Bool.false_eq_true,
    ite_false, sv_zero, decide_eq_true_eq]
  have hs : Wasm.IEEE64.scaledValue a.toBits ≠ 0 := by
    intro h0
    apply hz
    rw [← natAbs_scaledValue, h0]
    rfl
  constructor <;> intro <;> omega

/-- The sign `one` of the compensated sum of `Pow.powSpecialCase`. -/
theorem one_rel {Y Y' : Float} (h : Rel Y'.toBits Y.toBits)
    (hn : Wasm.IEEE64.isNaN Y.toBits = false) (hz : Wasm.IEEE64.scaledMagnitude Y.toBits ≠ 0) :
    Rel (if Y' < 0.0 then -1.0 else 1.0 : Float).toBits
      (if Y < 0.0 then -1.0 else 1.0 : Float).toBits := by
  have hl := flt_zero h hn hz
  by_cases hy : Y < 0.0
  · rw [ite_eq_left hy, ite_eq_right (fun h' => hl.mp h' hy)]
    exact rel_symm _ _ (fneg 1.0)
  · rw [ite_eq_right hy, ite_eq_left (hl.mpr hy)]
    exact fneg 1.0

/-- A NaN lies beyond the infinities in magnitude. -/
theorem not_within_nan (w : UInt64) (hn : Wasm.IEEE64.isNaN w = true) :
    ¬ w.toNat % 2 ^ 63 ≤ 0x7FF0000000000000 := by
  have hT := w.toNat_lt
  unfold Wasm.IEEE64.isNaN at hn
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hn
  obtain ⟨he, hf⟩ := hn
  have he' : w.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := he
  have hf' : ¬ w.toNat % 2 ^ 52 = 0 := hf
  simp only [Nat.reducePow] at hT he' hf' ⊢
  omega

/-- A word related to one within `n` steps of `E` lies within `n` steps of `-E`. -/
theorem within_rel (n : Nat) (E : ℝ) (x y : UInt64) (h : Rel x y)
    (hw : F64SignedRounding.WithinSteps n E y) : F64SignedRounding.WithinSteps n (-E) x := by
  rcases h with h | ⟨-, hy⟩
  · exact within_negrel n E x y h hw
  · exact absurd hw.1 (not_within_nan y hy)

#print axioms negate_negate
#print axioms rel_symm
#print axioms add_total
#print axioms mul_left
#print axioms mul_right
#print axioms fadd
#print axioms fsub
#print axioms fmul_left
#print axioms fmul_right
#print axioms fneg
#print axioms fofBits
#print axioms fabs
#print axioms fbeq_zero
#print axioms flt_zero
#print axioms one_rel
#print axioms within_rel

end Library.Numerics.Float64.Pow.PowSignRel
