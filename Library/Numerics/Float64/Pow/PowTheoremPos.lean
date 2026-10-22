import Library.Numerics.Float64.Pow.PowPositive

/-!
The accuracy theorem of `Pow.pow` for a positive finite `x` and a finite `y`:
`F64SignedRounding.WithinSteps 1 (value x ^ value y) (pow x y)`, with `Real.rpow` on the values.
-/

namespace Library.Numerics.Float64.Pow.PowTheoremPos
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- A positive finite word as `(2 ^ 52 + f) 2 ^ (E - 1075)`. -/
theorem positive_rep (x : Float) (hxf : Finite x.toBits) (hx : 0 < value x.toBits) :
    ∃ (E : Int) (f : Nat), -51 ≤ E ∧ E ≤ 2046 ∧ f < 2 ^ 52 ∧
      value x.toBits = ((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075) ∧
      (x.toBits = 0x3FF0000000000000 ↔ (E = 1023 ∧ f = 0)) := by
  have hs := PowExpPaths.sign_of_pos _ hx
  have hT : x.toBits.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hf2047 : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  by_cases he : 1 ≤ Wasm.IEEE64.exponent x.toBits
  · set E := Wasm.IEEE64.exponent x.toBits
    set f := Wasm.IEEE64.fraction x.toBits
    have hf : f < 2 ^ 52 := Nat.mod_lt _ (by positivity)
    have hix : x.toBits.toNat = E * 2 ^ 52 + f := by
      simp only [E, f, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
      simp only [Nat.reducePow] at hT ⊢
      omega
    obtain ⟨-, hv⟩ := PowLogFinal.z_value x.toBits E f he (by omega) hf hix
    refine ⟨E, f, by omega, by omega, hf, hv, ?_⟩
    constructor
    · intro h
      rw [h] at hix
      simp only [Nat.reducePow] at hix hf
      change 4607182418800017408 = _ at hix
      omega
    · rintro ⟨h1, h2⟩
      apply UInt64.toNat_inj.mp
      rw [hix]
      simp only [Nat.reducePow] at h1 h2 ⊢
      change _ = 4607182418800017408
      omega
  · have he0 : Wasm.IEEE64.exponent x.toBits = 0 := by omega
    have hs52 : x.toBits.toNat < 2 ^ 52 := by
      have : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 = 0 := he0
      simp only [Nat.reducePow] at hT this ⊢
      omega
    have h0 : 0 < x.toBits.toNat := by
      by_contra hn
      have : x.toBits = 0 := UInt64.toNat_inj.mp (by simp; omega)
      rw [this, F64Magnitude.value_zero] at hx
      exact lt_irrefl _ hx
    obtain ⟨E, f, hE1, hE2, hf, -, hv⟩ := PowSubnormal.subnormal_word x hs52 h0
    refine ⟨E, f, hE1, by omega, hf, hv, ?_⟩
    constructor
    · intro h
      rw [h] at hs52
      simp at hs52
    · rintro ⟨h1, -⟩
      omega

theorem sign_top (w : UInt64) : (w >>> 52 < 0x800) ↔ Wasm.IEEE64.sign w = false := by
  simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_shiftRight]
  change w.toNat >>> 52 < 2048 ↔ _
  rw [Nat.shiftRight_eq_div_pow]
  have := w.toNat_lt
  simp only [Nat.reducePow] at this ⊢
  omega

theorem prod_big (a b : ℝ) (ha : 1 / 2 ^ 53 ≤ a) (hb : 2 ^ 63 ≤ b) : 1024 ≤ a * b := by
  have h := mul_le_mul ha hb (by positivity) (by linarith)
  have h2 : (1 : ℝ) / 2 ^ 53 * 2 ^ 63 = 1024 := by norm_num
  linarith

theorem pow_pos_within (x y : Float) (hxf : Finite x.toBits) (hx : 0 < value x.toBits)
    (hyf : Finite y.toBits) :
    F64SignedRounding.WithinSteps 1 (value x.toBits ^ value y.toBits) (Pow.pow x y).toBits := by
  obtain ⟨E, f, hE1, hE2, hf, hXv, hone⟩ := positive_rep x hxf hx
  have hs := PowExpPaths.sign_of_pos _ hx
  have hT : x.toBits.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hxexp : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hyexp : Wasm.IEEE64.exponent y.toBits < 2047 := by
    have h := hyf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent y.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hx0 : x.toBits ≠ 0 := by
    intro h
    rw [h, F64Magnitude.value_zero] at hx
    exact lt_irrefl _ hx
  set X := value x.toBits
  set Y := value y.toBits
  have honef : Finite (0x3FF0000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
  -- `x = 1`
  have hX1 : x.toBits = 0x3FF0000000000000 → X = 1 := by
    intro h
    simp only [X, h]
    exact PowPositive.one_word_value
  have hlogb : x.toBits ≠ 0x3FF0000000000000 →
      1 / 2 ^ 53 ≤ |Real.log X| ∧ |Real.log X| ≤ 745 := by
    intro h
    rw [hXv]
    exact PowMainPath.log_bounds E f hE1 hE2 hf (fun h' => h (hone.mpr h'))
  have hpow : X ^ Y = Real.exp (Real.log X * Y) := Real.rpow_def_of_pos hx Y
  by_cases hy0 : 2 * y.toBits = 0
  · rw [PowPositive.y_zero x y hxexp hy0]
    have hYv : Y = 0 := by
      have hy : y.toBits = 0 ∨ y.toBits = 0x8000000000000000 := by
        have := congrArg UInt64.toNat hy0
        simp only [UInt64.toNat_mul, UInt64.reduceToNat] at this
        have hlt := y.toBits.toNat_lt
        simp only [Nat.reducePow] at this hlt
        rcases (show y.toBits.toNat = 0 ∨ y.toBits.toNat = 9223372036854775808 by omega) with
          h | h
        · exact Or.inl (UInt64.toNat_inj.mp (by rw [h]; rfl))
        · exact Or.inr (UInt64.toNat_inj.mp (by rw [h]; rfl))
      have hm : Wasm.IEEE64.scaledMagnitude y.toBits = 0 := by
        rcases hy with h | h <;> (rw [h]; decide)
      have hs0 : Wasm.IEEE64.scaledValue y.toBits = 0 := by
        have h1 := natAbs_scaledValue y.toBits
        rw [hm] at h1
        exact Int.natAbs_eq_zero.mp h1
      show value y.toBits = 0
      rw [value, hs0]
      simp
    rw [hYv, Real.rpow_zero]
    exact PowPositive.exact_within _ honef 1 PowPositive.one_word_value (by norm_num)
  rcases (show Wasm.IEEE64.exponent y.toBits < 958 ∨ 1086 ≤ Wasm.IEEE64.exponent y.toBits ∨
      (958 ≤ Wasm.IEEE64.exponent y.toBits ∧ Wasm.IEEE64.exponent y.toBits < 1086) by omega)
    with hey | hey | ⟨hey1, hey2⟩
  · -- `|y| < 2 ^ -65`
    have hw := Library.Numerics.Float64.Exp.ExpBranches.exponent_word_spec y.toBits
    simp only [Library.Numerics.Float64.Exp.ExpBranches.exponentWord] at hw
    have hc : ((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be := by
      have hs : (((y.toBits >>> 52) &&& 0x7ff) - 0x3be).toNat =
          (2 ^ 64 - 958 + Wasm.IEEE64.exponent y.toBits) % 2 ^ 64 := by
        rw [UInt64.toNat_sub, hw]
        rfl
      apply UInt64.le_iff_toNat_le.mpr
      rw [hs]
      change 128 ≤ _
      simp only [Nat.reducePow]
      omega
    have hlt : ((y.toBits >>> 52) &&& 0x7ff) < 0x3be := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [hw]
      exact hey
    rw [Pow.pow, PowBranches.positive_special _ _ x y hT hx0 hxexp hyexp hy0 (Or.inr hc),
      ite_eq_left hc]
    have hYb : |Y| ≤ 1 / 2 ^ 65 := by
      have := F64Magnitude.magnitude_lt y.toBits 958 (-65) (by norm_num) (by norm_num) hey
      have h65 : (2 : ℝ) ^ (-65 : Int) = 1 / 2 ^ 65 := by norm_num
      rw [h65] at this
      exact this.le
    by_cases hx1 : x.toBits = 0x3FF0000000000000
    · rw [ite_eq_left (by simp [hx1])]
      rw [hX1 hx1, Real.one_rpow]
      exact PowPositive.exact_within _ honef 1 PowPositive.one_word_value (by norm_num)
    · rw [ite_eq_right (by simp [hx1]), ite_eq_left (by simpa using hlt)]
      obtain ⟨-, hlog⟩ := hlogb hx1
      have ht : |Real.log X * Y| ≤ 1 / 2 ^ 55 := by
        rw [abs_mul]
        calc
          _ ≤ 745 * (1 / 2 ^ 65) := mul_le_mul hlog hYb (abs_nonneg _) (by norm_num)
          _ ≤ 1 / 2 ^ 55 := by norm_num
      obtain ⟨hp, hm⟩ := PowPositive.near_one_within y.toBits hyf (hYb.trans (by norm_num)) _ ht
      rw [hpow]
      by_cases hgt : x.toBits > 0x3FF0000000000000
      · rw [ite_eq_left hgt, F64Bits.toBits_add, Library.Numerics.Float64.Exp.ExpSpecialNegative.one_bits]
        exact hp
      · rw [ite_eq_right hgt, F64Bits.toBits_sub, Library.Numerics.Float64.Exp.ExpSpecialNegative.one_bits]
        exact hm
  · -- `|y| ≥ 2 ^ 63`
    have hw := Library.Numerics.Float64.Exp.ExpBranches.exponent_word_spec y.toBits
    simp only [Library.Numerics.Float64.Exp.ExpBranches.exponentWord] at hw
    have hc : ((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [UInt64.toNat_sub_of_le ((y.toBits >>> 52) &&& 0x7ff) 0x3be
        (UInt64.le_iff_toNat_le.mpr (by rw [hw]; change 958 ≤ _; omega)), hw]
      simp only [UInt64.reduceSub, UInt64.reduceToNat]
      omega
    have hnlt : ¬ ((y.toBits >>> 52) &&& 0x7ff) < 0x3be := by
      intro h
      have := UInt64.lt_iff_toNat_lt.mp h
      rw [hw] at this
      change _ < 958 at this
      omega
    rw [Pow.pow, PowBranches.positive_special _ _ x y hT hx0 hxexp hyexp hy0 (Or.inr hc),
      ite_eq_left hc]
    have hYb : 2 ^ 63 ≤ |Y| := by
      have := F64Magnitude.magnitude_ge y.toBits 1086 63 (by norm_num) (by norm_num) (by norm_num)
        hey
      simpa using this
    by_cases hx1 : x.toBits = 0x3FF0000000000000
    · rw [ite_eq_left (by simp [hx1])]
      rw [hX1 hx1, Real.one_rpow]
      exact PowPositive.exact_within _ honef 1 PowPositive.one_word_value (by norm_num)
    rw [ite_eq_right (by simp [hx1]), ite_eq_right (by simpa using hnlt)]
    obtain ⟨hlog, -⟩ := hlogb hx1
    rw [hpow]
    have hmag : 0 < Wasm.IEEE64.scaledMagnitude y.toBits := by
      simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq,
        show Wasm.IEEE64.exponent y.toBits ≠ 0 by omega, ite_false]
      positivity
    have hsy := F64Magnitude.sign_value y.toBits hmag
    have hgtX : x.toBits > 0x3FF0000000000000 ↔ 1 < X := by
      constructor
      · intro h
        have := F64PositiveOrder.value_strict hT (UInt64.lt_iff_toNat_lt.mp h)
        rwa [PowPositive.one_word_value] at this
      · intro h
        by_contra hn
        have hle : x.toBits.toNat ≤ (0x3FF0000000000000 : UInt64).toNat :=
          not_lt.mp (fun h' => hn (UInt64.lt_iff_toNat_lt.mpr h'))
        have := (F64PositiveOrder.value_le_iff hT (by decide)).mpr hle
        rw [PowPositive.one_word_value] at this
        linarith
    have hlogpos : 1 < X → 1 / 2 ^ 53 ≤ Real.log X := by
      intro h
      have := Real.log_pos h
      rwa [abs_of_pos this] at hlog
    have hlogneg : X ≤ 1 → Real.log X ≤ -(1 / 2 ^ 53) := by
      intro h
      have := Real.log_nonpos hx.le h
      rw [abs_of_nonpos this] at hlog
      linarith
    have hover : ∀ a : ℝ, 1024 ≤ a → F64SignedRounding.WithinSteps 1 (Real.exp a)
        (Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000).toBits := by
      intro a ha
      rw [PowExpBranches.overflow_bits]
      exact Library.Numerics.Float64.Exp2.Exp2Theorem.overflow_within _ (PowExpPaths.exp_overflow a (by linarith))
    have hunder : ∀ a : ℝ, a ≤ -1024 → F64SignedRounding.WithinSteps 1 (Real.exp a)
        (Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000).toBits := by
      intro a ha
      rw [PowExpBranches.underflow_bits]
      exact Library.Numerics.Float64.Exp2.Exp2Theorem.zero_within _ (Real.exp_pos _)
        ((PowExpPaths.exp_tiny a (by linarith)).trans (by norm_num))
    by_cases hypos : Wasm.IEEE64.sign y.toBits = false
    · have hy' : 0 < Y := by
        by_contra hn
        push Not at hn
        rcases hn.lt_or_eq with h | h
        · exact absurd (hsy.mpr h) (by rw [hypos]; decide)
        · have : Y ≠ 0 := by
            intro h0
            rw [h0, abs_zero] at hYb
            linarith [show (0 : ℝ) < 2 ^ 63 by positivity]
          exact this h
      rw [abs_of_pos hy'] at hYb
      have htop : y.toBits >>> 52 < 0x800 := (sign_top _).mpr hypos
      by_cases hgt : x.toBits > 0x3FF0000000000000
      · rw [ite_eq_left hgt, ite_eq_left htop]
        apply hover
        exact prod_big _ _ (hlogpos (hgtX.mp hgt)) hYb
      · rw [ite_eq_right hgt, ite_eq_left htop]
        apply hunder
        have h1 := hlogneg (not_lt.mp (fun h => hgt (hgtX.mpr h)))
        have h2 := prod_big _ _ (show 1 / 2 ^ 53 ≤ -Real.log X by linarith) hYb
        linarith
    · have hyneg : Wasm.IEEE64.sign y.toBits = true := by
        cases h : Wasm.IEEE64.sign y.toBits
        · exact absurd h hypos
        · rfl
      have hy' : Y < 0 := hsy.mp hyneg
      rw [abs_of_neg hy'] at hYb
      have htop : ¬ y.toBits >>> 52 < 0x800 := fun h => hypos ((sign_top _).mp h)
      by_cases hgt : x.toBits > 0x3FF0000000000000
      · rw [ite_eq_left hgt, ite_eq_right htop]
        apply hunder
        have h2 := prod_big _ _ (hlogpos (hgtX.mp hgt)) hYb
        linarith
      · rw [ite_eq_right hgt, ite_eq_right htop]
        apply hover
        have h1 := hlogneg (not_lt.mp (fun h => hgt (hgtX.mpr h)))
        have h2 := prod_big _ _ (show 1 / 2 ^ 53 ≤ -Real.log X by linarith) hYb
        linarith
  · -- `2 ^ -65 ≤ |y| < 2 ^ 63`
    have hY1 : 1 / 2 ^ 65 ≤ |Y| := by
      have := F64Magnitude.magnitude_ge y.toBits 958 (-65) (by norm_num) (by norm_num)
        (by norm_num) hey1
      have h65 : (2 : ℝ) ^ (-65 : Int) = 1 / 2 ^ 65 := by norm_num
      rwa [h65] at this
    have hY2 : |Y| < 2 ^ 63 := by
      have := F64Magnitude.magnitude_lt y.toBits 1086 63 (by norm_num) (by norm_num) hey2
      simpa using this
    by_cases hxe : 1 ≤ Wasm.IEEE64.exponent x.toBits
    · rw [Pow.pow, PowBranches.main_selected _ _ x y hT hxe (by omega) hey1 hey2]
      by_cases hx1 : x.toBits = 0x3FF0000000000000
      · rw [hx1, PowPositive.main_one y hyexp (by omega), hX1 hx1, Real.one_rpow]
        exact PowPositive.exact_within _ honef 1 PowPositive.one_word_value (by norm_num)
      · have hix : (x.toBits.toNat : Int) =
            ((Wasm.IEEE64.exponent x.toBits : Int) * 4503599627370496 +
              Wasm.IEEE64.fraction x.toBits) % 18446744073709551616 := by
          simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
          simp only [Nat.reducePow] at hT ⊢
          omega
        have hrep : X = ((2 ^ 52 + Wasm.IEEE64.fraction x.toBits : Nat) : ℝ) *
            (2 : ℝ) ^ ((Wasm.IEEE64.exponent x.toBits : Int) - 1075) :=
          (PowLogFinal.z_value x.toBits _ _ hxe (by omega) (Nat.mod_lt _ (by positivity))
            (by simp only [Wasm.IEEE64.exponent]
                simp only [Nat.reducePow] at hT ⊢
                omega)).2
        have hne : ¬ ((Wasm.IEEE64.exponent x.toBits : Int) = 1023 ∧
            Wasm.IEEE64.fraction x.toBits = 0) := by
          rintro ⟨h1, h2⟩
          apply hx1
          apply UInt64.toNat_inj.mp
          have h1' : Wasm.IEEE64.exponent x.toBits = 1023 := by exact_mod_cast h1
          simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at h1' h2
          simp only [Nat.reducePow] at hT h1' h2 ⊢
          change _ = 4607182418800017408
          omega
        rw [hrep]
        exact PowMainPath.main_general x.toBits _ _ (by omega) (by omega)
          (Nat.mod_lt _ (by norm_num)) hix hne y hyf hY1 hY2
    · -- subnormal `x`
      have he0 : Wasm.IEEE64.exponent x.toBits = 0 := by omega
      have hs52 : x.toBits.toNat < 2 ^ 52 := by
        have : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 = 0 := he0
        simp only [Nat.reducePow] at hT this ⊢
        omega
      have h0 : 0 < x.toBits.toNat := by
        by_contra hn
        exact hx0 (UInt64.toNat_inj.mp (by simp; omega))
      have hcx : (x.toBits >>> 52) - 1 ≥ (0x7ff : UInt64) - 1 := by
        have ht := PowBranches.top_word x.toBits hT
        rw [he0] at ht
        have h0' : x.toBits >>> 52 = 0 := UInt64.toNat_inj.mp (by rw [ht]; rfl)
        rw [h0']
        decide
      have hyr := PowBranches.y_guard y.toBits hey1 hey2
      have htop0 : (x.toBits >>> 52 == 0) = true := by
        have ht := PowBranches.top_word x.toBits hT
        rw [he0] at ht
        simp only [beq_iff_eq]
        exact UInt64.toNat_inj.mp (by rw [ht]; rfl)
      rw [Pow.pow, PowBranches.positive_special _ _ x y hT hx0 hxexp hyexp hy0 (Or.inl hcx),
        ite_eq_right hyr, ite_eq_left htop0]
      obtain ⟨E', f', hE1', hE2', hf', hix', hv'⟩ := PowSubnormal.subnormal_word x hs52 h0
      have hne : ¬ (E' = 1023 ∧ f' = 0) := by omega
      rw [show X = ((2 ^ 52 + f' : Nat) : ℝ) * (2 : ℝ) ^ (E' - 1075) from hv']
      exact PowMainPath.main_general _ E' f' hE1' (by omega) (by simpa using hf')
        (by simpa using hix') hne y hyf hY1 hY2

#print axioms positive_rep
#print axioms sign_top
#print axioms prod_big
#print axioms pow_pos_within

end Library.Numerics.Float64.Pow.PowTheoremPos
