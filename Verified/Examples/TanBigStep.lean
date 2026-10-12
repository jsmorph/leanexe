import Verified.Examples.TanBigWords
import Verified.Examples.TanBigClose

/-!
The path of `Tan.kernelTan` from `0x3FE59428` on: the result lies within one step of `tan ρ`
for even quadrants and of `-1/tan ρ` for odd quadrants when `x + y` approximates `ρ` within
`|ρ| / 2 ^ 59` and `0.6743 ≤ |x| ≤ 0.7854`.  With `b = π/4 - |ρ|`, the target is
`± T_v (tan b)`.  From `|x'| = 0.05` on, `T_v (tan b)` lies in `[1/2, 1)` for `v = 1` and in
`(-2, -1]` for `v = -1`, and the error stays below one spacing; below, the error stays below
`0.74 u |T_v (tan b)|`.
-/

namespace Verified.Examples.TanBigStep

open CodeLib.IEEE64 LeanExe.ProofKit TanWords TanOdd TanEven TanStep TanBigWords TanBigClose
  TrigKernelWords

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

theorem bigW_eq (x y : UInt64) (odd : Bool) (x' r w ww den q e1 f g h v s : UInt64)
    (hx' : bigArg x y = x') (hr : corrW x' 0 = r) (hw : Wasm.IEEE64.add x' r = w)
    (hww : Wasm.IEEE64.mul w w = ww) (hv : (if odd then negOne else one) = v)
    (hden : Wasm.IEEE64.add w v = den) (hq : Wasm.IEEE64.div ww den = q)
    (he1 : Wasm.IEEE64.sub q r = e1) (hf : Wasm.IEEE64.sub x' e1 = f)
    (hg : Wasm.IEEE64.mul two f = g) (hh : Wasm.IEEE64.sub v g = h)
    (hs : (if x >>> 32 >>> 31 == 1 then negOne else one) = s) :
    bigW x y odd = Wasm.IEEE64.mul s h := by
  subst hx' hr hw hww hv hden hq he1 hf hg hh hs
  simp only [bigW]

/-- The sign word keeps the nearest property, negated. -/
theorem signed_near (s h : UInt64) (τ σ : ℝ) (hs : (s = one ∧ σ = 1) ∨ (s = negOne ∧ σ = -1))
    (hhf : Finite h) (hτ : |τ| ≤ 2) (hnear : ∀ u : UInt64, |value h - τ| ≤ |value u - τ|) :
    Finite (Wasm.IEEE64.mul s h) ∧
      ∀ u : UInt64, Finite u → |value (Wasm.IEEE64.mul s h) - σ * τ| ≤ |value u - σ * τ| := by
  obtain ⟨hof, hnf, -, -, -, -⟩ := finite_words
  have hh0 := hnear 0
  rw [value_zero, zero_sub, abs_neg] at hh0
  have hhb : |value h| < 2 ^ 3 := by
    have := abs_sub_abs_le_abs_sub (value h) τ
    have : (2 : ℝ) ^ 3 = 8 := by norm_num
    linarith
  have he := exp_upper h 3 hhb
  have hsf : Finite s := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  have hsm : Wasm.IEEE64.scaledMagnitude s = 1 * 2 ^ 1074 := by
    rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact mag_one
    · exact mag_negOne
  have hsv : value s = σ := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact value_one
    · exact value_negOne
  obtain ⟨hmf, hmv⟩ := pow_mul s h 1074 hsf hhf hsm le_rfl (by omega)
  refine ⟨hmf, fun u hu => ?_⟩
  rw [hmv, hsv]
  rcases hs with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simpa using hnear u
  · obtain ⟨-, hnuv⟩ := F64Magnitude.negate_value u hu
    have := hnear (Wasm.IEEE64.negate u)
    rw [hnuv] at this
    calc |-1 * value h - -1 * τ| = |value h - τ| := by
          rw [show -1 * value h - -1 * τ = -(value h - τ) by ring, abs_neg]
      _ ≤ |-value u - τ| := this
      _ = |value u - -1 * τ| := by
          rw [show -value u - τ = -(value u - -1 * τ) by ring, abs_neg]

/-- One step from the error bounds of either region. -/
theorem final_step (c : UInt64) (v σ τ Tb X' : ℝ) (hv : v = 1 ∨ v = -1) (hσ : σ = 1 ∨ σ = -1)
    (hcf : Finite c) (hnear : ∀ u : UInt64, Finite u → |value c - σ * τ| ≤ |value u - σ * τ|)
    (hhi : 5 / 100 ≤ X' → |τ - Tb| < 95 / 100 * 𝐮 ∧
      (v = 1 → 79 / 100 ≤ Tb ∧ Tb ≤ 91 / 100) ∧ (v = -1 → -127 / 100 ≤ Tb ∧ Tb ≤ -109 / 100))
    (hlo : X' < 5 / 100 → |τ - Tb| ≤ 45 / 100 * 𝐮 ∧ 9 / 10 ≤ |Tb| ∧ |Tb| ≤ 2) :
    F64SignedRounding.WithinSteps 1 (σ * Tb) c := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hσa : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hd : |σ * τ - σ * Tb| = |τ - Tb| := by rw [← mul_sub, abs_mul, hσa, one_mul]
  have hT : |σ * Tb| = |Tb| := by rw [abs_mul, hσa, one_mul]
  have ht : |σ * τ| = |τ| := by rw [abs_mul, hσa, one_mul]
  have hs : σ * τ * (σ * Tb) = τ * Tb := by
    have : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    calc σ * τ * (σ * Tb) = σ * σ * (τ * Tb) := by ring
      _ = τ * Tb := by rw [this, one_mul]
  rcases le_or_gt (5 / 100) X' with hX | hX
  · obtain ⟨hdτ, h1, h2⟩ := hhi hX
    have hdτ' := abs_lt.mp hdτ
    rw [hu] at hdτ' hdτ
    rcases hv with rfl | rfl
    · obtain ⟨hT1, hT2⟩ := h1 rfl
      have hTp : 0 < Tb := by linarith
      have hτp : 0 < τ := by linarith
      refine near_bin c (σ * τ) (σ * Tb) 1022 (by norm_num) (by norm_num) hcf hnear ?_ ?_ ?_ ?_
      · rw [hT, B_1022, abs_of_pos hTp]
        constructor <;> linarith
      · rw [ht, B_1022, abs_of_pos hτp]
        constructor <;> linarith
      · rw [hs]
        exact mul_pos hτp hTp
      · rw [hd, S_1022]
        linarith
    · obtain ⟨hT1, hT2⟩ := h2 rfl
      have hTn : Tb < 0 := by linarith
      have hτn : τ < 0 := by linarith
      refine near_bin c (σ * τ) (σ * Tb) 1023 (by norm_num) (by norm_num) hcf hnear ?_ ?_ ?_ ?_
      · rw [hT, B_1023, abs_of_neg hTn]
        constructor <;> linarith
      · rw [ht, B_1023, abs_of_neg hτn]
        constructor <;> linarith
      · rw [hs]
        exact mul_pos_of_neg_of_neg hτn hTn
      · rw [hd, S_1023]
        have : (95 / 100 : ℝ) * (1 / 2 ^ 53) < 1 / 2 ^ 52 := by norm_num
        linarith
  · obtain ⟨hdτ, h1, h2⟩ := hlo hX
    refine near_rel c (σ * τ) (σ * Tb) hcf hnear ?_ ?_ ?_
    · rw [hT]
      have : (1 : ℝ) / 2 ^ 1000 ≤ 9 / 10 := by norm_num
      linarith
    · rw [hT]
      have : (2 : ℝ) ≤ 2 ^ 1000 := by norm_num
      linarith
    · rw [hd, hT]
      have : 45 / 100 * 𝐮 ≤ 74 / 100 * 𝐮 * (9 / 10) := by rw [hu]; norm_num
      have : 74 / 100 * 𝐮 * (9 / 10) ≤ 74 / 100 * 𝐮 * |Tb| :=
        mul_le_mul_of_nonneg_left h1 (by rw [hu]; positivity)
      linarith

/-- The ranges of `T_v (tan b)` from `b = 0.0499` on. -/
theorem hi_range (v b : ℝ) (hb0 : 499 / 10000 ≤ b) (hb1 : b ≤ 1114 / 10000) :
    (v = 1 → 79 / 100 ≤ Tv v (Real.tan b) ∧ Tv v (Real.tan b) ≤ 91 / 100) ∧
      (v = -1 → -127 / 100 ≤ Tv v (Real.tan b) ∧ Tv v (Real.tan b) ≤ -109 / 100) := by
  have hl := (tan_bounds b (by linarith) (by linarith)).1
  have hu := tan_small b (by rw [abs_of_pos (by linarith)]; linarith)
  rw [abs_of_pos (by linarith : (0 : ℝ) < b)] at hu
  rw [abs_of_pos (by linarith : (0 : ℝ) < Real.tan b)] at hu
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · subst hv
    rw [Tv_one _ (ne_of_gt (by linarith))]
    constructor
    · rw [le_div_iff₀ (by linarith)]; linarith
    · rw [div_le_iff₀ (by linarith)]; linarith
  · subst hv
    rw [Tv_negOne _ (ne_of_lt (by linarith)),
      show Real.tan b - 1 = -(1 - Real.tan b) by ring, div_neg]
    have hq1 : 109 / 100 ≤ (1 + Real.tan b) / (1 - Real.tan b) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hq2 : (1 + Real.tan b) / (1 - Real.tan b) ≤ 127 / 100 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    constructor <;> linarith

/-- The argument `x'` against `π/4 - |ρ|`. -/
theorem arg_real (a P A ρ X X' : ℝ) (hX0 : 6743 / 10000 ≤ X) (hX1 : X ≤ 78541 / 100000)
    (hA : X * (1 - 1 / 2 ^ 52) ≤ A ∧ A ≤ X * (1 + 1 / 2 ^ 52))
    (ha : |a - (P - A)| ≤ 𝐮 * |P - A| + 1 / 2 ^ 100) (hP : |P - Real.pi / 4| ≤ 1 / 2 ^ 68)
    (hAρ : |(A - |ρ|)| ≤ |ρ| / 2 ^ 59) (hX' : |a| = X') :
    X' ≤ 1112 / 10000 ∧ -1 / 2 ^ 16 ≤ a ∧
      |a - (Real.pi / 4 - |ρ|)| ≤ 1001 / 1000 * 𝐮 * X' + 1 / 2 ^ 59 ∧ |ρ| ≤ 7856 / 10000 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  norm_num at hp1 hp2
  obtain ⟨hA0, hA1⟩ := hA
  have hP' := abs_le.mp hP
  have hAρ' := abs_le.mp hAρ
  have hρ : |ρ| ≤ 7856 / 10000 := by linarith
  have hPA : |P - A| ≤ 1111 / 10000 := by
    rw [abs_le]
    constructor <;> linarith
  have hPA' : -13 / 1000000 ≤ P - A := by linarith
  rw [hu] at ha ⊢
  have ha' := abs_le.mp ha
  have hPAa := abs_sub_abs_le_abs_sub (P - A) a
  rw [abs_sub_comm (P - A) a, hX'] at hPAa
  have hPA0 := abs_nonneg (P - A)
  refine ⟨?_, ?_, ?_, hρ⟩
  · have := abs_sub_abs_le_abs_sub a (P - A)
    rw [hX'] at this
    linarith
  · linarith
  · have hid : a - (Real.pi / 4 - |ρ|) = (a - (P - A)) + (P - Real.pi / 4) - (A - |ρ|) := by
      ring
    rw [hid]
    have t1 := sub_abs ((a - (P - A)) + (P - Real.pi / 4)) (A - |ρ|)
    have t2 := abs_add_le (a - (P - A)) (P - Real.pi / 4)
    linarith

/-- The target of the kernel in terms of `b = π/4 - |ρ|`. -/
theorem target_eq (ρ b σ : ℝ) (odd : Bool) (hb : |b| ≤ 12 / 100) (hσ : σ = 1 ∨ σ = -1)
    (hρ : ρ = σ * (Real.pi / 4 - b)) :
    (if odd then -1 / Real.tan ρ else Real.tan ρ) =
      σ * Tv (if odd then -1 else 1) (Real.tan b) := by
  obtain ⟨h1, h2⟩ := tan_quarter b hb
  subst hρ
  rcases hσ with rfl | rfl <;> cases odd
  · simp only [↓reduceIte, Bool.false_eq_true, one_mul, h1]
  · simp only [↓reduceIte, one_mul, h2]
  · simp only [↓reduceIte, Bool.false_eq_true, neg_one_mul, Real.tan_neg, h1]
  · simp only [↓reduceIte, neg_one_mul, Real.tan_neg, div_neg, h2]

/-- The kernel from `0x3FE59428` on. -/
theorem big_within (x y : UInt64) (odd : Bool) (ρ X : ℝ) (hxf : Finite x) (hyf : Finite y)
    (hX : |value x| = X) (hX0 : 6743 / 10000 ≤ X) (hX1 : X ≤ 78541 / 100000)
    (hy : |value y| ≤ X / 2 ^ 52) (har : |value x + value y - ρ| ≤ |ρ| / 2 ^ 59) :
    F64SignedRounding.WithinSteps 1 (if odd then -1 / Real.tan ρ else Real.tan ρ)
      (bigW x y odd) := by
  obtain ⟨hx'f, hx'e⟩ := arg_spec x y X hxf hyf hX hX0 hX1 hy
  obtain ⟨x', hx'⟩ : ∃ x', bigArg x y = x' := ⟨_, rfl⟩
  rw [hx'] at hx'f hx'e
  have hA : X * (1 - 1 / 2 ^ 52) ≤ |value x + value y| ∧
      |value x + value y| ≤ X * (1 + 1 / 2 ^ 52) := by
    have h1 := abs_add_le (value x) (value y)
    have h2 := abs_sub_abs_le_abs_sub (value x) (-value y)
    rw [sub_neg_eq_add, abs_neg] at h2
    constructor <;> linarith
  have hAρ : |(|value x + value y| - |ρ|)| ≤ |ρ| / 2 ^ 59 :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans har
  obtain ⟨hX'1, ha0, hab, hρ1⟩ := arg_real (value x') _ _ ρ X |value x'| hX0 hX1 hA hx'e
    pi_close hAρ rfl
  obtain ⟨v, hv, hvdef, hvv⟩ : ∃ v : UInt64, (v = one ∨ v = negOne) ∧
      (if odd then negOne else one) = v ∧ value v = (if odd then -1 else 1) := by
    cases odd
    · exact ⟨one, Or.inl rfl, rfl, by simp [value_one]⟩
    · exact ⟨negOne, Or.inr rfl, rfl, by simp [value_negOne]⟩
  obtain ⟨r, hr⟩ : ∃ r, corrW x' 0 = r := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, Wasm.IEEE64.add x' r = w := ⟨_, rfl⟩
  obtain ⟨ww, hww⟩ : ∃ ww, Wasm.IEEE64.mul w w = ww := ⟨_, rfl⟩
  obtain ⟨den, hden⟩ : ∃ den, Wasm.IEEE64.add w v = den := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, Wasm.IEEE64.div ww den = q := ⟨_, rfl⟩
  obtain ⟨e1, he1⟩ : ∃ e1, Wasm.IEEE64.sub q r = e1 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, Wasm.IEEE64.sub x' e1 = f := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, Wasm.IEEE64.mul two f = g := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, Wasm.IEEE64.sub v g = h := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, (if x >>> 32 >>> 31 == 1 then negOne else one) = s := ⟨_, rfl⟩
  rw [bigW_eq x y odd x' r w ww den q e1 f g h v s hx' hr hw hww hvdef hden hq he1 hf hg hh hs]
  obtain ⟨hE, hhf, hnear, hτ, hv1, -, hτb⟩ := chain_spec x' v r w ww den q e1 f g h |value x'|
    hr hw hww hden hq he1 hf hg hh hx'f rfl (by linarith) hv
  have hv' : value v = 1 ∨ value v = -1 := by
    rcases hv with rfl | rfl
    · exact Or.inl value_one
    · exact Or.inr value_negOne
  -- The sign of `x`, `ρ`, and the word `s`.
  obtain ⟨σ, hσ, hsσ, hρσ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ((s = one ∧ σ = 1) ∨ (s = negOne ∧ σ = -1)) ∧ ρ = σ * |ρ| := by
    rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign x) with hsx | hsx
    · have hs1 : s = negOne := by
        rw [← hs, sign_bit, hsx]
        rfl
      have hxv := sign_true x hsx
      have hρn : ρ < 0 := by
        by_contra hc
        push Not at hc
        have h1 : value x + value y < 0 := by
          rw [hxv, hX]
          have := le_abs_self (value y)
          have : X / 2 ^ 52 < X := div_lt_self (by linarith) (by norm_num)
          linarith
        rw [abs_of_nonneg hc] at har
        have := abs_le.mp har
        have : ρ / 2 ^ 59 ≤ ρ := div_le_self hc (by norm_num)
        linarith
      exact ⟨-1, Or.inr rfl, Or.inr ⟨hs1, rfl⟩, by rw [abs_of_neg hρn]; ring⟩
    · have hs1 : s = one := by
        rw [← hs, sign_bit, hsx]
        rfl
      have hxv := sign_false x hsx
      have hρp : 0 ≤ ρ := by
        by_contra hc
        push Not at hc
        have h1 : 0 < value x + value y := by
          rw [hxv, hX]
          have := neg_abs_le (value y)
          have : X / 2 ^ 52 < X := div_lt_self (by linarith) (by norm_num)
          linarith
        rw [abs_of_neg hc] at har
        have := abs_le.mp har
        have : -ρ / 2 ^ 59 ≤ -ρ := div_le_self (by linarith) (by norm_num)
        linarith
      exact ⟨1, Or.inl rfl, Or.inl ⟨hs1, rfl⟩, by rw [abs_of_nonneg hρp]; ring⟩
  -- The target.
  have hb : |(Real.pi / 4 - |ρ|)| ≤ 12 / 100 := by
    have := abs_sub_abs_le_abs_sub (Real.pi / 4 - |ρ|) (value x')
    rw [abs_sub_comm (Real.pi / 4 - |ρ|) (value x')] at this
    have : 1001 / 1000 * 𝐮 * |value x'| ≤ 1 / 10000 := by
      rw [show 𝐮 = 1 / 2 ^ 53 from rfl]
      have := abs_nonneg (value x')
      linarith
    have : (1 : ℝ) / 2 ^ 59 ≤ 1 / 10000 := by norm_num
    linarith
  have htarget := target_eq ρ (Real.pi / 4 - |ρ|) σ odd hb hσ (by rw [sub_sub_cancel]; exact hρσ)
  rw [htarget, ← hvv]
  obtain ⟨hcf, hcnear⟩ := signed_near s h (value v - value g) σ hsσ hhf hτb hnear
  refine final_step _ (value v) σ (value v - value g) _ |value x'| hv' hσ hcf hcnear
    (fun hX' => ⟨big_close_hi (value v) _ _ (value x') _ |value x'| hv' rfl hX' (by linarith) hE
      hτ hab, ?_⟩)
    (fun hX' => big_close_lo (value v) _ _ (value x') _ |value x'| hv' rfl hX'.le hE hτ hab)
  have hapos : value x' = |value x'| := by
    rw [abs_of_nonneg]
    by_contra hc
    push Not at hc
    rw [abs_of_neg hc] at hX'
    have : (1 : ℝ) / 2 ^ 16 < 5 / 100 := by norm_num
    linarith
  have hab' := abs_le.mp hab
  have : 1001 / 1000 * 𝐮 * |value x'| ≤ 1 / 100000 := by
    rw [show 𝐮 = 1 / 2 ^ 53 from rfl]
    linarith
  have : (1 : ℝ) / 2 ^ 59 ≤ 1 / 100000 := by norm_num
  exact hi_range (value v) _ (by linarith) (by linarith)

#print axioms big_within

end Verified.Examples.TanBigStep
