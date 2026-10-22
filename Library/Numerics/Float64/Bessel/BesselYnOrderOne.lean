import Library.Numerics.Float64.Bessel.BesselYnSmall
import Library.Numerics.Float64.Tgamma.TgammaTop
import LeanExe.ProofKit.F64ExactProduct
import LeanExe.ProofKit.BesselModulus

/-!
The orders 1 and -1 of `yn`, which return `y1 x` times `1.0` or `-1.0`, and the form of the
decision of 2026-10-12 for results that can overflow.  `YBound r Y B` states that the word `r` is
finite and within `B` of `Y`, or that it is the infinity of the sign of `Y` and `|Y| > 2^1023`.

`y1_bound` states `YBound` for `y1` at every finite `x > 0` with `B = 12 u M₁`.  From `2^-1022` on,
`BesselY1Theorem.y1_accuracy` gives the bound, and `M₁ ≤ 2^1022` (`M1_le`) makes the result
finite.  Below `2^-1022`, `y1` returns `-(tpi ⊘ x)` (`BesselYnSmall.y1_code`), the exact quotient
`s = tpi/x` lies within `0.36 u/x` of `2/(π x)`, and `-Y₁(x)` within `300 x` of it
(`BesselY1Small.tiny_close`).  A quotient below the largest finite double rounds within `u s`
(`Library.Numerics.Float64.Tgamma.TgammaTop.div_top`), one from there to the overflow threshold rounds to that double
(`BesselDivTop.nearest_top`), and one at or above the threshold rounds to positive infinity
(`BesselDivTop.div_top`), where `|Y₁(x)| > 2^1023`.

`one_mul` and `neg_one_mul` state that the products with `1.0` and `-1.0` are exact for a finite
word, from `F64PowerScale.mul_power` for a normal word and `F64ExactProduct.mul_exact_scaled` for a
subnormal one, and `ybound_one` and `ybound_neg_one` carry `YBound` through them.
-/

namespace Library.Numerics.Float64.Bessel.BesselYnOrderOne
open Real CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.Bessel F64Approx BesselPQEval
  BesselOrderN BesselRecur BesselSmallSigns BesselYnSmallReal BesselStepF BesselOrderLoops
  BesselYnSteps BesselY1Tiny BesselYnSmall F64NearestNonnegative

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 4096

/-- The decided form of a result `r` for a target `Y`: finite and within `B` of `Y`, or the
infinity of the sign of `Y` with `|Y| > 2^1023`. -/
def YBound (r : UInt64) (Y B : ℝ) : Prop :=
  (Finite r ∧ |value r - Y| ≤ B) ∨
    (r = Wasm.IEEE64.infinity (decide (Y < 0)) ∧ 2 ^ 1023 < |Y|)

theorem ybound_mono {r : UInt64} {Y B B' : ℝ} (h : YBound r Y B) (hB : B ≤ B') :
    YBound r Y B' := by
  rcases h with ⟨hf, he⟩ | h
  · exact Or.inl ⟨hf, he.trans hB⟩
  · exact Or.inr h

theorem sign_flip {Y : ℝ} (hY : 2 ^ 1023 < |Y|) : (!decide (Y < 0)) = decide (-Y < 0) := by
  have hY0 : Y ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hY
    linarith [show (0 : ℝ) < 2 ^ 1023 by positivity]
  rcases lt_or_gt_of_ne hY0 with h | h
  · rw [decide_eq_true h, decide_eq_false (show ¬ (-Y < 0) by linarith)]
    rfl
  · rw [decide_eq_false (show ¬ (Y < 0) by linarith), decide_eq_true (show -Y < 0 by linarith)]
    rfl

theorem ybound_negate {r : UInt64} {Y B : ℝ} (h : YBound r Y B) :
    YBound (Wasm.IEEE64.negate r) (-Y) B := by
  rcases h with ⟨hf, he⟩ | ⟨hr, hY⟩
  · obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value r hf
    refine Or.inl ⟨hnf, ?_⟩
    rw [hnv, show -value r - -Y = -(value r - Y) by ring, abs_neg]
    exact he
  · refine Or.inr ⟨?_, by rw [abs_neg]; exact hY⟩
    rw [hr, F64NegateOps.negate_infinity, sign_flip hY]

theorem one_word : (0x3FF0000000000000 : UInt64) = Wasm.IEEE64.encodeFinite false 1023 0 := by
  decide

theorem one_finite : Finite (0x3FF0000000000000 : UInt64) := by
  unfold CodeLib.IEEE64.Finite; decide

theorem one_value : value (0x3FF0000000000000 : UInt64) = 1 := by
  rw [← PolyBound.ratOfWord_cast]
  have : PolyBound.ratOfWord 0x3FF0000000000000 = 1 := by decide +kernel
  rw [this]; norm_num

theorem one_mag : Wasm.IEEE64.scaledMagnitude (0x3FF0000000000000 : UInt64) ≠ 0 := by decide

theorem neg_one_word : (0xBFF0000000000000 : UInt64) = Wasm.IEEE64.negate 0x3FF0000000000000 := by
  decide

/-- `1 ⊗ y` is finite with the value of `y` for a finite `y`. -/
theorem one_mul (y : UInt64) (hy : Finite y) :
    Finite (Wasm.IEEE64.mul 0x3FF0000000000000 y) ∧
      value (Wasm.IEEE64.mul 0x3FF0000000000000 y) = value y := by
  by_cases he : 1 ≤ Wasm.IEEE64.exponent y
  · have hlt : Wasm.IEEE64.exponent y < 0x7FF := by
      have : Wasm.IEEE64.exponent y < 2048 := Nat.mod_lt _ (by norm_num)
      unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hy
      simp only [bne_iff_ne, ne_eq] at hy
      omega
    rw [one_word, F64PowerScale.mul_power 1023 y (by norm_num) (by norm_num) hy he (by omega),
      ite_eq_right (by omega),
      show Wasm.IEEE64.exponent y + 1023 - 1023 = Wasm.IEEE64.exponent y from by omega,
      F64Packing.encode_fields]
    exact ⟨hy, rfl⟩
  · have he0 : Wasm.IEEE64.exponent y = 0 := by omega
    have hm1 : Wasm.IEEE64.scaledMagnitude (0x3FF0000000000000 : UInt64) = 1 * 2 ^ 1074 := by
      decide +kernel
    have hmy : Wasm.IEEE64.scaledMagnitude y = Wasm.IEEE64.fraction y * 2 ^ 0 := by
      simp [Wasm.IEEE64.scaledMagnitude, he0]
    have hf : Wasm.IEEE64.fraction y < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
    obtain ⟨hf1, hv, -, -⟩ := F64ExactProduct.mul_exact_scaled _ y one_finite hy 1 _ 1074 0 hm1
      hmy (by omega) (by norm_num) (by norm_num)
    exact ⟨hf1, by rw [hv, one_value, _root_.one_mul]⟩

/-- `-1 ⊗ y` is finite with the value `-y` for a finite `y`. -/
theorem neg_one_mul (y : UInt64) (hy : Finite y) :
    Finite (Wasm.IEEE64.mul 0xBFF0000000000000 y) ∧
      value (Wasm.IEEE64.mul 0xBFF0000000000000 y) = -value y := by
  rw [neg_one_word, F64NegateOps.mul_negate_left _ _ one_finite hy]
  obtain ⟨hf, hv⟩ := one_mul y hy
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value _ hf
  exact ⟨hnf, by rw [hnv, hv]⟩

theorem ybound_one {r : UInt64} {Y B : ℝ} (h : YBound r Y B) :
    YBound (Wasm.IEEE64.mul 0x3FF0000000000000 r) Y B := by
  rcases h with ⟨hf, he⟩ | ⟨hr, hY⟩
  · obtain ⟨hf1, hv⟩ := one_mul r hf
    exact Or.inl ⟨hf1, by rw [hv]; exact he⟩
  · refine Or.inr ⟨?_, hY⟩
    rw [hr, mul_inf_right _ one_finite one_mag]
    have : Wasm.IEEE64.sign (0x3FF0000000000000 : UInt64) = false := by decide
    rw [this]
    generalize decide (Y < 0) = b
    cases b <;> rfl

theorem ybound_neg_one {r : UInt64} {Y B : ℝ} (h : YBound r Y B) :
    YBound (Wasm.IEEE64.mul 0xBFF0000000000000 r) (-Y) B := by
  rcases h with ⟨hf, he⟩ | ⟨hr, hY⟩
  · obtain ⟨hf1, hv⟩ := neg_one_mul r hf
    refine Or.inl ⟨hf1, ?_⟩
    rw [hv, show -value r - -Y = -(value r - Y) by ring, abs_neg]
    exact he
  · refine Or.inr ⟨?_, by rw [abs_neg]; exact hY⟩
    have hf : Finite (0xBFF0000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
    have hm : Wasm.IEEE64.scaledMagnitude (0xBFF0000000000000 : UInt64) ≠ 0 := by decide
    rw [hr, mul_inf_right _ hf hm, ← sign_flip hY]
    have : Wasm.IEEE64.sign (0xBFF0000000000000 : UInt64) = true := by decide
    rw [this]
    generalize decide (Y < 0) = b
    cases b <;> rfl

theorem value_1022 : value (0x0010000000000000 : UInt64) = 1 / 2 ^ 1022 := by
  rw [← PolyBound.ratOfWord_cast]
  have : PolyBound.ratOfWord 0x0010000000000000 = 1 / 2 ^ 1022 := by decide +kernel
  rw [this]; norm_num

/-- `M₁ ≤ 2^1022` from `2^-1022` on. -/
theorem M1_le (w : ℝ) (hw : 1 / 2 ^ 1022 ≤ w) : modn w 1 ≤ 2 ^ 1022 := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  by_cases h2 : 2 ≤ w
  · have h := (BesselModulus.modulus1_large w h2).2
    have hpi := Real.pi_gt_three
    have hc : 2 / (π * w) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h1 : J1 w ^ 2 + Y1 w ^ 2 ≤ 1 := by linarith
    unfold modn
    rw [Jn_one, Yn_one]
    have : √(J1 w ^ 2 + Y1 w ^ 2) ≤ 1 := by
      calc √(J1 w ^ 2 + Y1 w ^ 2) ≤ √1 := Real.sqrt_le_sqrt h1
        _ = 1 := Real.sqrt_one
    have : (1 : ℝ) ≤ 2 ^ 1022 := by norm_num
    linarith
  · push Not at h2
    obtain ⟨hJp, hJ⟩ := J1_le w hw0 h2
    have hYn := Y_neg w hw0 h2.le 1 le_rfl
    have hM : modn w 1 ≤ 1 + -Yn w 1 := by
      unfold modn
      have := sqrt_le_add (Jn 1 w) (Yn w 1)
      rw [abs_of_pos hJp, abs_of_neg hYn] at this
      linarith
    have hY : -Yn w 1 ≤ 2 ^ 1022 - 2 := by
      by_cases ht : w ≤ 1 / 2 ^ 53
      · have hmin : 1 / 2 ^ 1074 ≤ w := le_trans (by norm_num) hw
        obtain ⟨hlabs, -, hl2⟩ := BesselY0Small.log_facts w hmin (by norm_num at ht ⊢; linarith)
        have hcl := BesselY1Small.tiny_close w hw0 ht (by rw [hlabs]; exact hl2)
        rw [← Yn_one] at hcl
        have h1 := (abs_le.mp hcl).1
        have hpi := Real.pi_gt_three
        have h2 : 2 / (π * w) ≤ 3 * 2 ^ 1020 := by
          rw [div_le_iff₀ (by positivity)]
          have : 3 * (2 : ℝ) ^ 1020 * (3 * (1 / 2 ^ 1022)) ≤ 3 * 2 ^ 1020 * (π * w) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hpi.le hw (by positivity) (by positivity)
          have e : 3 * (2 : ℝ) ^ 1020 * (3 * (1 / 2 ^ 1022)) = 9 / 4 := by norm_num
          linarith
        have h3 : 300 * w ≤ 1 := by
          have : (300 : ℝ) * (1 / 2 ^ 53) ≤ 1 := by norm_num
          linarith
        have : 3 * (2 : ℝ) ^ 1020 + 1 ≤ 2 ^ 1022 - 2 := by norm_num
        linarith
      · push Not at ht
        have h1 := Y1_upper w hw0 h2
        have h4 : 4 / w ≤ 2 ^ 55 := by
          rw [div_le_iff₀ hw0]
          have : (2 : ℝ) ^ 55 * (1 / 2 ^ 53) ≤ 2 ^ 55 * w :=
            mul_le_mul_of_nonneg_left ht.le (by positivity)
          have e : (2 : ℝ) ^ 55 * (1 / 2 ^ 53) = 4 := by norm_num
          linarith
        have : (2 : ℝ) ^ 55 ≤ 2 ^ 1022 - 2 := by norm_num
        linarith
    linarith

/-- **`y1` at every finite `x > 0`** in the decided form with `12 u M₁`. -/
theorem y1_bound (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnz : x.toBits.toNat ≠ 0) :
    YBound (Bessel.y1 x).toBits (Yn (value x.toBits) 1) (12 * 𝐮 * modn (value x.toBits) 1) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hw0 := pos_value x.toBits hpos hnz
  have hY := Y_le_modn (value x.toBits) 1
  by_cases hnorm : 0x0010000000000000 ≤ x.toBits.toNat
  · left
    have e1 : modn (value x.toBits) 1 =
        √(J1 (value x.toBits) ^ 2 + Y1 (value x.toBits) ^ 2) := by
      unfold modn; rw [Jn_one, Yn_one]
    have h := BesselY1Theorem.y1_accuracy x hxf hpos hnorm
    have hv : |value (Bessel.y1 x).toBits - Yn (value x.toBits) 1| ≤
        12 * 𝐮 * modn (value x.toBits) 1 := by
      rw [Yn_one, e1, hu]
      convert h using 1
      ring
    refine ⟨finite_of_abs_lt _ ?_, hv⟩
    have hM := M1_le (value x.toBits) (by
      rw [← value_1022]
      exact (F64PositiveOrder.value_le_iff (by decide) hpos).mpr hnorm)
    have := abs_sub_abs_le_abs_sub (value (Bessel.y1 x).toBits) (Yn (value x.toBits) 1)
    have hM0 : 0 ≤ modn (value x.toBits) 1 := Real.sqrt_nonneg _
    have : 12 * 𝐮 * modn (value x.toBits) 1 ≤ modn (value x.toBits) 1 := by rw [hu]; nlinarith
    have : (2 : ℝ) ^ 1022 * 2 < 2 ^ 1024 := by norm_num
    linarith
  · push Not at hnorm
    -- the code and the facts of `BesselY1Tiny.y1_tiny`
    have hXs : Wasm.IEEE64.sign x.toBits = false := F64Exact.sign_of_pos _ hw0
    have hX0 := mag_ne_zero x.toBits hw0.ne'
    have hy1 := y1_code x hxf hpos hnz (by omega) hX0
    have hTf : Finite tpiWord := by unfold tpiWord CodeLib.IEEE64.Finite; decide
    have hTs : Wasm.IEEE64.sign tpiWord = false := by decide
    have hT0 : Wasm.IEEE64.scaledMagnitude tpiWord ≠ 0 := by decide
    obtain ⟨v, hv⟩ : ∃ v, v = value x.toBits := ⟨_, rfl⟩
    rw [← hv] at hw0 hY ⊢
    have hsmall : v < 1 / 2 ^ 1022 := by
      rw [hv, ← value_1022]
      exact F64PositiveOrder.value_strict (by decide) hnorm
    have hmin : 1 / 2 ^ 1074 ≤ v := by
      rw [hv]; exact BesselY0Small.value_ge_min _ hpos (by rw [← hv]; exact hw0)
    obtain ⟨hlabs, -, hl2⟩ := BesselY0Small.log_facts v hmin (by
      have : (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 := by norm_num
      linarith)
    have hcl := BesselY1Small.tiny_close v hw0 (by
      have : (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 ^ 53 := by norm_num
      linarith) (by rw [hlabs]; exact hl2)
    obtain ⟨Y, hYdef⟩ : ∃ Y, Y = 1 / v := ⟨_, rfl⟩
    have hY1022 : (2 : ℝ) ^ 1022 ≤ Y := by
      rw [hYdef, le_div_iff₀ hw0]
      have : (2 : ℝ) ^ 1022 * v ≤ 2 ^ 1022 * (1 / 2 ^ 1022) :=
        mul_le_mul_of_nonneg_left hsmall.le (by positivity)
      have e : (2 : ℝ) ^ 1022 * (1 / 2 ^ 1022) = 1 := by norm_num
      linarith
    have hY0 : 0 ≤ Y := le_trans (by positivity) hY1022
    have htv := tpi_value
    obtain ⟨hp1, hp2⟩ := BesselCombine.pi_bounds
    have hpi0 := Real.pi_pos
    have h2lo : 6366 / 10000 ≤ 2 / π := by rw [le_div_iff₀ hpi0]; linarith
    have h2pi : 2 / π * Y = 2 / (π * v) := by rw [hYdef]; ring
    obtain ⟨s, hsdef⟩ : ∃ s, s = value tpiWord / v := ⟨_, rfl⟩
    have hs_eq : s = value tpiWord * Y := by rw [hsdef, hYdef]; ring
    have hsd : |s - 2 / π * Y| ≤ 36 / 100 * 𝐮 * Y := by
      rw [hs_eq, ← sub_mul, abs_mul, abs_of_nonneg hY0]
      exact mul_le_mul_of_nonneg_right htv hY0
    obtain ⟨y, hydef⟩ : ∃ y, y = -Yn v 1 := ⟨_, rfl⟩
    have hyd : |y - 2 / π * Y| ≤ 300 * v := by
      rw [hydef, h2pi, Yn_one]
      rw [show -Y1 v - 2 / (π * v) = -(Y1 v - -(2 / (π * v))) by ring, abs_neg]
      exact hcl
    have hv300 : 300 * v ≤ 1 / 10 ^ 10 * 𝐮 * Y := by
      rw [hu]
      have h1 : (1 : ℝ) / 10 ^ 10 * (1 / 2 ^ 53) * 2 ^ 1022 ≤ 1 / 10 ^ 10 * (1 / 2 ^ 53) * Y :=
        mul_le_mul_of_nonneg_left hY1022 (by positivity)
      have : (300 : ℝ) * (1 / 2 ^ 1022) ≤ 1 / 10 ^ 10 * (1 / 2 ^ 53) * 2 ^ 1022 := by norm_num
      linarith
    have hsy : |s - y| ≤ 3601 / 10000 * 𝐮 * Y := by
      have := abs_sub_le s (2 / π * Y) y
      rw [abs_sub_comm (2 / π * Y) y] at this
      linarith
    have hyY : 6365 / 10000 * Y ≤ y := by
      have := (abs_le.mp hyd).1
      have h3 := mul_le_mul_of_nonneg_right h2lo hY0
      rw [hu] at hv300
      linarith
    have hsY : 6365 / 10000 * Y ≤ s := by
      have := (abs_le.mp hsd).1
      have h1 := mul_le_mul_of_nonneg_right h2lo hY0
      rw [hu] at this
      linarith
    have hyM : y ≤ modn v 1 := by
      rw [hydef]
      have := le_abs_self (-Yn v 1)
      rw [abs_neg] at this
      linarith
    have hy0 : 0 ≤ y := le_trans (by positivity) hyY
    have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
    have hYy : 3601 / 10000 * 𝐮 * Y ≤ 6 / 10 * 𝐮 * y := by
      have h1 : 3601 / 10000 * Y ≤ 6 / 10 * y := by linarith
      have := mul_le_mul_of_nonneg_left h1 hu0
      linarith
    have hs_hi : s ≤ 2 * y := by
      have := (abs_le.mp hsy).2
      have h1 : 6 / 10 * 𝐮 ≤ 1 := by rw [hu]; norm_num
      have := mul_le_mul_of_nonneg_right h1 hy0
      linarith
    have hYv : Yn v 1 = -y := by rw [hydef]; ring
    -- a finite rounded quotient within `u s` gives the bound
    have hfin : ∀ c : UInt64, Finite c → |value c - s| ≤ 𝐮 * s →
        Finite (Wasm.IEEE64.negate c) ∧
          |value (Wasm.IEEE64.negate c) - Yn v 1| ≤ 12 * 𝐮 * modn v 1 := by
      intro c hc hcs
      obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value c hc
      refine ⟨hnf, ?_⟩
      rw [hnv, hYv, show -value c - -y = -(value c - y) by ring, abs_neg]
      have h1 := abs_sub_le (value c) s y
      have h2 : 𝐮 * s ≤ 𝐮 * (2 * y) := mul_le_mul_of_nonneg_left hs_hi (by rw [hu]; positivity)
      have h3 : 12 * 𝐮 * y ≤ 12 * 𝐮 * modn v 1 :=
        mul_le_mul_of_nonneg_left hyM (by rw [hu]; positivity)
      have h4 : 0 ≤ 𝐮 * y := mul_nonneg hu0 hy0
      have := (abs_le.mp hsy).2
      have := (abs_le.mp hsy).1
      have h5 : |s - y| ≤ 6 / 10 * 𝐮 * y := hsy.trans hYy
      linarith
    by_cases hs1 : s < 2 ^ 1024 - 2 ^ 971
    · left
      have hs0 : 0 ≤ s := le_trans (by positivity) hsY
      have hlo : 1 ≤ |value tpiWord / value x.toBits| := by
        rw [← hv, ← hsdef, abs_of_nonneg hs0]
        have : (1 : ℝ) ≤ 6365 / 10000 * 2 ^ 1022 := by norm_num
        linarith
      obtain ⟨hcf, hce⟩ := Library.Numerics.Float64.Tgamma.TgammaTop.div_top tpiWord x.toBits hTf hxf hT0 hX0 hlo
        (by rw [← hv, ← hsdef, abs_of_nonneg hs0]; exact hs1)
      rw [← hv, ← hsdef, abs_of_nonneg hs0] at hce
      rw [hy1]
      exact hfin _ hcf (by rw [hu]; linarith)
    · push Not at hs1
      have h22 : (2 : ℝ) ^ 1022 ≤ value tpiWord / value x.toBits := by
        rw [← hv, ← hsdef]
        have : (2 : ℝ) ^ 1022 ≤ 2 ^ 1024 - 2 ^ 971 := by norm_num
        linarith
      rcases BesselDivTop.div_top tpiWord x.toBits hTf hxf hTs hXs h22 with ⟨hc, hth⟩ | ⟨hc, hth⟩
      · right
        rw [← hv, ← hsdef, BesselDivTop.threshold_eq] at hth
        refine ⟨?_, ?_⟩
        · rw [hy1, hc, hYv, show decide (-y < 0) = true by
            rw [decide_eq_true_iff]; linarith [show (0 : ℝ) < 2 ^ 1022 by positivity]]
          decide
        · rw [hYv, abs_neg, abs_of_nonneg hy0]
          have h1 := (abs_le.mp hsy).2
          by_contra hc
          push Not at hc
          have h2 : 6 / 10 * 𝐮 * y ≤ 6 / 10 * 𝐮 * 2 ^ 1023 :=
            mul_le_mul_of_nonneg_left hc (by rw [hu]; positivity)
          have h3 : (2 : ℝ) ^ 1023 + 6 / 10 * 𝐮 * 2 ^ 1023 < 2 ^ 1024 - 2 ^ 970 := by
            rw [hu]; norm_num
          linarith
      · left
        rw [← hv, ← hsdef] at hc hth
        have hmax := BesselDivTop.nearest_top s _ hc (by
          have : (2 : ℝ) ^ 1024 - 3 * 2 ^ 970 < 2 ^ 1024 - 2 ^ 971 := by norm_num
          linarith) hth
        have hcw : Wasm.IEEE64.div tpiWord x.toBits = BesselDivTop.maxWord :=
          UInt64.toNat_inj.mp (by rw [hmax]; rfl)
        have hmf : Finite BesselDivTop.maxWord := by
          unfold BesselDivTop.maxWord CodeLib.IEEE64.Finite; decide
        rw [BesselDivTop.threshold_eq] at hth
        rw [hy1, hcw]
        refine hfin _ hmf ?_
        rw [BesselDivTop.value_max, abs_le, hu]
        constructor
        · have h1 : 1 / 2 ^ 53 * (2 ^ 1024 - 2 ^ 971) ≤ 1 / 2 ^ 53 * s :=
            mul_le_mul_of_nonneg_left hs1 (by positivity)
          have : (2 : ℝ) ^ 1024 - 2 ^ 970 - (2 ^ 1024 - 2 ^ 971) ≤
              1 / 2 ^ 53 * (2 ^ 1024 - 2 ^ 971) := by norm_num
          linarith
        · have : 1 / 2 ^ 53 * (2 ^ 1024 - 2 ^ 971) ≤ 1 / 2 ^ 53 * s :=
            mul_le_mul_of_nonneg_left hs1 (by positivity)
          have : (0 : ℝ) ≤ 1 / 2 ^ 53 * (2 ^ 1024 - 2 ^ 971) := by norm_num
          linarith

#print axioms ybound_negate
#print axioms one_mul
#print axioms neg_one_mul
#print axioms ybound_one
#print axioms ybound_neg_one
#print axioms M1_le
#print axioms y1_bound

end Library.Numerics.Float64.Bessel.BesselYnOrderOne
