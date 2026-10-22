import Library.Numerics.Float64.Atan.AtanTheoremReduce
import Library.Numerics.Float64.Atan.AtanTheoremConst

/-!
The reduced branches of `Atan.atan` within one step.  `finish` combines the error of the reduced
argument, the tail of `AtanTheoremTail`, the constant `hi + lo`, the kernel polynomial's error, and
the Lipschitz bound of `arctan`, and applies `F64Approx.within_one_of_error` in the binade whose
start lies below the result.  Each case lemma instantiates it for an interval of `|x|` with the
constants that `scratchpad/w-poly/arc/cases.py` computed from the same formulas.
-/

namespace Library.Numerics.Float64.Atan.AtanTheoremCases
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound AtanTheoremPoly AtanTheoremBranches
  AtanTheoremTail AtanTheoremConst AtanTheoremReduce

set_option exponentiation.threshold 4096

theorem finish_err (h l : UInt64) (t : Float) (C tstar Mt et T0 Ml Y E : ℝ)
    (hfh : Wasm.IEEE64.isFinite h = true) (hfl : Wasm.IEEE64.isFinite l = true)
    (hMh : |value h| ≤ 2) (hMl : |value l| ≤ Ml) (hMl1 : Ml ≤ 1)
    (ht : FSApprox t tstar 1 Mt et) (hT : Mt + et ≤ T0) (hT07 : T0 ≤ 7 / 16)
    (hT0 : 1 / 2 ^ 27 ≤ T0) (hconst : |value h + value l - C| ≤ 1 / 2 ^ 64)
    (hY : |C + Real.arctan tstar| ≤ Y)
    (hY2 : Y + et + 1 / 2 ^ 64 + 5 / 8 / 2 ^ 57 * T0 ≤ 2)
    (hE : tailErr T0 Ml (Y + et + 1 / 2 ^ 64 + 5 / 8 / 2 ^ 57 * T0) + 1 / 2 ^ 64 +
      5 / 8 / 2 ^ 57 * T0 + et ≤ E)
    :
    Finite (atanTail (Float.ofBits h) (Float.ofBits l) t).toBits ∧
      |value (atanTail (Float.ofBits h) (Float.ofBits l) t).toBits - (C + Real.arctan tstar)| ≤ E := by
  have hta := ht.approx
  have htf : Finite t.toBits := hta.1
  have het : |value t.toBits - tstar| ≤ et := by
    have := hta.2
    rwa [mul_one] at this
  have het0 : 0 ≤ et := (abs_nonneg _).trans het
  have hts : |tstar| ≤ Mt := by
    have := ht.2.2.1
    rwa [mul_one] at this
  have hvt : |value t.toBits| ≤ T0 := by
    have := abs_sub_abs_le_abs_sub (value t.toBits) tstar
    linarith
  have hk := AtanKernelPoly.atan_kernel_error (value t.toBits) (hvt.trans hT07)
  rw [← kernel_link] at hk
  have hkb : |value t.toBits| * ((5 / 8) / 2 ^ 57) ≤ 5 / 8 / 2 ^ 57 * T0 := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hvt (by positivity)
  have hlip := arctan_lipschitz (value t.toBits) tstar
  set X := value h + value l + (value t.toBits - value t.toBits * polyS (value t.toBits)) with hX
  set y := C + Real.arctan tstar with hy
  have hD : |X - y| ≤ 1 / 2 ^ 64 + 5 / 8 / 2 ^ 57 * T0 + et := by
    have heq : X - y = (value h + value l - C) +
        ((value t.toBits - value t.toBits * polyS (value t.toBits)) -
          Real.arctan (value t.toBits)) +
        (Real.arctan (value t.toBits) - Real.arctan tstar) := by
      rw [hX, hy]
      ring
    rw [heq]
    have h2 : |(value t.toBits - value t.toBits * polyS (value t.toBits)) -
        Real.arctan (value t.toBits)| ≤ 5 / 8 / 2 ^ 57 * T0 := by
      rw [abs_sub_comm]
      exact hk.trans hkb
    calc _ ≤ |value h + value l - C| +
          |(value t.toBits - value t.toBits * polyS (value t.toBits)) -
            Real.arctan (value t.toBits)| +
          |Real.arctan (value t.toBits) - Real.arctan tstar| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 1 / 2 ^ 64 + 5 / 8 / 2 ^ 57 * T0 + et :=
          add_le_add (add_le_add hconst h2) (hlip.trans het)
  have hMz : |X| ≤ Y + et + 1 / 2 ^ 64 + 5 / 8 / 2 ^ 57 * T0 := by
    have := abs_sub_abs_le_abs_sub X y
    linarith
  obtain ⟨hzf, hz⟩ := tail_result h l t T0 Ml (Y + et + 1 / 2 ^ 64 + 5 / 8 / 2 ^ 57 * T0)
    hfh hfl hMh hMl hMl1 htf hvt hT07 hT0 hMz hY2
  have htot : |value (atanTail (Float.ofBits h) (Float.ofBits l) t).toBits - y| ≤ E := by
    have := abs_sub_le (value (atanTail (Float.ofBits h) (Float.ofBits l) t).toBits) X y
    linarith
  exact ⟨hzf, htot⟩

theorem finish (h l : UInt64) (t : Float) (C tstar Mt et T0 Ml Y E : ℝ) (n : ℕ)
    (hfh : Wasm.IEEE64.isFinite h = true) (hfl : Wasm.IEEE64.isFinite l = true)
    (hMh : |value h| ≤ 2) (hMl : |value l| ≤ Ml) (hMl1 : Ml ≤ 1)
    (ht : FSApprox t tstar 1 Mt et) (hT : Mt + et ≤ T0) (hT07 : T0 ≤ 7 / 16)
    (hT0 : 1 / 2 ^ 27 ≤ T0) (hconst : |value h + value l - C| ≤ 1 / 2 ^ 64)
    (hY : |C + Real.arctan tstar| ≤ Y)
    (hY2 : Y + et + 1 / 2 ^ 64 + 5 / 8 / 2 ^ 57 * T0 ≤ 2)
    (hE : tailErr T0 Ml (Y + et + 1 / 2 ^ 64 + 5 / 8 / 2 ^ 57 * T0) + 1 / 2 ^ 64 +
      5 / 8 / 2 ^ 57 * T0 + et ≤ E)
    (hn1 : 1 ≤ n) (hn : n < 2047)
    (hyB : value (UInt64.ofNat (n * 2 ^ 52)) + E ≤ C + Real.arctan tstar)
    (hEc : E < 3 * ((2 : ℝ) ^ (n - 1) / (2 : ℝ) ^ 1074) / 2) :
    F64SignedRounding.WithinSteps 1 (C + Real.arctan tstar)
      (atanTail (Float.ofBits h) (Float.ofBits l) t).toBits := by
  obtain ⟨hzf, htot⟩ := finish_err h l t C tstar Mt et T0 Ml Y E hfh hfl hMh hMl hMl1 ht hT hT07
    hT0 hconst hY hY2 hE
  have hB := F64PositiveSpacing.boundary_value n hn1 (by omega)
  have hB0 : 0 < value (UInt64.ofNat (n * 2 ^ 52)) := by rw [hB]; positivity
  exact within_one_of_error _ _ n hn E hzf htot hyB hEc (by linarith)

theorem arctan_le_max (v : ℝ) : Real.arctan v ≤ max v 0 := by
  rcases le_total v 0 with h | h
  · have := Real.arctan_mono h
    rw [Real.arctan_zero] at this
    exact this.trans (le_max_right _ _)
  · have h1 := abs_arctan_le v
    have h0 : 0 ≤ Real.arctan v := by
      have := Real.arctan_mono h
      rwa [Real.arctan_zero] at this
    rw [abs_of_nonneg h0, abs_of_nonneg h] at h1
    exact h1.trans (le_max_left _ _)

theorem min_le_arctan (v : ℝ) : min v 0 ≤ Real.arctan v := by
  have h := arctan_le_max (-v)
  rw [Real.arctan_neg] at h
  have : max (-v) 0 = -min v 0 := by
    rw [max_comm, ← neg_zero, max_neg_neg, neg_zero, min_comm]
  rw [this] at h
  linarith

theorem arctan_ge_cubic (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1 / 2) :
    v - v ^ 3 / (1 - v ^ 2) ≤ Real.arctan v := by
  have hr := TaylorRemainder.atan_remainder v (by rw [abs_of_nonneg h0]; linarith) 1
  simp only [TaylorRemainder.atanCoeffs, List.range_one, List.map_cons, List.map_nil, eval_cons,
    eval_nil, mul_zero, add_zero] at hr
  norm_num at hr
  rw [abs_of_nonneg h0] at hr
  have := (abs_le.mp hr).1
  linarith

theorem arctan_le_of_le_nonneg (v w : ℝ) (h : v ≤ w) (hw : 0 ≤ w) : Real.arctan v ≤ w :=
  (Real.arctan_mono h).trans ((arctan_le_max w).trans (le_of_eq (max_eq_left hw)))

theorem arctan_le_of_le_nonpos (v w : ℝ) (h : v ≤ w) (hw : w ≤ 0) : Real.arctan v ≤ 0 :=
  (Real.arctan_mono h).trans ((arctan_le_max w).trans (le_of_eq (max_eq_right hw)))

theorem le_arctan_of_le_nonpos (v w : ℝ) (h : w ≤ v) (hw : w ≤ 0) : w ≤ Real.arctan v :=
  (le_of_eq (min_eq_left hw).symm).trans ((min_le_arctan w).trans (Real.arctan_mono h))

/-- The value of a word, from its exact rational. -/
theorem word_eq (w : UInt64) (q : ℚ) (h : ratOfWord w = q) : value w = (q : ℝ) := value_word w q h


theorem case0_low_err (x : Float) (hx : Finite x.toBits) (h1 : (7 / 16 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (551 / 1000 : ℝ)) :
    Finite (atanTail (Float.ofBits 0x3FDDAC670561BB4F) (Float.ofBits 0x3C7A2B7F222F65E2)
        ((2.0 * x.abs - 1.0) / (2.0 + x.abs))).toBits ∧
      |value (atanTail (Float.ofBits 0x3FDDAC670561BB4F) (Float.ofBits 0x3C7A2B7F222F65E2)
        ((2.0 * x.abs - 1.0) / (2.0 + x.abs))).toBits - Real.arctan (|value x.toBits|)| ≤ (1657 / 22517998136852480000 : ℝ) ∧
      value (UInt64.ofNat (1021 * 2 ^ 52)) + (1657 / 22517998136852480000 : ℝ) + 1 / 2 ^ 52 ≤ Real.arctan |value x.toBits| := by
  set a := |value x.toBits| with ha
  have hapos : 0 < a := by linarith
  have hMn : |2 * a - 1| ≤ (1 / 8 : ℝ) := by rw [abs_le]; constructor <;> linarith
  have ht := reduce0 x hx (7 / 16 : ℝ) (551 / 1000 : ℝ) (1 / 8 : ℝ) (by norm_num) h1 h2 (by norm_num) hMn (by norm_num)
  have htL : (-2 / 39 : ℝ) ≤ (2 * a - 1) / (2 + a) := by
    rw [show (-2 / 39 : ℝ) = (2 * (7 / 16 : ℝ) - 1) / (2 + (7 / 16 : ℝ)) by norm_num, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have htH : (2 * a - 1) / (2 + a) ≤ (102 / 2551 : ℝ) := by
    rw [show (102 / 2551 : ℝ) = (2 * (551 / 1000 : ℝ) - 1) / (2 + (551 / 1000 : ℝ)) by norm_num, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hvh := word_eq 0x3FDDAC670561BB4F (8352332796509007 / 18014398509481984 : ℚ) (by decide +kernel)
  have hvl := word_eq 0x3C7A2B7F222F65E2 (3683087214424817 / 162259276829213363391578010288128 : ℚ) (by decide +kernel)
  have hc := atan_half
  rw [hvh, hvl, abs_le] at hc
  push_cast at hc
  have hcL : (4636476090008061 / 10000000000000000 : ℝ) ≤ Real.arctan (1 / 2) := by linarith [hc.2]
  have hcH : Real.arctan (1 / 2) ≤ (2318238045004031 / 5000000000000000 : ℝ) := by linarith [hc.1]
  have hat : Real.arctan ((2 * a - 1) / (2 + a)) ≤ (102 / 2551 : ℝ) := arctan_le_of_le_nonneg _ _ htH (by norm_num)
  have hal : (-2 / 39 : ℝ) ≤ Real.arctan ((2 * a - 1) / (2 + a)) := le_arctan_of_le_nonpos _ _ htL (by norm_num)
  rw [arctan_red0 a hapos]
  obtain ⟨hzf, htot⟩ := finish_err 0x3FDDAC670561BB4F 0x3C7A2B7F222F65E2 _ (Real.arctan (1 / 2)) ((2 * a - 1) / (2 + a)) _ _ (51283 / 1000000 : ℝ) (227 / 10000000000000000000 : ℝ) (125907982219 / 250000000000 : ℝ) (1657 / 22517998136852480000 : ℝ)
    (by decide +kernel) (by decide +kernel) (by rw [hvh]; norm_num) (by rw [hvl]; norm_num)
    (by norm_num) ht (by norm_num [red0Err]) (by norm_num) (by norm_num) atan_half
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [red0Err])
    (by norm_num [tailErr, red0Err]) 
  refine ⟨hzf, htot, ?_⟩
  rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]; norm_num; linarith

theorem case0_low (x : Float) (hx : Finite x.toBits) (h1 : (7 / 16 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (551 / 1000 : ℝ)) :
    F64SignedRounding.WithinSteps 1 (Real.arctan |value x.toBits|)
      (atanTail (Float.ofBits 0x3FDDAC670561BB4F) (Float.ofBits 0x3C7A2B7F222F65E2)
        ((2.0 * x.abs - 1.0) / (2.0 + x.abs))).toBits := by
  obtain ⟨hzf, htot, hyB⟩ := case0_low_err x hx h1 h2
  have hB0 : 0 < value (UInt64.ofNat (1021 * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]
    positivity
  refine within_one_of_error _ _ 1021 (by norm_num) _ hzf htot ?_ (by norm_num) ?_
  all_goals
    generalize value (UInt64.ofNat (1021 * 2 ^ 52)) = B at hyB hB0 ⊢
    linarith

theorem case0_high_err (x : Float) (hx : Finite x.toBits) (h1 : (551 / 1000 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (11 / 16 : ℝ)) :
    Finite (atanTail (Float.ofBits 0x3FDDAC670561BB4F) (Float.ofBits 0x3C7A2B7F222F65E2)
        ((2.0 * x.abs - 1.0) / (2.0 + x.abs))).toBits ∧
      |value (atanTail (Float.ofBits 0x3FDDAC670561BB4F) (Float.ofBits 0x3C7A2B7F222F65E2)
        ((2.0 * x.abs - 1.0) / (2.0 + x.abs))).toBits - Real.arctan (|value x.toBits|)| ≤ (10671 / 90071992547409920000 : ℝ) ∧
      value (UInt64.ofNat (1022 * 2 ^ 52)) + (10671 / 90071992547409920000 : ℝ) + 1 / 2 ^ 52 ≤ Real.arctan |value x.toBits| := by
  set a := |value x.toBits| with ha
  have hapos : 0 < a := by linarith
  have hMn : |2 * a - 1| ≤ (3 / 8 : ℝ) := by rw [abs_le]; constructor <;> linarith
  have ht := reduce0 x hx (551 / 1000 : ℝ) (11 / 16 : ℝ) (3 / 8 : ℝ) (by norm_num) h1 h2 (by norm_num) hMn (by norm_num)
  have htL : (102 / 2551 : ℝ) ≤ (2 * a - 1) / (2 + a) := by
    rw [show (102 / 2551 : ℝ) = (2 * (551 / 1000 : ℝ) - 1) / (2 + (551 / 1000 : ℝ)) by norm_num, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have htH : (2 * a - 1) / (2 + a) ≤ (6 / 43 : ℝ) := by
    rw [show (6 / 43 : ℝ) = (2 * (11 / 16 : ℝ) - 1) / (2 + (11 / 16 : ℝ)) by norm_num, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hvh := word_eq 0x3FDDAC670561BB4F (8352332796509007 / 18014398509481984 : ℚ) (by decide +kernel)
  have hvl := word_eq 0x3C7A2B7F222F65E2 (3683087214424817 / 162259276829213363391578010288128 : ℚ) (by decide +kernel)
  have hc := atan_half
  rw [hvh, hvl, abs_le] at hc
  push_cast at hc
  have hcL : (4636476090008061 / 10000000000000000 : ℝ) ≤ Real.arctan (1 / 2) := by linarith [hc.2]
  have hcH : Real.arctan (1 / 2) ≤ (2318238045004031 / 5000000000000000 : ℝ) := by linarith [hc.1]
  have hat : Real.arctan ((2 * a - 1) / (2 + a)) ≤ (6 / 43 : ℝ) := arctan_le_of_le_nonneg _ _ htH (by norm_num)
  have hal : (102 / 2551 : ℝ) - (102 / 2551 : ℝ) ^ 3 / (1 - (102 / 2551 : ℝ) ^ 2) ≤ Real.arctan ((2 * a - 1) / (2 + a)) :=
    (arctan_ge_cubic _ (by norm_num) (by norm_num)).trans (Real.arctan_mono htL)
  rw [arctan_red0 a hapos]
  obtain ⟨hzf, htot⟩ := finish_err 0x3FDDAC670561BB4F 0x3C7A2B7F222F65E2 _ (Real.arctan (1 / 2)) ((2 * a - 1) / (2 + a)) _ _ (73501 / 500000 : ℝ) (227 / 10000000000000000000 : ℝ) (301591246361 / 500000000000 : ℝ) (10671 / 90071992547409920000 : ℝ)
    (by decide +kernel) (by decide +kernel) (by rw [hvh]; norm_num) (by rw [hvl]; norm_num)
    (by norm_num) ht (by norm_num [red0Err]) (by norm_num) (by norm_num) atan_half
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [red0Err])
    (by norm_num [tailErr, red0Err]) 
  refine ⟨hzf, htot, ?_⟩
  rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num; linarith

theorem case0_high (x : Float) (hx : Finite x.toBits) (h1 : (551 / 1000 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (11 / 16 : ℝ)) :
    F64SignedRounding.WithinSteps 1 (Real.arctan |value x.toBits|)
      (atanTail (Float.ofBits 0x3FDDAC670561BB4F) (Float.ofBits 0x3C7A2B7F222F65E2)
        ((2.0 * x.abs - 1.0) / (2.0 + x.abs))).toBits := by
  obtain ⟨hzf, htot, hyB⟩ := case0_high_err x hx h1 h2
  have hB0 : 0 < value (UInt64.ofNat (1022 * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    positivity
  refine within_one_of_error _ _ 1022 (by norm_num) _ hzf htot ?_ (by norm_num) ?_
  all_goals
    generalize value (UInt64.ofNat (1022 * 2 ^ 52)) = B at hyB hB0 ⊢
    linarith

theorem case1_low_err (x : Float) (hx : Finite x.toBits) (h1 : (11 / 16 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (1 : ℝ)) :
    Finite (atanTail (Float.ofBits 0x3FE921FB54442D18) (Float.ofBits 0x3C81A62633145C07)
        ((x.abs - 1.0) / (x.abs + 1.0))).toBits ∧
      |value (atanTail (Float.ofBits 0x3FE921FB54442D18) (Float.ofBits 0x3C81A62633145C07)
        ((x.abs - 1.0) / (x.abs + 1.0))).toBits - Real.arctan (|value x.toBits|)| ≤ (2801 / 18014398509481984000 : ℝ) ∧
      value (UInt64.ofNat (1022 * 2 ^ 52)) + (2801 / 18014398509481984000 : ℝ) + 1 / 2 ^ 52 ≤ Real.arctan |value x.toBits| := by
  set a := |value x.toBits| with ha
  have hapos : 0 < a := by linarith
  have hMn : |(a - 1)| ≤ (5 / 16 : ℝ) := by rw [abs_le]; constructor <;> linarith
  have ht := reduce1 x hx (11 / 16 : ℝ) (1 : ℝ) (5 / 16 : ℝ) (by norm_num) h1 h2 (by norm_num) hMn (by norm_num)
  have htL : (-5 / 27 : ℝ) ≤ (a - 1) / (a + 1) := by
    rw [show (-5 / 27 : ℝ) = ((11 / 16 : ℝ) - 1) / ((11 / 16 : ℝ) + 1) by norm_num, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have htH : (a - 1) / (a + 1) ≤ (0 : ℝ) := by
    rw [show (0 : ℝ) = ((1 : ℝ) - 1) / ((1 : ℝ) + 1) by norm_num, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hvh := word_eq 0x3FE921FB54442D18 (884279719003555 / 1125899906842624 : ℚ) (by decide +kernel)
  have hvl := word_eq 0x3C81A62633145C07 (4967757600021511 / 162259276829213363391578010288128 : ℚ) (by decide +kernel)
  have hc := atan_one
  rw [hvh, hvl, abs_le] at hc
  push_cast at hc
  have hcL : (7853981633974483 / 10000000000000000 : ℝ) ≤ Real.arctan 1 := by linarith [hc.2]
  have hcH : Real.arctan 1 ≤ (1963495408493621 / 2500000000000000 : ℝ) := by linarith [hc.1]
  have hcL1 : (7853981633974483 / 10000000000000000 : ℝ) ≤ Real.pi / 4 := by rw [← Real.arctan_one]; exact hcL
  have hcH1 : Real.pi / 4 ≤ (1963495408493621 / 2500000000000000 : ℝ) := by rw [← Real.arctan_one]; exact hcH
  have hat : Real.arctan ((a - 1) / (a + 1)) ≤ (0 : ℝ) := arctan_le_of_le_nonneg _ _ htH (by norm_num)
  have hal : (-5 / 27 : ℝ) ≤ Real.arctan ((a - 1) / (a + 1)) := le_arctan_of_le_nonpos _ _ htL (by norm_num)
  rw [arctan_red1 a hapos]
  obtain ⟨hzf, htot⟩ := finish_err 0x3FE921FB54442D18 0x3C81A62633145C07 _ (Real.arctan 1) ((a - 1) / (a + 1)) _ _ (92593 / 500000 : ℝ) (1531 / 50000000000000000000 : ℝ) (392699081699 / 500000000000 : ℝ) (2801 / 18014398509481984000 : ℝ)
    (by decide +kernel) (by decide +kernel) (by rw [hvh]; norm_num) (by rw [hvl]; norm_num)
    (by norm_num) ht (by norm_num [red1Err]) (by norm_num) (by norm_num) atan_one
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [red1Err])
    (by norm_num [tailErr, red1Err]) 
  refine ⟨hzf, htot, ?_⟩
  rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num; linarith

theorem case1_low (x : Float) (hx : Finite x.toBits) (h1 : (11 / 16 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (1 : ℝ)) :
    F64SignedRounding.WithinSteps 1 (Real.arctan |value x.toBits|)
      (atanTail (Float.ofBits 0x3FE921FB54442D18) (Float.ofBits 0x3C81A62633145C07)
        ((x.abs - 1.0) / (x.abs + 1.0))).toBits := by
  obtain ⟨hzf, htot, hyB⟩ := case1_low_err x hx h1 h2
  have hB0 : 0 < value (UInt64.ofNat (1022 * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    positivity
  refine within_one_of_error _ _ 1022 (by norm_num) _ hzf htot ?_ (by norm_num) ?_
  all_goals
    generalize value (UInt64.ofNat (1022 * 2 ^ 52)) = B at hyB hB0 ⊢
    linarith

theorem case1_high_err (x : Float) (hx : Finite x.toBits) (h1 : (1 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (19 / 16 : ℝ)) :
    Finite (atanTail (Float.ofBits 0x3FE921FB54442D18) (Float.ofBits 0x3C81A62633145C07)
        ((x.abs - 1.0) / (x.abs + 1.0))).toBits ∧
      |value (atanTail (Float.ofBits 0x3FE921FB54442D18) (Float.ofBits 0x3C81A62633145C07)
        ((x.abs - 1.0) / (x.abs + 1.0))).toBits - Real.arctan (|value x.toBits|)| ≤ (2919 / 22517998136852480000 : ℝ) ∧
      value (UInt64.ofNat (1022 * 2 ^ 52)) + (2919 / 22517998136852480000 : ℝ) + 1 / 2 ^ 52 ≤ Real.arctan |value x.toBits| := by
  set a := |value x.toBits| with ha
  have hapos : 0 < a := by linarith
  have hMn : |(a - 1)| ≤ (3 / 16 : ℝ) := by rw [abs_le]; constructor <;> linarith
  have ht := reduce1 x hx (1 : ℝ) (19 / 16 : ℝ) (3 / 16 : ℝ) (by norm_num) h1 h2 (by norm_num) hMn (by norm_num)
  have htL : (0 : ℝ) ≤ (a - 1) / (a + 1) := by
    rw [show (0 : ℝ) = ((1 : ℝ) - 1) / ((1 : ℝ) + 1) by norm_num, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have htH : (a - 1) / (a + 1) ≤ (3 / 35 : ℝ) := by
    rw [show (3 / 35 : ℝ) = ((19 / 16 : ℝ) - 1) / ((19 / 16 : ℝ) + 1) by norm_num, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hvh := word_eq 0x3FE921FB54442D18 (884279719003555 / 1125899906842624 : ℚ) (by decide +kernel)
  have hvl := word_eq 0x3C81A62633145C07 (4967757600021511 / 162259276829213363391578010288128 : ℚ) (by decide +kernel)
  have hc := atan_one
  rw [hvh, hvl, abs_le] at hc
  push_cast at hc
  have hcL : (7853981633974483 / 10000000000000000 : ℝ) ≤ Real.arctan 1 := by linarith [hc.2]
  have hcH : Real.arctan 1 ≤ (1963495408493621 / 2500000000000000 : ℝ) := by linarith [hc.1]
  have hcL1 : (7853981633974483 / 10000000000000000 : ℝ) ≤ Real.pi / 4 := by rw [← Real.arctan_one]; exact hcL
  have hcH1 : Real.pi / 4 ≤ (1963495408493621 / 2500000000000000 : ℝ) := by rw [← Real.arctan_one]; exact hcH
  have hat : Real.arctan ((a - 1) / (a + 1)) ≤ (3 / 35 : ℝ) := arctan_le_of_le_nonneg _ _ htH (by norm_num)
  have hal : (0 : ℝ) - (0 : ℝ) ^ 3 / (1 - (0 : ℝ) ^ 2) ≤ Real.arctan ((a - 1) / (a + 1)) :=
    (arctan_ge_cubic _ (by norm_num) (by norm_num)).trans (Real.arctan_mono htL)
  rw [arctan_red1 a hapos]
  obtain ⟨hzf, htot⟩ := finish_err 0x3FE921FB54442D18 0x3C81A62633145C07 _ (Real.arctan 1) ((a - 1) / (a + 1)) _ _ (93751 / 1000000 : ℝ) (1531 / 50000000000000000000 : ℝ) (108889056139 / 125000000000 : ℝ) (2919 / 22517998136852480000 : ℝ)
    (by decide +kernel) (by decide +kernel) (by rw [hvh]; norm_num) (by rw [hvl]; norm_num)
    (by norm_num) ht (by norm_num [red1Err]) (by norm_num) (by norm_num) atan_one
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [red1Err])
    (by norm_num [tailErr, red1Err]) 
  refine ⟨hzf, htot, ?_⟩
  rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num; linarith

theorem case1_high (x : Float) (hx : Finite x.toBits) (h1 : (1 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (19 / 16 : ℝ)) :
    F64SignedRounding.WithinSteps 1 (Real.arctan |value x.toBits|)
      (atanTail (Float.ofBits 0x3FE921FB54442D18) (Float.ofBits 0x3C81A62633145C07)
        ((x.abs - 1.0) / (x.abs + 1.0))).toBits := by
  obtain ⟨hzf, htot, hyB⟩ := case1_high_err x hx h1 h2
  have hB0 : 0 < value (UInt64.ofNat (1022 * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    positivity
  refine within_one_of_error _ _ 1022 (by norm_num) _ hzf htot ?_ (by norm_num) ?_
  all_goals
    generalize value (UInt64.ofNat (1022 * 2 ^ 52)) = B at hyB hB0 ⊢
    linarith

theorem case2_a_err (x : Float) (hx : Finite x.toBits) (h1 : (19 / 16 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (3 / 2 : ℝ)) :
    Finite (atanTail (Float.ofBits 0x3FEF730BD281F69B) (Float.ofBits 0x3C7007887AF0CBBD)
        ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))).toBits ∧
      |value (atanTail (Float.ofBits 0x3FEF730BD281F69B) (Float.ofBits 0x3C7007887AF0CBBD)
        ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))).toBits - Real.arctan (|value x.toBits|)| ≤ (2877 / 18014398509481984000 : ℝ) ∧
      value (UInt64.ofNat (1022 * 2 ^ 52)) + (2877 / 18014398509481984000 : ℝ) + 1 / 2 ^ 52 ≤ Real.arctan |value x.toBits| := by
  set a := |value x.toBits| with ha
  have hapos : 0 < a := by linarith
  have hMn : |(a - 3 / 2)| ≤ (5 / 16 : ℝ) := by rw [abs_le]; constructor <;> linarith
  have ht := reduce2 x hx (19 / 16 : ℝ) (3 / 2 : ℝ) (5 / 16 : ℝ) (by norm_num) h1 h2 (by norm_num) hMn (by norm_num)
  have htL : (-10 / 89 : ℝ) ≤ (a - 3 / 2) / (1 + 3 / 2 * a) := by
    rw [show (-10 / 89 : ℝ) = ((19 / 16 : ℝ) - 3 / 2) / (1 + 3 / 2 * (19 / 16 : ℝ)) by norm_num, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have htH : (a - 3 / 2) / (1 + 3 / 2 * a) ≤ (0 : ℝ) := by
    rw [show (0 : ℝ) = ((3 / 2 : ℝ) - 3 / 2) / (1 + 3 / 2 * (3 / 2 : ℝ)) by norm_num, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hvh := word_eq 0x3FEF730BD281F69B (8852218891597467 / 9007199254740992 : ℚ) (by decide +kernel)
  have hvl := word_eq 0x3C7007887AF0CBBD (4511882386918333 / 324518553658426726783156020576256 : ℚ) (by decide +kernel)
  have hc := atan_three_halves
  rw [hvh, hvl, abs_le] at hc
  push_cast at hc
  have hcL : (982793723247329 / 1000000000000000 : ℝ) ≤ Real.arctan (3 / 2) := by linarith [hc.2]
  have hcH : Real.arctan (3 / 2) ≤ (9827937232473291 / 10000000000000000 : ℝ) := by linarith [hc.1]
  have hat : Real.arctan ((a - 3 / 2) / (1 + 3 / 2 * a)) ≤ (0 : ℝ) := arctan_le_of_le_nonneg _ _ htH (by norm_num)
  have hal : (-10 / 89 : ℝ) ≤ Real.arctan ((a - 3 / 2) / (1 + 3 / 2 * a)) := le_arctan_of_le_nonpos _ _ htL (by norm_num)
  rw [arctan_red2 a hapos]
  obtain ⟨hzf, htot⟩ := finish_err 0x3FEF730BD281F69B 0x3C7007887AF0CBBD _ (Real.arctan (3 / 2)) ((a - 3 / 2) / (1 + 3 / 2 * a)) _ _ (2809 / 25000 : ℝ) (1391 / 100000000000000000000 : ℝ) (61424607703 / 62500000000 : ℝ) (2877 / 18014398509481984000 : ℝ)
    (by decide +kernel) (by decide +kernel) (by rw [hvh]; norm_num) (by rw [hvl]; norm_num)
    (by norm_num) ht (by norm_num [red2Err]) (by norm_num) (by norm_num) atan_three_halves
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [red2Err])
    (by norm_num [tailErr, red2Err]) 
  refine ⟨hzf, htot, ?_⟩
  rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num; linarith

theorem case2_a (x : Float) (hx : Finite x.toBits) (h1 : (19 / 16 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (3 / 2 : ℝ)) :
    F64SignedRounding.WithinSteps 1 (Real.arctan |value x.toBits|)
      (atanTail (Float.ofBits 0x3FEF730BD281F69B) (Float.ofBits 0x3C7007887AF0CBBD)
        ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))).toBits := by
  obtain ⟨hzf, htot, hyB⟩ := case2_a_err x hx h1 h2
  have hB0 : 0 < value (UInt64.ofNat (1022 * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    positivity
  refine within_one_of_error _ _ 1022 (by norm_num) _ hzf htot ?_ (by norm_num) ?_
  all_goals
    generalize value (UInt64.ofNat (1022 * 2 ^ 52)) = B at hyB hB0 ⊢
    linarith

theorem case2_b_err (x : Float) (hx : Finite x.toBits) (h1 : (3 / 2 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (793 / 500 : ℝ)) :
    Finite (atanTail (Float.ofBits 0x3FEF730BD281F69B) (Float.ofBits 0x3C7007887AF0CBBD)
        ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))).toBits ∧
      |value (atanTail (Float.ofBits 0x3FEF730BD281F69B) (Float.ofBits 0x3C7007887AF0CBBD)
        ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))).toBits - Real.arctan (|value x.toBits|)| ≤ (11097 / 90071992547409920000 : ℝ) ∧
      value (UInt64.ofNat (1022 * 2 ^ 52)) + (11097 / 90071992547409920000 : ℝ) + 1 / 2 ^ 52 ≤ Real.arctan |value x.toBits| := by
  set a := |value x.toBits| with ha
  have hapos : 0 < a := by linarith
  have hMn : |(a - 3 / 2)| ≤ (43 / 500 : ℝ) := by rw [abs_le]; constructor <;> linarith
  have ht := reduce2 x hx (3 / 2 : ℝ) (793 / 500 : ℝ) (43 / 500 : ℝ) (by norm_num) h1 h2 (by norm_num) hMn (by norm_num)
  have htL : (0 : ℝ) ≤ (a - 3 / 2) / (1 + 3 / 2 * a) := by
    rw [show (0 : ℝ) = ((3 / 2 : ℝ) - 3 / 2) / (1 + 3 / 2 * (3 / 2 : ℝ)) by norm_num, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have htH : (a - 3 / 2) / (1 + 3 / 2 * a) ≤ (86 / 3379 : ℝ) := by
    rw [show (86 / 3379 : ℝ) = ((793 / 500 : ℝ) - 3 / 2) / (1 + 3 / 2 * (793 / 500 : ℝ)) by norm_num, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hvh := word_eq 0x3FEF730BD281F69B (8852218891597467 / 9007199254740992 : ℚ) (by decide +kernel)
  have hvl := word_eq 0x3C7007887AF0CBBD (4511882386918333 / 324518553658426726783156020576256 : ℚ) (by decide +kernel)
  have hc := atan_three_halves
  rw [hvh, hvl, abs_le] at hc
  push_cast at hc
  have hcL : (982793723247329 / 1000000000000000 : ℝ) ≤ Real.arctan (3 / 2) := by linarith [hc.2]
  have hcH : Real.arctan (3 / 2) ≤ (9827937232473291 / 10000000000000000 : ℝ) := by linarith [hc.1]
  have hat : Real.arctan ((a - 3 / 2) / (1 + 3 / 2 * a)) ≤ (86 / 3379 : ℝ) := arctan_le_of_le_nonneg _ _ htH (by norm_num)
  have hal : (0 : ℝ) - (0 : ℝ) ^ 3 / (1 - (0 : ℝ) ^ 2) ≤ Real.arctan ((a - 3 / 2) / (1 + 3 / 2 * a)) :=
    (arctan_ge_cubic _ (by norm_num) (by norm_num)).trans (Real.arctan_mono htL)
  rw [arctan_red2 a hapos]
  obtain ⟨hzf, htot⟩ := finish_err 0x3FEF730BD281F69B 0x3C7007887AF0CBBD _ (Real.arctan (3 / 2)) ((a - 3 / 2) / (1 + 3 / 2 * a)) _ _ (13231 / 500000 : ℝ) (1391 / 100000000000000000000 : ℝ) (504122520103 / 500000000000 : ℝ) (11097 / 90071992547409920000 : ℝ)
    (by decide +kernel) (by decide +kernel) (by rw [hvh]; norm_num) (by rw [hvl]; norm_num)
    (by norm_num) ht (by norm_num [red2Err]) (by norm_num) (by norm_num) atan_three_halves
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [red2Err])
    (by norm_num [tailErr, red2Err]) 
  refine ⟨hzf, htot, ?_⟩
  rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]; norm_num; linarith

theorem case2_b (x : Float) (hx : Finite x.toBits) (h1 : (3 / 2 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (793 / 500 : ℝ)) :
    F64SignedRounding.WithinSteps 1 (Real.arctan |value x.toBits|)
      (atanTail (Float.ofBits 0x3FEF730BD281F69B) (Float.ofBits 0x3C7007887AF0CBBD)
        ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))).toBits := by
  obtain ⟨hzf, htot, hyB⟩ := case2_b_err x hx h1 h2
  have hB0 : 0 < value (UInt64.ofNat (1022 * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    positivity
  refine within_one_of_error _ _ 1022 (by norm_num) _ hzf htot ?_ (by norm_num) ?_
  all_goals
    generalize value (UInt64.ofNat (1022 * 2 ^ 52)) = B at hyB hB0 ⊢
    linarith

theorem case2_c_err (x : Float) (hx : Finite x.toBits) (h1 : (793 / 500 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (39 / 16 : ℝ)) :
    Finite (atanTail (Float.ofBits 0x3FEF730BD281F69B) (Float.ofBits 0x3C7007887AF0CBBD)
        ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))).toBits ∧
      |value (atanTail (Float.ofBits 0x3FEF730BD281F69B) (Float.ofBits 0x3C7007887AF0CBBD)
        ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))).toBits - Real.arctan (|value x.toBits|)| ≤ (12459 / 45035996273704960000 : ℝ) ∧
      value (UInt64.ofNat (1023 * 2 ^ 52)) + (12459 / 45035996273704960000 : ℝ) + 1 / 2 ^ 52 ≤ Real.arctan |value x.toBits| := by
  set a := |value x.toBits| with ha
  have hapos : 0 < a := by linarith
  have hMn : |(a - 3 / 2)| ≤ (15 / 16 : ℝ) := by rw [abs_le]; constructor <;> linarith
  have ht := reduce2 x hx (793 / 500 : ℝ) (39 / 16 : ℝ) (15 / 16 : ℝ) (by norm_num) h1 h2 (by norm_num) hMn (by norm_num)
  have htL : (86 / 3379 : ℝ) ≤ (a - 3 / 2) / (1 + 3 / 2 * a) := by
    rw [show (86 / 3379 : ℝ) = ((793 / 500 : ℝ) - 3 / 2) / (1 + 3 / 2 * (793 / 500 : ℝ)) by norm_num, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have htH : (a - 3 / 2) / (1 + 3 / 2 * a) ≤ (30 / 149 : ℝ) := by
    rw [show (30 / 149 : ℝ) = ((39 / 16 : ℝ) - 3 / 2) / (1 + 3 / 2 * (39 / 16 : ℝ)) by norm_num, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hvh := word_eq 0x3FEF730BD281F69B (8852218891597467 / 9007199254740992 : ℚ) (by decide +kernel)
  have hvl := word_eq 0x3C7007887AF0CBBD (4511882386918333 / 324518553658426726783156020576256 : ℚ) (by decide +kernel)
  have hc := atan_three_halves
  rw [hvh, hvl, abs_le] at hc
  push_cast at hc
  have hcL : (982793723247329 / 1000000000000000 : ℝ) ≤ Real.arctan (3 / 2) := by linarith [hc.2]
  have hcH : Real.arctan (3 / 2) ≤ (9827937232473291 / 10000000000000000 : ℝ) := by linarith [hc.1]
  have hat : Real.arctan ((a - 3 / 2) / (1 + 3 / 2 * a)) ≤ (30 / 149 : ℝ) := arctan_le_of_le_nonneg _ _ htH (by norm_num)
  have hal : (86 / 3379 : ℝ) - (86 / 3379 : ℝ) ^ 3 / (1 - (86 / 3379 : ℝ) ^ 2) ≤ Real.arctan ((a - 3 / 2) / (1 + 3 / 2 * a)) :=
    (arctan_ge_cubic _ (by norm_num) (by norm_num)).trans (Real.arctan_mono htL)
  rw [arctan_red2 a hapos]
  obtain ⟨hzf, htot⟩ := finish_err 0x3FEF730BD281F69B 0x3C7007887AF0CBBD _ (Real.arctan (3 / 2)) ((a - 3 / 2) / (1 + 3 / 2 * a)) _ _ (277449 / 1000000 : ℝ) (1391 / 100000000000000000000 : ℝ) (1184136005127 / 1000000000000 : ℝ) (12459 / 45035996273704960000 : ℝ)
    (by decide +kernel) (by decide +kernel) (by rw [hvh]; norm_num) (by rw [hvl]; norm_num)
    (by norm_num) ht (by norm_num [red2Err]) (by norm_num) (by norm_num) atan_three_halves
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [red2Err])
    (by norm_num [tailErr, red2Err]) 
  refine ⟨hzf, htot, ?_⟩
  rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]; norm_num; linarith

theorem case2_c (x : Float) (hx : Finite x.toBits) (h1 : (793 / 500 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (39 / 16 : ℝ)) :
    F64SignedRounding.WithinSteps 1 (Real.arctan |value x.toBits|)
      (atanTail (Float.ofBits 0x3FEF730BD281F69B) (Float.ofBits 0x3C7007887AF0CBBD)
        ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))).toBits := by
  obtain ⟨hzf, htot, hyB⟩ := case2_c_err x hx h1 h2
  have hB0 : 0 < value (UInt64.ofNat (1023 * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]
    positivity
  refine within_one_of_error _ _ 1023 (by norm_num) _ hzf htot ?_ (by norm_num) ?_
  all_goals
    generalize value (UInt64.ofNat (1023 * 2 ^ 52)) = B at hyB hB0 ⊢
    linarith

theorem case3_err (x : Float) (hx : Finite x.toBits) (h1 : (39 / 16 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (73786976294838206464 : ℝ)) :
    Finite (atanTail (Float.ofBits 0x3FF921FB54442D18) (Float.ofBits 0x3C91A62633145C07)
        (-1.0 / x.abs)).toBits ∧
      |value (atanTail (Float.ofBits 0x3FF921FB54442D18) (Float.ofBits 0x3C91A62633145C07)
        (-1.0 / x.abs)).toBits - Real.arctan (|value x.toBits|)| ≤ (25981 / 90071992547409920000 : ℝ) ∧
      value (UInt64.ofNat (1023 * 2 ^ 52)) + (25981 / 90071992547409920000 : ℝ) + 1 / 2 ^ 52 ≤ Real.arctan |value x.toBits| := by
  set a := |value x.toBits| with ha
  have hapos : 0 < a := by linarith
  have ht := reduce3 x hx (39 / 16 : ℝ) (73786976294838206464 : ℝ) (by norm_num) h1 h2 (by norm_num)
  have htL : (-16 / 39 : ℝ) ≤ -1 / a := by
    rw [show (-16 / 39 : ℝ) = -1 / (39 / 16 : ℝ) by norm_num, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have htH : -1 / a ≤ (-1 / 73786976294838206464 : ℝ) := by
    rw [show (-1 / 73786976294838206464 : ℝ) = -1 / (73786976294838206464 : ℝ) by norm_num, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hvh := word_eq 0x3FF921FB54442D18 (884279719003555 / 562949953421312 : ℚ) (by decide +kernel)
  have hvl := word_eq 0x3C91A62633145C07 (4967757600021511 / 81129638414606681695789005144064 : ℚ) (by decide +kernel)
  have hc := atan_inf
  rw [hvh, hvl, abs_le] at hc
  push_cast at hc
  have hcL : (7853981633974483 / 5000000000000000 : ℝ) ≤ (Real.pi / 2) := by linarith [hc.2]
  have hcH : (Real.pi / 2) ≤ (15707963267948967 / 10000000000000000 : ℝ) := by linarith [hc.1]
  have hat : Real.arctan (-1 / a) ≤ 0 := arctan_le_of_le_nonpos _ _ htH (by norm_num)
  have hal : (-16 / 39 : ℝ) ≤ Real.arctan (-1 / a) := le_arctan_of_le_nonpos _ _ htL (by norm_num)
  rw [arctan_red3 a hapos]
  obtain ⟨hzf, htot⟩ := finish_err 0x3FF921FB54442D18 0x3C91A62633145C07 _ (Real.pi / 2) (-1 / a) _ _ (410257 / 1000000 : ℝ) (1531 / 25000000000000000000 : ℝ) (314159265359 / 200000000000 : ℝ) (25981 / 90071992547409920000 : ℝ)
    (by decide +kernel) (by decide +kernel) (by rw [hvh]; norm_num) (by rw [hvl]; norm_num)
    (by norm_num) ht (by norm_num [red3Err]) (by norm_num) (by norm_num) atan_inf
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [red3Err])
    (by norm_num [tailErr, red3Err]) 
  refine ⟨hzf, htot, ?_⟩
  rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]; norm_num; linarith

theorem case3 (x : Float) (hx : Finite x.toBits) (h1 : (39 / 16 : ℝ) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (73786976294838206464 : ℝ)) :
    F64SignedRounding.WithinSteps 1 (Real.arctan |value x.toBits|)
      (atanTail (Float.ofBits 0x3FF921FB54442D18) (Float.ofBits 0x3C91A62633145C07)
        (-1.0 / x.abs)).toBits := by
  obtain ⟨hzf, htot, hyB⟩ := case3_err x hx h1 h2
  have hB0 : 0 < value (UInt64.ofNat (1023 * 2 ^ 52)) := by
    rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]
    positivity
  refine within_one_of_error _ _ 1023 (by norm_num) _ hzf htot ?_ (by norm_num) ?_
  all_goals
    generalize value (UInt64.ofNat (1023 * 2 ^ 52)) = B at hyB hB0 ⊢
    linarith

#print axioms finish
#print axioms case0_low
#print axioms case0_high
#print axioms case1_low
#print axioms case1_high
#print axioms case2_a
#print axioms case2_b
#print axioms case2_c
#print axioms case3

end Library.Numerics.Float64.Atan.AtanTheoremCases
