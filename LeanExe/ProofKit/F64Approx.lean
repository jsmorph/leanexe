import LeanExe.ProofKit.F64ArithmeticBounds
import LeanExe.ProofKit.F64SqrtBounds
import LeanExe.ProofKit.F64SignedRounding
import LeanExe.ProofKit.F64FullStep
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64PositiveSpacing
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.PolyBound

/-!
Error tracking for straight-line binary64 code.  `Approx w v e` states that the word `w` is finite
and its value lies within `e` of the real number `v`.  Each rounded operation on approximations gives
an approximation of the exact operation on the real numbers, with the input errors propagated and
the rounding error added, from the relative bounds of `F64AddBounds`, `F64MulBounds`,
`F64DivBounds`, and `F64SqrtBounds`.  The hypotheses ask for magnitude bounds that the caller
discharges with `norm_num` or `linarith`.  `FApprox` states the same for a Lean `Float`, and its
lemmas follow the `Float` operations through `F64Bits`.

`within_one_of_error` turns a total error into one representable step: when `y` and the result lie
at or above the start `B` of binade `n`, an error below one and a half spacings of that binade,
`3 B / 2 ^ 53`, puts the result within one step of the nearest-even reference of `y`.
-/

namespace LeanExe.ProofKit.F64Approx
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

/-- The word `w` is finite and within `e` of `v`. -/
def Approx (w : UInt64) (v e : ℝ) : Prop := Finite w ∧ |value w - v| ≤ e

theorem Approx.mag {w : UInt64} {v e : ℝ} (h : Approx w v e) : |value w| ≤ |v| + e := by
  have := abs_sub_abs_le_abs_sub (value w) v
  linarith [h.2]

theorem Approx.mono {w : UInt64} {v e e' : ℝ} (h : Approx w v e) (he : e ≤ e') :
    Approx w v e' := ⟨h.1, h.2.trans he⟩

theorem Approx.congr {w : UInt64} {v v' e : ℝ} (h : Approx w v e) (hv : v = v') :
    Approx w v' e := hv ▸ h

theorem Approx.lower {w : UInt64} {v e : ℝ} (h : Approx w v e) : v - e ≤ value w := by
  have := (abs_le.mp h.2).1
  linarith

theorem Approx.upper {w : UInt64} {v e : ℝ} (h : Approx w v e) : value w ≤ v + e := by
  have := (abs_le.mp h.2).2
  linarith

theorem approx_self (w : UInt64) (hw : Finite w) : Approx w (value w) 0 :=
  ⟨hw, by simp⟩

theorem approx_add {a b : UInt64} {va vb ea eb : ℝ} (ha : Approx a va ea) (hb : Approx b vb eb)
    (B : ℝ) (hB : |va + vb| + (ea + eb) ≤ B) (hBmax : B < 2 ^ 1023) :
    Approx (Wasm.IEEE64.add a b) (va + vb) (ea + eb + B / 2 ^ 53) := by
  have hsum : |(value a + value b) - (va + vb)| ≤ ea + eb := by
    rw [show (value a + value b) - (va + vb) = (value a - va) + (value b - vb) by ring]
    exact (abs_add_le _ _).trans (add_le_add ha.2 hb.2)
  have hm : |value a + value b| ≤ B := by
    have := abs_sub_abs_le_abs_sub (value a + value b) (va + vb)
    linarith
  have hr := F64AddBounds.add_real_relative a b ha.1 hb.1 (hm.trans_lt hBmax)
  refine ⟨hr.1, ?_⟩
  have hu : unitRoundoff64 * |value a + value b| ≤ B / 2 ^ 53 := by
    rw [unitRoundoff64, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hm (by positivity)
  calc |value (Wasm.IEEE64.add a b) - (va + vb)|
      ≤ |value (Wasm.IEEE64.add a b) - (value a + value b)| +
          |(value a + value b) - (va + vb)| := abs_sub_le _ _ _
    _ ≤ B / 2 ^ 53 + (ea + eb) := add_le_add (hr.2.trans hu) hsum
    _ = ea + eb + B / 2 ^ 53 := by ring

theorem approx_sub {a b : UInt64} {va vb ea eb : ℝ} (ha : Approx a va ea) (hb : Approx b vb eb)
    (B : ℝ) (hB : |va - vb| + (ea + eb) ≤ B) (hBmax : B < 2 ^ 1023) :
    Approx (Wasm.IEEE64.sub a b) (va - vb) (ea + eb + B / 2 ^ 53) := by
  have hdiff : |(value a - value b) - (va - vb)| ≤ ea + eb := by
    rw [show (value a - value b) - (va - vb) = (value a - va) + -(value b - vb) by ring]
    exact (abs_add_le _ _).trans (add_le_add ha.2 (by rw [abs_neg]; exact hb.2))
  have hm : |value a - value b| ≤ B := by
    have := abs_sub_abs_le_abs_sub (value a - value b) (va - vb)
    linarith
  have hr := F64AddBounds.sub_real_relative a b ha.1 hb.1 (hm.trans_lt hBmax)
  refine ⟨hr.1, ?_⟩
  have hu : unitRoundoff64 * |value a - value b| ≤ B / 2 ^ 53 := by
    rw [unitRoundoff64, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hm (by positivity)
  calc |value (Wasm.IEEE64.sub a b) - (va - vb)|
      ≤ |value (Wasm.IEEE64.sub a b) - (value a - value b)| +
          |(value a - value b) - (va - vb)| := abs_sub_le _ _ _
    _ ≤ B / 2 ^ 53 + (ea + eb) := add_le_add (hr.2.trans hu) hdiff
    _ = ea + eb + B / 2 ^ 53 := by ring

theorem approx_mul {a b : UInt64} {va vb ea eb : ℝ} (ha : Approx a va ea) (hb : Approx b vb eb)
    (Ma Mb : ℝ) (hMa : |va| ≤ Ma) (hMb : |vb| ≤ Mb) (B : ℝ) (hB : (Ma + ea) * (Mb + eb) ≤ B)
    (hBmax : B < 2 ^ 1022) :
    Approx (Wasm.IEEE64.mul a b) (va * vb)
      (ea * Mb + Ma * eb + ea * eb + B / 2 ^ 53 + 1 / 2 ^ 1075) := by
  have hea : 0 ≤ ea := (abs_nonneg _).trans ha.2
  have heb : 0 ≤ eb := (abs_nonneg _).trans hb.2
  have hA : |value a| ≤ Ma + ea := ha.mag.trans (by linarith)
  have hBv : |value b| ≤ Mb + eb := hb.mag.trans (by linarith)
  have hprod : |value a * value b - va * vb| ≤ ea * Mb + Ma * eb + ea * eb := by
    rw [show value a * value b - va * vb =
      (value a - va) * value b + va * (value b - vb) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |value a - va| * |value b| ≤ ea * (Mb + eb) :=
      mul_le_mul ha.2 hBv (abs_nonneg _) hea
    have h2 : |va| * |value b - vb| ≤ Ma * eb :=
      mul_le_mul hMa hb.2 (abs_nonneg _) ((abs_nonneg _).trans hMa)
    linarith
  have hm : |value a * value b| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul hA hBv (abs_nonneg _) ((abs_nonneg _).trans hA)).trans hB
  have hr := F64MulBounds.mul_real_mixed a b ha.1 hb.1 (hm.trans_lt hBmax)
  refine ⟨hr.1, ?_⟩
  have hu : unitRoundoff64 * |value a * value b| + multiplicationUnderflowEpsilon ≤
      B / 2 ^ 53 + 1 / 2 ^ 1075 := by
    rw [unitRoundoff64, multiplicationUnderflowEpsilon, one_div_mul_eq_div]
    gcongr
  calc |value (Wasm.IEEE64.mul a b) - va * vb|
      ≤ |value (Wasm.IEEE64.mul a b) - value a * value b| +
          |value a * value b - va * vb| := abs_sub_le _ _ _
    _ ≤ (B / 2 ^ 53 + 1 / 2 ^ 1075) + (ea * Mb + Ma * eb + ea * eb) :=
        add_le_add (hr.2.trans hu) hprod
    _ = ea * Mb + Ma * eb + ea * eb + B / 2 ^ 53 + 1 / 2 ^ 1075 := by ring

theorem approx_div {a b : UInt64} {va vb ea eb : ℝ} (ha : Approx a va ea) (hb : Approx b vb eb)
    (Ma mb : ℝ) (hMa : |va| ≤ Ma) (hmb : mb ≤ |vb|) (hebm : eb < mb) (B : ℝ)
    (hB : (Ma + ea) / (mb - eb) ≤ B) (hBmax : B < 2 ^ 1022) :
    Approx (Wasm.IEEE64.div a b) (va / vb)
      ((ea + Ma * eb / mb) / (mb - eb) + B / 2 ^ 53 + 1 / 2 ^ 1075) := by
  have hea : 0 ≤ ea := (abs_nonneg _).trans ha.2
  have heb : 0 ≤ eb := (abs_nonneg _).trans hb.2
  have hMa0 : 0 ≤ Ma := (abs_nonneg _).trans hMa
  have hmb0 : 0 < mb := lt_of_le_of_lt heb hebm
  have hd0 : 0 < mb - eb := by linarith
  have hvb : 0 < |vb| := lt_of_lt_of_le hmb0 hmb
  have hbl : mb - eb ≤ |value b| := by
    have := abs_sub_abs_le_abs_sub vb (value b)
    rw [abs_sub_comm] at this
    linarith [hb.2]
  have hb0 : 0 < |value b| := lt_of_lt_of_le hd0 hbl
  have hA : |value a| ≤ Ma + ea := ha.mag.trans (by linarith)
  have hquot : |value a / value b - va / vb| ≤ (ea + Ma * eb / mb) / (mb - eb) := by
    have hbne : value b ≠ 0 := abs_pos.mp hb0
    have hvbne : vb ≠ 0 := abs_pos.mp hvb
    rw [show value a / value b - va / vb =
      ((value a - va) + va * (vb - value b) / vb) / value b by field_simp; ring]
    rw [abs_div]
    apply div_le_div₀ (add_nonneg hea (div_nonneg (mul_nonneg hMa0 heb) hmb0.le)) _ hd0 hbl
    refine (abs_add_le _ _).trans (add_le_add ha.2 ?_)
    rw [abs_div, abs_mul]
    apply div_le_div₀ (mul_nonneg hMa0 heb) _ hmb0 hmb
    exact mul_le_mul hMa (by rw [abs_sub_comm]; exact hb.2) (abs_nonneg _) hMa0
  have hm : |value a / value b| ≤ B := by
    rw [abs_div]
    exact (div_le_div₀ (by linarith) hA hd0 hbl).trans hB
  have hmag : Wasm.IEEE64.scaledMagnitude b ≠ 0 := by
    intro h0
    have : value b = 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, h0]
      split <;> simp
    rw [this, abs_zero] at hb0
    exact lt_irrefl _ hb0
  have hr := F64DivBounds.div_real_mixed a b ha.1 hb.1 hmag (hm.trans_lt hBmax)
  refine ⟨hr.1, ?_⟩
  have hu : unitRoundoff64 * |value a / value b| + multiplicationUnderflowEpsilon ≤
      B / 2 ^ 53 + 1 / 2 ^ 1075 := by
    rw [unitRoundoff64, multiplicationUnderflowEpsilon, one_div_mul_eq_div]
    gcongr
  calc |value (Wasm.IEEE64.div a b) - va / vb|
      ≤ |value (Wasm.IEEE64.div a b) - value a / value b| +
          |value a / value b - va / vb| := abs_sub_le _ _ _
    _ ≤ (B / 2 ^ 53 + 1 / 2 ^ 1075) + (ea + Ma * eb / mb) / (mb - eb) :=
        add_le_add (hr.2.trans hu) hquot
    _ = (ea + Ma * eb / mb) / (mb - eb) + B / 2 ^ 53 + 1 / 2 ^ 1075 := by ring

theorem approx_sqrt {a : UInt64} {va ea : ℝ} (ha : Approx a va ea) (m M : ℝ) (hm : 0 < m)
    (hmv : m ≤ va) (heam : ea < m) (hM : va ≤ M) (S : ℝ) (hS : Real.sqrt (M + ea) ≤ S) :
    Approx (Wasm.IEEE64.sqrt a) (Real.sqrt va) (ea / Real.sqrt m + S / 2 ^ 53) := by
  have hea : 0 ≤ ea := (abs_nonneg _).trans ha.2
  have hpos : 0 < value a := by linarith [ha.lower]
  have hmagpos : 0 < Wasm.IEEE64.scaledMagnitude a := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude a) with h0 | h0
    · have : value a = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h0]
        split <;> simp
      linarith
    · exact h0
  have hsign : Wasm.IEEE64.sign a = false := by
    cases hs : Wasm.IEEE64.sign a
    · rfl
    · have := (F64Magnitude.sign_value a hmagpos).mp hs
      linarith
  have hr := F64SqrtBounds.sqrt_real_relative a ha.1 hmagpos.ne' hsign
  refine ⟨hr.1, ?_⟩
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsv : Real.sqrt m ≤ Real.sqrt va := Real.sqrt_le_sqrt hmv
  have hdiff : |Real.sqrt (value a) - Real.sqrt va| ≤ ea / Real.sqrt m := by
    have hsa : 0 ≤ Real.sqrt (value a) := Real.sqrt_nonneg _
    have hsum : Real.sqrt m ≤ Real.sqrt (value a) + Real.sqrt va := by linarith
    have hprod : (Real.sqrt (value a) - Real.sqrt va) * (Real.sqrt (value a) + Real.sqrt va) =
        value a - va := by
      have h1 := Real.sq_sqrt hpos.le
      have h2 := Real.sq_sqrt (show 0 ≤ va by linarith)
      linear_combination h1 - h2
    rw [le_div_iff₀ hsm]
    calc |Real.sqrt (value a) - Real.sqrt va| * Real.sqrt m ≤
        |Real.sqrt (value a) - Real.sqrt va| * (Real.sqrt (value a) + Real.sqrt va) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = |value a - va| := by
          rw [← hprod, abs_mul, abs_of_nonneg
            (show (0 : ℝ) ≤ Real.sqrt (value a) + Real.sqrt va by positivity)]
      _ ≤ ea := ha.2
  have hsq : Real.sqrt (value a) ≤ S :=
    (Real.sqrt_le_sqrt (by linarith [ha.upper])).trans hS
  have hu : unitRoundoff64 * Real.sqrt (value a) ≤ S / 2 ^ 53 := by
    rw [unitRoundoff64, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hsq (by positivity)
  calc |value (Wasm.IEEE64.sqrt a) - Real.sqrt va|
      ≤ |value (Wasm.IEEE64.sqrt a) - Real.sqrt (value a)| +
          |Real.sqrt (value a) - Real.sqrt va| := abs_sub_le _ _ _
    _ ≤ S / 2 ^ 53 + ea / Real.sqrt m := add_le_add (hr.2.trans hu) hdiff
    _ = ea / Real.sqrt m + S / 2 ^ 53 := by ring

theorem approx_negate {a : UInt64} {va ea : ℝ} (ha : Approx a va ea) :
    Approx (Wasm.IEEE64.negate a) (-va) ea := by
  have h := F64Magnitude.negate_value a ha.1
  refine ⟨h.1, ?_⟩
  rw [h.2, show -value a - -va = -(value a - va) by ring, abs_neg]
  exact ha.2

/-- `Approx` for a Lean float. -/
def FApprox (x : Float) (v e : ℝ) : Prop := Approx x.toBits v e

theorem fapprox_add {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (B : ℝ) (hB : |va + vb| + (ea + eb) ≤ B) (hBmax : B < 2 ^ 1023) :
    FApprox (a + b) (va + vb) (ea + eb + B / 2 ^ 53) := by
  unfold FApprox
  rw [F64Bits.toBits_add]
  exact approx_add ha hb B hB hBmax

theorem fapprox_sub {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (B : ℝ) (hB : |va - vb| + (ea + eb) ≤ B) (hBmax : B < 2 ^ 1023) :
    FApprox (a - b) (va - vb) (ea + eb + B / 2 ^ 53) := by
  unfold FApprox
  rw [F64Bits.toBits_sub]
  exact approx_sub ha hb B hB hBmax

theorem fapprox_mul {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (Ma Mb : ℝ) (hMa : |va| ≤ Ma) (hMb : |vb| ≤ Mb) (B : ℝ)
    (hB : (Ma + ea) * (Mb + eb) ≤ B) (hBmax : B < 2 ^ 1022) :
    FApprox (a * b) (va * vb) (ea * Mb + Ma * eb + ea * eb + B / 2 ^ 53 + 1 / 2 ^ 1075) := by
  unfold FApprox
  rw [F64Bits.toBits_mul]
  exact approx_mul ha hb Ma Mb hMa hMb B hB hBmax

theorem fapprox_div {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (Ma mb : ℝ) (hMa : |va| ≤ Ma) (hmb : mb ≤ |vb|) (hebm : eb < mb)
    (B : ℝ) (hB : (Ma + ea) / (mb - eb) ≤ B) (hBmax : B < 2 ^ 1022) :
    FApprox (a / b) (va / vb) ((ea + Ma * eb / mb) / (mb - eb) + B / 2 ^ 53 + 1 / 2 ^ 1075) := by
  unfold FApprox
  rw [F64Bits.toBits_div]
  exact approx_div ha hb Ma mb hMa hmb hebm B hB hBmax

theorem fapprox_sqrt {a : Float} {va ea : ℝ} (ha : FApprox a va ea) (m M : ℝ) (hm : 0 < m)
    (hmv : m ≤ va) (heam : ea < m) (hM : va ≤ M) (S : ℝ) (hS : Real.sqrt (M + ea) ≤ S) :
    FApprox a.sqrt (Real.sqrt va) (ea / Real.sqrt m + S / 2 ^ 53) := by
  unfold FApprox
  rw [F64Bits.toBits_sqrt]
  exact approx_sqrt ha m M hm hmv heam hM S hS

theorem fapprox_neg {a : Float} {va ea : ℝ} (ha : FApprox a va ea) :
    FApprox (-a) (-va) ea := by
  unfold FApprox
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, not_nan_of_finite ha.1]
  simp only [Bool.false_eq_true, ite_false]
  exact approx_negate ha

theorem fapprox_ofBits (w : UInt64) (hw : Finite w) :
    FApprox (Float.ofBits w) (value w) 0 := by
  unfold FApprox
  rw [F64Bits.toBits_ofBits, not_nan_of_finite hw]
  simp only [Bool.false_eq_true, ite_false]
  exact approx_self w hw

/-- One step from a total error: `y` and the word lie at or above the start `B` of binade `n`, and
the error is below one and a half spacings of that binade. -/
theorem within_one_of_error (y : ℝ) (c : UInt64) (n : ℕ) (hn : n < 2047) (E : ℝ)
    (hcf : Finite c) (hc : |value c - y| ≤ E)
    (hy : value (UInt64.ofNat (n * 2 ^ 52)) + E ≤ y)
    (hE : E < 3 * ((2 : ℝ) ^ (n - 1) / (2 : ℝ) ^ 1074) / 2) (hpos : 0 < y - E) :
    F64SignedRounding.WithinSteps 1 y c := by
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hc
  have hyB : value (UInt64.ofNat (n * 2 ^ 52)) ≤ y := by linarith
  have hcl : value (UInt64.ofNat (n * 2 ^ 52)) ≤ value c := by
    have := (abs_le.mp hc).1
    linarith
  have hcpos : 0 < value c := by
    have := (abs_le.mp hc).1
    linarith
  have hmagpos : 0 < Wasm.IEEE64.scaledMagnitude c := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude c) with h0 | h0
    · have : value c = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h0]
        split <;> simp
      linarith
    · exact h0
  have hsign : Wasm.IEEE64.sign c = false := by
    cases hs : Wasm.IEEE64.sign c
    · rfl
    · have := (F64Magnitude.sign_value c hmagpos).mp hs
      linarith
  have hlim := F64Magnitude.lt_limit_of_finite c hcf hsign
  have hc63 : c.toNat < 2 ^ 63 := hlim.trans (by decide)
  have hinf : value c ≤ value (UInt64.ofNat (2047 * 2 ^ 52)) := by
    apply (F64PositiveOrder.value_le_iff hc63 (by decide)).mpr
    have : (UInt64.ofNat (2047 * 2 ^ 52)).toNat = 2047 * 2 ^ 52 := by decide
    rw [this]
    calc c.toNat ≤ F64NearestNonnegative.limit := hlim.le
      _ = 2047 * 2 ^ 52 := by decide
  have hstep := F64FullStep.one_step_binades y c n 2047 hn le_rfl hyB (fun h => absurd h
    (lt_irrefl _)) hc63 hcl hinf (lt_of_le_of_lt hc hE)
  have hy0 : 0 ≤ y := by linarith
  exact F64SignedRounding.within_of_nonneg 1 y hy0 c hlim.le hstep.1 hstep.2


/-- `w` approximates `v` at the positive scale `s ≤ 1`: `|v| ≤ M s` and the error is at most
`e s`.  The numbers `M` and `e` stay numerals while the scale carries the size of the input. -/
def SApprox (w : UInt64) (v s M e : ℝ) : Prop :=
  0 < s ∧ s ≤ 1 ∧ |v| ≤ M * s ∧ Approx w v (e * s)

theorem SApprox.approx {w : UInt64} {v s M e : ℝ} (h : SApprox w v s M e) :
    Approx w v (e * s) := h.2.2.2

theorem SApprox.e_nonneg {w : UInt64} {v s M e : ℝ} (h : SApprox w v s M e) : 0 ≤ e := by
  have h0 := (abs_nonneg _).trans h.2.2.2.2
  exact nonneg_of_mul_nonneg_left h0 h.1

theorem SApprox.M_nonneg {w : UInt64} {v s M e : ℝ} (h : SApprox w v s M e) : 0 ≤ M := by
  have h0 := (abs_nonneg _).trans h.2.2.1
  exact nonneg_of_mul_nonneg_left h0 h.1

/-- A larger scale: `s ≤ k s'` gives the bounds `M k` and `e k` at `s'`. -/
theorem SApprox.rescale {w : UInt64} {v s M e : ℝ} (h : SApprox w v s M e) (s' k : ℝ)
    (hs' : 0 < s') (hs'1 : s' ≤ 1) (hk : s ≤ k * s') :
    SApprox w v s' (M * k) (e * k) := by
  have hM := h.M_nonneg
  have he := h.e_nonneg
  refine ⟨hs', hs'1, ?_, h.approx.mono ?_⟩
  · calc |v| ≤ M * s := h.2.2.1
      _ ≤ M * (k * s') := mul_le_mul_of_nonneg_left hk hM
      _ = M * k * s' := by ring
  · calc e * s ≤ e * (k * s') := mul_le_mul_of_nonneg_left hk he
      _ = e * k * s' := by ring

theorem SApprox.mono {w : UInt64} {v s M e M' e' : ℝ} (h : SApprox w v s M e) (hM : M ≤ M')
    (he : e ≤ e') : SApprox w v s M' e' :=
  ⟨h.1, h.2.1, h.2.2.1.trans (mul_le_mul_of_nonneg_right hM h.1.le),
    h.approx.mono (mul_le_mul_of_nonneg_right he h.1.le)⟩

theorem sapprox_add {a b : UInt64} {va vb s Ma Mb ea eb : ℝ} (ha : SApprox a va s Ma ea)
    (hb : SApprox b vb s Mb eb) (M : ℝ) (hM : |va + vb| ≤ M * s)
    (hov : M + (ea + eb) < 2 ^ 1023) :
    SApprox (Wasm.IEEE64.add a b) (va + vb) s M (ea + eb + (M + (ea + eb)) / 2 ^ 53) := by
  refine ⟨ha.1, ha.2.1, hM, ?_⟩
  have h := approx_add ha.approx hb.approx ((M + (ea + eb)) * s) (by linarith)
    (lt_of_le_of_lt (mul_le_of_le_one_right (by linarith [abs_nonneg (va + vb),
      ha.e_nonneg, hb.e_nonneg, (show 0 ≤ M by
        have := (abs_nonneg _).trans hM; exact nonneg_of_mul_nonneg_left this ha.1)]) ha.2.1) hov)
  exact h.mono (le_of_eq (by ring))

theorem sapprox_sub {a b : UInt64} {va vb s Ma Mb ea eb : ℝ} (ha : SApprox a va s Ma ea)
    (hb : SApprox b vb s Mb eb) (M : ℝ) (hM : |va - vb| ≤ M * s)
    (hov : M + (ea + eb) < 2 ^ 1023) :
    SApprox (Wasm.IEEE64.sub a b) (va - vb) s M (ea + eb + (M + (ea + eb)) / 2 ^ 53) := by
  refine ⟨ha.1, ha.2.1, hM, ?_⟩
  have hM0 : 0 ≤ M := by
    have := (abs_nonneg _).trans hM
    exact nonneg_of_mul_nonneg_left this ha.1
  have h := approx_sub ha.approx hb.approx ((M + (ea + eb)) * s) (by linarith)
    (lt_of_le_of_lt (mul_le_of_le_one_right (by linarith [ha.e_nonneg, hb.e_nonneg])
      ha.2.1) hov)
  exact h.mono (le_of_eq (by ring))

theorem sapprox_mul {a b : UInt64} {va vb sa sb Ma Mb ea eb : ℝ} (ha : SApprox a va sa Ma ea)
    (hb : SApprox b vb sb Mb eb) (η : ℝ) (hη : 1 / 2 ^ 1075 ≤ η * (sa * sb))
    (hov : (Ma + ea) * (Mb + eb) < 2 ^ 1022) :
    SApprox (Wasm.IEEE64.mul a b) (va * vb) (sa * sb) (Ma * Mb)
      (ea * Mb + Ma * eb + ea * eb + (Ma + ea) * (Mb + eb) / 2 ^ 53 + η) := by
  have hMa := ha.M_nonneg
  have hMb := hb.M_nonneg
  have hea := ha.e_nonneg
  have heb := hb.e_nonneg
  have hs : 0 < sa * sb := mul_pos ha.1 hb.1
  have hs1 : sa * sb ≤ 1 := mul_le_one₀ ha.2.1 hb.1.le hb.2.1
  refine ⟨hs, hs1, ?_, ?_⟩
  · rw [abs_mul]
    calc |va| * |vb| ≤ (Ma * sa) * (Mb * sb) :=
          mul_le_mul ha.2.2.1 hb.2.2.1 (abs_nonneg _) (mul_nonneg hMa ha.1.le)
      _ = Ma * Mb * (sa * sb) := by ring
  · have h := approx_mul ha.approx hb.approx (Ma * sa) (Mb * sb) ha.2.2.1 hb.2.2.1
      ((Ma + ea) * (Mb + eb) * (sa * sb)) (le_of_eq (by ring))
      (lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) hs1) hov)
    refine h.mono ?_
    have : ea * sa * (Mb * sb) + Ma * sa * (eb * sb) + ea * sa * (eb * sb) +
        (Ma + ea) * (Mb + eb) * (sa * sb) / 2 ^ 53 =
        (ea * Mb + Ma * eb + ea * eb + (Ma + ea) * (Mb + eb) / 2 ^ 53) * (sa * sb) := by ring
    rw [this, add_mul]
    linarith

theorem sapprox_div {a b : UInt64} {va vb s Ma Mb ea eb : ℝ} (ha : SApprox a va s Ma ea)
    (hb : SApprox b vb 1 Mb eb) (mb : ℝ) (hmb : mb ≤ |vb|) (hebm : eb < mb) (η : ℝ)
    (hη : 1 / 2 ^ 1075 ≤ η * s) (hov : (Ma + ea) / (mb - eb) < 2 ^ 1022) :
    SApprox (Wasm.IEEE64.div a b) (va / vb) s (Ma / mb)
      ((ea + Ma * eb / mb) / (mb - eb) + (Ma + ea) / (mb - eb) / 2 ^ 53 + η) := by
  have hMa := ha.M_nonneg
  have hea := ha.e_nonneg
  have heb := hb.e_nonneg
  have hmb0 : 0 < mb := lt_of_le_of_lt heb hebm
  have hd : 0 < mb - eb := by linarith
  refine ⟨ha.1, ha.2.1, ?_, ?_⟩
  · rw [abs_div]
    calc |va| / |vb| ≤ (Ma * s) / mb :=
          div_le_div₀ (mul_nonneg hMa ha.1.le) ha.2.2.1 hmb0 hmb
      _ = Ma / mb * s := by ring
  · have hb' : Approx b vb (eb * 1) := hb.approx
    rw [mul_one] at hb'
    have h := approx_div ha.approx hb' (Ma * s) mb ha.2.2.1 hmb hebm
      ((Ma + ea) / (mb - eb) * s) (le_of_eq (by ring))
      (lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) ha.2.1) hov)
    refine h.mono ?_
    have : (ea * s + Ma * s * eb / mb) / (mb - eb) + (Ma + ea) / (mb - eb) * s / 2 ^ 53 =
        ((ea + Ma * eb / mb) / (mb - eb) + (Ma + ea) / (mb - eb) / 2 ^ 53) * s := by
      field_simp
    rw [this, add_mul]
    linarith

theorem sapprox_negate {a : UInt64} {va s M e : ℝ} (ha : SApprox a va s M e) :
    SApprox (Wasm.IEEE64.negate a) (-va) s M e :=
  ⟨ha.1, ha.2.1, by rw [abs_neg]; exact ha.2.2.1, approx_negate ha.approx⟩

/-- `SApprox` for a Lean float. -/
def FSApprox (x : Float) (v s M e : ℝ) : Prop := SApprox x.toBits v s M e

theorem fsapprox_add {a b : Float} {va vb s Ma Mb ea eb : ℝ} (ha : FSApprox a va s Ma ea)
    (hb : FSApprox b vb s Mb eb) (M : ℝ) (hM : |va + vb| ≤ M * s)
    (hov : M + (ea + eb) < 2 ^ 1023) :
    FSApprox (a + b) (va + vb) s M (ea + eb + (M + (ea + eb)) / 2 ^ 53) := by
  unfold FSApprox
  rw [F64Bits.toBits_add]
  exact sapprox_add ha hb M hM hov

theorem fsapprox_sub {a b : Float} {va vb s Ma Mb ea eb : ℝ} (ha : FSApprox a va s Ma ea)
    (hb : FSApprox b vb s Mb eb) (M : ℝ) (hM : |va - vb| ≤ M * s)
    (hov : M + (ea + eb) < 2 ^ 1023) :
    FSApprox (a - b) (va - vb) s M (ea + eb + (M + (ea + eb)) / 2 ^ 53) := by
  unfold FSApprox
  rw [F64Bits.toBits_sub]
  exact sapprox_sub ha hb M hM hov

theorem fsapprox_mul {a b : Float} {va vb sa sb Ma Mb ea eb : ℝ} (ha : FSApprox a va sa Ma ea)
    (hb : FSApprox b vb sb Mb eb) (η : ℝ) (hη : 1 / 2 ^ 1075 ≤ η * (sa * sb))
    (hov : (Ma + ea) * (Mb + eb) < 2 ^ 1022) :
    FSApprox (a * b) (va * vb) (sa * sb) (Ma * Mb)
      (ea * Mb + Ma * eb + ea * eb + (Ma + ea) * (Mb + eb) / 2 ^ 53 + η) := by
  unfold FSApprox
  rw [F64Bits.toBits_mul]
  exact sapprox_mul ha hb η hη hov

theorem fsapprox_div {a b : Float} {va vb s Ma Mb ea eb : ℝ} (ha : FSApprox a va s Ma ea)
    (hb : FSApprox b vb 1 Mb eb) (mb : ℝ) (hmb : mb ≤ |vb|) (hebm : eb < mb) (η : ℝ)
    (hη : 1 / 2 ^ 1075 ≤ η * s) (hov : (Ma + ea) / (mb - eb) < 2 ^ 1022) :
    FSApprox (a / b) (va / vb) s (Ma / mb)
      ((ea + Ma * eb / mb) / (mb - eb) + (Ma + ea) / (mb - eb) / 2 ^ 53 + η) := by
  unfold FSApprox
  rw [F64Bits.toBits_div]
  exact sapprox_div ha hb mb hmb hebm η hη hov

theorem fsapprox_neg {a : Float} {va s M e : ℝ} (ha : FSApprox a va s M e) :
    FSApprox (-a) (-va) s M e := by
  unfold FSApprox
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, not_nan_of_finite ha.approx.1]
  simp only [Bool.false_eq_true, ite_false]
  exact sapprox_negate ha

theorem fsapprox_const (w : UInt64) (hw : Wasm.IEEE64.isFinite w = true) (M : ℝ)
    (hM : |value w| ≤ M) :
    FSApprox (Float.ofBits w) (value w) 1 M 0 := by
  refine ⟨one_pos, le_rfl, by rw [mul_one]; exact hM, ?_⟩
  have h := fapprox_ofBits w hw
  rw [zero_mul]
  exact h

theorem fsapprox_input (x : Float) (hx : Finite x.toBits) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hxs : |value x.toBits| ≤ s) : FSApprox x (value x.toBits) s 1 0 :=
  ⟨hs, hs1, by rw [one_mul]; exact hxs, by rw [zero_mul]; exact approx_self _ hx⟩


theorem fsapprox_add' {a b : Float} {va vb s Ma Mb ea eb : ℝ} (ha : FSApprox a va s Ma ea)
    (hb : FSApprox b vb s Mb eb) (hov : Ma + Mb + (ea + eb) < 2 ^ 1023) :
    FSApprox (a + b) (va + vb) s (Ma + Mb) (ea + eb + (Ma + Mb + (ea + eb)) / 2 ^ 53) :=
  fsapprox_add ha hb (Ma + Mb)
    ((abs_add_le _ _).trans (by rw [add_mul]; exact add_le_add ha.2.2.1 hb.2.2.1)) hov

theorem fsapprox_sub' {a b : Float} {va vb s Ma Mb ea eb : ℝ} (ha : FSApprox a va s Ma ea)
    (hb : FSApprox b vb s Mb eb) (hov : Ma + Mb + (ea + eb) < 2 ^ 1023) :
    FSApprox (a - b) (va - vb) s (Ma + Mb) (ea + eb + (Ma + Mb + (ea + eb)) / 2 ^ 53) :=
  fsapprox_sub ha hb (Ma + Mb)
    ((abs_sub _ _).trans (by rw [add_mul]; exact add_le_add ha.2.2.1 hb.2.2.1)) hov

theorem FSApprox.rescale {x : Float} {v s M e : ℝ} (h : FSApprox x v s M e) (s' k : ℝ)
    (hs' : 0 < s') (hs'1 : s' ≤ 1) (hk : s ≤ k * s') : FSApprox x v s' (M * k) (e * k) :=
  SApprox.rescale h s' k hs' hs'1 hk

theorem FSApprox.mono {x : Float} {v s M e M' e' : ℝ} (h : FSApprox x v s M e) (hM : M ≤ M')
    (he : e ≤ e') : FSApprox x v s M' e' :=
  SApprox.mono h hM he


theorem FSApprox.congr {x : Float} {v v' s M e : ℝ} (h : FSApprox x v s M e) (hv : v = v') :
    FSApprox x v' s M e := hv ▸ h

/-- A word's value within a rational bound, checked by the kernel. -/
theorem abs_value_le (w : UInt64) (M : ℚ) (h : PolyBound.qabs (PolyBound.ratOfWord w) ≤ M) :
    |value w| ≤ (M : ℝ) := by
  rw [← PolyBound.ratOfWord_cast, ← PolyBound.qabs_cast]
  exact_mod_cast h

/-- One step relative to the input's binade: `X` lies in binade `n ≥ 2`, `y` between `(1 - κ) X`
and `X`, and the result within `ρ X` of `y`, with `ρ ≤ (3/2) 2 ^ -53 (1 - κ - ρ)`. -/
theorem within_one_rel (y : ℝ) (c : UInt64) (X : ℝ) (n : ℕ) (hn2 : 2 ≤ n) (hn : n < 2047)
    (hX : value (UInt64.ofNat (n * 2 ^ 52)) ≤ X)
    (hX2 : X < 2 * value (UInt64.ofNat (n * 2 ^ 52))) (κ ρ : ℝ) (hκ0 : 0 ≤ κ) (hρ0 : 0 ≤ ρ)
    (hcf : Finite c) (hc : |value c - y| ≤ ρ * X) (hyl : (1 - κ) * X ≤ y)
    (hρ : ρ ≤ 3 / 2 / 2 ^ 53 * (1 - κ - ρ)) (hκ : κ + ρ < 1 / 3) :
    F64SignedRounding.WithinSteps 1 y c := by
  have hB := F64PositiveSpacing.boundary_value n (by omega) (by omega)
  set B := value (UInt64.ofNat (n * 2 ^ 52)) with hBdef
  have hB0 : 0 < B := by rw [hB]; positivity
  have hX0 : 0 < X := lt_of_lt_of_le hB0 hX
  have hρlt : ρ < 3 / 2 / 2 ^ 53 := by
    rcases eq_or_lt_of_le hρ0 with h | h
    · rw [← h]
      positivity
    · nlinarith
  have hρX : ρ * X ≤ 2 * ρ * B := by nlinarith
  have hsp : (2 : ℝ) ^ (n - 1) / (2 : ℝ) ^ 1074 = B / 2 ^ 52 := by
    rw [hB, show n + 51 = (n - 1) + 52 by omega, pow_add]
    field_simp
  by_cases hhi : B + ρ * X ≤ y
  · refine within_one_of_error y c n hn (ρ * X) hcf hc hhi ?_ (by linarith)
    rw [hsp]
    have : 2 * ρ * B < 2 * (3 / 2 / 2 ^ 53) * B := by nlinarith
    linarith
  · have hn0 : n - 1 < 2047 := by omega
    have hBl : value (UInt64.ofNat ((n - 1) * 2 ^ 52)) = B / 2 := by
      rw [F64PositiveSpacing.boundary_value (n - 1) (by omega) (by omega), hB,
        show n + 51 = (n - 1 + 51) + 1 by omega, pow_succ]
      ring
    have hsp' : (2 : ℝ) ^ (n - 1 - 1) / (2 : ℝ) ^ 1074 = B / 2 ^ 53 := by
      rw [hB, show n + 51 = (n - 1 - 1) + 53 by omega, pow_add]
      field_simp
    have hy' : y < B + ρ * X := lt_of_not_ge hhi
    have hk : 0 < 1 - κ - ρ := by linarith
    have hXB : X * (1 - κ - ρ) < B := by nlinarith
    have hρX' : ρ * X ≤ 3 / 2 / 2 ^ 53 * (X * (1 - κ - ρ)) := by
      have := mul_le_mul_of_nonneg_right hρ hX0.le
      linarith
    have hlow : (1 - κ) * B ≤ (1 - κ) * X := by
      apply mul_le_mul_of_nonneg_left hX
      linarith
    refine within_one_of_error y c (n - 1) hn0 (ρ * X) hcf hc ?_ ?_ (by nlinarith)
    · rw [hBl]
      have : 2 * ρ * B ≤ (1 / 2 - κ) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0.le
        linarith
      linarith
    · rw [hsp']
      have : 3 / 2 / 2 ^ 53 * (X * (1 - κ - ρ)) < 3 / 2 / 2 ^ 53 * B := by
        apply mul_lt_mul_of_pos_left hXB
        positivity
      linarith


/-- A negative result through its negation. -/
theorem within_of_negate (k : ℕ) (y : ℝ) (c : UInt64)
    (h : F64SignedRounding.WithinSteps k (-y) (Wasm.IEEE64.negate c)) :
    F64SignedRounding.WithinSteps k y c := (F64SignedRounding.within_negate k y c).mp h

/-- The binade of a normal word: its magnitude lies between the start of the binade of its
exponent field and twice that start. -/
theorem binade_bounds (x : UInt64) (hx : Finite x) (he : 1 ≤ Wasm.IEEE64.exponent x) :
    value (UInt64.ofNat (Wasm.IEEE64.exponent x * 2 ^ 52)) ≤ |value x| ∧
      |value x| < 2 * value (UInt64.ofNat (Wasm.IEEE64.exponent x * 2 ^ 52)) := by
  have he2 : Wasm.IEEE64.exponent x < 2047 := by
    have h := hx
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hb := F64PositiveSpacing.boundary_value (Wasm.IEEE64.exponent x) he (by omega)
  have hpow : (2 : ℝ) ^ (Wasm.IEEE64.exponent x + 51) / 2 ^ 1074 =
      (2 : ℝ) ^ ((Wasm.IEEE64.exponent x : ℤ) - 1023) := by
    rw [← zpow_natCast, ← zpow_natCast (2 : ℝ) 1074, ← zpow_sub₀ (by norm_num)]
    congr 1
    push_cast
    ring
  rw [hb, hpow]
  constructor
  · exact F64Magnitude.magnitude_ge x (Wasm.IEEE64.exponent x)
      ((Wasm.IEEE64.exponent x : ℤ) - 1023) he (by omega) (by ring) le_rfl
  · have h := F64Magnitude.magnitude_lt x (Wasm.IEEE64.exponent x + 1)
      ((Wasm.IEEE64.exponent x : ℤ) - 1022) (by omega) (by push_cast; ring) (by omega)
    calc |value x| < (2 : ℝ) ^ ((Wasm.IEEE64.exponent x : ℤ) - 1022) := h
      _ = 2 * (2 : ℝ) ^ ((Wasm.IEEE64.exponent x : ℤ) - 1023) := by
        rw [show (Wasm.IEEE64.exponent x : ℤ) - 1022 = ((Wasm.IEEE64.exponent x : ℤ) - 1023) + 1
          by ring, zpow_add_one₀ (by norm_num)]
        ring

#print axioms approx_add
#print axioms approx_sub
#print axioms approx_mul
#print axioms approx_div
#print axioms approx_sqrt
#print axioms approx_negate
#print axioms fapprox_neg
#print axioms fapprox_ofBits
#print axioms within_one_of_error
#print axioms sapprox_add
#print axioms sapprox_sub
#print axioms sapprox_mul
#print axioms sapprox_div
#print axioms fsapprox_neg
#print axioms within_one_rel

end LeanExe.ProofKit.F64Approx
