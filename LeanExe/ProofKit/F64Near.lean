import LeanExe.ProofKit.F64TwoSteps
import LeanExe.ProofKit.F64RoundNearest

/-!
A word that is a nearest rounding of a real within `E` of `y`.  The last operation of a computed
function rounds its exact value `S` to a nearest word, so a bound `|S - y| ≤ E` holds every error
except that rounding.  `Near.within_one` and `Near.within_two` turn the bound into one or two steps
without charging the rounding, `Near.shift` moves the target, and `Near.half` carries the bound
through an exact halving of the word.
-/

namespace LeanExe.ProofKit.F64Near
open CodeLib.IEEE64 F64Approx F64RoundNearest

set_option exponentiation.threshold 4096

/-- `c` is a nearest rounding of a real within `E` of `y`. -/
def Near (c : UInt64) (y E : ℝ) : Prop := ∃ S : ℝ, Rounded c S ∧ |S - y| ≤ E

theorem Near.mono {c : UInt64} {y E E' : ℝ} (h : Near c y E) (hE : E ≤ E') : Near c y E' :=
  let ⟨S, hS, hd⟩ := h
  ⟨S, hS, hd.trans hE⟩

theorem Near.shift {c : UInt64} {y E : ℝ} (h : Near c y E) (y' : ℝ) :
    Near c y' (E + |y - y'|) := by
  obtain ⟨S, hS, hd⟩ := h
  refine ⟨S, hS, ?_⟩
  have := abs_sub_le S y y'
  linarith

theorem near_sub {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea) (hb : FApprox b vb eb)
    (y E : ℝ) (hE : ea + eb + |va - vb - y| ≤ E) (hEy : E < |y|) (hyt : |y| + E < 2 ^ 1023) :
    Near (a - b).toBits y E := by
  have hc := (fapprox_diff_close ha hb y).trans hE
  refine ⟨_, ?_, hc⟩
  rw [F64Bits.toBits_sub]
  refine sub_rounded _ _ ha.1 hb.1 ?_ ?_
  · intro h0
    rw [h0, zero_sub, abs_neg] at hc
    linarith
  · have := abs_sub_abs_le_abs_sub (value a.toBits - value b.toBits) y
    linarith

theorem near_add {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea) (hb : FApprox b vb eb)
    (y E : ℝ) (hE : ea + eb + |va + vb - y| ≤ E) (hEy : E < |y|) (hyt : |y| + E < 2 ^ 1023) :
    Near (a + b).toBits y E := by
  have hc := (fapprox_sum_close ha hb y).trans hE
  refine ⟨_, ?_, hc⟩
  rw [F64Bits.toBits_add]
  refine add_rounded _ _ ha.1 hb.1 ?_ ?_
  · intro h0
    rw [h0, zero_sub, abs_neg] at hc
    linarith
  · have := abs_sub_abs_le_abs_sub (value a.toBits + value b.toBits) y
    linarith

/-- One step when `|y|` lies `E` above the start of binade `n` and `E` is below its spacing. -/
theorem Near.within_one {c : UInt64} {y E : ℝ} (h : Near c y E) (n : ℕ) (hn1 : 1 ≤ n)
    (hn : n < 2047) (hy : value (UInt64.ofNat (n * 2 ^ 52)) + E ≤ |y|)
    (hE : E < (2 : ℝ) ^ (n - 1) / 2 ^ 1074) (hyt : |y| < 2 ^ 1023) :
    F64SignedRounding.WithinSteps 1 y c := by
  obtain ⟨S, hS, hd⟩ := h
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hd
  have h1 := abs_sub_abs_le_abs_sub y S
  rw [abs_sub_comm] at h1
  exact within_one_of_rounded c S y hS n hn1 hn (by linarith) (by linarith)
    (lt_of_le_of_lt hd hE) hyt

theorem Near.within_one_rel {c : UInt64} {y ρ : ℝ} (h : Near c y (ρ * |y|)) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 1 / (2 ^ 53 + 1)) (hy : 1 / 2 ^ 1021 ≤ |y|) (hyt : |y| < 2 ^ 1022) :
    F64SignedRounding.WithinSteps 1 y c :=
  let ⟨S, hS, hd⟩ := h
  within_one_of_rounded_rel c S y hS ρ hρ0 hρ hd hy hyt

/-- Two steps when `|y|` lies `E` above the start of binade `n` and `E` is below two of its
spacings. -/
theorem Near.within_two {c : UInt64} {y E : ℝ} (h : Near c y E) (n : ℕ) (hn1 : 1 ≤ n)
    (hn : n < 2047) (hy : value (UInt64.ofNat (n * 2 ^ 52)) + E ≤ |y|)
    (hE : E < 2 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074)) (hyt : |y| < 2 ^ 1023) :
    F64SignedRounding.WithinSteps 2 y c := by
  obtain ⟨S, hS, hd⟩ := h
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hd
  have h1 := abs_sub_abs_le_abs_sub y S
  rw [abs_sub_comm] at h1
  exact F64TwoSteps.within_two_of_rounded c S y hS n hn1 hn (by linarith) (by linarith)
    (lt_of_le_of_lt hd hE) hyt

/-- Two steps from a relative bound `E ≤ ρ |y|` with `ρ (2 ^ 52 + 1) < 1`: `y` lies in a binade
`[B, 2B)`, and either `B + E ≤ |y|` with `E < 2 ρ B` below two spacings, or `|y| < B + E`, where
`E < B 2 ^ -52` stays below two spacings of the binade below. -/
theorem Near.within_two_rel {c : UInt64} {y E ρ : ℝ} (h : Near c y E) (hE : E ≤ ρ * |y|)
    (hρ0 : 0 ≤ ρ) (hρ : ρ * (2 ^ 52 + 1) < 1) (hy : 1 / 2 ^ 1020 ≤ |y|) (hyt : |y| < 2 ^ 1022) :
    F64SignedRounding.WithinSteps 2 y c := by
  obtain ⟨n, hn2, hn, hBy, hyB⟩ := binade_of_real |y| (le_trans (by norm_num) hy) hyt
  have hB := F64PositiveSpacing.boundary_value n (by omega) (by omega)
  set B := value (UInt64.ofNat (n * 2 ^ 52)) with hBdef
  have hB0 : 0 < B := by rw [hB]; positivity
  have hsp : (2 : ℝ) ^ (n - 1) / 2 ^ 1074 = B / 2 ^ 52 := by
    rw [hB, show n + 51 = (n - 1) + 52 by omega, pow_add]
    field_simp
  have hρ1 : ρ * 2 ^ 52 < 1 := by nlinarith
  have hyt' : |y| < 2 ^ 1023 := hyt.trans (by norm_num)
  by_cases hhi : B + E ≤ |y|
  · refine h.within_two n (by omega) (by omega) hhi ?_ hyt'
    rw [hsp]
    have h1 : ρ * |y| ≤ ρ * (2 * B) := mul_le_mul_of_nonneg_left hyB.le hρ0
    have h2 : ρ * (2 * B) * 2 ^ 52 < 2 * B := by nlinarith
    have h3 : 2 * (B / 2 ^ 52) * 2 ^ 52 = 2 * B := by field_simp
    nlinarith
  · have hlo : |y| < B + E := lt_of_not_ge hhi
    have hBl : value (UInt64.ofNat ((n - 1) * 2 ^ 52)) = B / 2 := by
      rw [F64PositiveSpacing.boundary_value (n - 1) (by omega) (by omega), hB,
        show n + 51 = (n - 1 + 51) + 1 by omega, pow_succ]
      ring
    have hsp' : (2 : ℝ) ^ (n - 1 - 1) / 2 ^ 1074 = B / 2 ^ 53 := by
      rw [hB, show n + 51 = (n - 1 - 1) + 53 by omega, pow_add]
      field_simp
    have h5 : 0 < 1 - ρ := by nlinarith
    have h3 : E * (1 - ρ) ≤ ρ * B := by
      have := hE.trans (mul_le_mul_of_nonneg_left hlo.le hρ0)
      nlinarith
    have h6 : E * 2 ^ 52 < B := by
      by_contra hc
      push Not at hc
      have h7 := mul_le_mul_of_nonneg_left hc h5.le
      have h8 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 ^ 52)
      nlinarith
    have hE1 : E < B / 2 ^ 52 := by
      rw [lt_div_iff₀ (by positivity)]
      exact h6
    have hE0 : 0 ≤ E := by
      obtain ⟨S, _, hd⟩ := h
      exact (abs_nonneg _).trans hd
    refine h.within_two (n - 1) (by omega) (by omega) ?_ ?_ hyt'
    · rw [hBl]
      have : B / 2 ^ 52 ≤ B / 2 := div_le_div_of_nonneg_left hB0.le (by norm_num) (by norm_num)
      linarith
    · rw [hsp']
      have : 2 * (B / 2 ^ 53) = B / 2 ^ 52 := by field_simp
      linarith

/-- A nearest rounding of a representable number is that number. -/
theorem Rounded.exact {c w : UInt64} {S : ℝ} (hc : Rounded c S) (hw : value w = S) :
    value c = S := by
  obtain ⟨hcf, hneg, hpos, hnear⟩ := hc
  have h := hnear w
  rw [hw, sub_self, abs_zero] at h
  have habs : |value c| = |S| := by
    have h0 : |(|value c| - |S|)| = 0 := le_antisymm h (abs_nonneg _)
    have := abs_eq_zero.mp h0
    linarith
  rcases lt_trichotomy S 0 with hS | hS | hS
  · have hs := hneg hS
    have hle : value c ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have := F64Exact.sign_of_pos c hcon
      rw [hs] at this
      exact Bool.noConfusion this
    rw [abs_of_nonpos hle, abs_of_neg hS] at habs
    linarith
  · rw [hS, abs_zero, abs_eq_zero] at habs
    rw [habs, hS]
  · have hs := hpos hS
    have hct : c.toNat < 2 ^ 63 := by
      simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
    rw [abs_of_nonneg (value_nonneg_of_lt c hct), abs_of_pos hS] at habs
    exact habs

/-- `a + a` is exact for `2 ^ -1000 ≤ |a| < 2 ^ 900`: the sum rounds to a nearest word of
`2 a`, which the word `2 a` represents. -/
theorem add_self_exact (a : Float) (ha : Finite a.toBits) (h1 : 1 / 2 ^ 1000 ≤ |value a.toBits|)
    (h2 : |value a.toBits| < 2 ^ 900) :
    Finite (a + a).toBits ∧ value (a + a).toBits = 2 * value a.toBits := by
  have hne : value a.toBits + value a.toBits ≠ 0 := by
    intro h0
    have : value a.toBits = 0 := by linarith
    rw [this, abs_zero] at h1
    linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 1000)]
  have hr := add_rounded a.toBits a.toBits ha ha hne (by
    have : |value a.toBits + value a.toBits| ≤ |value a.toBits| + |value a.toBits| := abs_add_le _ _
    linarith [(by norm_num : (2 : ℝ) ^ 900 + 2 ^ 900 < 2 ^ 1023)])
  obtain ⟨_, hwv⟩ := F64Exact.mul_two_exact a.toBits ha
    (le_trans (by norm_num) (F64Exact.exponent_two_of_value _ h1)) (F64Exact.exponent_le_of_value _ h2)
  rw [F64Bits.toBits_add]
  refine ⟨hr.1, ?_⟩
  rw [Rounded.exact hr (w := Wasm.IEEE64.mul 0x4000000000000000 a.toBits) (by rw [hwv]; ring)]
  ring

theorem nonzero_of_magnitude (w : UInt64) (h : value w ≠ 0) :
    0 < Wasm.IEEE64.scaledMagnitude w := by
  rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude w) with h0 | h0
  · exfalso
    apply h
    simp only [value, Wasm.IEEE64.scaledValue, h0]
    split <;> simp
  · exact h0

/-- Halving a nearest rounding gives a nearest rounding of half the number, for
`2 ^ -998 ≤ |S| < 2 ^ 1000`.  A word `v` compares through its double, which is exact, or lies far
from `S/2`. -/
theorem Rounded.half {c : UInt64} {S : ℝ} (hc : Rounded c S) (hS : 1 / 2 ^ 998 ≤ |S|)
    (hS2 : |S| < 2 ^ 1000) : Rounded (Wasm.IEEE64.mul 0x3FE0000000000000 c) (S / 2) := by
  obtain ⟨hcf, hneg, hpos, hnear⟩ := hc
  obtain ⟨n, hn2, hn, hBS, hSB⟩ := binade_of_real |S| (le_trans (by norm_num) hS)
    (lt_trans hS2 (by norm_num))
  set B := value (UInt64.ofNat (n * 2 ^ 52)) with hBdef
  have hB0 : 0 < B := by
    rw [hBdef, F64PositiveSpacing.boundary_value n (by omega) (by omega)]
    positivity
  have hcB : |(|value c| - |S|)| ≤ |S| - B := by
    have h1 := hnear (UInt64.ofNat (n * 2 ^ 52))
    rw [← hBdef, abs_of_pos hB0, abs_of_nonpos (by linarith : B - |S| ≤ 0)] at h1
    linarith
  have hcl := abs_le.mp hcB
  have hcge : B ≤ |value c| := by linarith [hcl.1]
  have hc1000 : 1 / 2 ^ 1000 ≤ |value c| := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 998 / 2)]
  obtain ⟨hhf, hhv⟩ := F64Exact.mul_half_exact c hcf (F64Exact.exponent_two_of_value c hc1000)
  set h := Wasm.IEEE64.mul 0x3FE0000000000000 c with hhdef
  have hcne : value c ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hcge
    linarith
  have hhne : value h ≠ 0 := by
    rw [hhv]
    exact div_ne_zero hcne two_ne_zero
  refine ⟨hhf, ?_, ?_, ?_⟩
  · intro hS0
    have hsc := hneg (by linarith)
    have hv := (F64Magnitude.sign_value c (nonzero_of_magnitude c hcne)).mp hsc
    exact (F64Magnitude.sign_value h (nonzero_of_magnitude h hhne)).mpr (by rw [hhv]; linarith)
  · intro hS0
    have hsc := hpos (by linarith)
    have hv : 0 < value c := by
      rcases lt_or_gt_of_ne hcne with hl | hl
      · have := (F64Magnitude.sign_value c (nonzero_of_magnitude c hcne)).mpr hl
        rw [hsc] at this
        exact absurd this Bool.false_ne_true
      · exact hl
    exact F64Exact.sign_of_pos h (by rw [hhv]; linarith)
  · intro v
    have hhabs : |value h| = |value c| / 2 := by rw [hhv, abs_div, abs_two]
    have hSabs : |S / 2| = |S| / 2 := by rw [abs_div, abs_two]
    rw [hhabs, hSabs, show |value c| / 2 - |S| / 2 = (|value c| - |S|) / 2 by ring, abs_div,
      abs_two]
    rcases Nat.lt_or_ge (Wasm.IEEE64.exponent v) 2 with he | he
    · have hv := F64Magnitude.magnitude_lt v 2 (-1021) (by norm_num) (by norm_num) he
      have h2 : (2 : ℝ) ^ (-1021 : ℤ) = 1 / 2 ^ 1021 := by norm_num
      rw [h2] at hv
      have h3 : |S| / 2 - |value v| ≤ |(|value v| - |S| / 2)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      have h4 : (1 : ℝ) / 2 ^ 1021 ≤ |S| / 4 := by
        rw [le_div_iff₀ (by norm_num)]
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 1021 * 4 = 1 / 2 ^ 1019),
          (by norm_num : (1 : ℝ) / 2 ^ 1019 ≤ 1 / 2 ^ 998)]
      have h5 : |(|value c| - |S|)| / 2 ≤ |S| / 4 := by
        have : |S| - B ≤ |S| / 2 := by linarith
        linarith
      linarith
    rcases Nat.lt_or_ge (Wasm.IEEE64.exponent v) 2041 with he2 | he2
    · obtain ⟨hwf, hwv⟩ := F64Exact.mul_two_exact v (by
          simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq]
          omega) (by omega) (by omega)
      have h1 := hnear (Wasm.IEEE64.mul 0x4000000000000000 v)
      rw [hwv, abs_mul, abs_two, show 2 * |value v| - |S| = 2 * (|value v| - |S| / 2) by ring,
        abs_mul, abs_two] at h1
      linarith
    · have hv := F64Magnitude.magnitude_ge v 2041 1018 (by norm_num) (by norm_num) (by norm_num)
        he2
      have h3 : |value v| - |S| / 2 ≤ |(|value v| - |S| / 2)| := le_abs_self _
      have h5 : |(|value c| - |S|)| / 2 ≤ |S| / 4 := by
        have : |S| - B ≤ |S| / 2 := by linarith
        linarith
      have h6 : (2 : ℝ) ^ (1018 : ℤ) = 2 ^ 1018 := by norm_num
      rw [h6] at hv
      have h7 : (2 : ℝ) ^ 1000 * 3 / 4 ≤ 2 ^ 1018 := by norm_num
      linarith

/-- An exact halving of the word halves the target and the bound. -/
theorem Near.half {c : UInt64} {y E : ℝ} (h : Near c y E) (hy : 1 / 2 ^ 998 + E ≤ |y|)
    (hyt : |y| + E < 2 ^ 1000) :
    Near (Wasm.IEEE64.mul 0x3FE0000000000000 c) (y / 2) (E / 2) := by
  obtain ⟨S, hS, hd⟩ := h
  have h1 := abs_sub_abs_le_abs_sub y S
  have h2 := abs_sub_abs_le_abs_sub S y
  rw [abs_sub_comm] at h1
  refine ⟨S / 2, Rounded.half hS (by linarith) (by linarith), ?_⟩
  rw [show S / 2 - y / 2 = (S - y) / 2 by ring, abs_div, abs_two]
  linarith

#print axioms near_sub
#print axioms near_add
#print axioms Near.within_one
#print axioms Near.within_one_rel
#print axioms Near.within_two
#print axioms Near.within_two_rel
#print axioms Rounded.exact
#print axioms add_self_exact
#print axioms Rounded.half
#print axioms Near.half

end LeanExe.ProofKit.F64Near
