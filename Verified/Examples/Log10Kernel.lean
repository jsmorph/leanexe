import Verified.Examples.Log10Bits
import Verified.Examples.Log10Consts
import Verified.Examples.LogCoreFinal
import LeanExe.ProofKit.F64DivBounds
import LeanExe.ProofKit.F64ExactProduct

/-!
The error of `Log10Bits.kWord`, fdlibm's `k_log1p`, and of `hfsq = f²/2`, for `f = x' - 1` from
`-0.2929` to `0.41422`.  With `R` the value of `f`, `S = R / (2 + R)`, and `σ = |S| ≤ 0.1716`,
each word is compared with its value in exact arithmetic, and each error is a multiple of `u σ`
plus a term below `2 ^ -1060`: `s` is within `2.0001 u σ` of `S`, `hfsq` within `0.50001 u σ` of
`R²/2`, and the result `r` within `0.6713 u σ` of `S (R²/2 + Rp S)`, where `Rp` is the code's
polynomial in `S²`.  Products of two bounds that both shrink with `σ` take one of them in a form
that holds for all `σ ≤ 0.1716`, so that every bound stays linear in `σ`.
-/

namespace Verified.Examples.Log10Kernel
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack LogCoreFinal Log10Bits

set_option exponentiation.threshold 4096

theorem consts10 :
    Finite 0x3FE0000000000000 ∧ Finite 0x4000000000000000 ∧ Finite 0x3FE5555555555593 ∧
    Finite 0x3FD999999997FA04 ∧ Finite 0x3FD2492494229359 ∧ Finite 0x3FCC71C51D8E78AF ∧
    Finite 0x3FC7466496CB03DE ∧ Finite 0x3FC39A09D078C69F ∧ Finite 0x3FC2F112DF3E5244 ∧
    Wasm.IEEE64.scaledMagnitude 0x3FE0000000000000 = 1 * 2 ^ 1073 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem bounds10 :
    PolyBound.ratOfWord 0x3FE0000000000000 = 1 / 2 ∧ PolyBound.ratOfWord 0x4000000000000000 = 2 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FE5555555555593) ≤ 66667 / 100000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FD999999997FA04) ≤ 4 / 10 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FD2492494229359) ≤ 28572 / 100000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FCC71C51D8E78AF) ≤ 22223 / 100000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FC7466496CB03DE) ≤ 18184 / 100000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FC39A09D078C69F) ≤ 15314 / 100000 ∧
    PolyBound.qabs (PolyBound.ratOfWord 0x3FC2F112DF3E5244) ≤ 14799 / 100000 := by
  decide +kernel

/-- `Lg1 S² + ... + Lg7 S¹⁴` in the grouping of `k_log1p`. -/
noncomputable def Rp (S : ℝ) : ℝ :=
  S * S * (value 0x3FE5555555555593 + S * S * (S * S) * (value 0x3FD2492494229359 +
      S * S * (S * S) * (value 0x3FC7466496CB03DE + S * S * (S * S) * value 0x3FC2F112DF3E5244))) +
    S * S * (S * S) * (value 0x3FD999999997FA04 + S * S * (S * S) * (value 0x3FCC71C51D8E78AF +
      S * S * (S * S) * value 0x3FC39A09D078C69F))

/-- `R - R²/2 + S (R²/2 + Rp S) = S (2 + Lg1 S² + ... + Lg7 S¹⁴)` for `S = R / (2 + R)`. -/
theorem kernel_identity (R : ℝ) (h : 0 < 2 + R) :
    R - 1 / 2 * R * R + R / (2 + R) * (1 / 2 * R * R + Rp (R / (2 + R))) =
      R / (2 + R) * PolyBound.eval Log1pKernelPoly.log1pKernel ((R / (2 + R)) ^ 2) := by
  simp only [Log1pKernelPoly.log1pKernel, PolyBound.eval_cons, PolyBound.eval_nil,
    PolyBound.ratOfWord_cast, Rp]
  push_cast
  field_simp
  ring

/-- The scaled magnitude of a word that is zero or of exponent field at least 2, split as a
mantissa below `2 ^ 53` times a power of 2 from 1 on. -/
theorem mag_split (w : UInt64) (h : Wasm.IEEE64.scaledMagnitude w = 0 ∨ 2 ≤ Wasm.IEEE64.exponent w) :
    ∃ ma sa : Nat, Wasm.IEEE64.scaledMagnitude w = ma * 2 ^ sa ∧ ma < 2 ^ 53 ∧ 1 ≤ sa ∧
      (sa = 1 ∨ sa + 1 = Wasm.IEEE64.exponent w) := by
  rcases h with h | h
  · exact ⟨0, 1, by rw [h]; ring, by norm_num, le_rfl, Or.inl rfl⟩
  · refine ⟨2 ^ 52 + Wasm.IEEE64.fraction w, Wasm.IEEE64.exponent w - 1, ?_, ?_, by omega, ?_⟩
    · have hne : (Wasm.IEEE64.exponent w == 0) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      simp only [Wasm.IEEE64.scaledMagnitude, hne, Bool.false_eq_true, ↓reduceIte]
    · have : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by positivity)
      omega
    · right
      omega

set_option maxHeartbeats 4000000 in
/-- The errors of `hfsq` and of `k_log1p`. -/
theorem kernel10 (f : UInt64) (hf : Finite f)
    (hlo : -29290 / 100000 ≤ value f) (hhi : value f ≤ 41422 / 100000)
    (hmag : Wasm.IEEE64.scaledMagnitude f = 0 ∨ 2 ≤ Wasm.IEEE64.exponent f) :
    Finite (Wasm.IEEE64.mul 0x3FE0000000000000 f) ∧
    value (Wasm.IEEE64.mul 0x3FE0000000000000 f) = 1 / 2 * value f ∧
    Approx (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0x3FE0000000000000 f) f)
      (1 / 2 * value f * value f)
      (1 / 2 ^ 53 * |value f / (2 + value f)| * (50001 / 100000) + 1 / 2 ^ 1070) ∧
    |1 / 2 * value f * value f| ≤ |value f / (2 + value f)| * (50001 / 100000) ∧
    Approx (kWord f)
      (value f / (2 + value f) * (1 / 2 * value f * value f + Rp (value f / (2 + value f))))
      (1 / 2 ^ 53 * |value f / (2 + value f)| * (6713 / 10000) + 8 / 2 ^ 1070) ∧
    |value f / (2 + value f) * (1 / 2 * value f * value f + Rp (value f / (2 + value f)))| ≤
      |value f / (2 + value f)| * (10579 / 100000) := by
  obtain ⟨c0, c2, cL1, cL2, cL3, cL4, cL5, cL6, cL7, hmh⟩ := consts10
  obtain ⟨b0, b2, bL1, bL2, bL3, bL4, bL5, bL6, bL7⟩ := bounds10
  have vL1 := value_bound _ _ bL1
  have vL2 := value_bound _ _ bL2
  have vL3 := value_bound _ _ bL3
  have vL4 := value_bound _ _ bL4
  have vL5 := value_bound _ _ bL5
  have vL6 := value_bound _ _ bL6
  have vL7 := value_bound _ _ bL7
  push_cast at vL1 vL2 vL3 vL4 vL5 vL6 vL7
  have vhalf : value (0x3FE0000000000000 : UInt64) = 1 / 2 := by
    rw [← PolyBound.ratOfWord_cast, b0]
    norm_num
  have vtwo : value (0x4000000000000000 : UInt64) = 2 := by
    rw [← PolyBound.ratOfWord_cast, b2]
    norm_num
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hmu : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  have hexpf : Wasm.IEEE64.exponent f < 1023 := by
    apply F64ExponentBounds.exponent_lt_of_magnitude_lt f 1023 (by norm_num)
    show |value f| < |value (UInt64.ofNat (1023 * 2 ^ 52))|
    rw [F64NearestBinade.boundary_power 1023 0 (by norm_num) (by norm_num) (by norm_num),
      zpow_zero, abs_one, abs_lt]
    constructor <;> linarith
  set R := value f with hRdef
  have h2R : 0 < 2 + R := by linarith
  set S := R / (2 + R) with hSdef
  set σ := |S| with hσdef
  have hσR : σ = |R| / (2 + R) := by rw [hσdef, hSdef, abs_div, abs_of_pos h2R]
  have hσ0 : 0 ≤ σ := abs_nonneg _
  have hρmax : |R| ≤ 41422 / 100000 := by
    rw [abs_le]
    constructor <;> linarith
  have hρσ : |R| ≤ 241422 / 100000 * σ := by
    rw [hσR, mul_div_assoc', le_div_iff₀ h2R]
    have : 0 ≤ |R| := abs_nonneg R
    nlinarith
  have hσmax : σ ≤ 1716 / 10000 := by
    rw [hσR, div_le_iff₀ h2R]
    rcases le_or_gt 0 R with h | h
    · rw [abs_of_nonneg h]
      linarith
    · rw [abs_of_neg h]
      linarith
  have hρρ : |R| * |R| ≤ 100002 / 100000 * σ := by
    have h1 : |R| * |R| ≤ 41422 / 100000 * |R| :=
      mul_le_mul_of_nonneg_right hρmax (abs_nonneg R)
    nlinarith
  have hσσ : σ * σ ≤ 1716 / 10000 * σ := mul_le_mul_of_nonneg_right hσmax hσ0
  -- `0.5 f`, exact
  obtain ⟨ma, sa, hma, hma53, hsa1, hsa2⟩ := mag_split f hmag
  have hsa3 : sa ≤ 1022 := by omega
  obtain ⟨hh0f, hh0v, -, -⟩ := F64ExactProduct.mul_exact_scaled 0x3FE0000000000000 f c0 hf 1 ma
    1073 sa hmh hma (by omega) (by omega) (by omega)
  rw [vhalf] at hh0v
  have aH0 : Approx (Wasm.IEEE64.mul 0x3FE0000000000000 f) (1 / 2 * R) 0 :=
    ⟨hh0f, by rw [hh0v, sub_self, abs_zero]⟩
  have aF : Approx f R 0 := approx_self f hf
  -- `hfsq`
  have hH0 : |1 / 2 * R| ≤ |R| / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have aH := (mul_approx aH0 aF (|R| / 2) |R| hH0 le_rfl (by nlinarith)).mono
    (e' := 1 / 2 ^ 53 * σ * (50001 / 100000) + 1 / 2 ^ 1070) (by rw [hu, hmu]; nlinarith)
  have hHb : |1 / 2 * R * R| ≤ σ * (50001 / 100000) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith
  -- `2 + f`
  have aD := (add_approx (approx_self _ c2) aF (2 + R)
    (by rw [vtwo, abs_of_pos h2R]; linarith) (by linarith))
  rw [vtwo] at aD
  set D := value (Wasm.IEEE64.add 0x4000000000000000 f) with hDdef
  have eD := abs_le.mp aD.2
  rw [hu] at eD
  have hDlo : (2 + R) * (1 - 1 / 2 ^ 53) ≤ D := by nlinarith
  have hDpos : 0 < D := by nlinarith
  -- `s = f / (2 + f)`
  have hDmag : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.add 0x4000000000000000 f) ≠ 0 := by
    intro h0
    have : D = 0 := by
      rw [hDdef]
      simp only [value, Wasm.IEEE64.scaledValue, h0]
      split <;> simp
    linarith
  have hRD : |R / D| ≤ σ * (1 + 1 / 2 ^ 50) := by
    rw [abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos, hσR]
    have h1 : |R| / (2 + R) * (1 + 1 / 2 ^ 50) * D ≥ |R| / (2 + R) * (1 + 1 / 2 ^ 50) *
        ((2 + R) * (1 - 1 / 2 ^ 53)) := by
      apply mul_le_mul_of_nonneg_left hDlo
      positivity
    have h2 : |R| / (2 + R) * (1 + 1 / 2 ^ 50) * ((2 + R) * (1 - 1 / 2 ^ 53)) =
        |R| * ((1 + 1 / 2 ^ 50) * (1 - 1 / 2 ^ 53)) := by
      field_simp
    have h3 : |R| ≤ |R| * ((1 + 1 / 2 ^ 50) * (1 - 1 / 2 ^ 53)) := by
      have : (1 : ℝ) ≤ (1 + 1 / 2 ^ 50) * (1 - 1 / 2 ^ 53) := by norm_num
      nlinarith [abs_nonneg R]
    linarith
  obtain ⟨hsf, hsv⟩ := F64DivBounds.div_real_mixed f _ hf aD.1 hDmag (by
    have : σ * (1 + 1 / 2 ^ 50) < 2 ^ 1022 := by nlinarith
    linarith)
  have hRDS : |R / D - S| ≤ 1 / 2 ^ 53 * σ * (1 + 1 / 2 ^ 50) := by
    have heq : R / D - S = R * ((2 + R) - D) / (D * (2 + R)) := by
      rw [hSdef]
      field_simp <;> ring
    rw [heq, abs_div, abs_mul, abs_of_pos (mul_pos hDpos h2R)]
    have hdd : |(2 + R) - D| ≤ 1 / 2 ^ 53 * (2 + R) := by
      rw [abs_sub_comm, abs_le]
      constructor <;> linarith [eD.1, eD.2]
    rw [div_le_iff₀ (mul_pos hDpos h2R)]
    have h1 : |R| * |(2 + R) - D| ≤ |R| * (1 / 2 ^ 53 * (2 + R)) :=
      mul_le_mul_of_nonneg_left hdd (abs_nonneg R)
    have h3 : 1 / 2 ^ 53 * σ * (1 + 1 / 2 ^ 50) * (D * (2 + R)) ≥
        1 / 2 ^ 53 * σ * (1 + 1 / 2 ^ 50) * ((2 + R) * (1 - 1 / 2 ^ 53) * (2 + R)) := by
      apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hDlo h2R.le)
      positivity
    have h4 : 1 / 2 ^ 53 * σ * (1 + 1 / 2 ^ 50) * ((2 + R) * (1 - 1 / 2 ^ 53) * (2 + R)) ≥
        |R| * (1 / 2 ^ 53 * (2 + R)) := by
      rw [hσR]
      have h5 : |R| / (2 + R) * (2 + R) = |R| := by field_simp
      have h6 : (1 : ℝ) ≤ (1 + 1 / 2 ^ 50) * (1 - 1 / 2 ^ 53) := by norm_num
      have h7 : 0 ≤ |R| * (2 + R) := mul_nonneg (abs_nonneg R) h2R.le
      calc 1 / 2 ^ 53 * (|R| / (2 + R)) * (1 + 1 / 2 ^ 50) * ((2 + R) * (1 - 1 / 2 ^ 53) * (2 + R))
          = 1 / 2 ^ 53 * (|R| / (2 + R) * (2 + R)) * (2 + R) *
              ((1 + 1 / 2 ^ 50) * (1 - 1 / 2 ^ 53)) := by ring
        _ = 1 / 2 ^ 53 * |R| * (2 + R) * ((1 + 1 / 2 ^ 50) * (1 - 1 / 2 ^ 53)) := by rw [h5]
        _ ≥ 1 / 2 ^ 53 * |R| * (2 + R) * 1 := by
            apply mul_le_mul_of_nonneg_left h6
            positivity
        _ = |R| * (1 / 2 ^ 53 * (2 + R)) := by ring
    linarith
  set s := Wasm.IEEE64.div f (Wasm.IEEE64.add 0x4000000000000000 f) with hsdef
  have aS : Approx s S (1 / 2 ^ 53 * σ * (20001 / 10000) + 1 / 2 ^ 1070 / 32) := by
    refine ⟨hsf, ?_⟩
    have h1 := abs_sub_le (value s) (R / D) S
    rw [hu, hmu] at hsv
    have h2 : 1 / 2 ^ 53 * |R / D| ≤ 1 / 2 ^ 53 * (σ * (1 + 1 / 2 ^ 50)) :=
      mul_le_mul_of_nonneg_left hRD (by norm_num)
    have h3 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1070 / 32 := by norm_num
    nlinarith
  have aSc : Approx s S (1 / 2 ^ 53 * (1716 / 10000) * (20001 / 10000) + 1 / 2 ^ 1070 / 32) :=
    aS.mono (by nlinarith)
  have hSb : |S| ≤ σ := le_rfl
  have hSc : |S| ≤ 1716 / 10000 := hσmax
  -- `z = s s` and `w = z z`
  have aZ := (mul_approx aS aSc σ (1716 / 10000) hSb hSc (by nlinarith)).mono
    (e' := 1 / 2 ^ 53 * σ * (8581 / 10000) + 1 / 2 ^ 1070 / 8) (by rw [hu, hmu]; nlinarith)
  have hZb : |S * S| ≤ 1716 / 10000 * σ := by
    rw [abs_mul]
    nlinarith
  have hZc : |S * S| ≤ 1716 / 10000 * (1716 / 10000) := by
    rw [abs_mul]
    nlinarith
  have aZc : Approx (Wasm.IEEE64.mul s s) (S * S)
      (1 / 2 ^ 53 * (1716 / 10000) * (8581 / 10000) + 1 / 2 ^ 1070 / 8) := aZ.mono (by nlinarith)
  have aW := (mul_approx aZ aZc (1716 / 10000 * σ) (1716 / 10000 * (1716 / 10000)) hZb hZc
    (by nlinarith)).mono (e' := 1 / 2 ^ 53 * σ * (556 / 10000) + 1 / 2 ^ 1070 / 4)
    (by rw [hu, hmu]; nlinarith)
  have hWb : |S * S * (S * S)| ≤ 1716 / 10000 * σ * (1716 / 10000 * (1716 / 10000)) :=
    abs_mul_bound hZb hZc
  have hWc : |S * S * (S * S)| ≤ 1716 / 10000 * (1716 / 10000) * (1716 / 10000 * (1716 / 10000)) :=
    abs_mul_bound hZc hZc
  have aWc : Approx (Wasm.IEEE64.mul (Wasm.IEEE64.mul s s) (Wasm.IEEE64.mul s s)) (S * S * (S * S))
      (1 / 2 ^ 53 * (1716 / 10000) * (556 / 10000) + 1 / 2 ^ 1070 / 4) := aW.mono (by nlinarith)
  set Wc : ℝ := 1716 / 10000 * (1716 / 10000) * (1716 / 10000 * (1716 / 10000)) with hWcdef
  -- `t1 = w (Lg2 + w (Lg4 + w Lg6))`
  have aM6 := (mul_approx aWc (approx_self _ cL6) Wc (15314 / 100000) hWc vL6
    (by norm_num [hWcdef])).mono (e' := 1 / 2 ^ 53 * (16 / 10000)) (by rw [hu, hmu]; norm_num [hWcdef])
  have hM6 := abs_mul_bound hWc vL6
  have aA46 := (add_approx (approx_self _ cL4) aM6 (22223 / 100000 + Wc * (15314 / 100000) + 0 +
    1 / 2 ^ 53 * (16 / 10000)) (by have := abs_add_bound vL4 hM6; linarith)
    (by norm_num [hWcdef])).mono (e' := 1 / 2 ^ 53 * (2240 / 10000)) (by rw [hu]; norm_num [hWcdef])
  have hA46 := abs_add_bound vL4 hM6
  have aM46 := (mul_approx aWc aA46 Wc (22223 / 100000 + Wc * (15314 / 100000)) hWc hA46
    (by norm_num [hWcdef])).mono (e' := 1 / 2 ^ 53 * (26 / 10000)) (by rw [hu, hmu]; norm_num [hWcdef])
  have hM46 := abs_mul_bound hWc hA46
  have aA246 := (add_approx (approx_self _ cL2) aM46 (4 / 10 + Wc * (22223 / 100000 + Wc *
    (15314 / 100000)) + 0 + 1 / 2 ^ 53 * (26 / 10000)) (by have := abs_add_bound vL2 hM46; linarith)
    (by norm_num [hWcdef])).mono (e' := 1 / 2 ^ 53 * (4030 / 10000)) (by rw [hu]; norm_num [hWcdef])
  have hA246 := abs_add_bound vL2 hM46
  have aT1 := (mul_approx aW aA246 (1716 / 10000 * σ * (1716 / 10000 * (1716 / 10000)))
    (4 / 10 + Wc * (22223 / 100000 + Wc * (15314 / 100000))) hWb hA246 (by
      norm_num [hWcdef]; nlinarith)).mono
    (e' := 1 / 2 ^ 53 * σ * (264 / 10000) + 1 / 2 ^ 1070 / 2) (by rw [hu, hmu]; norm_num [hWcdef]; nlinarith)
  have hT1 := abs_mul_bound hWb hA246
  -- `t2 = z (Lg1 + w (Lg3 + w (Lg5 + w Lg7)))`
  have aM7 := (mul_approx aWc (approx_self _ cL7) Wc (14799 / 100000) hWc vL7
    (by norm_num [hWcdef])).mono (e' := 1 / 2 ^ 53 * (16 / 10000)) (by rw [hu, hmu]; norm_num [hWcdef])
  have hM7 := abs_mul_bound hWc vL7
  have aA57 := (add_approx (approx_self _ cL5) aM7 (18184 / 100000 + Wc * (14799 / 100000) + 0 +
    1 / 2 ^ 53 * (16 / 10000)) (by have := abs_add_bound vL5 hM7; linarith)
    (by norm_num [hWcdef])).mono (e' := 1 / 2 ^ 53 * (1840 / 10000)) (by rw [hu]; norm_num [hWcdef])
  have hA57 := abs_add_bound vL5 hM7
  have aM57 := (mul_approx aWc aA57 Wc (18184 / 100000 + Wc * (14799 / 100000)) hWc hA57
    (by norm_num [hWcdef])).mono (e' := 1 / 2 ^ 53 * (21 / 10000)) (by rw [hu, hmu]; norm_num [hWcdef])
  have hM57 := abs_mul_bound hWc hA57
  have aA357 := (add_approx (approx_self _ cL3) aM57 (28572 / 100000 + Wc * (18184 / 100000 + Wc *
    (14799 / 100000)) + 0 + 1 / 2 ^ 53 * (21 / 10000)) (by have := abs_add_bound vL3 hM57; linarith)
    (by norm_num [hWcdef])).mono (e' := 1 / 2 ^ 53 * (2881 / 10000)) (by rw [hu]; norm_num [hWcdef])
  have hA357 := abs_add_bound vL3 hM57
  have aM357 := (mul_approx aWc aA357 Wc (28572 / 100000 + Wc * (18184 / 100000 + Wc *
    (14799 / 100000))) hWc hA357 (by norm_num [hWcdef])).mono (e' := 1 / 2 ^ 53 * (33 / 10000))
    (by rw [hu, hmu]; norm_num [hWcdef])
  have hM357 := abs_mul_bound hWc hA357
  have aA1357 := (add_approx (approx_self _ cL1) aM357 (66667 / 100000 + Wc * (28572 / 100000 +
    Wc * (18184 / 100000 + Wc * (14799 / 100000))) + 0 + 1 / 2 ^ 53 * (33 / 10000))
    (by have := abs_add_bound vL1 hM357; linarith) (by norm_num [hWcdef])).mono
    (e' := 1 / 2 ^ 53 * (6703 / 10000)) (by rw [hu]; norm_num [hWcdef])
  have hA1357 := abs_add_bound vL1 hM357
  have aT2 := (mul_approx aZ aA1357 (1716 / 10000 * σ) (66667 / 100000 + Wc * (28572 / 100000 +
    Wc * (18184 / 100000 + Wc * (14799 / 100000)))) hZb hA1357 (by
      norm_num [hWcdef]; nlinarith)).mono
    (e' := 1 / 2 ^ 53 * σ * (8020 / 10000) + 1 / 2 ^ 1070 / 2) (by rw [hu, hmu]; norm_num [hWcdef]; nlinarith)
  have hT2 := abs_mul_bound hZb hA1357
  -- `R = t2 + t1`
  have hRp : |Rp S| ≤ σ * (11647 / 100000) := by
    have := abs_add_bound hT2 hT1
    rw [Rp]
    norm_num [hWcdef] at this ⊢
    nlinarith
  have aRp : Approx _ (Rp S) (1 / 2 ^ 53 * σ * (9450 / 10000) + 2 / 2 ^ 1070) :=
    ((add_approx aT2 aT1 (σ * (11647 / 100000) + (1 / 2 ^ 53 * σ * (8020 / 10000) +
      1 / 2 ^ 1070 / 2) + (1 / 2 ^ 53 * σ * (264 / 10000) + 1 / 2 ^ 1070 / 2))
      (by rw [Rp] at hRp; linarith) (by nlinarith)).congr (by rw [Rp])).mono
      (by rw [hu]; nlinarith)
  -- `hfsq + R`
  have hHR : |1 / 2 * R * R + Rp S| ≤ σ * (61648 / 100000) := by
    have := abs_add_bound hHb hRp
    linarith
  have aHR := (add_approx aH aRp (σ * (61648 / 100000) + (1 / 2 ^ 53 * σ * (50001 / 100000) +
    1 / 2 ^ 1070) + (1 / 2 ^ 53 * σ * (9450 / 10000) + 2 / 2 ^ 1070)) (by linarith)
    (by nlinarith)).mono (e' := 1 / 2 ^ 53 * σ * (20620 / 10000) + 4 / 2 ^ 1070)
    (by rw [hu]; nlinarith)
  have aHRc : Approx _ (1 / 2 * R * R + Rp S)
      (1 / 2 ^ 53 * (1716 / 10000) * (20620 / 10000) + 4 / 2 ^ 1070) := aHR.mono (by nlinarith)
  have hHRc : |1 / 2 * R * R + Rp S| ≤ 1716 / 10000 * (61648 / 100000) := by nlinarith
  -- `r = s (hfsq + R)`
  have aR := (mul_approx aS aHRc σ (1716 / 10000 * (61648 / 100000)) hSb hHRc (by nlinarith)).mono
    (e' := 1 / 2 ^ 53 * σ * (6713 / 10000) + 8 / 2 ^ 1070) (by rw [hu, hmu]; nlinarith)
  refine ⟨hh0f, hh0v, aH, hHb, ?_, ?_⟩
  · have hk : kWord f = Wasm.IEEE64.mul s (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0x3FE0000000000000 f) f)
        (Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.mul s s) (Wasm.IEEE64.add 0x3FE5555555555593
          (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul s s) (Wasm.IEEE64.mul s s))
            (Wasm.IEEE64.add 0x3FD2492494229359
              (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul s s) (Wasm.IEEE64.mul s s))
                (Wasm.IEEE64.add 0x3FC7466496CB03DE
                  (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul s s) (Wasm.IEEE64.mul s s))
                    0x3FC2F112DF3E5244)))))))
          (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul s s) (Wasm.IEEE64.mul s s))
            (Wasm.IEEE64.add 0x3FD999999997FA04
              (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul s s) (Wasm.IEEE64.mul s s))
                (Wasm.IEEE64.add 0x3FCC71C51D8E78AF
                  (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul s s) (Wasm.IEEE64.mul s s))
                    0x3FC39A09D078C69F))))))) := rfl
    rw [hk]
    exact aR
  · have := abs_mul_bound hSb hHRc
    nlinarith

#print axioms kernel_identity
#print axioms mag_split
#print axioms kernel10

end Verified.Examples.Log10Kernel
