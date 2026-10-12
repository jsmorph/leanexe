import Verified.Examples.Expm1ReduceWords

/-!
The reduced argument of fdlibm's `expm1`.  `yc_spec`: from the exact `hi` and the small `lo`, the
code forms `y = hi - lo` and the correction `c = (hi - y) - lo`, and `y + c` lies within `2 ^ -74`
of `hi - lo`, with `abs(c) ≤ 0.36 u`.  `reduce_one_pos` and `reduce_one_neg` treat `k = ±1`, where
`hi = x ∓ ln2Hi` is exact and `lo = ±ln2Lo`: `y + c` lies within `2 ^ -70` of `x ∓ log 2`.
-/

namespace Verified.Examples.Expm1ReduceOne
open CodeLib.IEEE64 LeanExe.ProofKit Expm1ReduceConst Expm1ReduceWords

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

theorem yc_spec (hi lo : UInt64) (hhf : Finite hi) (hlf : Finite lo)
    (hH : |value hi| ≤ 34658 / 100000) (hL : |value lo| ≤ 2 / 10 ^ 7) :
    Finite (Wasm.IEEE64.sub hi lo) ∧
      Finite (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo) ∧
      |value (Wasm.IEEE64.sub hi lo)| ≤ 3466 / 10000 ∧
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo)| ≤ 36 / 100 * u ∧
      |value (Wasm.IEEE64.sub hi lo) +
          value (Wasm.IEEE64.sub (Wasm.IEEE64.sub hi (Wasm.IEEE64.sub hi lo)) lo) -
        (value hi - value lo)| ≤ 1 / 2 ^ 74 := by
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  set H := value hi
  set Lo := value lo
  have hD : |H - Lo| ≤ 3465802 / 10000000 := by
    refine (abs_sub _ _).trans ?_
    have : (34658 : ℝ) / 100000 + 2 / 10 ^ 7 = 3465802 / 10000000 := by norm_num
    linarith
  -- `y`.
  have sy := F64AddBounds.sub_real_relative hi lo hhf hlf (hD.trans_lt (by norm_num))
  set y := Wasm.IEEE64.sub hi lo
  set Y := value y
  have hYD : |Y - (H - Lo)| ≤ u * |H - Lo| := sy.2
  have hYm : |Y| ≤ 3466 / 10000 := by
    have := abs_sub_abs_le_abs_sub Y (H - Lo)
    have h1 : u * |H - Lo| ≤ 1 / 10 ^ 10 := by
      rw [hu]
      have : |H - Lo| ≤ 1 := hD.trans (by norm_num)
      nlinarith [abs_nonneg (H - Lo)]
    linarith
  -- `d1 = hi - y`.
  have hHY : |H - Y| ≤ 2 / 10 ^ 7 + 1 / 10 ^ 10 := by
    have h1 : H - Y = Lo - (Y - (H - Lo)) := by ring
    rw [h1]
    refine (abs_sub _ _).trans ?_
    have h2 : u * |H - Lo| ≤ 1 / 10 ^ 10 := by
      rw [hu]
      have : |H - Lo| ≤ 1 := hD.trans (by norm_num)
      nlinarith [abs_nonneg (H - Lo)]
    linarith
  have sd := F64AddBounds.sub_real_relative hi y hhf sy.1 (hHY.trans_lt (by norm_num))
  set d1 := Wasm.IEEE64.sub hi y
  have hd1 : |value d1 - (H - Y)| ≤ 1 / 2 ^ 75 := by
    refine sd.2.trans ?_
    calc u * |H - Y| ≤ u * (2 / 10 ^ 7 + 1 / 10 ^ 10) := mul_le_mul_of_nonneg_left hHY hu0
      _ ≤ 1 / 2 ^ 75 := by rw [hu]; norm_num
  -- `c = d1 - lo`.
  have hdL : |value d1 - Lo| ≤ 1 / 2 ^ 75 + u * (3465802 / 10000000) := by
    have h1 : value d1 - Lo = (value d1 - (H - Y)) - (Y - (H - Lo)) := by ring
    rw [h1]
    refine (abs_sub _ _).trans (add_le_add hd1 (hYD.trans ?_))
    exact mul_le_mul_of_nonneg_left hD hu0
  have sc := F64AddBounds.sub_real_relative d1 lo sd.1 hlf (hdL.trans_lt (by rw [hu]; norm_num))
  set c := Wasm.IEEE64.sub d1 lo
  have hcd : |value c - (value d1 - Lo)| ≤ u * (1 / 2 ^ 75 + u * (3465802 / 10000000)) :=
    sc.2.trans (mul_le_mul_of_nonneg_left hdL hu0)
  refine ⟨sy.1, sc.1, hYm, ?_, ?_⟩
  · have := abs_sub_abs_le_abs_sub (value c) (value d1 - Lo)
    have h2 : 1 / 2 ^ 75 + u * (3465802 / 10000000) + u * (1 / 2 ^ 75 + u * (3465802 / 10000000)) ≤
        36 / 100 * u := by rw [hu]; norm_num
    linarith
  · have h1 : Y + value c - (H - Lo) = (value c - (value d1 - Lo)) + (value d1 - (H - Y)) := by ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    have h2 : u * (1 / 2 ^ 75 + u * (3465802 / 10000000)) + 1 / 2 ^ 75 ≤ 1 / 2 ^ 74 := by
      rw [hu]; norm_num
    linarith

theorem ln2Hi_value : value ln2Hi = 2977044471 / 2 ^ 32 := by
  have h : Wasm.IEEE64.scaledValue ln2Hi = 2977044471 * 2 ^ 1042 := by decide +kernel
  rw [value, h]; push_cast; field_simp; norm_num

theorem ln2Lo_bound : 0 < value ln2Lo ∧ value ln2Lo ≤ 1909 / 10 ^ 13 := by
  rw [← PolyBound.ratOfWord_cast]
  have h : 0 < PolyBound.ratOfWord ln2Lo ∧ PolyBound.ratOfWord ln2Lo ≤ 1909 / 10 ^ 13 := by
    decide +kernel
  exact ⟨by exact_mod_cast h.1, ((Rat.cast_le (K := ℝ)).mpr h.2).trans (le_of_eq (by norm_num))⟩

theorem ln2Hi_grid : 2 ^ 1021 ∣ Wasm.IEEE64.scaledMagnitude ln2Hi := by
  rw [ln2Hi_magnitude.1]
  exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by norm_num)) _

/-- `k = 1`: `hi = x - ln2Hi`, `lo = ln2Lo`. -/
theorem reduce_one_pos (x : UInt64) (hxf : Finite x) (hlo : 34657359 / 100000000 ≤ value x)
    (hhi : value x < 10397206 / 10000000) :
    let hi := Wasm.IEEE64.sub x ln2Hi
    let y := Wasm.IEEE64.sub hi ln2Lo
    let c := Wasm.IEEE64.sub (Wasm.IEEE64.sub hi y) ln2Lo
    Finite y ∧ Finite c ∧ |value y| ≤ 3466 / 10000 ∧ |value c| ≤ 36 / 100 * u ∧
      |value y + value c - (value x - Real.log 2)| ≤ 1 / 2 ^ 70 := by
  intro hi y c
  obtain ⟨hHf, hLf, -⟩ := const_finite
  have hL1 := ln2Hi_value
  have hx20 : 2 ^ 1020 ∣ Wasm.IEEE64.scaledMagnitude x :=
    grid_of_magnitude x 1020 (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
  have hl20 : 2 ^ 1020 ∣ Wasm.IEEE64.scaledMagnitude ln2Hi :=
    Nat.pow_dvd_of_le_of_pow_dvd (by norm_num) ln2Hi_grid
  have hb : |value x - value ln2Hi| ≤ 34658 / 100000 := by
    rw [hL1, abs_le]; constructor <;> norm_num <;> linarith
  obtain ⟨hhf, hhv⟩ := diff_exact x ln2Hi hxf hHf 1020 (by norm_num) hx20 hl20
    (hb.trans (by norm_num))
  obtain ⟨hL0, hL2⟩ := ln2Lo_bound
  obtain ⟨hyf, hcf, hy, hc, hyc⟩ := yc_spec hi ln2Lo hhf hLf (by rw [hhv]; exact hb)
    (by rw [abs_of_pos hL0]; linarith)
  refine ⟨hyf, hcf, hy, hc, ?_⟩
  have hs := ln2_split
  rw [hhv] at hyc
  have h1 : value y + value c - (value x - Real.log 2) =
      (value y + value c - (value x - value ln2Hi - value ln2Lo)) +
        (Real.log 2 - value ln2Hi - value ln2Lo) := by ring
  rw [h1]
  refine (abs_add_le _ _).trans ?_
  have : (1 : ℝ) / 2 ^ 74 + 1 / 2 ^ 86 ≤ 1 / 2 ^ 70 := by norm_num
  have h2 : value x - value ln2Hi - value ln2Lo = value x - value ln2Hi - value ln2Lo := rfl
  linarith

/-- `k = -1`: `hi = x + ln2Hi`, `lo = -ln2Lo`. -/
theorem reduce_one_neg (x : UInt64) (hxf : Finite x) (hlo : -(10397206 / 10000000) < value x)
    (hhi : value x ≤ -(34657359 / 100000000)) :
    let hi := Wasm.IEEE64.add x ln2Hi
    let lo := Wasm.IEEE64.negate ln2Lo
    let y := Wasm.IEEE64.sub hi lo
    let c := Wasm.IEEE64.sub (Wasm.IEEE64.sub hi y) lo
    Finite y ∧ Finite c ∧ |value y| ≤ 3466 / 10000 ∧ |value c| ≤ 36 / 100 * u ∧
      |value y + value c - (value x + Real.log 2)| ≤ 1 / 2 ^ 70 := by
  intro hi lo y c
  obtain ⟨hHf, hLf, -⟩ := const_finite
  have hL1 := ln2Hi_value
  have hx20 : 2 ^ 1020 ∣ Wasm.IEEE64.scaledMagnitude x :=
    grid_of_magnitude x 1020 (by rw [abs_of_neg (by linarith)]; norm_num; linarith)
  have hl20 : 2 ^ 1020 ∣ Wasm.IEEE64.scaledMagnitude ln2Hi :=
    Nat.pow_dvd_of_le_of_pow_dvd (by norm_num) ln2Hi_grid
  have hb : |value x + value ln2Hi| ≤ 34658 / 100000 := by
    rw [hL1, abs_le]; constructor <;> norm_num <;> linarith
  obtain ⟨hhf, hhv⟩ := sum_exact x ln2Hi hxf hHf 1020 (by norm_num) hx20 hl20
    (hb.trans (by norm_num))
  obtain ⟨hL0, hL2⟩ := ln2Lo_bound
  obtain ⟨hlof, hlov⟩ := F64Magnitude.negate_value ln2Lo hLf
  obtain ⟨hyf, hcf, hy, hc, hyc⟩ := yc_spec hi lo hhf hlof (by rw [hhv]; exact hb)
    (by rw [hlov, abs_neg, abs_of_pos hL0]; linarith)
  refine ⟨hyf, hcf, hy, hc, ?_⟩
  have hs := ln2_split
  rw [hhv, hlov] at hyc
  have h1 : value y + value c - (value x + Real.log 2) =
      (value y + value c - (value x + value ln2Hi - -value ln2Lo)) -
        (Real.log 2 - value ln2Hi - value ln2Lo) := by ring
  rw [h1]
  refine (abs_sub _ _).trans ?_
  have : (1 : ℝ) / 2 ^ 74 + 1 / 2 ^ 86 ≤ 1 / 2 ^ 70 := by norm_num
  linarith

#print axioms yc_spec
#print axioms reduce_one_pos
#print axioms reduce_one_neg

end Verified.Examples.Expm1ReduceOne
