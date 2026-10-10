import Verified.Examples.ExpSpecialPositive
import Verified.Examples.ExpTableReconstruction
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.RealRoundedError

/-!
The negative special path of `Exp.exp`.  For finite `-768 ≤ a ≤ -512`, the reconstruction `y`
approximates `2 ^ 1022 exp a`.  When `y ≥ 1`, the result is the exact product `2 ^ -1022 y`.
When `y < 1`, the compensated sequence of Arm's `specialcase` rounds `1 + y` once on the grid of
`2 ^ -52`, and the result is the exact product of `2 ^ -1022` and that sum minus 1.  Either way
the result is within one step of the nonnegative nearest-even reference of `exp a`.
-/

namespace Verified.Examples.ExpSpecialNegative
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative F64Magnitude RealRoundedError

set_option exponentiation.threshold 4096

/-- The compensated rounding of `specialCase` for a scaled result `y` below 1. -/
def compensated (s tmp y : Float) : Float :=
  let lo := s - y + s * tmp
  let hi := 1.0 + y
  let lo := 1.0 - hi + y + lo
  let y := hi + lo - 1.0
  if y == 0.0 then 0.0 else y

/-- The negative branch of `specialCase` on the scale `s` and the correction `tmp`. -/
def negativeResult (s tmp : Float) : Float :=
  let y := s + s * tmp
  Float.ofBits 0x0010000000000000 * (if y < 1.0 then compensated s tmp y else y)

def one : UInt64 := 0x3FF0000000000000

/-- The sum `hi + lo` of the compensated sequence, on words, for `y = s + p`. -/
def compSum (s p : UInt64) : UInt64 :=
  let y := Wasm.IEEE64.add s p
  let hi := Wasm.IEEE64.add one y
  let lo := Wasm.IEEE64.add (Wasm.IEEE64.sub s y) p
  Wasm.IEEE64.add hi (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.sub one hi) y) lo)

/-- The compensated value `z - 1`, with a zero result written as positive zero. -/
def compRounded (z : UInt64) : UInt64 :=
  let y := Wasm.IEEE64.sub z one
  if Wasm.IEEE64.eq y 0 then 0 else y

private theorem negative_special_case (tmp : Float) (sbits ki : UInt64)
    (hg : ¬ (ki &&& 0x80000000 == 0) = true) :
    Exp.specialCase tmp sbits ki =
      negativeResult (Float.ofBits (sbits + ((1022 : UInt64) <<< (52 : UInt64)))) tmp := by
  unfold Exp.specialCase
  rw [ite_eq_right hg]
  rfl

theorem core_negative_eq (x : Float)
    (hg : ¬ ((ExpCoreBounds.floatShifted x).toBits &&& 0x80000000 == 0) = true) :
    Exp.expCore Exp.expTable x true =
      negativeResult
        (Float.ofBits (ExpSpecialScale.negativeScale (ExpCoreBounds.floatShifted x).toBits))
        (ExpEvaluationBounds.floatEvaluation (ExpResidualBounds.floatResidual x)
          (Float.ofBits Exp.expTable[(ExpScaleBits.index
            (ExpCoreBounds.floatShifted x).toBits).toNat]!)) := by
  dsimp only [ExpCoreBounds.floatShifted] at hg
  dsimp only [Exp.expCore]
  simp only [ite_true]
  rw [negative_special_case _ _ _ hg]
  simp only [ExpSpecialScale.negativeScale, ExpCoreBounds.floatShifted,
    ExpResidualBounds.floatResidual, ExpReductionSelection.floatInteger,
    ExpEvaluationBounds.floatEvaluation, ExpScaleBits.scaleBits, ExpScaleBits.index]

theorem one_bits : (1.0 : Float).toBits = one := rfl

theorem zero_bits : (0.0 : Float).toBits = 0 := rfl

theorem compensated_bits (s tmp : Float) :
    (compensated s tmp (s + s * tmp)).toBits =
      compRounded (compSum s.toBits (Wasm.IEEE64.mul s.toBits tmp.toBits)) := by
  simp only [compensated, compRounded, compSum, apply_ite Float.toBits, F64Bits.beq_eq,
    F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, one_bits, zero_bits]
  rfl

theorem negativeResult_bits (s tmp : Float) :
    (negativeResult s tmp).toBits =
      Wasm.IEEE64.mul 0x0010000000000000
        (if Wasm.IEEE64.lt (s + s * tmp).toBits one then
          compRounded (compSum s.toBits (Wasm.IEEE64.mul s.toBits tmp.toBits))
        else (s + s * tmp).toBits) := by
  simp only [negativeResult]
  rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits]
  simp only [show Wasm.IEEE64.isNaN 0x0010000000000000 = false by decide, Bool.false_eq_true,
    ite_false]
  congr 1
  by_cases h : s + s * tmp < 1.0
  · rw [ite_eq_left h, ite_eq_left (by rw [← one_bits]; exact (F64Bits.lt_iff _ _).mp h),
      compensated_bits]
  · rw [ite_eq_right h, ite_eq_right
      (by rw [← one_bits]; exact fun h' => h ((F64Bits.lt_iff _ _).mpr h'))]

theorem one_scaled : Wasm.IEEE64.scaledValue one = 2 ^ 1074 := by decide +kernel

theorem one_finite : Finite one := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem one_value : value one = 1 := by
  rw [value, one_scaled, Int.cast_pow, Int.cast_ofNat]
  exact div_self (pow_ne_zero 1074 (two_ne_zero : (2 : ℝ) ≠ 0))

/-- The bounds on `y = s ⊕ p` used by the compensated sequence. -/
theorem comp_y_real (u S P Y0 : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1 / 1024) (hS : 0 < S)
    (hP : |P| ≤ S / 32) (hY : |Y0 - (S + P)| ≤ u * (S + P)) (hY1 : Y0 < 1) :
    0 < Y0 ∧ S + P < 1 + 101 / 100 * u ∧ S < 2 ∧ S + P ≤ 2 * S ∧
      |S + -Y0| ≤ S / 16 := by
  have hPb := abs_le.mp hP
  have hYb := abs_le.mp hY
  have hSP0 : 31 / 32 * S ≤ S + P := by linarith
  have hSP1 : S + P ≤ 33 / 32 * S := by linarith
  have huSP : u * (S + P) ≤ 1 / 1024 * (33 / 32 * S) :=
    mul_le_mul hu1 hSP1 (by linarith) (by norm_num)
  have huSP0 : 0 ≤ u * (S + P) := mul_nonneg hu0.le (by linarith)
  have hY0 : 0 < Y0 := by linarith
  have hlt : S + P < 1 + 101 / 100 * u := by
    by_contra h
    push Not at h
    have hm := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ 1 - u)
    have hsq : u * u ≤ u * (1 / 1024) := mul_le_mul_of_nonneg_left hu1 hu0.le
    nlinarith
  refine ⟨hY0, hlt, by linarith, by linarith, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- The error budget of the compensated sequence: with `e2 = 1 + y - hi` the rounding error of
`hi`, the exact sum `hi + lo2` is within `3 u |e2| + u S / 8` of `1 + S + P`. -/
theorem comp_error_real (u S P Y0 Hi A2 B1 L1 L2 : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1 / 1024)
    (hS : 0 < S) (hSP2 : S + P ≤ 2 * S)
    (hY : |Y0 - (S + P)| ≤ u * (S + P)) (hSY : |S + -Y0| ≤ S / 16)
    (hA2 : |A2 - (1 + Y0 - Hi)| ≤ u * |1 + Y0 - Hi|)
    (hB1 : |B1 - (S + -Y0)| ≤ u * |S + -Y0|)
    (hL1 : |L1 - (B1 + P)| ≤ u * |B1 + P|)
    (hL2 : |L2 - (A2 + L1)| ≤ u * |A2 + L1|) :
    |Hi + L2 - (1 + S + P)| ≤ 3 * u * |1 + Y0 - Hi| + u * S / 8 := by
  set a := |1 + Y0 - Hi| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have huS : 0 ≤ u * S := mul_nonneg hu0.le hS.le
  have hB1' : |B1 - (S + -Y0)| ≤ u * (S / 16) :=
    hB1.trans (mul_le_mul_of_nonneg_left hSY hu0.le)
  have hYS : |Y0 - (S + P)| ≤ u * (2 * S) := hY.trans (mul_le_mul_of_nonneg_left hSP2 hu0.le)
  have hBP : |B1 + P| ≤ 3 * (u * S) := by
    have h1 := abs_le.mp hB1'
    have h2 := abs_le.mp hYS
    rw [abs_le]
    constructor <;> linarith
  have hu3 : u * (3 * (u * S)) ≤ u * S / 64 := by
    have : 3 * u ≤ 1 / 64 := by linarith
    nlinarith
  have hL1' : |L1 - (B1 + P)| ≤ u * S / 64 :=
    (hL1.trans (mul_le_mul_of_nonneg_left hBP hu0.le)).trans hu3
  have hL1v : |L1| ≤ 4 * (u * S) := by
    have h1 := abs_le.mp hL1'
    have h2 := abs_le.mp hBP
    rw [abs_le]
    constructor <;> linarith
  have hua : u * a ≤ a := by nlinarith
  have hA2v : |A2| ≤ 2 * a := by
    have h1 := abs_le.mp hA2
    rw [abs_le]
    constructor <;> cases abs_cases (1 + Y0 - Hi) <;> linarith
  have hAL : |A2 + L1| ≤ 2 * a + 4 * (u * S) := (abs_add_le _ _).trans (add_le_add hA2v hL1v)
  have hu4 : u * (2 * a + 4 * (u * S)) ≤ 2 * (u * a) + u * S / 64 := by
    have : 4 * u ≤ 1 / 64 := by linarith
    nlinarith
  have hL2' : |L2 - (A2 + L1)| ≤ 2 * (u * a) + u * S / 64 :=
    (hL2.trans (mul_le_mul_of_nonneg_left hAL hu0.le)).trans hu4
  have h1 := abs_le.mp hA2
  have h2 := abs_le.mp hB1'
  have h3 := abs_le.mp hL1'
  have h4 := abs_le.mp hL2'
  rw [abs_le]
  constructor <;> linarith

/-- `hi = 1 ⊕ y` for `0 < y < 1`: `1 - hi` is exact, and the rounding error `1 + y - hi` is at
most `u` and at most `y`. -/
theorem comp_hi (y : UInt64) (hyf : Finite y) (hy0 : 0 < value y) (hy1 : value y < 1) :
    Finite (Wasm.IEEE64.add one y) ∧ Finite (Wasm.IEEE64.sub one (Wasm.IEEE64.add one y)) ∧
      value (Wasm.IEEE64.sub one (Wasm.IEEE64.add one y)) = 1 - value (Wasm.IEEE64.add one y) ∧
      |1 + value y - value (Wasm.IEEE64.add one y)| ≤ unitRoundoff64 ∧
      |1 + value y - value (Wasm.IEEE64.add one y)| ≤ value y := by
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  obtain ⟨hhif, ⟨Rh, hRh, hRhl, hRhu⟩, hhie⟩ :=
    F64GridExact.add_binade one y one_finite hyf 1022 (by norm_num) (by norm_num)
      (scaled_ge _ _ 0 (by rw [one_value, pow_zero]; linarith))
      (scaled_lt _ _ 1 (by rw [one_value, pow_one]; linarith))
  rw [half_unit 1022 0 (by norm_num), zpow_zero, one_mul, one_value] at hhie
  have hhiv : value (Wasm.IEEE64.add one y) = (Rh : ℝ) / (2 : ℝ) ^ 52 := by
    rw [grid_value _ Rh 1022 hRh, show (2 : ℝ) ^ 1074 = 2 ^ 52 * 2 ^ 1022 by rw [← pow_add],
      mul_div_mul_right _ _ (pow_ne_zero 1022 (two_ne_zero : (2 : ℝ) ≠ 0))]
  have he2u : |1 + value y - value (Wasm.IEEE64.add one y)| ≤ unitRoundoff64 := by
    rw [abs_sub_comm]
    simpa only [add_comm] using hhie
  obtain ⟨ha1f, ha1s⟩ := F64GridExact.sub_grid_exact one _ one_finite hhif
    ((2 ^ 52 : Int) - Rh) 1022 (by rw [one_scaled, hRh]; ring) (by omega) (by norm_num)
  refine ⟨hhif, ha1f, ?_, he2u, ?_⟩
  · rw [← one_value]
    simp only [value, ha1s]
    rw [Int.cast_sub, sub_div]
  · by_cases hsmall : value y < unitRoundoff64
    · have hRh2 : Rh = 2 ^ 52 := by
        have hb := abs_le.mp hhie
        have hv : value (Wasm.IEEE64.add one y) < 1 + 2 * unitRoundoff64 := by linarith
        rw [hhiv, hu, div_lt_iff₀ (by positivity)] at hv
        have h2 : (1 + 2 * (1 / (2 : ℝ) ^ 53)) * 2 ^ 52 = 2 ^ 52 + 1 := by norm_num
        have hv' : (Rh : ℝ) < 2 ^ 52 + 1 := by linarith
        have : Rh < 2 ^ 52 + 1 := by exact_mod_cast hv'
        omega
      have hv1 : value (Wasm.IEEE64.add one y) = 1 := by
        rw [hhiv, hRh2, Nat.cast_pow, Nat.cast_ofNat]
        exact div_self (pow_ne_zero 52 (two_ne_zero : (2 : ℝ) ≠ 0))
      rw [hv1, show 1 + value y - 1 = value y by ring, abs_of_pos hy0]
    · exact he2u.trans (le_of_not_gt hsmall)

/-- The final rounding `z = hi ⊕ lo` of a sum in `[1, 2 + 3u/2)`: `z` lies on the grid of
`2 ^ -52` in `[1, 2]`, within `2 u` of the sum. -/
theorem comp_round (hi lo : UInt64) (hhif : Finite hi) (hlof : Finite lo)
    (hl : 1 ≤ value hi + value lo) (hh : value hi + value lo < 2 + 3 / 2 * unitRoundoff64) :
    Finite (Wasm.IEEE64.add hi lo) ∧
      (∃ R : Nat, Wasm.IEEE64.scaledValue (Wasm.IEEE64.add hi lo) = (R : Int) * 2 ^ 1022 ∧
        2 ^ 52 ≤ R ∧ R ≤ 2 ^ 53) ∧
      |value (Wasm.IEEE64.add hi lo) - (value hi + value lo)| ≤ 2 * unitRoundoff64 := by
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hu0 : 0 < unitRoundoff64 := by rw [hu]; positivity
  by_cases htwo : value hi + value lo < 2
  · obtain ⟨hzf, ⟨Rz, hRz, hRzl, hRzu⟩, hze⟩ :=
      F64GridExact.add_binade hi lo hhif hlof 1022 (by norm_num) (by norm_num)
        (scaled_ge _ _ 0 (by rw [pow_zero]; exact hl))
        (scaled_lt _ _ 1 (by rw [pow_one]; exact htwo))
    rw [half_unit 1022 0 (by norm_num), zpow_zero, one_mul] at hze
    exact ⟨hzf, ⟨Rz, hRz, hRzl, hRzu⟩, by linarith⟩
  · push Not at htwo
    have hu4 : 2 + 3 / 2 * unitRoundoff64 < (2 : ℝ) ^ 2 := by rw [hu]; norm_num
    obtain ⟨hzf, ⟨Rz, hRz, hRzl, hRzu⟩, hze⟩ :=
      F64GridExact.add_binade hi lo hhif hlof 1023 (by norm_num) (by norm_num)
        (scaled_ge _ _ 1 (by rw [pow_one]; exact htwo))
        (scaled_lt _ _ 2 (by linarith))
    rw [half_unit 1023 1 (by norm_num), zpow_one] at hze
    have hzv : value (Wasm.IEEE64.add hi lo) = (Rz : ℝ) / (2 : ℝ) ^ 51 := by
      rw [grid_value _ Rz 1023 hRz, show (2 : ℝ) ^ 1074 = 2 ^ 51 * 2 ^ 1023 by rw [← pow_add],
        mul_div_mul_right _ _ (pow_ne_zero 1023 (two_ne_zero : (2 : ℝ) ≠ 0))]
    have hRz2 : Rz = 2 ^ 52 := by
      have hb := abs_le.mp hze
      have hv : value (Wasm.IEEE64.add hi lo) < 2 + 4 * unitRoundoff64 := by linarith
      rw [hzv, hu, div_lt_iff₀ (by positivity)] at hv
      have h2 : (2 + 4 * (1 / (2 : ℝ) ^ 53)) * 2 ^ 51 = 2 ^ 52 + 1 := by norm_num
      have hv' : (Rz : ℝ) < 2 ^ 52 + 1 := by linarith
      have : Rz < 2 ^ 52 + 1 := by exact_mod_cast hv'
      omega
    refine ⟨hzf, ⟨2 ^ 53, by rw [hRz, hRz2]; ring, by norm_num, le_rfl⟩, ?_⟩
    have hb := abs_le.mp hze
    rw [abs_le]
    constructor <;> linarith

/-- The sum `z = hi + lo` of the compensated sequence for `y = s ⊕ p < 1` lies in `[1, 2]` on the
grid of `2 ^ -52` and is within `2 u + 3 u ^ 2 + u s / 8` of `1 + s + p`. -/
theorem comp_sum_bounds (s p : UInt64) (hsf : Finite s) (hpf : Finite p)
    (hS : 0 < value s) (hS2 : value s ≤ (2 : ℝ) ^ 1000) (hP : |value p| ≤ value s / 32)
    (hy1 : value (Wasm.IEEE64.add s p) < 1) :
    Finite (compSum s p) ∧
      (∃ R : Nat, Wasm.IEEE64.scaledValue (compSum s p) = (R : Int) * 2 ^ 1022 ∧
        2 ^ 52 ≤ R ∧ R ≤ 2 ^ 53) ∧
      |value (compSum s p) - (1 + value s + value p)| ≤
        2 * unitRoundoff64 + 3 * unitRoundoff64 ^ 2 + unitRoundoff64 * value s / 8 ∧
      value s < 2 := by
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hu0 : 0 < unitRoundoff64 := by rw [hu]; positivity
  have hu1 : unitRoundoff64 ≤ 1 / 1024 := by rw [hu]; norm_num
  have hu1' : unitRoundoff64 ≤ 1 := by linarith
  have hbig : (2 : ℝ) ^ 1000 * 4 < (2 : ℝ) ^ 1023 := by norm_num
  have hPb := abs_le.mp hP
  have hSPb : |value s + value p| < (2 : ℝ) ^ 1023 := by
    rw [abs_lt]
    constructor <;> linarith
  obtain ⟨hyf, hye⟩ := F64AddBounds.add_real_relative s p hsf hpf hSPb
  rw [abs_of_pos (by linarith : 0 < value s + value p)] at hye
  obtain ⟨hy0, hSP1, hSlt, hSP2, hSY⟩ :=
    comp_y_real _ _ _ _ hu0 hu1 hS hP hye hy1
  set y := Wasm.IEEE64.add s p with hy_def
  obtain ⟨hhif, ha1f, ha1v, he2u, he2y⟩ := comp_hi y hyf hy0 hy1
  set hi := Wasm.IEEE64.add one y with hhi_def
  -- a2 = (1 - hi) + y
  have hsum2 : |value (Wasm.IEEE64.sub one hi) + value y| < (2 : ℝ) ^ 1023 := by
    rw [ha1v, show 1 - value hi + value y = 1 + value y - value hi by ring]
    exact he2u.trans_lt (by rw [hu]; norm_num)
  obtain ⟨ha2f, ha2e⟩ := F64AddBounds.add_real_relative _ y ha1f hyf hsum2
  rw [ha1v, show 1 - value hi + value y = 1 + value y - value hi by ring] at ha2e
  have ha2v : |value (Wasm.IEEE64.add (Wasm.IEEE64.sub one hi) y)| ≤ 2 := by
    have := rel_bound hu1' ha2e
    have h1 : |1 + value y - value hi| ≤ 1 := he2u.trans hu1'
    linarith
  -- b1 = s - y
  obtain ⟨hnyf, hnyv⟩ := negate_value y hyf
  have hsum3 : |value s + value (Wasm.IEEE64.negate y)| < (2 : ℝ) ^ 1023 := by
    rw [hnyv]
    exact hSY.trans_lt (by linarith)
  obtain ⟨hb1f, hb1e⟩ := F64AddBounds.add_real_relative s _ hsf hnyf hsum3
  rw [hnyv] at hb1e
  have hb1v : |value (Wasm.IEEE64.add s (Wasm.IEEE64.negate y))| ≤ 1 := by
    have := rel_bound hu1' hb1e
    have h1 := abs_le.mp hSY
    have h2 : |value s + -value y| ≤ 1 / 8 := by linarith
    linarith
  -- lo1 = b1 + p
  have hb1p : |value (Wasm.IEEE64.add s (Wasm.IEEE64.negate y)) + value p| ≤ 2 := by
    have := abs_add_le (value (Wasm.IEEE64.add s (Wasm.IEEE64.negate y))) (value p)
    have h2 : |value p| ≤ 1 := by linarith
    linarith
  obtain ⟨hlo1f, hlo1e⟩ := F64AddBounds.add_real_relative _ p hb1f hpf
    (hb1p.trans_lt (by norm_num))
  have hlo1v := rel_bound hu1' hlo1e
  -- lo2 = a2 + lo1
  have hsum5 : |value (Wasm.IEEE64.add (Wasm.IEEE64.sub one hi) y) +
      value (Wasm.IEEE64.add (Wasm.IEEE64.add s (Wasm.IEEE64.negate y)) p)| < (2 : ℝ) ^ 1023 := by
    have := abs_add_le (value (Wasm.IEEE64.add (Wasm.IEEE64.sub one hi) y))
      (value (Wasm.IEEE64.add (Wasm.IEEE64.add s (Wasm.IEEE64.negate y)) p))
    have h8 : (8 : ℝ) < 2 ^ 1023 := by norm_num
    linarith
  obtain ⟨hlo2f, hlo2e⟩ := F64AddBounds.add_real_relative _ _ ha2f hlo1f hsum5
  have hε := comp_error_real unitRoundoff64 (value s) (value p) (value y) (value hi)
    (value (Wasm.IEEE64.add (Wasm.IEEE64.sub one hi) y))
    (value (Wasm.IEEE64.add s (Wasm.IEEE64.negate y)))
    (value (Wasm.IEEE64.add (Wasm.IEEE64.add s (Wasm.IEEE64.negate y)) p))
    (value (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.sub one hi) y)
      (Wasm.IEEE64.add (Wasm.IEEE64.add s (Wasm.IEEE64.negate y)) p)))
    hu0 hu1 hS hSP2 hye hSY ha2e hb1e hlo1e hlo2e
  set lo2 := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.sub one hi) y)
      (Wasm.IEEE64.add (Wasm.IEEE64.add s (Wasm.IEEE64.negate y)) p) with hlo2_def
  have h3u : 3 * unitRoundoff64 * |1 + value y - value hi| ≤ 3 * unitRoundoff64 ^ 2 := by
    have := mul_le_mul_of_nonneg_left he2u (by positivity : (0 : ℝ) ≤ 3 * unitRoundoff64)
    rw [sq]
    linarith
  have hεu : |value hi + value lo2 - (1 + value s + value p)| ≤
      3 * unitRoundoff64 ^ 2 + unitRoundoff64 * value s / 8 := by linarith
  have hy3 : value y ≤ 3 * value s := by
    have h1 := abs_le.mp hye
    have h2 : unitRoundoff64 * (value s + value p) ≤ 1 / 1024 * (2 * value s) :=
      mul_le_mul hu1 hSP2 (by linarith) (by norm_num)
    linarith
  have hεy : |value hi + value lo2 - (1 + value s + value p)| ≤ value s / 64 := by
    have h1 : 3 * unitRoundoff64 * |1 + value y - value hi| ≤ 3 * unitRoundoff64 * (3 * value s) :=
      mul_le_mul_of_nonneg_left (he2y.trans hy3) (by positivity)
    have h2 : unitRoundoff64 * value s ≤ 1 / 1024 * value s :=
      mul_le_mul_of_nonneg_right hu1 hS.le
    linarith
  have hsumlo : 1 ≤ value hi + value lo2 := by
    have := abs_le.mp hεy
    linarith
  have hsumhi : value hi + value lo2 < 2 + 3 / 2 * unitRoundoff64 := by
    have h1 := abs_le.mp hεu
    have h2 : unitRoundoff64 ^ 2 ≤ 1 / 1024 * unitRoundoff64 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hu1 hu0.le
    have h3 : unitRoundoff64 * value s ≤ unitRoundoff64 * 2 :=
      mul_le_mul_of_nonneg_left hSlt.le hu0.le
    linarith
  obtain ⟨hzf, hzR, hze⟩ := comp_round hi lo2 hhif hlo2f hsumlo hsumhi
  have hzdef : compSum s p = Wasm.IEEE64.add hi lo2 := rfl
  rw [hzdef]
  refine ⟨hzf, hzR, ?_, hSlt⟩
  have h1 := abs_le.mp hze
  have h2 := abs_le.mp hεu
  rw [abs_le]
  constructor <;> linarith

#print axioms core_negative_eq
#print axioms compensated_bits
#print axioms negativeResult_bits
#print axioms comp_hi
#print axioms comp_round
#print axioms comp_sum_bounds

end Verified.Examples.ExpSpecialNegative
