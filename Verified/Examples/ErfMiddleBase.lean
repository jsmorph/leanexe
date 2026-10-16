import Verified.Examples.ErfKernelMiddle
import Verified.Examples.ErfSmallBase

/-!
The rounding error on the middle range `[0.84375, 1.25)` of `s_erf.c`.  There `s = |x| - 1` is
exact (`sub_one_exact`), `P` and `Q` are evaluated by Horner's rule at `s`, and `erf |x|` is
`erx + P/Q` rounded once more.  For `s` in `[slo, shi]`, `middleOK` checks with one
`decide +kernel` that the quotient's error `middleErr` from `F64Horner.hornerW_approx` and
`F64DivApprox.div_approx`, plus the kernel's `(21/16) 2^-58`, stays below the spacing `2^-53` of
`[1/2, 1)` and that `erf x` lies in that binade.  `middle_erf` then gives one step through the
nearest rounding of the final sum.
-/

namespace Verified.Examples.ErfMiddleBase
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyChecks PolyCalculus F64ErrorTrack F64Horner
  ErfKernelSmall ErfKernelMiddle ErfSmallBase RealErf

set_option exponentiation.threshold 4096

/-- The words of `pa0, ..., pa6`. -/
def paW : List UInt64 :=
  [0xBF6359B8BEF77538, 0x3FDA8D00AD92B34D, 0xBFD7D240FBB8C3F1, 0x3FD45FCA805120E4,
    0xBFBC63983D3E28EC, 0x3FA22A36599795EB, 0xBF61BF380A96073F]

/-- The words of `1, qa1, ..., qa6`. -/
def qaW : List UInt64 :=
  [0x3FF0000000000000, 0x3FBB3E6618EEE323, 0x3FE14AF092EB6F33, 0x3FB2635CD99FE9A7,
    0x3FC02660E763351F, 0x3F8BEDC26B51DD1C, 0x3F888B545735151D]

theorem erfMiddle_bits (s : Float) :
    (Erf.erfMiddle s).1.toBits = hornerW paW s.toBits ∧
      (Erf.erfMiddle s).2.toBits = hornerW qaW s.toBits := by
  have hone : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
  have n0 : Wasm.IEEE64.isNaN 0xBF6359B8BEF77538 = false := by decide
  have n1 : Wasm.IEEE64.isNaN 0x3FDA8D00AD92B34D = false := by decide
  have n2 : Wasm.IEEE64.isNaN 0xBFD7D240FBB8C3F1 = false := by decide
  have n3 : Wasm.IEEE64.isNaN 0x3FD45FCA805120E4 = false := by decide
  have n4 : Wasm.IEEE64.isNaN 0xBFBC63983D3E28EC = false := by decide
  have n5 : Wasm.IEEE64.isNaN 0x3FA22A36599795EB = false := by decide
  have n6 : Wasm.IEEE64.isNaN 0xBF61BF380A96073F = false := by decide
  have m1 : Wasm.IEEE64.isNaN 0x3FBB3E6618EEE323 = false := by decide
  have m2 : Wasm.IEEE64.isNaN 0x3FE14AF092EB6F33 = false := by decide
  have m3 : Wasm.IEEE64.isNaN 0x3FB2635CD99FE9A7 = false := by decide
  have m4 : Wasm.IEEE64.isNaN 0x3FC02660E763351F = false := by decide
  have m5 : Wasm.IEEE64.isNaN 0x3F8BEDC26B51DD1C = false := by decide
  have m6 : Wasm.IEEE64.isNaN 0x3F888B545735151D = false := by decide
  constructor <;>
  simp only [Erf.erfMiddle, paW, qaW, hornerW, F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, hone, n0, n1, n2, n3, n4, n5, n6, m1, m2, m3, m4, m5, m6,
    Bool.false_eq_true, ↓reduceIte]

theorem pa_rel : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ))
    paW erfPA := by
  simp only [paW, erfPA, List.forall₂_cons, List.Forall₂.nil, and_true, ratOfWord_cast]
  unfold CodeLib.IEEE64.Finite
  decide

theorem qa_rel : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ))
    qaW erfQA := by
  simp only [qaW, erfQA, List.forall₂_cons, List.Forall₂.nil, and_true, ratOfWord_cast,
    Rat.cast_one, one_value]
  unfold CodeLib.IEEE64.Finite
  decide

/-- The bound on the computed `P/Q` against `P (s)/Q (s)`. -/
def middleErr (slo shi : ℚ) : ℚ :=
  let eP := hornerErr erfPA slo shi
  let eQ := hornerErr erfQA slo shi
  let MP := magBound erfPA slo shi
  let mQ := lowBound erfQA slo shi
  eP / (mQ - eQ) + MP * eQ / ((mQ - eQ) * mQ) + uQ * ((MP + eP) / (mQ - eQ)) + etaQ

/-- The middle kernel's error bound. -/
def middleKern : ℚ := (21 / 16) / 2 ^ 58

/-- The rational conditions of `middle_erf` for `s` in `[slo, shi]`. -/
def middleOK (slo shi : ℚ) : Bool :=
  decide (-5 / 32 ≤ slo) && decide (slo ≤ shi) && decide (shi ≤ 1 / 4) &&
    hornerOK erfPA slo shi && hornerOK erfQA slo shi &&
    decide (hornerErr erfQA slo shi < lowBound erfQA slo shi) &&
    decide (0 < lowBound erfQA slo shi) &&
    decide ((magBound erfPA slo shi + hornerErr erfPA slo shi) /
      (lowBound erfQA slo shi - hornerErr erfQA slo shi) < 2 ^ 1000) &&
    decide (middleErr slo shi + middleKern < 1 / 2 ^ 53) &&
    decide (1 / 2 + (middleErr slo shi + middleKern) + middleKern ≤
      erx - magBound erfPA slo shi / lowBound erfQA slo shi)

/-- The value of the word of `erx`. -/
theorem erx_value : value (0x3FEB0AC160000000 : UInt64) = (erx : ℝ) := by
  rw [erx, ratOfWord_cast]

/-- One step for `erf x` on the middle range, from the word `S` of `s = x - 1`. -/
theorem middle_erf (slo shi : ℚ) (hok : middleOK slo shi = true) (X S : UInt64)
    (hS : Finite S) (hSv : value S = value X - 1) (hsl : (slo : ℝ) ≤ value S)
    (hsh : value S ≤ shi) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add 0x3FEB0AC160000000
        (Wasm.IEEE64.div (hornerW paW S) (hornerW qaW S))) := by
  simp only [middleOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hs0, hs01⟩, hs1⟩, hokP⟩, hokQ⟩, hQe⟩, hmQ⟩, hmaxq⟩, hcrit⟩, hbin⟩ := hok
  set s := value S
  have hu : unitRoundoff64 = ((uQ : ℚ) : ℝ) := uQ_eq.symm
  have he : multiplicationUnderflowEpsilon = ((etaQ : ℚ) : ℝ) := etaQ_eq.symm
  have hP := hornerW_approx erfPA paW pa_rel (by simp [erfPA]) slo shi S hS hsl hsh hokP
  have hQ := hornerW_approx erfQA qaW qa_rel (by simp [erfQA]) slo shi S hS hsl hsh hokQ
  have hMP : |eval erfPA s| ≤ ((magBound erfPA slo shi : ℚ) : ℝ) :=
    magBound_sound erfPA slo shi s hsl hsh
  have hmQs : ((lowBound erfQA slo shi : ℚ) : ℝ) ≤ eval erfQA s :=
    lowBound_sound erfQA slo shi s hsl hsh
  have hQe' : ((hornerErr erfQA slo shi : ℚ) : ℝ) < lowBound erfQA slo shi := by
    exact_mod_cast hQe
  have hmQ' : (0 : ℝ) < lowBound erfQA slo shi := by exact_mod_cast hmQ
  have hmaxq' : (((magBound erfPA slo shi : ℚ) : ℝ) + hornerErr erfPA slo shi) /
      ((lowBound erfQA slo shi : ℝ) - hornerErr erfQA slo shi) < 2 ^ 1022 := by
    have h : ((((magBound erfPA slo shi + hornerErr erfPA slo shi) /
        (lowBound erfQA slo shi - hornerErr erfQA slo shi)) : ℚ) : ℝ) < 2 ^ 1000 := by
      exact_mod_cast hmaxq
    push_cast at h
    linarith [show (2 : ℝ) ^ 1000 ≤ 2 ^ 1022 by norm_num]
  have hD := F64DivApprox.div_approx hP hQ _ _ hMP hmQs hQe' hmaxq'
  have hDe : |value (Wasm.IEEE64.div (hornerW paW S) (hornerW qaW S)) -
      eval erfPA s / eval erfQA s| ≤ ((middleErr slo shi : ℚ) : ℝ) := by
    have h := hD.2
    have hdef : ((middleErr slo shi : ℚ) : ℝ) =
        ((hornerErr erfPA slo shi : ℚ) : ℝ) /
            ((lowBound erfQA slo shi : ℝ) - hornerErr erfQA slo shi) +
          (magBound erfPA slo shi : ℝ) * hornerErr erfQA slo shi /
            (((lowBound erfQA slo shi : ℝ) - hornerErr erfQA slo shi) * lowBound erfQA slo shi) +
          unitRoundoff64 * (((magBound erfPA slo shi : ℝ) + hornerErr erfPA slo shi) /
            ((lowBound erfQA slo shi : ℝ) - hornerErr erfQA slo shi)) +
          multiplicationUnderflowEpsilon := by
      rw [hu, he]
      simp only [middleErr]
      push_cast
      ring
    rw [hdef]
    exact h
  -- the kernel
  have hsl' : (-5 / 32 : ℝ) ≤ s := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs0
    push_cast at h
    exact le_trans h hsl
  have hsh' : s ≤ (1 / 4 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs1
    push_cast at h
    exact le_trans hsh h
  have hk := middle_kernel_error s hsl' hsh'
  have hx : 1 + s = value X := by rw [hSv]; ring
  rw [hx] at hk
  have hQpos : 0 < eval erfQA s := lt_of_lt_of_le hmQ' hmQs
  have hR : |eval erfPA s / eval erfQA s| ≤
      ((magBound erfPA slo shi / lowBound erfQA slo shi : ℚ) : ℝ) := by
    rw [abs_div, abs_of_pos hQpos]
    push_cast
    exact div_le_div₀ ((abs_nonneg _).trans hMP) hMP hmQ' hmQs
  set D := Wasm.IEEE64.div (hornerW paW S) (hornerW qaW S)
  have hcrit' : ((middleErr slo shi : ℚ) : ℝ) + middleKern < 1 / 2 ^ 53 := by
    have h : (((middleErr slo shi + middleKern) : ℚ) : ℝ) < ((1 / 2 ^ 53 : ℚ) : ℝ) := by
      exact_mod_cast hcrit
    push_cast at h
    exact h
  have hbin' : 1 / 2 + (((middleErr slo shi : ℚ) : ℝ) + middleKern) + middleKern ≤
      (erx : ℝ) - ((magBound erfPA slo shi / lowBound erfQA slo shi : ℚ) : ℝ) := by
    have h : (((1 / 2 + (middleErr slo shi + middleKern) + middleKern) : ℚ) : ℝ) ≤
        (((erx - magBound erfPA slo shi / lowBound erfQA slo shi) : ℚ) : ℝ) := by
      exact_mod_cast hbin
    push_cast at h ⊢
    linarith
  have hkern : ((middleKern : ℚ) : ℝ) = (21 / 16) / 2 ^ 58 := by simp [middleKern]
  have herr : |value 0x3FEB0AC160000000 + value D - erf (value X)| ≤
      ((middleErr slo shi : ℚ) : ℝ) + middleKern := by
    rw [erx_value, hkern]
    have h1 := abs_sub_le ((erx : ℝ) + value D) ((erx : ℝ) + eval erfPA s / eval erfQA s)
      (erf (value X))
    have h2 : |(erx : ℝ) + value D - ((erx : ℝ) + eval erfPA s / eval erfQA s)| =
        |value D - eval erfPA s / eval erfQA s| := by ring_nf
    have h3 : |(erx : ℝ) + eval erfPA s / eval erfQA s - erf (value X)| =
        |erf (value X) - erx - eval erfPA s / eval erfQA s| := by
      rw [abs_sub_comm]
      ring_nf
    linarith
  have hylo : 1 / 2 + (((middleErr slo shi : ℚ) : ℝ) + middleKern) ≤ erf (value X) := by
    have h := (abs_le.mp hk).1
    have h2 := (abs_le.mp hR).1
    rw [hkern] at hbin'
    linarith
  have hvl := (abs_le.mp herr).1
  have hvu := (abs_le.mp herr).2
  have hy1 := erf_lt_one (value X)
  have hE0 : (0 : ℝ) ≤ ((middleErr slo shi : ℚ) : ℝ) + middleKern := (abs_nonneg _).trans herr
  have hDf : Finite D := hD.1
  have herxf : Finite (0x3FEB0AC160000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  have hn := F64NearestSum.add_nearest _ D herxf hDf (by linarith)
    (by linarith [show (2 : ℝ) ≤ 2 ^ 1023 by norm_num])
  have hb : value (UInt64.ofNat (1022 * 2 ^ 52)) = 1 / 2 := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    norm_num
  refine F64AddNearest.within_of_nearest 1 le_rfl (erf (value X)) _ _ 1022 (by norm_num)
    (by norm_num) (by rw [hb]; linarith) (by rw [hb]; linarith) ?_ hn ?_
  · have h : (1 : ℝ) < F64PositiveRounding.overflowThreshold := by
      rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 from rfl]
      norm_num
    linarith
  · have hsp2 : ((1 : Nat) : ℝ) * ((2 : ℝ) ^ (1022 - 1) / (2 : ℝ) ^ 1074) = 1 / 2 ^ 53 := by
      norm_num
    rw [hsp2]
    linarith

/-- `x - 1` is exact for `x` in `[1/2, 2]`. -/
theorem sub_one_exact (X : UInt64) (hX : Finite X) (hlo : 1 / 2 ≤ value X) (hhi : value X ≤ 2) :
    Finite (Wasm.IEEE64.sub X 0x3FF0000000000000) ∧
      value (Wasm.IEEE64.sub X 0x3FF0000000000000) = value X - 1 := by
  have hone : Finite (0x3FF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  have h1022 : (1 : ℝ) / 2 ^ 1022 < 1 / 2 := by norm_num
  have hnorm := F64Magnitude.normal_of_value X (by linarith)
  have he : 1022 ≤ Wasm.IEEE64.exponent X :=
    F64Magnitude.exponent_ge_of_value X 1022 (by norm_num) (by norm_num; linarith)
  have hsv : Wasm.IEEE64.scaledValue X =
      (((2 ^ 52 + Wasm.IEEE64.fraction X) * 2 ^ (Wasm.IEEE64.exponent X - 1) : ℕ) : Int) := by
    have h0 : (Wasm.IEEE64.exponent X == 0) = false := beq_false_of_ne (by omega)
    simp [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, hnorm.2, h0]
  have hone_sv : Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) = 2 ^ 1074 := by
    decide +kernel
  have h := F64ErrorTrack.sub_exact_grid X _ hX hone 1021 (by norm_num) (by
    rw [hsv]
    have h1 : (2 : ℕ) ^ 1021 ∣ (2 ^ 52 + Wasm.IEEE64.fraction X) * 2 ^ (Wasm.IEEE64.exponent X - 1) :=
      Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
    exact_mod_cast Int.natCast_dvd_natCast.mpr h1) (by
    rw [hone_sv]
    exact pow_dvd_pow 2 (by norm_num)) (by
    have hv : (Wasm.IEEE64.scaledValue X : ℝ) = value X * 2 ^ 1074 := by
      simp only [value]
      field_simp
    have h1 : |(Wasm.IEEE64.scaledValue X : ℝ) - (2 : ℝ) ^ 1074| ≤ 2 ^ 53 * 2 ^ 1021 := by
      rw [hv, show value X * 2 ^ 1074 - (2 : ℝ) ^ 1074 = (value X - 1) * 2 ^ 1074 by ring,
        abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
      have h2 : |value X - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |value X - 1| * 2 ^ 1074 ≤ 1 * 2 ^ 1074 :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = 2 ^ 53 * 2 ^ 1021 := by norm_num
    rw [hone_sv]
    exact_mod_cast h1)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  have h1 : value (0x3FF0000000000000 : UInt64) = 1 := one_value
  rw [h1]

#print axioms erfMiddle_bits
#print axioms pa_rel
#print axioms qa_rel
#print axioms middle_erf
#print axioms sub_one_exact

end Verified.Examples.ErfMiddleBase
