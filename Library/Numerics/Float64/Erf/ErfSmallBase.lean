import Library.Numerics.Float64.Erf.ErfKernelSmall
import Library.Numerics.Float64.Erf.Compiled
import LeanExe.ProofKit.F64Horner
import LeanExe.ProofKit.F64DivApprox
import LeanExe.ProofKit.F64AddNearest
import LeanExe.ProofKit.F64Bits

/-!
The rounding error of `x R̂` on the first range of `s_erf.c`, where `R̂ = erfSmall (x x)` is the
computed `pp/qq` at the computed `z = x x`.  For `|x|` in `[xlo, xhi]` and `z` in `[zlo, zhi]`,
`small_core` bounds `|x R̂ - x R (x²)|` by `|x| smallErr + 2^-1075`, from `F64Horner.hornerW_approx`
for `pp` and `qq`, `F64DivApprox.div_approx` for the quotient, the change of `R = pp/qq` between `z`
and `x²` (`F64DivApprox.ratio_lipschitz`, with the derivative's numerator bounded by `magBound` and
`qq` by `lowBound`), and `F64ErrorTrack.mul_approx` for the product.  `smallOK` collects the rational
conditions that one `decide +kernel` checks for each interval.  `small_erf_rel` and `small_erf_top`
turn the bound into one representable step for `erf` through the nearest rounding of the final sum:
relative to `erf x ≥ κ x (1 - x²/3)` below `1/2`, and against the spacing `2^-53` of `[1/2, 1)`.
-/

namespace Library.Numerics.Float64.Erf.ErfSmallBase
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyChecks PolyCalculus F64ErrorTrack F64Horner
  ErfKernelSmall RealErf

set_option exponentiation.threshold 4096

/-- The words of `pp0, ..., pp4`. -/
def ppW : List UInt64 :=
  [0x3FC06EBA8214DB68, 0xBFD4CD7D691CB913, 0xBF9D2A51DBD7194F, 0xBF77A291236668E4,
    0xBEF8EAD6120016AC]

/-- The words of `1, qq1, ..., qq5`. -/
def qqW : List UInt64 :=
  [0x3FF0000000000000, 0x3FD97779CDDADC09, 0x3FB0A54C5536CEBA, 0x3F74D022C4D36B0F,
    0x3F215DC9221C1A10, 0xBED09C4342A26120]

theorem erfSmall_bits (z : Float) :
    (Erf.erfSmall z).toBits = Wasm.IEEE64.div (hornerW ppW z.toBits) (hornerW qqW z.toBits) := by
  have hone : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
  have n0 : Wasm.IEEE64.isNaN 0x3FC06EBA8214DB68 = false := by decide
  have n1 : Wasm.IEEE64.isNaN 0xBFD4CD7D691CB913 = false := by decide
  have n2 : Wasm.IEEE64.isNaN 0xBF9D2A51DBD7194F = false := by decide
  have n3 : Wasm.IEEE64.isNaN 0xBF77A291236668E4 = false := by decide
  have n4 : Wasm.IEEE64.isNaN 0xBEF8EAD6120016AC = false := by decide
  have n5 : Wasm.IEEE64.isNaN 0x3FD97779CDDADC09 = false := by decide
  have n6 : Wasm.IEEE64.isNaN 0x3FB0A54C5536CEBA = false := by decide
  have n7 : Wasm.IEEE64.isNaN 0x3F74D022C4D36B0F = false := by decide
  have n8 : Wasm.IEEE64.isNaN 0x3F215DC9221C1A10 = false := by decide
  have n9 : Wasm.IEEE64.isNaN 0xBED09C4342A26120 = false := by decide
  simp only [Erf.erfSmall, ppW, qqW, hornerW, F64Bits.toBits_div, F64Bits.toBits_add,
    F64Bits.toBits_mul, F64Bits.toBits_ofBits, hone, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9,
    Bool.false_eq_true, ↓reduceIte]

theorem pp_rel : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ))
    ppW erfPP := by
  simp only [ppW, erfPP, List.forall₂_cons, List.Forall₂.nil, and_true, ratOfWord_cast]
  unfold CodeLib.IEEE64.Finite
  decide

theorem one_value : value (0x3FF0000000000000 : UInt64) = 1 := by
  have h : Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) = 2 ^ 1074 := by decide +kernel
  rw [value, h]
  norm_num

theorem qq_rel : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ))
    qqW erfQQ := by
  simp only [qqW, erfQQ, List.forall₂_cons, List.Forall₂.nil, and_true, ratOfWord_cast,
    Rat.cast_one, one_value]
  unfold CodeLib.IEEE64.Finite
  decide

/-- `P' Q - P Q'` for `P = pp` and `Q = qq`. -/
def smallDer : List ℚ := subP (mulP (derivP erfPP) erfQQ) (mulP erfPP (derivP erfQQ))

theorem eval_smallDer (t : ℝ) :
    eval smallDer t =
      eval (derivP erfPP) t * eval erfQQ t - eval erfPP t * eval (derivP erfQQ) t := by
  simp only [smallDer, eval_subP, eval_mulP]

/-- The bound on `|R̂ - R (x²)|`: the quotient's error at the computed `z` and the change of `R`
from `x²` to `z`. -/
def smallRatioErr (xhi zlo zhi : ℚ) : ℚ :=
  let eP := hornerErr erfPP zlo zhi
  let eQ := hornerErr erfQQ zlo zhi
  let MP := magBound erfPP zlo zhi
  let mQ := lowBound erfQQ zlo zhi
  let L := magBound smallDer zlo zhi / mQ ^ 2
  (eP / (mQ - eQ) + MP * eQ / ((mQ - eQ) * mQ) + uQ * ((MP + eP) / (mQ - eQ)) + etaQ) +
    L * (uQ * xhi ^ 2 + etaQ)

/-- The bound on `|x R̂ - x R (x²)|` relative to `|x|`. -/
def smallErr (xhi zlo zhi : ℚ) : ℚ :=
  smallRatioErr xhi zlo zhi +
    uQ * (magBound erfPP zlo zhi / lowBound erfQQ zlo zhi + smallRatioErr xhi zlo zhi)

/-- The rational conditions of `small_core` for one interval. -/
def smallOK (xlo xhi zlo zhi : ℚ) : Bool :=
  decide (0 < xlo) && decide (xlo ≤ xhi) && decide (xhi < 1) && decide (0 ≤ zlo) &&
    decide (zlo ≤ xlo ^ 2 * (1 - uQ) - etaQ) && decide (xhi ^ 2 * (1 + uQ) + etaQ ≤ zhi) &&
    hornerOK erfPP zlo zhi && hornerOK erfQQ zlo zhi &&
    decide (hornerErr erfQQ zlo zhi < lowBound erfQQ zlo zhi) &&
    decide (0 < lowBound erfQQ zlo zhi) &&
    decide ((magBound erfPP zlo zhi + hornerErr erfPP zlo zhi) /
      (lowBound erfQQ zlo zhi - hornerErr erfQQ zlo zhi) < 2 ^ 1000) &&
    decide (magBound erfPP zlo zhi / lowBound erfQQ zlo zhi + smallRatioErr xhi zlo zhi < 1)

theorem smallOK_pos (xlo xhi zlo zhi : ℚ) (hok : smallOK xlo xhi zlo zhi = true) : 0 < xlo := by
  simp only [smallOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hx0, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hok
  exact hx0

/-- The computed `x R̂` lies within `|x| smallErr + 2^-1075` of `x R (x²)`. -/
theorem small_core (xlo xhi zlo zhi : ℚ) (hok : smallOK xlo xhi zlo zhi = true)
    (X : UInt64) (hX : Finite X) (hxl : (xlo : ℝ) ≤ |value X|) (hxh : |value X| ≤ xhi) :
    Approx (Wasm.IEEE64.mul X
        (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X)) (hornerW qqW (Wasm.IEEE64.mul X X))))
      (value X * (eval erfPP (value X ^ 2) / eval erfQQ (value X ^ 2)))
      (|value X| * smallErr xhi zlo zhi + multiplicationUnderflowEpsilon) := by
  simp only [smallOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hx0, hxx⟩, hx1⟩, hz0⟩, hzlo⟩, hzhi⟩, hokP⟩, hokQ⟩, hQe⟩, hmQ⟩, hmaxq⟩,
    hMB⟩ := hok
  have hu : unitRoundoff64 = ((uQ : ℚ) : ℝ) := uQ_eq.symm
  have he : multiplicationUnderflowEpsilon = ((etaQ : ℚ) : ℝ) := etaQ_eq.symm
  have hu0 : (0 : ℝ) ≤ uQ := by rw [← hu]; norm_num [unitRoundoff64]
  have he0 : (0 : ℝ) ≤ etaQ := by rw [← he]; norm_num [multiplicationUnderflowEpsilon,
    unitRoundoff64, minNormal64]
  set x := value X with hxdef
  have hax : |x| ^ 2 = x ^ 2 := sq_abs x
  have hxl' : (xlo : ℝ) ^ 2 ≤ x ^ 2 := by
    rw [← hax]
    exact pow_le_pow_left₀ (by exact_mod_cast hx0.le) hxl 2
  have hxh' : x ^ 2 ≤ (xhi : ℝ) ^ 2 := by
    rw [← hax]
    exact pow_le_pow_left₀ (abs_nonneg _) hxh 2
  have hxh1 : (xhi : ℝ) < 1 := by exact_mod_cast hx1
  have hxhi0 : (0 : ℝ) ≤ xhi := le_trans (abs_nonneg _) hxh
  -- the computed square
  have hsq : |x * x| < (2 : ℝ) ^ 1022 := by
    rw [abs_mul, ← sq, sq_abs]
    have : x ^ 2 ≤ 1 := by nlinarith
    linarith [show (1 : ℝ) < 2 ^ 1022 by norm_num]
  obtain ⟨hZf, hZe⟩ := F64MulBounds.mul_real_mixed X X hX hX hsq
  set Z := Wasm.IEEE64.mul X X
  set z := value Z
  have hxx2 : x * x = x ^ 2 := by ring
  rw [hxx2, abs_of_nonneg (sq_nonneg x)] at hZe
  have hZl := (abs_le.mp hZe).1
  have hZh := (abs_le.mp hZe).2
  have hzl : (zlo : ℝ) ≤ z := by
    have h1 : ((zlo : ℚ) : ℝ) ≤ (xlo : ℝ) ^ 2 * (1 - uQ) - etaQ := by exact_mod_cast hzlo
    have h2 : (xlo : ℝ) ^ 2 * (1 - uQ) ≤ x ^ 2 * (1 - uQ) :=
      mul_le_mul_of_nonneg_right hxl' (by rw [← hu]; norm_num [unitRoundoff64])
    rw [hu, he] at hZl
    nlinarith
  have hzh : z ≤ (zhi : ℝ) := by
    have h1 : (xhi : ℝ) ^ 2 * (1 + uQ) + etaQ ≤ ((zhi : ℚ) : ℝ) := by exact_mod_cast hzhi
    have h2 : x ^ 2 * (1 + uQ) ≤ (xhi : ℝ) ^ 2 * (1 + uQ) :=
      mul_le_mul_of_nonneg_right hxh' (by linarith)
    rw [hu, he] at hZh
    nlinarith
  have hzlo0 : (0 : ℝ) ≤ zlo := by exact_mod_cast hz0
  have hx2l : (zlo : ℝ) ≤ x ^ 2 := by
    have h1 : ((zlo : ℚ) : ℝ) ≤ (xlo : ℝ) ^ 2 * (1 - uQ) - etaQ := by exact_mod_cast hzlo
    nlinarith
  have hx2h : x ^ 2 ≤ (zhi : ℝ) := by
    have h1 : (xhi : ℝ) ^ 2 * (1 + uQ) + etaQ ≤ ((zhi : ℚ) : ℝ) := by exact_mod_cast hzhi
    nlinarith
  -- the polynomials at the computed square
  have hP := hornerW_approx erfPP ppW pp_rel (by simp [erfPP]) zlo zhi Z hZf hzl hzh hokP
  have hQ := hornerW_approx erfQQ qqW qq_rel (by simp [erfQQ]) zlo zhi Z hZf hzl hzh hokQ
  have hMP : |eval erfPP z| ≤ ((magBound erfPP zlo zhi : ℚ) : ℝ) :=
    magBound_sound erfPP zlo zhi z hzl hzh
  have hmQz : ((lowBound erfQQ zlo zhi : ℚ) : ℝ) ≤ eval erfQQ z :=
    lowBound_sound erfQQ zlo zhi z hzl hzh
  have hQe' : ((hornerErr erfQQ zlo zhi : ℚ) : ℝ) < lowBound erfQQ zlo zhi := by
    exact_mod_cast hQe
  have hmQ' : (0 : ℝ) < lowBound erfQQ zlo zhi := by exact_mod_cast hmQ
  have hmaxq' : (((magBound erfPP zlo zhi : ℚ) : ℝ) + hornerErr erfPP zlo zhi) /
      ((lowBound erfQQ zlo zhi : ℝ) - hornerErr erfQQ zlo zhi) < 2 ^ 1022 := by
    have h : ((((magBound erfPP zlo zhi + hornerErr erfPP zlo zhi) /
        (lowBound erfQQ zlo zhi - hornerErr erfQQ zlo zhi)) : ℚ) : ℝ) < 2 ^ 1000 := by
      exact_mod_cast hmaxq
    push_cast at h
    linarith [show (2 : ℝ) ^ 1000 ≤ 2 ^ 1022 by norm_num]
  have hD := F64DivApprox.div_approx hP hQ _ _ hMP hmQz hQe' hmaxq'
  -- the change of `R` between `x²` and `z`
  have hQpos : ∀ t ∈ Set.Icc (zlo : ℝ) zhi, 0 < eval erfQQ t :=
    fun t ht => lt_of_lt_of_le hmQ' (lowBound_sound erfQQ zlo zhi t ht.1 ht.2)
  have hL0 : (0 : ℝ) ≤ ((magBound smallDer zlo zhi / lowBound erfQQ zlo zhi ^ 2 : ℚ) : ℝ) := by
    push_cast
    exact div_nonneg (magBound_nonneg smallDer zlo zhi z hzl hzh) (by positivity)
  have hLd : ∀ t ∈ Set.Icc (zlo : ℝ) zhi,
      |eval (derivP erfPP) t * eval erfQQ t - eval erfPP t * eval (derivP erfQQ) t| ≤
        ((magBound smallDer zlo zhi / lowBound erfQQ zlo zhi ^ 2 : ℚ) : ℝ) *
          eval erfQQ t ^ 2 := by
    intro t ht
    rw [← eval_smallDer]
    have h1 := magBound_sound smallDer zlo zhi t ht.1 ht.2
    have h2 : ((lowBound erfQQ zlo zhi : ℚ) : ℝ) ^ 2 ≤ eval erfQQ t ^ 2 :=
      pow_le_pow_left₀ hmQ'.le (lowBound_sound erfQQ zlo zhi t ht.1 ht.2) 2
    have h3 : ((magBound smallDer zlo zhi : ℚ) : ℝ) =
        ((magBound smallDer zlo zhi / lowBound erfQQ zlo zhi ^ 2 : ℚ) : ℝ) *
          ((lowBound erfQQ zlo zhi : ℚ) : ℝ) ^ 2 := by
      push_cast
      field_simp
    calc |eval smallDer t| ≤ ((magBound smallDer zlo zhi : ℚ) : ℝ) := h1
      _ = _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hL0
  have hLip := F64DivApprox.ratio_lipschitz erfPP erfQQ zlo zhi _ hQpos hLd
    (x := z) (y := x ^ 2) ⟨hzl, hzh⟩ ⟨hx2l, hx2h⟩
  have hzx : |z - x ^ 2| ≤ uQ * (xhi : ℝ) ^ 2 + etaQ := by
    rw [hu, he] at hZe
    have : (uQ : ℝ) * x ^ 2 ≤ uQ * (xhi : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hxh' hu0
    linarith
  have hR : Approx (Wasm.IEEE64.div (hornerW ppW Z) (hornerW qqW Z))
      (eval erfPP (x ^ 2) / eval erfQQ (x ^ 2)) (smallRatioErr xhi zlo zhi) := by
    refine ⟨hD.1, ?_⟩
    have h1 := hD.2
    have h2 : |eval erfPP z / eval erfQQ z - eval erfPP (x ^ 2) / eval erfQQ (x ^ 2)| ≤
        ((magBound smallDer zlo zhi / lowBound erfQQ zlo zhi ^ 2 : ℚ) : ℝ) *
          (uQ * (xhi : ℝ) ^ 2 + etaQ) :=
      hLip.trans (mul_le_mul_of_nonneg_left hzx hL0)
    have hsum := abs_sub_le (value (Wasm.IEEE64.div (hornerW ppW Z) (hornerW qqW Z)))
      (eval erfPP z / eval erfQQ z) (eval erfPP (x ^ 2) / eval erfQQ (x ^ 2))
    have hdef : ((smallRatioErr xhi zlo zhi : ℚ) : ℝ) =
        (((hornerErr erfPP zlo zhi : ℚ) : ℝ) /
            ((lowBound erfQQ zlo zhi : ℝ) - hornerErr erfQQ zlo zhi) +
          (magBound erfPP zlo zhi : ℝ) * hornerErr erfQQ zlo zhi /
            (((lowBound erfQQ zlo zhi : ℝ) - hornerErr erfQQ zlo zhi) * lowBound erfQQ zlo zhi) +
          unitRoundoff64 * (((magBound erfPP zlo zhi : ℝ) + hornerErr erfPP zlo zhi) /
            ((lowBound erfQQ zlo zhi : ℝ) - hornerErr erfQQ zlo zhi)) +
          multiplicationUnderflowEpsilon) +
        ((magBound smallDer zlo zhi / lowBound erfQQ zlo zhi ^ 2 : ℚ) : ℝ) *
          (uQ * (xhi : ℝ) ^ 2 + etaQ) := by
      rw [hu, he]
      simp only [smallRatioErr]
      push_cast
      ring
    rw [hdef]
    linarith
  -- the product with `x`
  have hRb : |eval erfPP (x ^ 2) / eval erfQQ (x ^ 2)| ≤
      ((magBound erfPP zlo zhi / lowBound erfQQ zlo zhi : ℚ) : ℝ) := by
    have hq := hQpos (x ^ 2) ⟨hx2l, hx2h⟩
    have hm := lowBound_sound erfQQ zlo zhi (x ^ 2) hx2l hx2h
    have hp := magBound_sound erfPP zlo zhi (x ^ 2) hx2l hx2h
    rw [abs_div, abs_of_pos hq]
    push_cast
    exact div_le_div₀ ((abs_nonneg _).trans hp) hp hmQ' hm
  have hMBr : ((magBound erfPP zlo zhi / lowBound erfQQ zlo zhi : ℚ) : ℝ) +
      smallRatioErr xhi zlo zhi < 1 := by exact_mod_cast hMB
  have hT := mul_approx (approx_self X hX) hR |x|
    ((magBound erfPP zlo zhi / lowBound erfQQ zlo zhi : ℚ) : ℝ) le_rfl hRb (by
    rw [add_zero]
    have h1 : |x| < 1 := lt_of_le_of_lt hxh hxh1
    have h2 : 0 ≤ ((magBound erfPP zlo zhi / lowBound erfQQ zlo zhi : ℚ) : ℝ) +
        smallRatioErr xhi zlo zhi := by
      have := (abs_nonneg _).trans hRb
      have := (abs_nonneg _).trans hR.2
      linarith
    have h3 : |x| * (((magBound erfPP zlo zhi / lowBound erfQQ zlo zhi : ℚ) : ℝ) +
        smallRatioErr xhi zlo zhi) < 1 * 1 :=
      mul_lt_mul'' h1 hMBr (abs_nonneg _) h2
    linarith [show (1 : ℝ) < 2 ^ 1022 by norm_num])
  refine hT.mono (le_of_eq ?_)
  rw [hu]
  simp only [smallErr]
  push_cast
  ring

/-- The kernel's error bound relative to `|x|`. -/
def smallKern : ℚ := (21 / 32) / 2 ^ 55

theorem erfCoeffs_one : erfCoeffs 1 = [1] := by decide +kernel

/-- `erf x ≥ κ x (1 - x²/3)` for `x ≥ 0`, with `κ = 2/√π`. -/
theorem erf_lower (x : ℝ) (hx : 0 ≤ x) : scale * (x * (1 - x ^ 2 / 3)) ≤ erf x := by
  have h := erf_series 1 x
  rw [erfCoeffs_one] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one, mul_one] at h
  have hf : ((Nat.factorial 1 * (2 * 1 + 1) : ℕ) : ℝ) = 3 := by norm_num [Nat.factorial]
  rw [hf, abs_of_nonneg hx] at h
  have := (abs_le.mp h).1
  have h3 : x ^ (2 * 1 + 1) = x * x ^ 2 := by ring
  rw [h3] at this
  nlinarith [scale_pos]

/-- The sum `x + x R̂` for positive `x` in `[xlo, xhi]` lies within
`x (smallErr + smallKern) + 2^-1075` of `erf x`. -/
theorem small_sum (xlo xhi zlo zhi : ℚ) (hok : smallOK xlo xhi zlo zhi = true)
    (hxh27 : xhi ≤ 27 / 32) (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : (xlo : ℝ) ≤ value X) (hxh : value X ≤ xhi) :
    Finite (Wasm.IEEE64.mul X
        (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X)) (hornerW qqW (Wasm.IEEE64.mul X X)))) ∧
      |value X + value (Wasm.IEEE64.mul X
        (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X)) (hornerW qqW (Wasm.IEEE64.mul X X))))
        - erf (value X)| ≤
      value X * (smallErr xhi zlo zhi + smallKern) + multiplicationUnderflowEpsilon := by
  have habs : |value X| = value X := abs_of_pos hx0
  have hc := small_core xlo xhi zlo zhi hok X hX (by rw [habs]; exact hxl) (by rw [habs]; exact hxh)
  rw [habs] at hc
  refine ⟨hc.1, ?_⟩
  have hk := small_kernel_error (value X) (by
    rw [habs]
    have h := (Rat.cast_le (K := ℝ)).mpr hxh27
    push_cast at h
    exact hxh.trans h)
  rw [habs] at hk
  have hk' : |value X * (eval erfPP (value X ^ 2) / eval erfQQ (value X ^ 2)) -
      (erf (value X) - value X)| ≤ value X * smallKern := by
    rw [abs_sub_comm]
    simp only [smallKern]
    push_cast
    convert hk using 2
  have h2 := hc.2
  calc |value X + value (Wasm.IEEE64.mul X
        (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X)) (hornerW qqW (Wasm.IEEE64.mul X X))))
        - erf (value X)|
      = |(value (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
          (hornerW qqW (Wasm.IEEE64.mul X X)))) -
          value X * (eval erfPP (value X ^ 2) / eval erfQQ (value X ^ 2))) +
        (value X * (eval erfPP (value X ^ 2) / eval erfQQ (value X ^ 2)) -
          (erf (value X) - value X))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ (value X * smallErr xhi zlo zhi + multiplicationUnderflowEpsilon) +
        value X * smallKern := add_le_add h2 hk'
    _ = _ := by ring

/-- The relative criterion of `small_erf_rel`. -/
def smallRelOK (xlo xhi zlo zhi : ℚ) : Bool :=
  decide (xhi ≤ 27 / 32) && decide (1 / 2 ^ 1021 ≤ kappaLo * xlo * (1 - xhi ^ 2 / 3)) &&
    decide (smallErr xhi zlo zhi + smallKern + etaQ / xlo ≤
      63 / 64 * uQ * (kappaLo * (1 - xhi ^ 2 / 3)))

/-- The criterion of `small_erf_top`, for results in `[1/2, 1)`. -/
def smallTopOK (xlo xhi zlo zhi : ℚ) : Bool :=
  decide (xhi ≤ 27 / 32) && decide (0 ≤ smallErr xhi zlo zhi + smallKern) &&
    decide (xhi * (smallErr xhi zlo zhi + smallKern) + etaQ < 1 / 2 ^ 53) &&
    decide (1 / 2 + (xhi * (smallErr xhi zlo zhi + smallKern) + etaQ) ≤
      kappaLo * xlo * (1 - xhi ^ 2 / 3))

theorem kappaLo_le : ((kappaLo : ℚ) : ℝ) ≤ scale := by
  rw [kappaLo_cast]
  exact scale_bounds.1

/-- `erf` within one step on `[xlo, xhi]` for positive arguments, relative to `erf x`. -/
theorem small_erf_rel (xlo xhi zlo zhi : ℚ) (hok : smallOK xlo xhi zlo zhi = true)
    (hrel : smallRelOK xlo xhi zlo zhi = true) (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : (xlo : ℝ) ≤ value X) (hxh : value X ≤ xhi) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X
        (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
          (hornerW qqW (Wasm.IEEE64.mul X X))))) := by
  simp only [smallRelOK, Bool.and_eq_true, decide_eq_true_eq] at hrel
  obtain ⟨⟨hxh27, hy0⟩, hcrit⟩ := hrel
  obtain ⟨hTf, hsum⟩ := small_sum xlo xhi zlo zhi hok hxh27 X hX hx0 hxl hxh
  set x := value X
  have hxlo0 : (0 : ℝ) < xlo := by exact_mod_cast smallOK_pos xlo xhi zlo zhi hok
  have hxh2 : x ^ 2 ≤ (xhi : ℝ) ^ 2 := pow_le_pow_left₀ hx0.le hxh 2
  have hfac : (0 : ℝ) ≤ 1 - (xhi : ℝ) ^ 2 / 3 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hxh27
    push_cast at h
    nlinarith
  -- the lower bound on `erf x`
  have hy := erf_lower x hx0.le
  have hk := kappaLo_le
  have hylo : (kappaLo : ℝ) * x * (1 - (xhi : ℝ) ^ 2 / 3) ≤ erf x := by
    have h1 : (kappaLo : ℝ) * x * (1 - (xhi : ℝ) ^ 2 / 3) ≤ scale * (x * (1 - x ^ 2 / 3)) := by
      have h2 : (1 - (xhi : ℝ) ^ 2 / 3) ≤ 1 - x ^ 2 / 3 := by linarith
      have h3 : (0 : ℝ) ≤ kappaLo := by rw [kappaLo_cast]; positivity
      calc (kappaLo : ℝ) * x * (1 - (xhi : ℝ) ^ 2 / 3) ≤ scale * x * (1 - (xhi : ℝ) ^ 2 / 3) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hx0.le) hfac
        _ ≤ scale * x * (1 - x ^ 2 / 3) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg scale_pos.le hx0.le)
        _ = scale * (x * (1 - x ^ 2 / 3)) := by ring
    linarith
  -- the error relative to `erf x`
  have hcr : ((smallErr xhi zlo zhi : ℚ) : ℝ) + smallKern + etaQ / xlo ≤
      63 / 64 * uQ * (kappaLo * (1 - (xhi : ℝ) ^ 2 / 3)) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcrit
    push_cast at h
    exact h
  have he : multiplicationUnderflowEpsilon = ((etaQ : ℚ) : ℝ) := etaQ_eq.symm
  have hu : unitRoundoff64 = ((uQ : ℚ) : ℝ) := uQ_eq.symm
  have he0 : (0 : ℝ) ≤ etaQ := by rw [← he]; norm_num [multiplicationUnderflowEpsilon,
    unitRoundoff64, minNormal64]
  have heta : (etaQ : ℝ) ≤ x * (etaQ / xlo) := by
    rw [mul_div_assoc', le_div_iff₀ hxlo0]
    linarith [mul_le_mul_of_nonneg_left hxl he0, mul_comm x (etaQ : ℝ)]
  have herr : |x + value (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
      (hornerW qqW (Wasm.IEEE64.mul X X)))) - erf x| ≤
      1 * (63 / 64) * unitRoundoff64 * erf x := by
    rw [he] at hsum
    rw [hu]
    have h1 : x * (((smallErr xhi zlo zhi : ℚ) : ℝ) + smallKern + etaQ / xlo) ≤
        x * (63 / 64 * uQ * (kappaLo * (1 - (xhi : ℝ) ^ 2 / 3))) :=
      mul_le_mul_of_nonneg_left hcr hx0.le
    have hu0 : (0 : ℝ) ≤ uQ := by rw [← hu]; norm_num [unitRoundoff64]
    have h2 : 63 / 64 * (uQ : ℝ) * ((kappaLo : ℝ) * x * (1 - (xhi : ℝ) ^ 2 / 3)) ≤
        63 / 64 * uQ * erf x := mul_le_mul_of_nonneg_left hylo (by positivity)
    nlinarith
  have hyl : (1 : ℝ) / 2 ^ 1021 ≤ erf x := by
    have h1 : ((1 / 2 ^ 1021 : ℚ) : ℝ) ≤ (kappaLo : ℝ) * xlo * (1 - (xhi : ℝ) ^ 2 / 3) := by
      exact_mod_cast hy0
    have h2 : (kappaLo : ℝ) * xlo * (1 - (xhi : ℝ) ^ 2 / 3) ≤
        (kappaLo : ℝ) * x * (1 - (xhi : ℝ) ^ 2 / 3) := by
      have h3 : (0 : ℝ) ≤ kappaLo := by rw [kappaLo_cast]; positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxl h3) hfac
    push_cast at h1
    linarith
  have hyt : erf x < (2 : ℝ) ^ 1000 := by
    have := erf_lt_one x
    linarith [show (1 : ℝ) < 2 ^ 1000 by norm_num]
  have hu1 : 1 * (63 / 64) * unitRoundoff64 ≤ 1 / 2 := by norm_num [unitRoundoff64]
  have hvpos : 0 < x + value (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
      (hornerW qqW (Wasm.IEEE64.mul X X)))) := by
    have := (abs_le.mp herr).1
    have hy0' : 0 < erf x := lt_of_lt_of_le (by positivity) hyl
    nlinarith
  have hn := F64NearestSum.add_nearest X _ hX hTf hvpos (by
    have := (abs_le.mp herr).2
    have := erf_lt_one x
    have h3 : 1 * (63 / 64) * unitRoundoff64 * erf x ≤ 1 / 2 * 1 :=
      mul_le_mul hu1 this.le (lt_of_lt_of_le (by positivity) hyl).le (by norm_num)
    linarith [show (2 : ℝ) ≤ 2 ^ 1023 by norm_num])
  exact F64AddNearest.within_nearest_relative 1 le_rfl (by norm_num) (erf x) _ _ hn hyl hyt
    (by have h := herr; push_cast; linarith)

/-- `erf` within one step on `[xlo, xhi]` for positive arguments whose `erf` lies in `[1/2, 1)`. -/
theorem small_erf_top (xlo xhi zlo zhi : ℚ) (hok : smallOK xlo xhi zlo zhi = true)
    (htop : smallTopOK xlo xhi zlo zhi = true) (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : (xlo : ℝ) ≤ value X) (hxh : value X ≤ xhi) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X
        (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
          (hornerW qqW (Wasm.IEEE64.mul X X))))) := by
  simp only [smallTopOK, Bool.and_eq_true, decide_eq_true_eq] at htop
  obtain ⟨⟨⟨hxh27, hE0⟩, hsp⟩, hbin⟩ := htop
  obtain ⟨hTf, hsum⟩ := small_sum xlo xhi zlo zhi hok hxh27 X hX hx0 hxl hxh
  have hxlo0 : (0 : ℝ) < xlo := by exact_mod_cast smallOK_pos xlo xhi zlo zhi hok
  set x := value X
  set T := Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
      (hornerW qqW (Wasm.IEEE64.mul X X)))
  have he : multiplicationUnderflowEpsilon = ((etaQ : ℚ) : ℝ) := etaQ_eq.symm
  rw [he] at hsum
  have hxh2 : x ^ 2 ≤ (xhi : ℝ) ^ 2 := pow_le_pow_left₀ hx0.le hxh 2
  have hfac : (0 : ℝ) ≤ 1 - (xhi : ℝ) ^ 2 / 3 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hxh27
    push_cast at h
    nlinarith
  have hE0' : (0 : ℝ) ≤ (smallErr xhi zlo zhi : ℝ) + smallKern := by exact_mod_cast hE0
  have herr : |x + value T - erf x| ≤ xhi * ((smallErr xhi zlo zhi : ℝ) + smallKern) + etaQ := by
    have := mul_le_mul_of_nonneg_right hxh hE0'
    linarith
  have hEnn : (0 : ℝ) ≤ xhi * ((smallErr xhi zlo zhi : ℝ) + smallKern) + etaQ :=
    (abs_nonneg _).trans herr
  have hsp' : (xhi : ℝ) * ((smallErr xhi zlo zhi : ℝ) + smallKern) + etaQ < 1 / 2 ^ 53 := by
    have h : (((xhi * (smallErr xhi zlo zhi + smallKern) + etaQ) : ℚ) : ℝ) <
        ((1 / 2 ^ 53 : ℚ) : ℝ) := by exact_mod_cast hsp
    push_cast at h
    exact h
  have hbin' : 1 / 2 + ((xhi : ℝ) * ((smallErr xhi zlo zhi : ℝ) + smallKern) + etaQ) ≤
      (kappaLo : ℝ) * xlo * (1 - (xhi : ℝ) ^ 2 / 3) := by
    have h : (((1 / 2 + (xhi * (smallErr xhi zlo zhi + smallKern) + etaQ)) : ℚ) : ℝ) ≤
        ((kappaLo * xlo * (1 - xhi ^ 2 / 3) : ℚ) : ℝ) := by exact_mod_cast hbin
    push_cast at h
    exact h
  have hylo : (kappaLo : ℝ) * xlo * (1 - (xhi : ℝ) ^ 2 / 3) ≤ erf x := by
    have hy := erf_lower x hx0.le
    have hk := kappaLo_le
    have h2 : (1 - (xhi : ℝ) ^ 2 / 3) ≤ 1 - x ^ 2 / 3 := by linarith
    calc (kappaLo : ℝ) * xlo * (1 - (xhi : ℝ) ^ 2 / 3) ≤ scale * x * (1 - (xhi : ℝ) ^ 2 / 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk hxl hxlo0.le scale_pos.le) hfac
      _ ≤ scale * x * (1 - x ^ 2 / 3) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg scale_pos.le hx0.le)
      _ = scale * (x * (1 - x ^ 2 / 3)) := by ring
      _ ≤ erf x := hy
  have hb : value (UInt64.ofNat (1022 * 2 ^ 52)) = 1 / 2 := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    norm_num
  have hvl := (abs_le.mp herr).1
  have hvu := (abs_le.mp herr).2
  have hy1 := erf_lt_one x
  have hvpos : 0 < x + value T := by linarith
  have hn := F64NearestSum.add_nearest X T hX hTf hvpos (by
    linarith [show (2 : ℝ) ≤ 2 ^ 1023 by norm_num])
  refine F64AddNearest.within_of_nearest 1 le_rfl (erf x) _ _ 1022 (by norm_num) (by norm_num)
    (by rw [hb]; linarith) (by rw [hb]; linarith) ?_ hn ?_
  · have h : (1 : ℝ) < F64PositiveRounding.overflowThreshold := by
      rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 from rfl]
      norm_num
    linarith
  · have hsp2 : ((1 : Nat) : ℝ) * ((2 : ℝ) ^ (1022 - 1) / (2 : ℝ) ^ 1074) = 1 / 2 ^ 53 := by
      norm_num
    rw [hsp2]
    linarith

#print axioms erfSmall_bits
#print axioms pp_rel
#print axioms qq_rel
#print axioms small_core
#print axioms erf_lower
#print axioms small_sum
#print axioms small_erf_rel
#print axioms small_erf_top

end Library.Numerics.Float64.Erf.ErfSmallBase
