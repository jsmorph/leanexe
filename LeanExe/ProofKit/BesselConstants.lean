import LeanExe.ProofKit.EulerGamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Rational enclosures for the constants of the Bessel proofs, with the arithmetic on enclosures
that combines them.  `Encl v c e` states `|v - c| ≤ e` for a real `v` and rationals `c` and `e`;
sums, products, quotients, and square roots of enclosed values are enclosed by rationals that
the kernel computes.

* `π` from Machin's formula `π = 16 arctan (1/5) - 4 arctan (1/239)` with 40 and 12 terms of the
  alternating arctangent series, the method of `Library.Numerics.Float64.Trig.TrigPi` with fewer terms, within
  `2 ^ -190`.
* `cos 1` and `sin 1` from 20 terms of their series (`TaylorRemainder`), and `cos 2` and `sin 2`
  from the double-angle formulas.
-/

namespace LeanExe.ProofKit.BesselConstants

open Real Finset PolyBound PolyCalc TaylorRemainder

/-- `|v - c| ≤ e`. -/
def Encl (v : ℝ) (c e : ℚ) : Prop := |v - c| ≤ e

theorem Encl.nonneg {v : ℝ} {c e : ℚ} (h : Encl v c e) : (0 : ℝ) ≤ e := (abs_nonneg _).trans h

theorem Encl.exact (c : ℚ) : Encl (c : ℝ) c 0 := by simp [Encl]

theorem Encl.add {u v : ℝ} {cu eu cv ev : ℚ} (hu : Encl u cu eu) (hv : Encl v cv ev) :
    Encl (u + v) (cu + cv) (eu + ev) := by
  unfold Encl at *
  push_cast
  calc |u + v - (cu + cv)| = |(u - cu) + (v - cv)| := by ring_nf
    _ ≤ |u - cu| + |v - cv| := abs_add_le _ _
    _ ≤ eu + ev := add_le_add hu hv

theorem Encl.sub {u v : ℝ} {cu eu cv ev : ℚ} (hu : Encl u cu eu) (hv : Encl v cv ev) :
    Encl (u - v) (cu - cv) (eu + ev) := by
  unfold Encl at *
  push_cast
  calc |u - v - (cu - cv)| = |(u - cu) - (v - cv)| := by ring_nf
    _ ≤ |u - cu| + |v - cv| := abs_sub _ _
    _ ≤ eu + ev := add_le_add hu hv

theorem Encl.neg {u : ℝ} {cu eu : ℚ} (hu : Encl u cu eu) : Encl (-u) (-cu) eu := by
  unfold Encl at *
  push_cast
  rw [show -u - -(cu : ℝ) = -(u - cu) by ring, abs_neg]
  exact hu

theorem Encl.mul {u v : ℝ} {cu eu cv ev : ℚ} (hu : Encl u cu eu) (hv : Encl v cv ev) :
    Encl (u * v) (cu * cv) (qabs cu * ev + qabs cv * eu + eu * ev) := by
  have heu := hu.nonneg
  have hev := hv.nonneg
  unfold Encl at *
  push_cast [qabs_cast]
  have e : u * v - cu * cv = cu * (v - cv) + cv * (u - cu) + (u - cu) * (v - cv) := by ring
  rw [e]
  calc |(cu : ℝ) * (v - cv) + cv * (u - cu) + (u - cu) * (v - cv)|
      ≤ |(cu : ℝ) * (v - cv)| + |(cv : ℝ) * (u - cu)| + |(u - cu) * (v - cv)| := abs_add_three _ _ _
    _ = |(cu : ℝ)| * |v - cv| + |(cv : ℝ)| * |u - cu| + |u - cu| * |v - cv| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |(cu : ℝ)| * ev + |(cv : ℝ)| * eu + eu * ev := by gcongr

theorem Encl.const_mul {u : ℝ} {cu eu : ℚ} (q : ℚ) (hu : Encl u cu eu) :
    Encl (q * u) (q * cu) (qabs q * eu) := by
  have := (Encl.exact q).mul hu
  simpa using this

theorem Encl.mono {u : ℝ} {c e e' : ℚ} (h : Encl u c e) (he : e ≤ e') : Encl u c e' :=
  h.trans (by exact_mod_cast he)

theorem Encl.recenter {u : ℝ} {c e c' e' : ℚ} (h : Encl u c e) (hc : qabs (c - c') + e ≤ e') :
    Encl u c' e' := by
  unfold Encl at *
  have hc' : ((qabs (c - c') + e : ℚ) : ℝ) ≤ e' := by exact_mod_cast hc
  push_cast [qabs_cast] at hc'
  calc |u - c'| = |(u - c) + ((c : ℝ) - c')| := by ring_nf
    _ ≤ |u - c| + |(c : ℝ) - c'| := abs_add_le _ _
    _ ≤ e' := by linarith

theorem Encl.abs_bound {u : ℝ} {c e : ℚ} (h : Encl u c e) : |u| ≤ ((qabs c + e : ℚ) : ℝ) := by
  unfold Encl at h
  push_cast [qabs_cast]
  calc |u| = |(u - c) + c| := by ring_nf
    _ ≤ |u - c| + |(c : ℝ)| := abs_add_le _ _
    _ ≤ |(c : ℝ)| + e := by linarith

theorem Encl.congr {u v : ℝ} {c e : ℚ} (h : Encl u c e) (huv : u = v) : Encl v c e := huv ▸ h

/-- The reciprocal of an enclosed value whose enclosure excludes 0. -/
theorem Encl.inv {u : ℝ} {c e : ℚ} (h : Encl u c e) (hc : e < qabs c) :
    Encl u⁻¹ c⁻¹ (e / (qabs c * (qabs c - e))) := by
  have he := h.nonneg
  unfold Encl at *
  have hc' : (e : ℝ) < |(c : ℝ)| := by
    have : ((e : ℚ) : ℝ) < ((qabs c : ℚ) : ℝ) := by exact_mod_cast hc
    rwa [qabs_cast] at this
  have hcpos : (0 : ℝ) < |(c : ℝ)| := lt_of_le_of_lt he hc'
  have hc0 : (c : ℝ) ≠ 0 := abs_pos.mp hcpos
  have hu : |(c : ℝ)| - e ≤ |u| := by
    have := abs_sub_abs_le_abs_sub (c : ℝ) u
    rw [abs_sub_comm] at h
    linarith
  have hupos : 0 < |u| := by linarith
  have hu0 : u ≠ 0 := abs_pos.mp hupos
  push_cast [qabs_cast]
  rw [show u⁻¹ - (c : ℝ)⁻¹ = (c - u) / (u * c) by field_simp, abs_div, abs_mul, abs_sub_comm]
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  have h1 : |(c : ℝ)| - e ≤ |u| := hu
  have h2 : 0 ≤ |(c : ℝ)| - e := by linarith
  have key : |(c : ℝ)| * (|(c : ℝ)| - e) ≤ |u| * |(c : ℝ)| := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  calc |u - c| * (|(c : ℝ)| * (|(c : ℝ)| - e)) ≤ e * (|(c : ℝ)| * (|(c : ℝ)| - e)) :=
        mul_le_mul_of_nonneg_right h (mul_nonneg (abs_nonneg _) h2)
    _ ≤ e * (|u| * |(c : ℝ)|) := mul_le_mul_of_nonneg_left key he

/-- Square roots, from rational bounds whose squares straddle the enclosure. -/
theorem Encl.sqrt {u : ℝ} {c e lo hi : ℚ} (h : Encl u c e) (hlo : 0 ≤ lo)
    (hl : lo ^ 2 ≤ c - e) (hh : c + e ≤ hi ^ 2) (hlh : lo ≤ hi) :
    Encl √u ((lo + hi) / 2) ((hi - lo) / 2) := by
  unfold Encl at *
  rw [abs_le] at h ⊢
  have hlo' : (0 : ℝ) ≤ lo := by exact_mod_cast hlo
  have hl' : ((lo : ℝ)) ^ 2 ≤ u := by
    have : ((lo ^ 2 : ℚ) : ℝ) ≤ ((c - e : ℚ) : ℝ) := by exact_mod_cast hl
    push_cast at this
    linarith [h.1]
  have hh' : u ≤ ((hi : ℝ)) ^ 2 := by
    have : ((c + e : ℚ) : ℝ) ≤ ((hi ^ 2 : ℚ) : ℝ) := by exact_mod_cast hh
    push_cast at this
    linarith [h.2]
  have hhi' : (0 : ℝ) ≤ hi := le_trans hlo' (by exact_mod_cast hlh)
  have s1 : (lo : ℝ) ≤ √u := by rw [← Real.sqrt_sq hlo']; exact Real.sqrt_le_sqrt hl'
  have s2 : √u ≤ hi := by rw [← Real.sqrt_sq hhi']; exact Real.sqrt_le_sqrt hh'
  push_cast
  constructor <;> linarith

/-! `π` by Machin's formula. -/

/-- The magnitude of term `n` of the arctangent series at `x`. -/
def term (x : ℚ) (n : ℕ) : ℚ := x ^ (2 * n + 1) / (2 * n + 1)

/-- The sum of the first `n` terms of the arctangent series at `x`. -/
def partialSum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => partialSum x n + (-1) ^ n * term x n

theorem partialSum_cast (x : ℚ) (n : ℕ) :
    ((partialSum x n : ℚ) : ℝ) =
      ∑ i ∈ range n, (-1 : ℝ) ^ i * ((x : ℝ) ^ (2 * i + 1) / (2 * i + 1)) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    rw [partialSum, sum_range_succ, ← ih, term]
    push_cast
    ring

theorem arctan_error (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    |Real.arctan x - partialSum x n| ≤ term x n := by
  have hy0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hy1 : (x : ℝ) < 1 := by exact_mod_cast h1
  set f : ℕ → ℝ := fun i => (x : ℝ) ^ (2 * i + 1) / (2 * i + 1) with hf
  have hfa : Antitone f := by
    apply antitone_nat_of_succ_le
    intro i
    simp only [hf]
    apply div_le_div₀ (by positivity) (pow_le_pow_of_le_one hy0 hy1.le (by omega))
      (by positivity)
    push_cast
    linarith
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le (fun i => by simp only [hf]; positivity) (fun i => ?_)
      (summable_geometric_of_lt_one hy0 hy1)
    simp only [hf]
    rw [div_le_iff₀ (by positivity)]
    have hp : (x : ℝ) ^ (2 * i + 1) ≤ (x : ℝ) ^ i :=
      pow_le_pow_of_le_one hy0 hy1.le (by omega)
    have hpos : 0 ≤ (x : ℝ) ^ i := by positivity
    nlinarith [mul_nonneg hpos (Nat.cast_nonneg (α := ℝ) i)]
  have hb := alternating_series_error_bound f hfa hfs n
  have hs := Real.hasSum_arctan (x := (x : ℝ))
    (by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith)
  have ht : ∑' i, (-1 : ℝ) ^ i * f i = Real.arctan x := by
    rw [← hs.tsum_eq]
    congr 1
    funext i
    simp only [hf]
    push_cast
    ring
  rw [ht, ← partialSum_cast] at hb
  have hterm : f n = ((term x n : ℚ) : ℝ) := by
    simp only [hf, term]
    push_cast
    ring
  rwa [hterm] at hb

/-- Machin's formula with 40 and 12 terms. -/
def piMid : ℚ := 16 * partialSum (1 / 5) 40 - 4 * partialSum (1 / 239) 12

/-- The error bound of `piMid`. -/
def piRad : ℚ := 16 * term (1 / 5) 40 + 4 * term (1 / 239) 12

theorem pi_encl : Encl π piMid piRad := by
  have h5 := arctan_error (1 / 5) (by norm_num) (by norm_num) 40
  have h239 := arctan_error (1 / 239) (by norm_num) (by norm_num) 12
  have hpi : π = 16 * Real.arctan ((1 / 5 : ℚ) : ℝ) - 4 * Real.arctan ((1 / 239 : ℚ) : ℝ) := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    have h5 : ((1 / 5 : ℚ) : ℝ) = 5⁻¹ := by norm_num
    have h239 : ((1 / 239 : ℚ) : ℝ) = 239⁻¹ := by norm_num
    rw [h5, h239]
    linarith
  unfold Encl
  rw [piMid, piRad, hpi]
  push_cast at h5 h239 ⊢
  rw [abs_le] at h5 h239 ⊢
  constructor <;> linarith [h5.1, h5.2, h239.1, h239.2]

/-! `cos 2` and `sin 2`. -/

def cos1Mid : ℚ := evalQ (cosCoeffs 20) 1
def sin1Mid : ℚ := evalQ (sinCoeffs 20) 1
def trigRad : ℚ := 2 / (40 : ℕ).factorial

theorem cos1_encl : Encl (Real.cos 1) cos1Mid trigRad := by
  have h := cos_remainder 1 (by norm_num) 20
  unfold Encl
  rw [cos1Mid, trigRad, evalQ_cast]
  push_cast
  simpa using h

theorem sin1_encl : Encl (Real.sin 1) sin1Mid (2 / (41 : ℕ).factorial) := by
  have h := sin_remainder 1 (by norm_num) 20
  unfold Encl
  rw [sin1Mid, evalQ_cast]
  push_cast
  simpa using h

theorem cos2_encl : Encl (Real.cos 2)
    (2 * (cos1Mid * cos1Mid) - 1)
    (2 * (qabs cos1Mid * trigRad + qabs cos1Mid * trigRad + trigRad * trigRad)) := by
  have h := ((cos1_encl.mul cos1_encl).const_mul 2).sub (Encl.exact 1)
  have e : ((2 : ℚ) : ℝ) * (Real.cos 1 * Real.cos 1) - ((1 : ℚ) : ℝ) = Real.cos 2 := by
    have := Real.cos_two_mul (1 : ℝ)
    rw [mul_one] at this
    rw [this]
    push_cast
    ring
  refine (h.congr e).mono ?_
  norm_num [qabs]

theorem sin2_encl : Encl (Real.sin 2) (2 * (sin1Mid * cos1Mid))
    (2 * (qabs sin1Mid * trigRad + qabs cos1Mid * (2 / (41 : ℕ).factorial) +
      2 / (41 : ℕ).factorial * trigRad)) := by
  have h := (sin1_encl.mul cos1_encl).const_mul 2
  have e : ((2 : ℚ) : ℝ) * (Real.sin 1 * Real.cos 1) = Real.sin 2 := by
    have := Real.sin_two_mul (1 : ℝ)
    rw [mul_one] at this
    rw [this]
    push_cast
    ring
  refine (h.congr e).mono ?_
  norm_num [qabs]

#print axioms Encl.mul
#print axioms Encl.inv
#print axioms Encl.sqrt
#print axioms pi_encl
#print axioms cos2_encl
#print axioms sin2_encl

end LeanExe.ProofKit.BesselConstants
