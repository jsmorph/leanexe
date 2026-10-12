import Verified.Examples.FourierMath
import Verified.Examples.FourierPositive
import Verified.Examples.FFTComplex
import Verified.Examples.FFTBits
import Mathlib.Data.Complex.BigOperators

namespace Verified.Examples.FFTMath

open CodeLib.IEEE64 FourierSpec
open scoped BigOperators

noncomputable def sign (inverse : Bool) : ℝ := if inverse then 1 else -1

noncomputable def cis (inverse : Bool) (theta : ℝ) : ℂ :=
  ⟨Real.cos theta, sign inverse * Real.sin theta⟩

noncomputable def root (inverse : Bool) (n m : Nat) : ℂ := cis inverse (phase n m)

@[simp] theorem root_re (inverse : Bool) (n m : Nat) :
    (root inverse n m).re = Real.cos (phase n m) := rfl

@[simp] theorem root_im (inverse : Bool) (n m : Nat) :
    (root inverse n m).im = sign inverse * Real.sin (phase n m) := rfl

theorem cis_norm (inverse : Bool) (theta : ℝ) : ‖cis inverse theta‖ = 1 := by
  have hsign : sign inverse ^ 2 = 1 := by cases inverse <;> norm_num [sign]
  have hsq : ‖cis inverse theta‖ ^ 2 = 1 := by
    rw [FFTComplex.norm_sq]
    dsimp [cis]
    rw [mul_pow, hsign, one_mul]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  nlinarith [norm_nonneg (cis inverse theta)]

theorem root_norm (inverse : Bool) (n m : Nat) : ‖root inverse n m‖ = 1 :=
  cis_norm inverse (phase n m)

theorem root_zero (inverse : Bool) (n : Nat) : root inverse n 0 = 1 := by
  apply Complex.ext <;> simp [root, cis, phase]

theorem cis_add (inverse : Bool) (a b : ℝ) :
    cis inverse (a + b) = cis inverse a * cis inverse b := by
  cases inverse <;> apply Complex.ext
  all_goals simp [cis, sign, Real.cos_add, Real.sin_add]
  all_goals ring

theorem cis_add_pi (inverse : Bool) (a : ℝ) :
    cis inverse (a + Real.pi) = -cis inverse a := by
  cases inverse <;> apply Complex.ext <;> simp [cis, sign]

theorem cis_add_nat_mul_two_pi (inverse : Bool) (a : ℝ) (m : Nat) :
    cis inverse (a + (m : ℝ) * (2 * Real.pi)) = cis inverse a := by
  unfold cis
  rw [Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

theorem root_even (inverse : Bool) (h t k : Nat) (hh : 0 < h) :
    root inverse (2 * h) ((2 * t) * k) = root inverse h (t * k) := by
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
  unfold root
  congr 1
  unfold phase
  push_cast
  field_simp [hh0]

theorem root_odd (inverse : Bool) (h t k : Nat) (hh : 0 < h) :
    root inverse (2 * h) ((2 * t + 1) * k) =
      root inverse h (t * k) * root inverse (2 * h) k := by
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
  unfold root
  rw [← cis_add]
  congr 1
  unfold phase
  push_cast
  field_simp [hh0]

theorem root_frequency_add (inverse : Bool) (n t k : Nat) (hn : 0 < n) :
    root inverse n (t * (k + n)) = root inverse n (t * k) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp : phase n (t * (k + n)) = phase n (t * k) + (t : ℝ) * (2 * Real.pi) := by
    unfold phase
    push_cast
    field_simp [hn0]
  unfold root
  rw [hp, cis_add_nat_mul_two_pi]

theorem root_half_add (inverse : Bool) (h k : Nat) (hh : 0 < h) :
    root inverse (2 * h) (k + h) = -root inverse (2 * h) k := by
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
  have hp : phase (2 * h) (k + h) = phase (2 * h) k + Real.pi := by
    unfold phase
    push_cast
    field_simp [hh0]
  unfold root
  rw [hp, cis_add_pi]

theorem root_stage (inverse : Bool) (p s j : Nat) (hs : s ≤ p) :
    root inverse (2 ^ p) (j * 2 ^ (p - s)) = root inverse (2 ^ s) j := by
  have hpow : (2 : Nat) ^ p = 2 ^ s * 2 ^ (p - s) := by
    rw [← pow_add]
    congr 1
    omega
  unfold root
  congr 1
  unfold phase
  rw [hpow]
  push_cast
  field_simp

theorem root_stage_succ (inverse : Bool) (p s j : Nat) (hs : s < p) :
    root inverse (2 ^ p) (j * 2 ^ (p - s - 1)) = root inverse (2 ^ (s + 1)) j := by
  simpa only [Nat.sub_sub] using root_stage inverse p (s + 1) j (by omega)

theorem sum_even_odd {α : Type} [AddCommMonoid α] (f : Nat → α) (h : Nat) :
    (∑ t ∈ Finset.range (2 * h), f t) =
      (∑ t ∈ Finset.range h, f (2 * t)) + (∑ t ∈ Finset.range h, f (2 * t + 1)) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 2 * (h + 1) = (2 * h + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    abel

noncomputable def dft (inverse : Bool) (n : Nat) (f : Nat → ℂ) (k : Nat) : ℂ :=
  ∑ t ∈ Finset.range n, f t * root inverse n (t * k)

theorem dft_frequency_add (inverse : Bool) (n : Nat) (f : Nat → ℂ) (k : Nat)
    (hn : 0 < n) : dft inverse n f (k + n) = dft inverse n f k := by
  unfold dft
  apply Finset.sum_congr rfl
  intro t _
  rw [root_frequency_add inverse n t k hn]

theorem dft_even_odd (inverse : Bool) (h : Nat) (f : Nat → ℂ) (k : Nat) (hh : 0 < h) :
    dft inverse (2 * h) f k = dft inverse h (fun t => f (2 * t)) k +
      dft inverse h (fun t => f (2 * t + 1)) k * root inverse (2 * h) k := by
  unfold dft
  rw [sum_even_odd]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    rw [root_even inverse h t k hh]
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [root_odd inverse h t k hh]
    ring

theorem dft_even_odd_upper (inverse : Bool) (h : Nat) (f : Nat → ℂ) (k : Nat)
    (hh : 0 < h) :
    dft inverse (2 * h) f (k + h) = dft inverse h (fun t => f (2 * t)) k -
      dft inverse h (fun t => f (2 * t + 1)) k * root inverse (2 * h) k := by
  rw [dft_even_odd inverse h f (k + h) hh,
    dft_frequency_add inverse h _ k hh, dft_frequency_add inverse h _ k hh,
    root_half_add inverse h k hh]
  ring

noncomputable def inputValue (xs : Array Float) (j : Nat) : ℂ :=
  ⟨value xs[2 * j]!.toBits, value xs[2 * j + 1]!.toBits⟩

def sampleIndex (p s b t : Nat) : Nat :=
  FFTBits.reverseNat (p - s) b + 2 ^ (p - s) * t

noncomputable def stageValue (xs : Array Float) (inverse : Bool) (p s b k : Nat) : ℂ :=
  dft inverse (2 ^ s) (fun t => inputValue xs (sampleIndex p s b t)) k

noncomputable def stageMass (xs : Array Float) (p s b : Nat) : ℝ :=
  ∑ t ∈ Finset.range (2 ^ s),
    (|(inputValue xs (sampleIndex p s b t)).re| + |(inputValue xs (sampleIndex p s b t)).im|)

theorem stageValue_zero (xs : Array Float) (inverse : Bool) (p b k : Nat) :
    stageValue xs inverse p 0 b k = inputValue xs (FFTBits.reverseNat p b) := by
  simp [stageValue, dft, sampleIndex, root_zero]

theorem stageMass_zero (xs : Array Float) (p b : Nat) :
    stageMass xs p 0 b = |(inputValue xs (FFTBits.reverseNat p b)).re| +
      |(inputValue xs (FFTBits.reverseNat p b)).im| := by
  simp [stageMass, sampleIndex]

theorem stageMass_nonneg (xs : Array Float) (p s b : Nat) : 0 ≤ stageMass xs p s b :=
  Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem stageValue_norm_le_mass (xs : Array Float) (inverse : Bool) (p s b k : Nat) :
    ‖stageValue xs inverse p s b k‖ ≤ stageMass xs p s b := by
  unfold stageValue dft stageMass
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t _
  rw [norm_mul, root_norm, mul_one]
  exact Complex.norm_le_abs_re_add_abs_im _

theorem sampleIndex_even (p s b t : Nat) (hs : s + 1 ≤ p) :
    sampleIndex p (s + 1) b (2 * t) = sampleIndex p s (2 * b) t := by
  unfold sampleIndex
  rw [show p - s = (p - (s + 1)) + 1 by omega, FFTBits.reverseNat_even, pow_succ]
  ring

theorem sampleIndex_odd (p s b t : Nat) (hs : s + 1 ≤ p) :
    sampleIndex p (s + 1) b (2 * t + 1) = sampleIndex p s (2 * b + 1) t := by
  unfold sampleIndex
  rw [show p - s = (p - (s + 1)) + 1 by omega, FFTBits.reverseNat_odd, pow_succ]
  ring

theorem stageValue_lower (xs : Array Float) (inverse : Bool) (p s b k : Nat)
    (hs : s + 1 ≤ p) :
    stageValue xs inverse p (s + 1) b k = stageValue xs inverse p s (2 * b) k +
      stageValue xs inverse p s (2 * b + 1) k * root inverse (2 ^ (s + 1)) k := by
  unfold stageValue
  rw [pow_succ, mul_comm (2 ^ s) 2, dft_even_odd inverse (2 ^ s) _ k (by positivity)]
  simp_rw [sampleIndex_even p s b _ hs, sampleIndex_odd p s b _ hs]

theorem stageValue_upper (xs : Array Float) (inverse : Bool) (p s b k : Nat)
    (hs : s + 1 ≤ p) :
    stageValue xs inverse p (s + 1) b (k + 2 ^ s) =
      stageValue xs inverse p s (2 * b) k -
      stageValue xs inverse p s (2 * b + 1) k * root inverse (2 ^ (s + 1)) k := by
  unfold stageValue
  rw [pow_succ, mul_comm (2 ^ s) 2, dft_even_odd_upper inverse (2 ^ s) _ k (by positivity)]
  simp_rw [sampleIndex_even p s b _ hs, sampleIndex_odd p s b _ hs]

theorem stageMass_children (xs : Array Float) (p s b : Nat) (hs : s + 1 ≤ p) :
    stageMass xs p (s + 1) b = stageMass xs p s (2 * b) + stageMass xs p s (2 * b + 1) := by
  unfold stageMass
  rw [pow_succ, mul_comm (2 ^ s) 2, sum_even_odd]
  simp_rw [sampleIndex_even p s b _ hs, sampleIndex_odd p s b _ hs]

theorem stageMass_final (xs : Array Float) (p b : Nat) (hn : xs.size / 2 = 2 ^ p) :
    stageMass xs p p b = inputNorm xs := by
  unfold stageMass sampleIndex inputNorm
  simp only [Nat.sub_self, FFTBits.reverseNat_zero, pow_zero, zero_add, one_mul]
  rw [hn]
  rfl

theorem sampleIndex_lt (p s b t : Nat) (hs : s ≤ p) (ht : t < 2 ^ s) :
    sampleIndex p s b t < 2 ^ p := by
  have hb := FFTBits.reverseNat_lt (p - s) b
  have hpow : (2 : Nat) ^ (p - s) * 2 ^ s = 2 ^ p := by
    rw [← pow_add, Nat.sub_add_cancel hs]
  calc
    sampleIndex p s b t < 2 ^ (p - s) + 2 ^ (p - s) * t := Nat.add_lt_add_right hb _
    _ = 2 ^ (p - s) * (t + 1) := by ring
    _ ≤ 2 ^ (p - s) * 2 ^ s := Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ p := hpow

theorem stageMass_le_inputNorm (xs : Array Float) (p s b : Nat)
    (hn : xs.size / 2 = 2 ^ p) (hs : s ≤ p) : stageMass xs p s b ≤ inputNorm xs := by
  let mass (j : Nat) := |(inputValue xs j).re| + |(inputValue xs j).im|
  have hinj : Function.Injective (sampleIndex p s b) := by
    intro a c hac
    unfold sampleIndex at hac
    exact mul_left_cancel₀ (by positivity : (2 : Nat) ^ (p - s) ≠ 0) (Nat.add_left_cancel hac)
  have hsubset : (Finset.range (2 ^ s)).image (sampleIndex p s b) ⊆ Finset.range (xs.size / 2) := by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_range.mpr
    rw [hn]
    exact sampleIndex_lt p s b t hs (Finset.mem_range.mp ht)
  change (∑ t ∈ Finset.range (2 ^ s), mass (sampleIndex p s b t)) ≤
    (∑ j ∈ Finset.range (xs.size / 2), mass j)
  rw [← Finset.sum_image hinj.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun j _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem stageValue_final_re (xs : Array Float) (inverse : Bool) (p b k : Nat)
    (hn : xs.size / 2 = 2 ^ p) :
    (stageValue xs inverse p p b k).re =
      if inverse then FourierPositive.realReference xs k else realDFT xs k := by
  unfold stageValue dft sampleIndex
  simp only [Nat.sub_self, FFTBits.reverseNat_zero, pow_zero, zero_add, one_mul, Complex.re_sum]
  cases inverse <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · unfold realDFT
    rw [hn]
    apply Finset.sum_congr rfl
    intro t _
    simp [inputValue, root, cis, sign]
  · unfold FourierPositive.realReference
    rw [hn]
    apply Finset.sum_congr rfl
    intro t _
    simp [inputValue, root, cis, sign]

theorem stageValue_final_im (xs : Array Float) (inverse : Bool) (p b k : Nat)
    (hn : xs.size / 2 = 2 ^ p) :
    (stageValue xs inverse p p b k).im =
      if inverse then FourierPositive.imagReference xs k else imagDFT xs k := by
  unfold stageValue dft sampleIndex
  simp only [Nat.sub_self, FFTBits.reverseNat_zero, pow_zero, zero_add, one_mul, Complex.im_sum]
  cases inverse <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · unfold imagDFT
    rw [hn]
    apply Finset.sum_congr rfl
    intro t _
    simp [inputValue, root, cis, sign]
    ring
  · unfold FourierPositive.imagReference
    rw [hn]
    apply Finset.sum_congr rfl
    intro t _
    simp [inputValue, root, cis, sign]

#print axioms root_norm
#print axioms root_stage
#print axioms root_stage_succ
#print axioms dft_even_odd
#print axioms dft_even_odd_upper
#print axioms stageValue_zero
#print axioms stageMass_zero
#print axioms stageMass_nonneg
#print axioms stageValue_norm_le_mass
#print axioms stageValue_lower
#print axioms stageValue_upper
#print axioms stageMass_children
#print axioms stageMass_final
#print axioms stageMass_le_inputNorm
#print axioms stageValue_final_re
#print axioms stageValue_final_im

end Verified.Examples.FFTMath
