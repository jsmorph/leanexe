import Project.ProofKit.F64NormalizeTiny
import Project.ProofKit.F64OrderComplete

namespace Project.ProofKit.F64AdmissibilityTiny
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64Normalize
open Project.ProofKit.F64NormalizeTiny
open Project.ProofKit.F64Admissibility
  (topExponent maxWord_toNat normalizable normalizable_spec finite_exponent_bound)

def residual (rho mx my energy : UInt64) : UInt64 :=
  let top := topExponent rho mx my energy
  F64InternalEnergy.residual (normalizedMagnitude rho top)
    (normalizedMomentum mx top) (normalizedMomentum my top) (normalizedMagnitude energy top)

noncomputable def exactResidual (rho mx my energy : UInt64) : ℝ :=
  let top := topExponent rho mx my energy
  exactMagnitude rho top * exactMagnitude energy top -
    ((exactMagnitude mx top)^2 + (exactMagnitude my top)^2) / 2

def checked (rho mx my energy : UInt64) : Bool :=
  if positiveBits rho && finiteBits mx && finiteBits my && positiveBits energy then
    let top := topExponent rho mx my energy
    if normalizable rho top && momentumNormalizable mx top &&
        momentumNormalizable my top && normalizable energy top then
      let result := residual rho mx my energy
      positiveBits result && decide ((0x3CE0000000000000 : UInt64) < result)
    else false
  else false

theorem residual_bounds (rho mx my energy : UInt64)
    (hr : Finite rho) (hx : Finite mx) (hy : Finite my) (he : Finite energy)
    (nr : normalizable rho (topExponent rho mx my energy) = true)
    (nx : momentumNormalizable mx (topExponent rho mx my energy) = true)
    (ny : momentumNormalizable my (topExponent rho mx my energy) = true)
    (ne : normalizable energy (topExponent rho mx my energy) = true) :
    Finite (residual rho mx my energy) ∧
      exactResidual rho mx my energy - 5 * arithmeticEpsilon ≤ value (residual rho mx my energy) ∧
      value (residual rho mx my energy) ≤ exactResidual rho mx my energy +
        5 * arithmeticEpsilon + arithmeticEpsilon^2 := by
  let top := topExponent rho mx my energy
  have ht_eq : top.toNat = max (max (Wasm.IEEE64.exponent rho) (Wasm.IEEE64.exponent mx))
      (max (Wasm.IEEE64.exponent my) (Wasm.IEEE64.exponent energy)) := by
    simp only [top, topExponent, maxWord_toNat, exponentBits_toNat]
  have ht : top.toNat ≤ 2046 := by
    rw [ht_eq]
    exact max_le (max_le (finite_exponent_bound rho hr) (finite_exponent_bound mx hx))
      (max_le (finite_exponent_bound my hy) (finite_exponent_bound energy he))
  have lr : Wasm.IEEE64.exponent rho ≤ top.toNat := by
    rw [ht_eq]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have lx : Wasm.IEEE64.exponent mx ≤ top.toNat := by
    rw [ht_eq]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have ly : Wasm.IEEE64.exponent my ≤ top.toNat := by
    rw [ht_eq]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have le : Wasm.IEEE64.exponent energy ≤ top.toNat := by
    rw [ht_eq]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have sr := normalizedMagnitude_spec rho top ht lr (normalizable_spec rho top hr nr)
  have sx := normalizedMomentum_spec mx top hx ht lx nx
  have sy := normalizedMomentum_spec my top hy ht ly ny
  have se := normalizedMagnitude_spec energy top ht le (normalizable_spec energy top he ne)
  have err := F64InternalEnergy.residual_error _ _ _ _ sr.1 sx.1 sy.1 se.1
    sr.2.1 sx.2.1 sy.2.1 se.2.1
  rw [normalizedMagnitude_exact rho top hr ht lr nr,
    normalizedMagnitude_exact energy top he ht le ne] at err
  have bounds := abs_le.mp err.2
  have dx := sx.2.2.2.2
  have dy := sy.2.2.2.2
  dsimp only [top] at bounds dx dy
  refine ⟨err.1, ?_, ?_⟩ <;> dsimp only [exactResidual, residual]
  · nlinarith only [bounds.1, dx.1, dy.1]
  · nlinarith only [bounds.2, dx.2, dy.2]

set_option exponentiation.threshold 4096 in
theorem threshold_value : value 0x3CE0000000000000 = 8 * arithmeticEpsilon := by
  change ((2^1025 : Nat) : ℝ) / (2 : ℝ)^1074 = 8 * (1 / (2 : ℝ)^52)
  norm_num

set_option exponentiation.threshold 4096 in
theorem exactResidual_scaled (rho mx my energy : UInt64)
    (hr : 0 < value rho) (he : 0 < value energy) :
    exactResidual rho mx my energy * ((2 : ℝ)^(topExponent rho mx my energy).toNat)^2 =
      (value rho * value energy - ((value mx)^2 + (value my)^2) / 2) * ((2 : ℝ)^1021)^2 := by
  simp only [exactResidual, exactMagnitude, abs_of_pos hr, abs_of_pos he]
  field_simp
  simp only [sq_abs]

theorem checked_sound (rho mx my energy : UInt64)
    (h : checked rho mx my energy = true) :
    Finite rho ∧ Finite mx ∧ Finite my ∧ Finite energy ∧
      0 < value rho ∧ 0 < value energy ∧
      0 < value rho * value energy - ((value mx)^2 + (value my)^2) / 2 := by
  unfold checked at h
  split at h
  · rename_i hi
    obtain ⟨⟨⟨hr, hx⟩, hy⟩, he⟩ := by simpa only [Bool.and_eq_true_iff] using hi
    have hr' := positiveBits_spec rho hr
    have he' := positiveBits_spec energy he
    have hx' := (finiteBits_iff mx).mp hx
    have hy' := (finiteBits_iff my).mp hy
    dsimp only at h
    split at h
    · rename_i hn
      obtain ⟨⟨⟨nr, nx⟩, ny⟩, ne⟩ := by simpa only [Bool.and_eq_true_iff] using hn
      have bounds := residual_bounds rho mx my energy hr'.1 hx' hy' he'.1 nr nx ny ne
      obtain ⟨hp, hm⟩ := Bool.and_eq_true_iff.mp h
      have hThreshold := (positive_word_lt_iff _ _ (by decide) hp).mp (of_decide_eq_true hm)
      rw [threshold_value] at hThreshold
      have eps : 0 < arithmeticEpsilon := by norm_num [arithmeticEpsilon]
      have epsSquare : arithmeticEpsilon^2 < arithmeticEpsilon := by norm_num [arithmeticEpsilon]
      have hExact : 0 < exactResidual rho mx my energy := by linarith [bounds.2.2]
      have hScaled : 0 <
          (value rho * value energy - ((value mx)^2 + (value my)^2) / 2) * ((2 : ℝ)^1021)^2 := by
        rw [← exactResidual_scaled rho mx my energy hr'.2 he'.2]
        exact mul_pos hExact (by positivity)
      exact ⟨hr'.1, hx', hy', he'.1, hr'.2, he'.2,
        (mul_pos_iff_of_pos_right (by positivity : 0 < ((2 : ℝ)^1021)^2)).mp hScaled⟩
    · contradiction
  · contradiction

theorem checked_of_margin (rho mx my energy : UInt64)
    (hr : positiveBits rho = true) (hx : finiteBits mx = true)
    (hy : finiteBits my = true) (he : positiveBits energy = true)
    (nr : normalizable rho (topExponent rho mx my energy) = true)
    (nx : momentumNormalizable mx (topExponent rho mx my energy) = true)
    (ny : momentumNormalizable my (topExponent rho mx my energy) = true)
    (ne : normalizable energy (topExponent rho mx my energy) = true)
    (hMargin : 13 * arithmeticEpsilon < exactResidual rho mx my energy) :
    checked rho mx my energy = true := by
  have bounds := residual_bounds rho mx my energy (positiveBits_spec rho hr).1
    ((finiteBits_iff mx).mp hx) ((finiteBits_iff my).mp hy) (positiveBits_spec energy he).1
    nr nx ny ne
  have hLower : 8 * arithmeticEpsilon < value (residual rho mx my energy) := by
    linarith [bounds.2.1]
  have hp := positiveBits_of_finite_value_pos _ bounds.1
    (lt_trans (by norm_num [arithmeticEpsilon]) hLower)
  have hWord : (0x3CE0000000000000 : UInt64) < residual rho mx my energy := by
    apply (positive_word_lt_iff _ _ (by decide) hp).mpr
    rwa [threshold_value]
  simp only [checked, hr, hx, hy, he, Bool.and_self, ite_true, nr, nx, ny, ne,
    hp, Bool.true_and, decide_eq_true_eq]
  exact hWord

theorem checked_extends (rho mx my energy : UInt64)
    (h : Project.ProofKit.F64Admissibility.checked rho mx my energy = true) :
    checked rho mx my energy = true := by
  unfold Project.ProofKit.F64Admissibility.checked at h
  split at h
  · rename_i hi
    dsimp only at h
    split at h
    · rename_i hn
      obtain ⟨⟨⟨nr, nx⟩, ny⟩, ne⟩ := by simpa only [Bool.and_eq_true_iff] using hn
      simpa only [checked, hi, ite_true, nr, ne, momentumNormalizable, nx, ny,
        Bool.true_or, Bool.and_self, residual, normalizedMomentum, ite_true] using h
    · contradiction
  · contradiction

#print axioms residual_bounds
#print axioms exactResidual_scaled
#print axioms checked_sound
#print axioms checked_of_margin
#print axioms checked_extends
end Project.ProofKit.F64AdmissibilityTiny
