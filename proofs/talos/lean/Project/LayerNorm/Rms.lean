import Project.LayerNorm.Quotient

namespace Project.LayerNorm
open CodeLib.IEEE64 Project.ProofKit RealNormalization

set_option exponentiation.threshold 4096

noncomputable def energy (c : Fin 4 → UInt64) : ℝ := sumSquares (fun i => value (c i))
noncomputable def rms (c : Fin 4 → UInt64) : ℝ := Real.sqrt (energy c/4+1/100000)

def varianceWords (c : Fin 4 → UInt64) : UInt64 :=
  average (Wasm.IEEE64.mul (c 0) (c 0)) (Wasm.IEEE64.mul (c 1) (c 1))
    (Wasm.IEEE64.mul (c 2) (c 2)) (Wasm.IEEE64.mul (c 3) (c 3))

theorem variance_roundoff (c : Fin 4 → UInt64) (hf : ∀ i, Finite (c i))
    (hRange : 14*(energy c+1/100000) < (2:ℝ)^1022) :
    Finite (varianceWords c) ∧ |value (varianceWords c)| ≤ energy c+1/100000 ∧
      |value (varianceWords c)-energy c/4| ≤ 11*arithmeticEpsilon*(energy c+1/100000) := by
  let b := energy c+1/100000
  have hEnergy : 0 ≤ energy c := sumSquares_nonneg _
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hNormal : minNormal64 ≤ b := by
    have h : minNormal64 ≤ (1:ℝ)/100000 := by norm_num [minNormal64]
    dsimp [b]
    linarith
  have hs (i : Fin 4) := F64ArithmeticBounds.mul_error_scaled (c i) (c i) (hf i) (hf i)
    b hNormal (by dsimp [b] at *; linarith)
    (by rw [abs_of_nonneg (mul_self_nonneg _)]; have := coordinate_square_le (fun j => value (c j)) i
        change (value (c i))^2 ≤ energy c at this
        dsimp [b]; nlinarith)
  have hsMag (i : Fin 4) : |value (Wasm.IEEE64.mul (c i) (c i))| ≤ 2*b := by
    have hp : |value (c i)*value (c i)| ≤ b := by
      rw [abs_of_nonneg (mul_self_nonneg _)]
      have := coordinate_square_le (fun j => value (c j)) i
      change (value (c i))^2 ≤ energy c at this
      dsimp [b]; nlinarith
    have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ (hs i).2 hp
    have hu : arithmeticEpsilon ≤ 1 := by norm_num [arithmeticEpsilon]
    nlinarith [mul_le_mul_of_nonneg_right hu hb0]
  have ha := average_error_scaled (fun i => Wasm.IEEE64.mul (c i) (c i)) (2*b)
    (by linarith) (by dsimp [b]; linarith) (fun i => (hs i).1) hsMag
  have hp := mean_perturbation (fun i => value (Wasm.IEEE64.mul (c i) (c i)))
    (fun i => (value (c i))^2) (arithmeticEpsilon*b)
    (fun i => by simpa only [pow_two] using (hs i).2)
  have hError : |value (varianceWords c)-energy c/4| ≤ 11*arithmeticEpsilon*b :=
    (abs_sub_le _ _ _).trans ((add_le_add ha.2.2 hp).trans_eq (by ring))
  refine ⟨ha.1, ?_, hError⟩
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ (energy c/4) hError
    (by rw [abs_of_nonneg (by positivity)])
  have hu : 11*arithmeticEpsilon ≤ 1/2 := by norm_num [arithmeticEpsilon]
  have hScale := mul_le_mul_of_nonneg_right hu hb0
  dsimp [b] at *
  nlinarith only [hm, hScale, hEnergy]

theorem rms_pos (c : Fin 4 → UInt64) : 0 < rms c := by
  apply Real.sqrt_pos.mpr
  have := sumSquares_nonneg (fun i => value (c i))
  change 0 ≤ energy c at this
  linarith

theorem rms_energy (c : Fin 4 → UInt64) : energy c = 4*((rms c)^2-1/100000) := by
  have hEnergy : 0 ≤ energy c := sumSquares_nonneg _
  have hr := Real.sq_sqrt (show 0 ≤ energy c/4+1/100000 by linarith)
  change (rms c)^2 = energy c/4+1/100000 at hr
  linarith

theorem rms_lower (c : Fin 4 → UInt64) : 1/1000 ≤ rms c := by
  have hEnergy : 0 ≤ energy c := sumSquares_nonneg _
  apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
  linarith

theorem rms_normalized_magnitude (c : Fin 4 → UInt64) (i : Fin 4) :
    |value (c i)/rms c| ≤ 2 := by
  rw [abs_div, abs_of_pos (rms_pos c)]
  apply (div_le_iff₀ (rms_pos c)).mpr
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity [rms_pos c])).mp
  have hc := coordinate_square_le (fun j => value (c j)) i
  change (value (c i))^2 ≤ energy c at hc
  rw [rms_energy c] at hc
  rw [sq_abs]
  nlinarith only [hc]

theorem epsilon_relative :
    |value 0x3EE4F8B588E368F1-1/100000| ≤ arithmeticEpsilon/100000 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
    UInt64.toNat_ofNat, arithmeticEpsilon]

theorem denominator_roundoff (c : Fin 4 → UInt64) (hf : ∀ i, Finite (c i))
    (hRange : 14*(energy c+1/100000) < (2:ℝ)^1022) :
    let d := denominator (c 0) (c 1) (c 2) (c 3)
    Finite d ∧ 0 < value d ∧ rms c/2 ≤ value d ∧
      |value d-rms c| ≤ 61*arithmeticEpsilon*rms c := by
  let a := Wasm.IEEE64.add (varianceWords c) 0x3EE4F8B588E368F1
  let target := energy c/4+1/100000
  have hEnergy : 0 ≤ energy c := sumSquares_nonneg _
  have ht : 0 < target := by dsimp [target]; linarith
  have hv := variance_roundoff c hf hRange
  have hEpsilon : |value 0x3EE4F8B588E368F1| ≤ 2/100000 := by
    have h := F64ArithmeticBounds.magnitude_of_error _ _ _ (1/100000) epsilon_relative
      (by norm_num)
    have hu : arithmeticEpsilon ≤ 1 := by norm_num [arithmeticEpsilon]
    linarith
  have ha := F64ArithmeticBounds.add_error_scaled (varianceWords c) 0x3EE4F8B588E368F1
    hv.1 (by unfold CodeLib.IEEE64.Finite; decide) (3*(energy c+1/100000))
    (by norm_num at hRange ⊢; linarith)
    ((abs_add_le _ _).trans (by linarith [hv.2.1]))
  have hRelative : |value a-target| ≤ (60*arithmeticEpsilon)*target := by
    have h1 := abs_le.mp ha.2
    have h2 := abs_le.mp hv.2.2
    have h3 := abs_le.mp epsilon_relative
    have hu := F64ArithmeticBounds.epsilon_pos
    apply abs_le.mpr
    dsimp [a, target]
    constructor <;> nlinarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hu, hEnergy]
  have hSmall : 60*arithmeticEpsilon ≤ 1/2 := by norm_num [arithmeticEpsilon]
  have hp : 0 < value a := by
    have h := (abs_le.mp hRelative).1
    have hScale := mul_le_mul_of_nonneg_right hSmall ht.le
    linarith
  have hs := F64SqrtComposition.input_error a
    (F64Order.positiveBits_of_finite_value_pos a ha.1 hp) target (60*arithmeticEpsilon)
    ht (by linarith) hRelative
  have hd := F64Order.positiveBits_spec _ hs.1
  have he : |value (Wasm.IEEE64.sqrt a)-rms c| ≤ 61*arithmeticEpsilon*rms c :=
    hs.2.trans_eq (by dsimp [target, rms]; ring)
  refine ⟨hd.1, hd.2, ?_, he⟩
  have hScale := mul_le_mul_of_nonneg_right
    (show 61*arithmeticEpsilon ≤ (1:ℝ)/2 by norm_num [arithmeticEpsilon]) (rms_pos c).le
  have h := (abs_le.mp he).1
  change rms c/2 ≤ value (Wasm.IEEE64.sqrt a)
  linarith only [h, hScale]

theorem normalized_roundoff (c : Fin 4 → UInt64) (hf : ∀ i, Finite (c i))
    (hRange : 14*(energy c+1/100000) < (2:ℝ)^1022) (i : Fin 4) :
    let q := Wasm.IEEE64.div (c i) (denominator (c 0) (c 1) (c 2) (c 3))
    Finite q ∧ |value q| ≤ 3 ∧
      |value q-value (c i)/rms c| ≤ 247*arithmeticEpsilon := by
  let d := denominator (c 0) (c 1) (c 2) (c 3)
  have hd := denominator_roundoff c hf hRange
  have hm := rms_normalized_magnitude c i
  have hq := quotient_error_bounded (value (c i)) (value d) (value (c i)) (rms c) 0 61
    (by norm_num) (by norm_num) (rms_lower c) hd.2.2.1 hm (by simp) hd.2.2.2
  have hQuotient : |value (c i)/value d| ≤ 3 := by
    have h := F64ArithmeticBounds.magnitude_of_error _ _ _ 2 hq hm
    norm_num [arithmeticEpsilon] at h
    linarith
  have hd0 : Wasm.IEEE64.scaledMagnitude d ≠ 0 := by
    intro hz
    have hp := hd.2.1
    change 0 < value d at hp
    simp [value, Wasm.IEEE64.scaledValue, hz] at hp
  have ho := F64ArithmeticBounds.div_error (c i) d (hf i) hd.1 hd0 3
    (by norm_num) (by norm_num) hQuotient
  have he : |value (Wasm.IEEE64.div (c i) d)-value (c i)/rms c| ≤ 247*arithmeticEpsilon :=
    (abs_sub_le _ _ _).trans ((add_le_add ho.2 hq).trans_eq (by ring))
  refine ⟨ho.1, ?_, he⟩
  exact (F64ArithmeticBounds.magnitude_of_error _ _ _ 2 he hm).trans (by norm_num [arithmeticEpsilon])

#print axioms variance_roundoff
#print axioms rms_normalized_magnitude
#print axioms denominator_roundoff
#print axioms normalized_roundoff
end Project.LayerNorm
