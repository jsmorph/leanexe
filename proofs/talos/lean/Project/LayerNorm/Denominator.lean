import Project.LayerNorm.Variance
import Project.ProofKit.F64SqrtComposition

namespace Project.LayerNorm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem epsilon_bounds : |value 0x3EE4F8B588E368F1| ≤ 1 ∧
    |value 0x3EE4F8B588E368F1 - 1/100000| ≤ arithmeticEpsilon := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
    UInt64.toNat_ofNat, arithmeticEpsilon]

theorem sqrt_variance_error_bounded (v : UInt64) (exactVariance bound error ratio : ℝ)
    (hb1 : 1 ≤ bound) (hbmax : bound ≤ 2048) (he0 : 0 ≤ error)
    (hratio : (error+bound+2)*100000 ≤ ratio)
    (hsmall : (ratio+1)*arithmeticEpsilon ≤ 1/2)
    (hf : Finite v) (hb : |value v| ≤ bound) (hv : 0 ≤ exactVariance)
    (he : |value v-exactVariance| ≤ error*arithmeticEpsilon) :
    let d := Wasm.IEEE64.sqrt (Wasm.IEEE64.add v 0x3EE4F8B588E368F1)
    let r := Real.sqrt (exactVariance + 1/100000)
    Finite d ∧ 0 < value d ∧ r/2 ≤ value d ∧
      |value d-r| ≤ (ratio+1)*arithmeticEpsilon*r := by
  let a := Wasm.IEEE64.add v 0x3EE4F8B588E368F1
  let r := Real.sqrt (exactVariance + 1/100000)
  have ha := F64ArithmeticBounds.add_error v 0x3EE4F8B588E368F1 hf
    (by unfold CodeLib.IEEE64.Finite; decide) (bound+1) (by linarith) (by norm_num; linarith)
    ((abs_add_le _ _).trans (by linarith [epsilon_bounds.1]))
  have herr : |value a - (exactVariance + 1/100000)| ≤ (error+bound+2)*arithmeticEpsilon := by
    have h1 := abs_le.mp ha.2
    have h2 := abs_le.mp he
    have h3 := abs_le.mp epsilon_bounds.2
    apply abs_le.mpr
    constructor <;> nlinarith
  have hr0 : 0 ≤ ratio := by linarith
  have hbudget : (error+bound+2)*arithmeticEpsilon ≤ ratio*arithmeticEpsilon*(1/100000) := by
    have h := mul_le_mul_of_nonneg_right hratio F64ArithmeticBounds.epsilon_pos.le
    nlinarith only [h]
  have hratioSmall : ratio*arithmeticEpsilon ≤ 1/2 := by
    nlinarith [F64ArithmeticBounds.epsilon_pos]
  have hp : 0 < value a := by
    have hh := (abs_le.mp herr).1
    have hu := mul_le_mul_of_nonneg_right hratioSmall (by norm_num : (0:ℝ) ≤ 1/100000)
    linarith only [hh, hv, hu, hbudget]
  have hrelative : |value a - (exactVariance + 1/100000)| ≤
      (ratio*arithmeticEpsilon) * (exactVariance + 1/100000) := by
    apply herr.trans
    calc
      _ ≤ (ratio*arithmeticEpsilon) * (1/100000) := hbudget
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hv])
        (mul_nonneg hr0 F64ArithmeticBounds.epsilon_pos.le)
  have hs := F64SqrtComposition.input_error a
    (F64Order.positiveBits_of_finite_value_pos a ha.1 hp)
    (exactVariance+1/100000) (ratio*arithmeticEpsilon)
    (by linarith only [hv]) (by linarith only [hratioSmall]) hrelative
  have hd := F64Order.positiveBits_spec _ hs.1
  have he' : |value (Wasm.IEEE64.sqrt a)-r| ≤ (ratio+1)*arithmeticEpsilon*r :=
    hs.2.trans_eq (by dsimp [r]; ring)
  refine ⟨hd.1, hd.2, ?_, he'⟩
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hh := (abs_le.mp he').1
  have hu := mul_le_mul_of_nonneg_right hsmall hr
  linarith only [hh, hu]

theorem sqrt_variance_error (v : UInt64) (exactVariance : ℝ)
    (hf : Finite v) (hb : |value v| ≤ 65) (hv : 0 ≤ exactVariance)
    (he : |value v-exactVariance| ≤ 1536*arithmeticEpsilon) :
    let d := Wasm.IEEE64.sqrt (Wasm.IEEE64.add v 0x3EE4F8B588E368F1)
    let r := Real.sqrt (exactVariance+1/100000)
    Finite d ∧ 0 < value d ∧ r/2 ≤ value d ∧
      |value d-r| ≤ 200000001*arithmeticEpsilon*r := by
  convert sqrt_variance_error_bounded v exactVariance 65 1536 200000000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon]) hf hb hv he using 1 <;> norm_num

def centeredWords (x : Fin 4 → UInt64) (i : Fin 4) : UInt64 :=
  Wasm.IEEE64.sub (x i) (average (x 0) (x 1) (x 2) (x 3))

theorem denominator_error_bounded (x : Fin 4 → UInt64) (bound : ℝ)
    (hb : 1 ≤ bound) (hbmax : bound ≤ 16)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ bound) :
    let c := centeredWords x
    let d := denominator (c 0) (c 1) (c 2) (c 3)
    let r := Real.deviation (1/100000) (fun i => value (x i))
    Finite d ∧ 0 < value d ∧ r/2 ≤ value d ∧
      |value d-r| ≤ (10000000*bound^2+1000001)*arithmeticEpsilon*r := by
  let c := centeredWords x
  let r := Real.centered (fun i => value (x i))
  have hc (i : Fin 4) := centered_error_bounded x bound hb (by linarith) hf hx i
  have br (i : Fin 4) : |r i| ≤ 2*bound :=
    (abs_sub _ _).trans (by linarith [hx i, mean_magnitude _ bound hx])
  have hv := variance_error_bounded c r bound hb hbmax
    (fun i => (hc i).1) (fun i => (hc i).2.1) br (fun i => (hc i).2.2)
  have hb2 : bound^2 ≤ 256 := by nlinarith
  have h := sqrt_variance_error_bounded _ _ (4*bound^2+1) (94*bound^2+5)
    (10000000*bound^2+1000000) (by nlinarith [sq_nonneg bound]) (by nlinarith)
    (by positivity) (by nlinarith [sq_nonneg bound])
    (by norm_num [arithmeticEpsilon]; nlinarith) hv.1 hv.2.1
    (Real.variance_nonneg (fun i => value (x i))) hv.2.2
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans_eq (by dsimp [Real.deviation]; ring)⟩

theorem denominator_error (x : Fin 4 → UInt64)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ 4) :
    let c := centeredWords x
    let d := denominator (c 0) (c 1) (c 2) (c 3)
    let r := Real.deviation (1/100000) (fun i => value (x i))
    Finite d ∧ 0 < value d ∧ r/2 ≤ value d ∧
      |value d-r| ≤ 200000001*arithmeticEpsilon*r := by
  let c := centeredWords x
  let r := Real.centered (fun i => value (x i))
  have hc (i : Fin 4) := centered_error x hf hx i
  have br (i : Fin 4) : |r i| ≤ 8 :=
    (abs_sub _ _).trans (by linarith [hx i, mean_magnitude _ 4 hx])
  have hv := variance_error c r (fun i => (hc i).1) (fun i => (hc i).2.1) br
    (fun i => (hc i).2.2)
  exact sqrt_variance_error _ _ hv.1 hv.2.1
    (Real.variance_nonneg (fun i => value (x i))) hv.2.2

#print axioms epsilon_bounds
#print axioms sqrt_variance_error
#print axioms denominator_error
end Project.LayerNorm
