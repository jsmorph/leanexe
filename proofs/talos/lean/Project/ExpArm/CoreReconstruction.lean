import Project.ExpArm.RealScale
import Project.ProofKit.F64NearBinade
import Project.ProofKit.F64MulBounds

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

def normalReconstruction (scale correction : UInt64) : UInt64 :=
  Wasm.IEEE64.add scale (Wasm.IEEE64.mul scale correction)

theorem core_reconstruction_error (scale correction : UInt64)
    (hs : Finite scale) (ht : Finite correction) (e : Nat) (hel : 55 ≤ e) (heu : e ≤ 2000)
    (y : ℝ) (hsl : (2 : ℝ)^e/2^1074 ≤ value scale)
    (hsu : value scale ≤ (199/100)*((2 : ℝ)^e/2^1074))
    (hc : |value correction| ≤ 4/1000)
    (he : |value scale*(1+value correction)-y| ≤
      (3/100000000000000000)*((2 : ℝ)^e/2^1074)) :
    Finite (normalReconstruction scale correction) ∧
    ((2 : ℝ)^e/2^1074)/2 ≤ y ∧ y < 2*((2 : ℝ)^e/2^1074) ∧
    |value (normalReconstruction scale correction)-y| <
      if y < (2 : ℝ)^e/2^1074 then ((2 : ℝ)^e/2^1074)/2^53
      else ((2 : ℝ)^e/2^1074)/2^52 := by
  let f := (2 : ℝ)^e/2^1074
  change f ≤ value scale at hsl
  change value scale ≤ (199/100)*f at hsu
  change |value scale*(1+value correction)-y| ≤ (3/100000000000000000)*f at he
  have hf : 0 < f := by dsimp [f]; positivity
  have hsp : 0 < value scale := hf.trans_le hsl
  have hfl : (2 : ℝ)^55/2^1074 ≤ f :=
    div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hel) (by positivity)
  have hfu : f ≤ (2 : ℝ)^926 := by
    calc
      _ ≤ (2 : ℝ)^2000/2^1074 :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) heu) (by positivity)
      _ = _ := by norm_num
  have hunder : multiplicationUnderflowEpsilon ≤ f/2^56 := by
    calc
      _ = ((2 : ℝ)^55/2^1074)/2^56 := by norm_num [multiplicationUnderflowEpsilon]
      _ ≤ _ := div_le_div_of_nonneg_right hfl (by positivity)
  have hp : |value scale*value correction| ≤ (8/1000)*f := by
    rw [abs_mul, abs_of_pos hsp]
    have h := mul_le_mul hsu hc (abs_nonneg _) (by positivity : 0 ≤ (199/100)*f)
    nlinarith only [h, hf]
  have hm := F64MulBounds.mul_real_mixed scale correction hs ht (by
    calc
      _ ≤ (8/1000)*f := hp
      _ ≤ (8/1000)*(2 : ℝ)^926 := mul_le_mul_of_nonneg_left hfu (by norm_num)
      _ < _ := by norm_num)
  have hme : |value (Wasm.IEEE64.mul scale correction)-value scale*value correction| ≤
      unitRoundoff64*((8/1000)*f)+f/2^56 :=
    hm.2.trans (add_le_add
      (mul_le_mul_of_nonneg_left hp (by norm_num [unitRoundoff64])) hunder)
  have hsum : |value scale+value (Wasm.IEEE64.mul scale correction)-y| < f/2^54 := by
    have hid : value scale+value (Wasm.IEEE64.mul scale correction)-y =
        (value (Wasm.IEEE64.mul scale correction)-value scale*value correction) +
        (value scale*(1+value correction)-y) := by ring
    rw [hid]
    have h := (abs_add_le _ _).trans (add_le_add hme he)
    norm_num [unitRoundoff64] at h ⊢
    linarith
  have hcl := (abs_le.mp hc).1
  have hcu := (abs_le.mp hc).2
  have hlo : (996/1000)*f ≤ value scale*(1+value correction) := by
    have h : (996/1000)*f ≤ f*(1+value correction) := by nlinarith
    exact h.trans (mul_le_mul_of_nonneg_right hsl (by linarith))
  have hhi : value scale*(1+value correction) ≤ (199/100)*(1004/1000)*f := by
    have h := mul_le_mul hsu (show 1+value correction ≤ 1004/1000 by linarith)
      (show 0 ≤ 1+value correction by linarith) (show 0 ≤ (199/100)*f by positivity)
    nlinarith only [h]
  have hyl : f/2 ≤ y := by
    have h := (abs_le.mp he).2
    linarith
  have hyu : y ≤ (1999/1000)*f := by
    have h := (abs_le.mp he).1
    linarith
  have h := F64NearBinade.add_error scale _ hs hm.1 e (by omega) (by omega) y hyl hyu hsum
  exact ⟨h.1, hyl, by change y < 2*f; linarith, h.2⟩

#print axioms core_reconstruction_error
end Project.ExpArm
