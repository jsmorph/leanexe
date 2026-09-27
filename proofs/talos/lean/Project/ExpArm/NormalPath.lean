import Project.ExpArm.CoreReconstruction
import Project.ExpArm.ReductionError

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit.F64Rational

set_option exponentiation.threshold 4096

def normalPath (x : UInt64) : UInt64 :=
  let word := reductionWord x
  let i := (word &&& 127).toNat
  normalReconstruction (table[2*i+1]! + (word <<< 45))
    (correctionWord (reducedWord x) table[2*i]!)

set_option maxRecDepth 4096 in
theorem table_upper_rational : ∀ i : Fin 128, decode (tableScaleWord i) ≤ 199/100 := by
  decide +kernel

theorem table_upper (i : Nat) (hi : i < 128) : value (tableScaleWord i) ≤ 199/100 := by
  have h := (Rat.cast_le (K := ℝ)).mpr (table_upper_rational ⟨i, hi⟩)
  simpa only [decode_cast, Rat.cast_div, Rat.cast_ofNat] using h

theorem scaleFactor_scaled (m : Int) (hm : 0 ≤ 1023+m) :
    scaleFactor m = (2 : ℝ)^(1074+m).toNat/2^1074 := by
  have he : (1074+m).toNat = 51+(1023+m).toNat := by omega
  rw [he, pow_add, scaleFactor]
  ring

theorem normal_path_error (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 512) :
    let f := scaleFactor (reductionInteger x/128)
    Finite (normalPath x) ∧ f/2 ≤ Real.exp (value x) ∧ Real.exp (value x) < 2*f ∧
    |value (normalPath x)-Real.exp (value x)| <
      if Real.exp (value x) < f then f/2^53 else f/2^52 := by
  let word := reductionWord x
  let i := (word &&& 127).toNat
  let scale := table[2*i+1]! + (word <<< 45)
  let correction := correctionWord (reducedWord x) table[2*i]!
  let m := reductionInteger x/128
  let f := scaleFactor m
  let e := (1074+m).toNat
  have hk : |reductionInteger x| ≤ (94721 : Int) := by
    have h := reductionInteger_abs x hf (hx.trans (by norm_num))
    have h' : |(reductionInteger x : ℝ)| ≤ 94721 := by linarith
    exact_mod_cast h'
  have hm : -741 ≤ m ∧ m ≤ 740 := by
    have h := abs_le.mp hk
    dsimp [m]
    omega
  have hb : 1 ≤ 1023+shiftInteger word/128 ∧ 1023+shiftInteger word/128 < 2047 := by
    change 1 ≤ 1023+m ∧ 1023+m < 2047
    omega
  have he : 55 ≤ e ∧ e ≤ 2000 := by dsimp [e]; omega
  have hfe : f = (2 : ℝ)^e/2^1074 := scaleFactor_scaled m (by omega)
  have hfp := scaleFactor_pos m
  have hi : i < 128 := by
    have h : (word &&& 127).toNat ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
    dsimp [i]
    omega
  have hs := unadjusted_scale_value word hb
  have hv : value scale = value (tableScaleWord i)*f := by
    change value scale = value (tableScaleWord i)*((2 : ℝ)^(1023+m).toNat/2^1023)
    rw [← mul_div_assoc]
    exact (eq_div_iff (by positivity)).mpr hs.2.2
  have htable := table_real_bounds i hi
  have hsl : f ≤ value scale := by
    rw [hv]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htable.2.2.1 hfp.le
  have hsu : value scale ≤ (199/100)*f := by
    rw [hv]
    exact mul_le_mul_of_nonneg_right (table_upper i hi) hfp.le
  have hr := reduction_error x hf (hx.trans (by norm_num))
  have hc := correction_rounding (reducedWord x) table[2*i]! hr.1 htable.2.1 hr.2.2 htable.2.2.2.2
  have hideal : |value x-(shiftInteger word : ℝ)*(Real.log 2/128)| ≤ 3/1000 :=
    (ideal_reduction_bound x hf (hx.trans (by norm_num))).trans (by norm_num)
  have herr := scaled_correction_error (value x) word (reducedWord x) scale 0
    (by change 0 ≤ 1023+(m+0); omega)
    (by simpa only [add_zero] using hs.2.2) hr.1 hr.2.2 hideal hr.2.1
  simp only [add_zero, Int.cast_zero, zero_mul] at herr
  have h := core_reconstruction_error scale correction hs.1 hc.finite e he.1 he.2
    (Real.exp (value x)) (by rw [← hfe]; exact hsl) (by rw [← hfe]; exact hsu)
    hc.magnitude (by rw [← hfe]; exact herr)
  rw [← hfe] at h
  exact h

#print axioms normal_path_error
end Project.ExpArm
