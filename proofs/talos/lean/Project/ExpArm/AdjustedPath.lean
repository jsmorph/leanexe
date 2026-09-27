import Project.ExpArm.NormalPath
import Project.ExpArm.AdjustedScale

namespace Project.ExpArm
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

def adjustedPath (x scale : UInt64) : UInt64 :=
  normalReconstruction scale
    (correctionWord (reducedWord x) table[2*(reductionWord x &&& 127).toNat]!)

theorem adjusted_path_error (x scale : UInt64) (hf : Finite x) (hx : |value x| ≤ 800)
    (c : Int) (hm : -1019 ≤ reductionInteger x/128+c ∧ reductionInteger x/128+c ≤ 926)
    (hsf : Finite scale)
    (hs : value scale * (2 : ℝ)^1023 =
      value (tableScaleWord (reductionWord x &&& 127).toNat) *
        (2 : ℝ)^(1023+(reductionInteger x/128+c)).toNat) :
    let f := scaleFactor (reductionInteger x/128+c)
    let y := Real.exp (value x+(c : ℝ)*Real.log 2)
    Finite (adjustedPath x scale) ∧ f/2 ≤ y ∧ y < 2*f ∧
    |value (adjustedPath x scale)-y| < if y < f then f/2^53 else f/2^52 := by
  let word := reductionWord x
  let i := (word &&& 127).toNat
  let correction := correctionWord (reducedWord x) table[2*i]!
  let m := reductionInteger x/128+c
  let f := scaleFactor m
  let e := (1074+m).toNat
  have he : 55 ≤ e ∧ e ≤ 2000 := by dsimp [e, m]; omega
  have hfe : f = (2 : ℝ)^e/2^1074 := scaleFactor_scaled m (by dsimp [m]; omega)
  have hfp := scaleFactor_pos m
  have hi : i < 128 := by
    have h : (word &&& 127).toNat ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
    dsimp [i]
    omega
  have hv : value scale = value (tableScaleWord i)*f := by
    change value scale = value (tableScaleWord i)*((2 : ℝ)^(1023+m).toNat/2^1023)
    rw [← mul_div_assoc]
    exact (eq_div_iff (by positivity)).mpr hs
  have ht := table_real_bounds i hi
  have hsl : f ≤ value scale := by
    rw [hv]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2.2.1 hfp.le
  have hsu : value scale ≤ (199/100)*f := by
    rw [hv]
    exact mul_le_mul_of_nonneg_right (table_upper i hi) hfp.le
  have hr := reduction_error x hf hx
  have hc := correction_rounding (reducedWord x) table[2*i]! hr.1 ht.2.1 hr.2.2 ht.2.2.2.2
  have hideal : |value x-(shiftInteger word : ℝ)*(Real.log 2/128)| ≤ 3/1000 :=
    (ideal_reduction_bound x hf (hx.trans (by norm_num))).trans (by norm_num)
  have herr := scaled_correction_error (value x) word (reducedWord x) scale c
    (by change 0 ≤ 1023+m; dsimp [m]; omega) hs hr.1 hr.2.2 hideal hr.2.1
  have h := core_reconstruction_error scale correction hsf hc.finite e he.1 he.2
    (Real.exp (value x+(c : ℝ)*Real.log 2))
    (by rw [← hfe]; exact hsl) (by rw [← hfe]; exact hsu)
    hc.magnitude (by rw [← hfe]; exact herr)
  rw [← hfe] at h
  exact h

theorem positive_reduction_bounds (x : UInt64) (hf : Finite x)
    (hx : 512 ≤ value x ∧ value x ≤ 800) :
    735 ≤ reductionInteger x/128 ∧ reductionInteger x/128 ≤ 1156 := by
  have habs : |value x| ≤ 1024 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := abs_le.mp (integer_selection x hf habs).2.2.2.2
  have hi := inverse_log_bounds
  have hl : (94080 : ℝ) ≤ (reductionInteger x : ℝ) := by nlinarith
  have hu : (reductionInteger x : ℝ) ≤ 148001 := by nlinarith
  have hl' : (94080 : Int) ≤ reductionInteger x := by exact_mod_cast hl
  have hu' : reductionInteger x ≤ (148001 : Int) := by exact_mod_cast hu
  omega

theorem negative_reduction_bounds (x : UInt64) (hf : Finite x)
    (hx : -800 ≤ value x ∧ value x ≤ -512) :
    -1157 ≤ reductionInteger x/128 ∧ reductionInteger x/128 ≤ -736 := by
  have habs : |value x| ≤ 1024 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := abs_le.mp (integer_selection x hf habs).2.2.2.2
  have hi := inverse_log_bounds
  have hl : (-148001 : ℝ) ≤ (reductionInteger x : ℝ) := by nlinarith
  have hu : (reductionInteger x : ℝ) ≤ -94081 := by nlinarith
  have hl' : (-148001 : Int) ≤ reductionInteger x := by exact_mod_cast hl
  have hu' : reductionInteger x ≤ (-94081 : Int) := by exact_mod_cast hu
  omega

#print axioms adjusted_path_error
#print axioms positive_reduction_bounds
#print axioms negative_reduction_bounds
end Project.ExpArm
