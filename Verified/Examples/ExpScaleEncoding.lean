import Verified.Examples.ExpScaleFacts
import LeanExe.ProofKit.F64Packing
import LeanExe.ProofKit.F64Magnitude

namespace Verified.Examples.ExpScaleEncoding
open CodeLib.IEEE64
open LeanExe.ProofKit F64Magnitude

set_option exponentiation.threshold 4096

def encodedScale (j : Fin 128) (q : Int) : UInt64 :=
  Wasm.IEEE64.encodeFinite false (1023 + q).toNat
    (Wasm.IEEE64.fraction (ExpTableBounds.headBits j.val))

theorem encoded_scale_value (j : Fin 128) (q : Int) (hqlo : -1000 ≤ q) (hqhi : q ≤ 999) :
    Finite (encodedScale j q) ∧
      value (encodedScale j q) = (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val) ∧
      1 / (2 : ℝ) ^ 1000 ≤ value (encodedScale j q) ∧
      value (encodedScale j q) ≤ (2 : ℝ) ^ 1000 := by
  let e := (1023 + q).toNat
  let f := Wasm.IEEE64.fraction (ExpTableBounds.headBits j.val)
  have he0 : 0 < e := by dsimp [e]; omega
  have he : e < 2047 := by dsimp [e]; omega
  have hf : f < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hs := sign_encodeFinite false e f (by omega) hf
  have hex := exponent_encodeFinite false e f (by omega) hf
  have hfr := fraction_encodeFinite false e f (by omega) hf
  have hE : ((e - 1 : Nat) : Int) = q + 1022 := by dsimp [e]; omega
  have hp : (2 : ℝ) ^ (e - 1) = (2 : ℝ) ^ q * (2 : ℝ) ^ 1022 := by
    calc
      _ = (2 : ℝ) ^ ((e - 1 : Nat) : Int) := (zpow_natCast _ _).symm
      _ = (2 : ℝ) ^ q * (2 : ℝ) ^ ((1022 : Nat) : Int) := by
        rw [hE, zpow_add₀ (by norm_num)]
        simp only [Nat.cast_ofNat]
      _ = _ := by rw [zpow_natCast]
  obtain ⟨hhs, hhe, _⟩ := ExpScaleFacts.checked_head_fields j
  have hval : value (encodedScale j q) =
      (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val) := by
    change value (Wasm.IEEE64.encodeFinite false e f) = _
    rw [normal_value _ hs (by rw [hex]; exact he0), hex, hfr,
      normal_value _ hhs (by rw [hhe]; norm_num), hhe, hp]
    norm_num only [Nat.reduceSub]
    dsimp [f]
    ring
  have hP : 0 < (2 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hplo : 1 / (2 : ℝ) ^ 1000 ≤ (2 : ℝ) ^ q := by
    have h : (2 : ℝ) ^ (-((1000 : Nat) : Int)) ≤ (2 : ℝ) ^ q :=
      zpow_le_zpow_right₀ (by norm_num) hqlo
    simpa only [zpow_neg, zpow_natCast, inv_eq_one_div] using h
  have hphi : (2 : ℝ) ^ q ≤ (2 : ℝ) ^ 999 := by
    have h : (2 : ℝ) ^ q ≤ (2 : ℝ) ^ ((999 : Nat) : Int) :=
      zpow_le_zpow_right₀ (by norm_num) hqhi
    simpa only [zpow_natCast] using h
  have hb := ExpTableBounds.entry_bounds j
  refine ⟨finite_encodeFinite false e f he hf, hval, ?_, ?_⟩
  · rw [hval]
    exact hplo.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2.2.1 hP.le)
  · rw [hval]
    calc
      _ ≤ (2 : ℝ) ^ q * 2 := mul_le_mul_of_nonneg_left hb.2.2.2.1 hP.le
      _ ≤ (2 : ℝ) ^ 999 * 2 := mul_le_mul_of_nonneg_right hphi (by norm_num)
      _ = (2 : ℝ) ^ 1000 := (pow_succ (2 : ℝ) 999).symm

#print axioms encoded_scale_value

end Verified.Examples.ExpScaleEncoding
