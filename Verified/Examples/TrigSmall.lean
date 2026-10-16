import Verified.Examples.Trig
import Verified.Examples.TrigPi
import LeanExe.ProofKit.F64ValueExact
import LeanExe.ProofKit.F64Bits
import Mathlib.Analysis.Real.Pi.Bounds

/-!
The accuracy of `Trig.remSmall`, fdlibm's one-step reduction `x - k π/2` for `k` from 1 to 4.  The
product `k · pio2_1` is exact, `z = x - k · pio2_1` is exact, and `y0 + y1` equals
`z - fl(k · pio2_1t)` exactly.  For `|x - k π/2|` from `2 ^ -22` to `π/4 + 2 ^ -17`, the result lies
within `2 ^ -60` relative of `x - k π/2`.
-/

namespace Verified.Examples.TrigSmall

open CodeLib.IEEE64 LeanExe.ProofKit F64ValueExact TrigPi

set_option exponentiation.threshold 4096

/-- The first 33 bits of `π/2`. -/
def pio2_1 : UInt64 := 0x3FF921FB54400000

/-- `π/2 - pio2_1`, rounded. -/
def pio2_1t : UInt64 := 0x3DD0B4611A626331

theorem pio2_checked :
    (Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_1t : ℚ) / 2 ^ 1074 ≤
        (piApprox - piError) / 2 + 1 / 2 ^ 86 ∧
      (piApprox + piError) / 2 - 1 / 2 ^ 86 ≤
        (Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_1t : ℚ) / 2 ^ 1074 := by
  decide +kernel

/-- `pio2_1 + pio2_1t` lies within `2 ^ -86` of `π/2`. -/
theorem pio2_close : |value pio2_1 + value pio2_1t - Real.pi / 2| ≤ 1 / 2 ^ 86 := by
  obtain ⟨h1, h2⟩ := pio2_checked
  have hl := pi_lower
  have hu := pi_upper
  have h1' : ((Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_1t : ℚ) / 2 ^ 1074 : ℝ) ≤
      (((piApprox - piError) / 2 + 1 / 2 ^ 86 : ℚ) : ℝ) := by exact_mod_cast h1
  have h2' : (((piApprox + piError) / 2 - 1 / 2 ^ 86 : ℚ) : ℝ) ≤
      ((Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_1t : ℚ) / 2 ^ 1074 : ℝ) := by
    exact_mod_cast h2
  have hv : value pio2_1 + value pio2_1t =
      ((Wasm.IEEE64.scaledValue pio2_1 + Wasm.IEEE64.scaledValue pio2_1t : ℚ) / 2 ^ 1074 : ℝ) := by
    simp only [value]
    push_cast
    ring
  rw [hv, abs_le]
  push_cast at h1' h2' hl hu ⊢
  constructor <;> linarith

/-- The constants of one branch of `remSmall`: the word `kb` of `k`, `C = k · pio2_1`, exact,
and `W = k · pio2_1t`, rounded. -/
structure SmallConst (K : Nat) (kb C W : UInt64) : Prop where
  hC : Wasm.IEEE64.mul kb pio2_1 = C
  hW : Wasm.IEEE64.mul kb pio2_1t = W
  Cf : Finite C
  Wf : Finite W
  Cv : Wasm.IEEE64.scaledValue C = K * Wasm.IEEE64.scaledValue pio2_1
  Wv : |Wasm.IEEE64.scaledValue W - K * Wasm.IEEE64.scaledValue pio2_1t| ≤ 2 ^ 988
  Cd : (2 : Int) ^ 1042 ∣ Wasm.IEEE64.scaledValue C
  Wd : (2 : Int) ^ 988 ∣ Wasm.IEEE64.scaledValue W
  Wlo : (2 : Int) ^ 1040 ≤ Wasm.IEEE64.scaledValue W
  Whi : Wasm.IEEE64.scaledValue W ≤ 2 ^ 1043

theorem const1 : SmallConst 1 0x3FF0000000000000 0x3FF921FB54400000 0x3DD0B4611A626331 := by
  constructor <;> (try unfold CodeLib.IEEE64.Finite) <;> decide +kernel

theorem const2 : SmallConst 2 0x4000000000000000 0x400921FB54400000 0x3DE0B4611A626331 := by
  constructor <;> (try unfold CodeLib.IEEE64.Finite) <;> decide +kernel

theorem const3 : SmallConst 3 0x4008000000000000 0x4012D97C7F300000 0x3DE90E91A79394CA := by
  constructor <;> (try unfold CodeLib.IEEE64.Finite) <;> decide +kernel

theorem const4 : SmallConst 4 0x4010000000000000 0x401921FB54400000 0x3DF0B4611A626331 := by
  constructor <;> (try unfold CodeLib.IEEE64.Finite) <;> decide +kernel

theorem pio2_1t_bounds : (2 : Int) ^ 1040 ≤ Wasm.IEEE64.scaledValue pio2_1t ∧
    Wasm.IEEE64.scaledValue pio2_1t ≤ 2 ^ 1041 := by
  decide +kernel

/-- `remSmall` on words. -/
def remSmallW (x kb : UInt64) : UInt64 × UInt64 :=
  let z := Wasm.IEEE64.sub x (Wasm.IEEE64.mul kb pio2_1)
  let y0 := Wasm.IEEE64.sub z (Wasm.IEEE64.mul kb pio2_1t)
  (y0, Wasm.IEEE64.sub (Wasm.IEEE64.sub z y0) (Wasm.IEEE64.mul kb pio2_1t))

theorem remSmall_bits (x k : Float) :
    (Trig.remSmall x k).1.toBits = (remSmallW x.toBits k.toBits).1 ∧
      (Trig.remSmall x k).2.toBits = (remSmallW x.toBits k.toBits).2 := by
  have h1 : (Float.ofBits 0x3FF921FB54400000).toBits = pio2_1 := by
    rw [F64Bits.toBits_ofBits]
    decide
  have h2 : (Float.ofBits 0x3DD0B4611A626331).toBits = pio2_1t := by
    rw [F64Bits.toBits_ofBits]
    decide
  simp only [Trig.remSmall, remSmallW, F64Bits.toBits_sub, F64Bits.toBits_mul, h1, h2]
  exact ⟨trivial, trivial⟩

theorem value_of_scaled (w : UInt64) : value w = (Wasm.IEEE64.scaledValue w : ℝ) / 2 ^ 1074 := rfl

/-- The accuracy of `remSmall` on words. -/
theorem remSmallW_spec (x kb C W : UInt64) (K : Nat) (hc : SmallConst K kb C W) (hK1 : 1 ≤ K)
    (hK4 : K ≤ 4) (hxf : Finite x) (hx : 1 / 2 ≤ |value x|)
    (hr1 : 1 / 2 ^ 22 ≤ |value x - K * (Real.pi / 2)|)
    (hr2 : |value x - K * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 17) :
    Finite (remSmallW x kb).1 ∧ Finite (remSmallW x kb).2 ∧
      |value (remSmallW x kb).1 + value (remSmallW x kb).2 - (value x - K * (Real.pi / 2))| ≤
        |value x - K * (Real.pi / 2)| / 2 ^ 60 ∧
      |value (remSmallW x kb).2| ≤ |value (remSmallW x kb).1| / 2 ^ 52 := by
  unfold remSmallW
  rw [hc.hC, hc.hW]
  dsimp only
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK4r : (K : ℝ) ≤ 4 := by exact_mod_cast hK4
  -- The constants as values.
  have hCv : value C = K * value pio2_1 := by
    rw [value_of_scaled, value_of_scaled, hc.Cv]
    push_cast
    ring
  have hWv : |value W - K * value pio2_1t| ≤ 1 / 2 ^ 86 := by
    have h : |(Wasm.IEEE64.scaledValue W : ℝ) - K * Wasm.IEEE64.scaledValue pio2_1t| ≤ 2 ^ 988 := by
      exact_mod_cast hc.Wv
    rw [value_of_scaled, value_of_scaled, ← mul_div_assoc, ← sub_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), div_le_iff₀ (by positivity)]
    calc _ ≤ (2 : ℝ) ^ 988 := h
      _ = 1 / 2 ^ 86 * 2 ^ 1074 := by norm_num
  have hWlo : 1 / 2 ^ 34 ≤ value W := by
    rw [value_of_scaled, le_div_iff₀ (by positivity)]
    have : ((2 : Int) ^ 1040 : ℝ) ≤ (Wasm.IEEE64.scaledValue W : ℝ) := by exact_mod_cast hc.Wlo
    calc (1 : ℝ) / 2 ^ 34 * 2 ^ 1074 = 2 ^ 1040 := by norm_num
      _ ≤ _ := by exact_mod_cast this
  have hWhi : value W ≤ 1 / 2 ^ 31 := by
    rw [value_of_scaled, div_le_iff₀ (by positivity)]
    have : (Wasm.IEEE64.scaledValue W : ℝ) ≤ ((2 : Int) ^ 1043 : ℝ) := by exact_mod_cast hc.Whi
    calc (Wasm.IEEE64.scaledValue W : ℝ) ≤ 2 ^ 1043 := by exact_mod_cast this
      _ = 1 / 2 ^ 31 * 2 ^ 1074 := by norm_num
  have ht : value pio2_1t ≤ 1 / 2 ^ 33 := by
    rw [value_of_scaled, div_le_iff₀ (by positivity)]
    have : (Wasm.IEEE64.scaledValue pio2_1t : ℝ) ≤ ((2 : Int) ^ 1041 : ℝ) := by
      exact_mod_cast pio2_1t_bounds.2
    calc (Wasm.IEEE64.scaledValue pio2_1t : ℝ) ≤ 2 ^ 1041 := by exact_mod_cast this
      _ = 1 / 2 ^ 33 * 2 ^ 1074 := by norm_num
  have ht0 : 0 ≤ value pio2_1t := by
    rw [value_of_scaled]
    have : ((2 : Int) ^ 1040 : ℝ) ≤ (Wasm.IEEE64.scaledValue pio2_1t : ℝ) := by
      exact_mod_cast pio2_1t_bounds.1
    have h0 : (0 : ℝ) ≤ (2 : Int) ^ 1040 := by positivity
    exact div_nonneg (by push_cast at this h0 ⊢; linarith) (by positivity)
  have hp := pio2_close
  rw [abs_le] at hp hWv
  set r := value x - K * (Real.pi / 2) with hr
  -- `z = x - C` is exact.
  have hdx : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue x :=
    dvd_of_value x hxf 1021 (by norm_num; linarith)
  have hdC : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue C :=
    dvd_trans (pow_dvd_pow 2 (by norm_num)) hc.Cd
  have hzr : |value x - value C - r| ≤ 1 / 2 ^ 30 := by
    rw [hCv, hr, abs_le]
    constructor <;> nlinarith
  obtain ⟨hzf, hzv⟩ := sub_exact x C hxf hc.Cf 1021 (by norm_num) hdx hdC (by
    rw [abs_le] at hr2 hzr ⊢
    norm_num
    constructor <;> linarith)
  generalize Wasm.IEEE64.sub x C = z at hzf hzv ⊢
  -- The rounded difference `y0`.
  have hD : |value z - value W - r| ≤ 1 / 2 ^ 83 := by
    rw [hzv, hCv, hr, abs_le]
    constructor <;> nlinarith
  have hDlo : 1 / 2 ^ 22 - 1 / 2 ^ 83 ≤ |value z - value W| := by
    have h := abs_add_le (value z - value W) (r - (value z - value W))
    rw [show value z - value W + (r - (value z - value W)) = r by ring,
      abs_sub_comm r (value z - value W)] at h
    linarith
  have hDhi : |value z - value W| ≤ 4 / 5 := by
    have h := abs_add_le r (value z - value W - r)
    rw [show r + (value z - value W - r) = value z - value W by ring] at h
    have hr' : |r| ≤ Real.pi / 4 + 1 / 2 ^ 17 := hr2
    have : Real.pi / 4 + 1 / 2 ^ 17 + 1 / 2 ^ 83 ≤ (4 : ℝ) / 5 := by nlinarith
    linarith
  obtain ⟨hyf, hye⟩ := sub_rel z W hzf hc.Wf (by linarith)
  generalize Wasm.IEEE64.sub z W = y0 at hyf hye ⊢
  -- `z - y0` is exact on the grid of `2 ^ -76`.
  have hzlo : 1 / 2 ^ 24 ≤ |value z| := by
    have h := abs_add_le (value z) (-value W)
    rw [show value z + -value W = value z - value W by ring, abs_neg,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ value W)] at h
    have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 2 ^ 22 - 1 / 2 ^ 83 - 1 / 2 ^ 31 := by norm_num
    linarith
  have hq53 : |value z - value W| / 2 ^ 53 ≤ 4 / 5 / 2 ^ 53 :=
    div_le_div_of_nonneg_right hDhi (by positivity)
  have hylo : 1 / 2 ^ 24 ≤ |value y0| := by
    have h := abs_add_le (value y0) (value z - value W - value y0)
    rw [show value y0 + (value z - value W - value y0) = value z - value W by ring,
      abs_sub_comm (value z - value W) (value y0)] at h
    have : (1 : ℝ) / 2 ^ 24 ≤ (1 / 2 ^ 22 - 1 / 2 ^ 83) - 4 / 5 / 2 ^ 53 := by norm_num
    linarith
  have hdz : (2 : Int) ^ 998 ∣ Wasm.IEEE64.scaledValue z :=
    dvd_of_value z hzf 998 (by norm_num; linarith)
  have hdy : (2 : Int) ^ 998 ∣ Wasm.IEEE64.scaledValue y0 :=
    dvd_of_value y0 hyf 998 (by norm_num; linarith)
  obtain ⟨hdf, hdv⟩ := sub_exact z y0 hzf hyf 998 (by norm_num) hdz hdy (by
    have h := abs_add_le (value W) (value z - value W - value y0)
    rw [show value W + (value z - value W - value y0) = value z - value y0 by ring,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ value W),
      abs_sub_comm (value z - value W) (value y0)] at h
    have : (1 : ℝ) / 2 ^ 31 + 4 / 5 / 2 ^ 53 ≤ 2 ^ (53 + 998) / 2 ^ 1074 := by norm_num
    linarith)
  have hsd := scaled_of_value_sub z y0 _ hdv
  generalize Wasm.IEEE64.sub z y0 = d at hdf hdv hsd ⊢
  -- `d - W` is exact on the grid of `2 ^ -86`.
  have hdd : (2 : Int) ^ 988 ∣ Wasm.IEEE64.scaledValue d := by
    rw [hsd]
    exact dvd_sub (dvd_trans (pow_dvd_pow 2 (by norm_num)) hdz)
      (dvd_trans (pow_dvd_pow 2 (by norm_num)) hdy)
  have hdW : value d - value W = -(value y0 - (value z - value W)) := by rw [hdv]; ring
  obtain ⟨hef, hev⟩ := sub_exact d W hdf hc.Wf 988 (by norm_num) hdd hc.Wd (by
    rw [hdW, abs_neg]
    have : (4 : ℝ) / 5 / 2 ^ 53 ≤ 2 ^ (53 + 988) / 2 ^ 1074 := by norm_num
    linarith)
  refine ⟨hyf, hef, ?_, ?_⟩
  · rw [hev, hdv, show value y0 + (value z - value y0 - value W) - r =
      value z - value W - r by ring]
    have : (1 : ℝ) / 2 ^ 83 ≤ 1 / 2 ^ 22 / 2 ^ 60 := by norm_num
    have h2 : 1 / 2 ^ 22 / 2 ^ 60 ≤ |r| / 2 ^ 60 := div_le_div_of_nonneg_right hr1 (by positivity)
    linarith
  · rw [hev, hdW, abs_neg]
    have h := abs_add_le (value y0) (value z - value W - value y0)
    rw [show value y0 + (value z - value W - value y0) = value z - value W by ring,
      abs_sub_comm (value z - value W) (value y0)] at h
    have hn := abs_nonneg (value z - value W)
    have h2 : |value z - value W| / 2 ^ 53 ≤ |value z - value W| / 2 := by
      apply div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
    have h3 : |value z - value W| ≤ 2 * |value y0| := by linarith
    have h4 : |value z - value W| / 2 ^ 53 ≤ 2 * |value y0| / 2 ^ 53 :=
      div_le_div_of_nonneg_right h3 (by positivity)
    have h5 : 2 * |value y0| / 2 ^ 53 = |value y0| / 2 ^ 52 := by ring
    linarith

#print axioms pio2_close
#print axioms const1
#print axioms const2
#print axioms const3
#print axioms const4
#print axioms remSmall_bits
#print axioms remSmallW_spec

end Verified.Examples.TrigSmall
