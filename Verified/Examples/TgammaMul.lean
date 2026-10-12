import Verified.Examples.TgammaDD

/-!
`Tgamma.mulDD`, the product of two double-doubles: `a = ch xh` rounded, and the low part
`(ch xl + cl xh) + fma ch xh (-a)`.  It approximates `(xh + xl)(ch + cl)` within the dropped term
`|cl xl|` plus the roundings of the low part (`mulDD_spec`), for bounds `H` on `|ch xh|`, `P1` on
`|ch xl|`, `P2` on `|cl xh|`, and `L2` on `|cl xl|`.
-/

namespace Verified.Examples.TgammaMul
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD

set_option exponentiation.threshold 4096

/-- **`mulDD xh xl ch cl`** approximates `(xh + xl)(ch + cl)`. -/
theorem mulDD_spec (hF : FmaSpec.FmaNearest) (xh xl ch cl : Float) (hxh : Finite xh.toBits)
    (hxl : Finite xl.toBits) (hch : Finite ch.toBits) (hcl : Finite cl.toBits) (H P1 P2 L2 : ℝ)
    (hH : |value ch.toBits| * |value xh.toBits| ≤ H)
    (hP1 : |value ch.toBits| * |value xl.toBits| ≤ P1)
    (hP2 : |value cl.toBits| * |value xh.toBits| ≤ P2)
    (hL2 : |value cl.toBits| * |value xl.toBits| ≤ L2)
    (hHmax : H ≤ 2 ^ 900) (hPmax : P1 + P2 ≤ 2 ^ 900) :
    Finite (mulDD xh xl ch cl).1.toBits ∧ Finite (mulDD xh xl ch cl).2.toBits ∧
      |value (mulDD xh xl ch cl).1.toBits + value (mulDD xh xl ch cl).2.toBits -
          (value xh.toBits + value xl.toBits) * (value ch.toBits + value cl.toBits)| ≤
        L2 + (4 * (P1 + P2) + H / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1070 ∧
      |value (mulDD xh xl ch cl).2.toBits| ≤ (P1 + P2) * (1 + 1 / 2 ^ 50) + H / 2 ^ 52 + 1 / 2 ^ 1070 ∧
      |value (mulDD xh xl ch cl).1.toBits| ≤ H * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have hP10 : 0 ≤ P1 := le_trans (by positivity) hP1
  have hP20 : 0 ≤ P2 := le_trans (by positivity) hP2
  set vxh := value xh.toBits
  set vxl := value xl.toBits
  set vch := value ch.toBits
  set vcl := value cl.toBits
  have hp1022 : ∀ B : ℝ, B ≤ 2 ^ 900 → B < 2 ^ 1022 := fun B h =>
    lt_of_le_of_lt h (by norm_num)
  -- `a = ch xh`
  have ha0 := fapprox_mul (fapprox_self ch hch) (fapprox_self xh hxh) |vch| |vxh| le_rfl le_rfl H
    (by simpa using hH) (hp1022 H hHmax)
  have ha : FApprox (ch * xh) (vch * vxh) (H / 2 ^ 53 + 1 / 2 ^ 1075) :=
    Approx.mono ha0 (le_of_eq (by ring))
  set va := value (ch * xh).toBits
  have hna := fapprox_neg (fapprox_self (ch * xh) ha.1)
  have hnav : value (-(ch * xh)).toBits = -va := by
    have h0 := abs_nonpos_iff.mp hna.2
    linarith
  have hS : |vch * vxh - va| ≤ H / 2 ^ 53 + 1 / 2 ^ 1075 := by
    rw [abs_sub_comm]; exact ha.2
  have hSb : |vch * vxh + value (-(ch * xh)).toBits| ≤ 2 ^ 1000 := by
    rw [hnav, ← sub_eq_add_neg]
    have : H / 2 ^ 53 ≤ 2 ^ 900 := (div_le_self hH0 (by norm_num)).trans hHmax
    linarith [(by norm_num : (2 : ℝ) ^ 900 + 1 / 2 ^ 1075 ≤ 2 ^ 1000)]
  have hf := fma_approx hF ch xh (-(ch * xh)) hch hxh hna.1 hSb
  rw [hnav, ← sub_eq_add_neg] at hf
  have hf' : FApprox (Fma.fma ch xh (-(ch * xh))) (vch * vxh - va)
      ((H / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 + 1 / 2 ^ 1075) :=
    Approx.mono hf (by gcongr)
  -- `u1 = ch xl`, `u2 = cl xh`
  have hu1 : FApprox (ch * xl) (vch * vxl) (P1 / 2 ^ 53 + 1 / 2 ^ 1075) :=
    Approx.mono (fapprox_mul (fapprox_self ch hch) (fapprox_self xl hxl) |vch| |vxl| le_rfl le_rfl
      P1 (by simpa using hP1) (hp1022 P1 (by linarith))) (le_of_eq (by ring))
  have hu2 : FApprox (cl * xh) (vcl * vxh) (P2 / 2 ^ 53 + 1 / 2 ^ 1075) :=
    Approx.mono (fapprox_mul (fapprox_self cl hcl) (fapprox_self xh hxh) |vcl| |vxh| le_rfl le_rfl
      P2 (by simpa using hP2) (hp1022 P2 (by linarith))) (le_of_eq (by ring))
  have hab1 : |vch * vxl| ≤ P1 := by rw [abs_mul]; exact hP1
  have hab2 : |vcl * vxh| ≤ P2 := by rw [abs_mul]; exact hP2
  set B1 := (P1 + P2) * (1 + 1 / 2 ^ 52) + 1 / 2 ^ 1073 with hB1
  have hu := fapprox_add hu1 hu2 B1 (by
      rw [hB1]
      have := abs_add_le (vch * vxl) (vcl * vxh)
      have : (P1 + P2) * (1 / 2 ^ 52) = P1 / 2 ^ 53 + P2 / 2 ^ 53 + (P1 + P2) / 2 ^ 53 := by ring
      nlinarith)
    (by rw [hB1]; nlinarith [(by norm_num : (2 : ℝ) ^ 900 * (1 + 1 / 2 ^ 52) + 1 < 2 ^ 1023)])
  set B2 := (P1 + P2) * (1 + 1 / 2 ^ 51) + H / 2 ^ 52 + 1 / 2 ^ 1071 with hB2
  have hlow := fapprox_add hu hf' B2 (by
      rw [hB2]
      have := abs_add_le (vch * vxl + vcl * vxh) (vch * vxh - va)
      have := abs_add_le (vch * vxl) (vcl * vxh)
      rw [hB1]
      have : (P1 + P2) * (1 / 2 ^ 51) ≥ (P1 + P2) * (1 + 1 / 2 ^ 52) / 2 ^ 53 + P1 / 2 ^ 53 + P2 / 2 ^ 53 := by
        nlinarith
      nlinarith)
    (by rw [hB2]; nlinarith [(by norm_num : (2 : ℝ) ^ 900 * (1 + 1 / 2 ^ 51) + 2 ^ 900 + 1 < 2 ^ 1023),
      div_le_self hH0 (by norm_num : (1 : ℝ) ≤ 2 ^ 52)])
  have hdef : mulDD xh xl ch cl = (ch * xh, (ch * xl + cl * xh) + Fma.fma ch xh (-(ch * xh))) := rfl
  rw [hdef]
  have hlowe := hlow.2
  rw [hB1, hB2] at hlowe
  set low := value ((ch * xl + cl * xh) + Fma.fma ch xh (-(ch * xh))).toBits
  refine ⟨ha.1, hlow.1, ?_, ?_, ?_⟩
  · have hL2' : |vcl * vxl| ≤ L2 := by rw [abs_mul]; exact hL2
    rw [show va + low - (vxh + vxl) * (vch + vcl) =
      (low - (vch * vxl + vcl * vxh + (vch * vxh - va))) - vcl * vxl by ring]
    have := abs_sub (low - (vch * vxl + vcl * vxh + (vch * vxh - va))) (vcl * vxl)
    nlinarith
  · have h2 := abs_sub_abs_le_abs_sub low (vch * vxl + vcl * vxh + (vch * vxh - va))
    have h3 := abs_add_le (vch * vxl + vcl * vxh) (vch * vxh - va)
    have h4 := abs_add_le (vch * vxl) (vcl * vxh)
    nlinarith
  · have h := ha.2
    have h2 := abs_sub_abs_le_abs_sub va (vch * vxh)
    have h4 : |vch * vxh| ≤ H := by rw [abs_mul]; exact hH
    nlinarith

#print axioms mulDD_spec

end Verified.Examples.TgammaMul
