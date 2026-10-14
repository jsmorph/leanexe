import Verified.Examples.TgammaSinpidPoly
import Verified.Examples.TgammaSinpidParts
import Verified.Examples.TgammaSinpidComb
import Verified.Examples.TgammaSinpidTab

/-!
The code of `Tgamma.asSinpid` after the argument reduction and the table lookups, as `sinTail`,
and its error bound `sinTail_spec`: for the reduced argument `d` with `|d| ≤ 1/2`, table rows
`sh + sl` and `ch + cl` that satisfy the conditions of `TgammaSinpidComb`, and the code's kernel
coefficients, the result lies within `|d|/2^71 + sh/2^100 + 2^-1060` of
`(sh + sl) + d ((ch + cl) Ks (d²) + d Kc (d²) (sh + sl))`, and its low part is at most `2^-50` of
its high part.  The proof composes `TgammaSinpidPoly`, `TgammaSinpidParts`, and
`TgammaSinpidComb`.
-/

namespace Verified.Examples.TgammaSinpidTail
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaSinpidPoly TgammaSinpidParts
  TgammaSinpidComb TgammaSinpidTab

set_option exponentiation.threshold 4096

/-- The code of `asSinpid` after the reduction, for the remainder `d`, the table rows
`(sh, sl)` and `(ch, cl)`, and the coefficients at 130 to 137. -/
def sinTail (d sh sl ch cl c130 c131 c132 c133 c134 c135 c136 c137 : Float) : Float × Float :=
  let d2 := d * d
  let c0 := Float.ofBits 0xBBD692B66E3CF6E8
  let s0 := Float.ofBits 0x3C31A624B88C9448
  let p := d2 * (c131 + d2 * (c132 + d2 * c133))
  let q := d2 * (c135 + d2 * (c136 + d2 * c137))
  let Q := fastTwoSum c134 q
  let C1 := mulDD Q.1 (Q.2 + s0) ch cl
  let T := fastTwoSum c130 p
  let T2 := mulDDD d T.1 (T.2 + c0)
  let P := mulDD T2.1 T2.2 sh sl
  let C2 := fastSum C1.1 C1.2 P.1 P.2
  let C3 := mulDDD d C2.1 C2.2
  fastSum sh sl C3.1 C3.2

theorem lit_bits (w : UInt64) (h : Finite w) : (Float.ofBits w).toBits = w := by
  rw [F64Bits.toBits_ofBits, not_nan_of_finite h]
  simp only [Bool.false_eq_true, ite_false]

set_option maxHeartbeats 1000000 in
/-- **The error of `sinTail`.** -/
theorem sinTail_spec (hF : FmaSpec.FmaNearest)
    (d sh sl ch cl c130 c131 c132 c133 c134 c135 c136 c137 : Float)
    (h130 : c130.toBits = 0xBF33BD3CC9BE45DE) (h131 : c131.toBits = 0x3E503C1F081B5AC4)
    (h132 : c132.toBits = 0xBD555D3C7E3BD8BF) (h133 : c133.toBits = 0x3C4E1F4826790653)
    (h134 : c134.toBits = 0x3F9921FB54442D18) (h135 : c135.toBits = 0xBEC4ABBCE625BE53)
    (h136 : c136.toBits = 0x3DD466BC67748EFC) (h137 : c137.toBits = 0xBCD32D26E446373A)
    (hd : Finite d.toBits) (hD : |value d.toBits| ≤ 1 / 2)
    (hshf : Finite sh.toBits) (hslf : Finite sl.toBits) (hchf : Finite ch.toBits)
    (hclf : Finite cl.toBits) (hsh0 : 0 ≤ value sh.toBits) (hsh1 : value sh.toBits ≤ 1)
    (hsl : |value sl.toBits| ≤ value sh.toBits / 2 ^ 53) (hch0 : 0 ≤ value ch.toBits)
    (hch1 : value ch.toBits ≤ 1) (hcl : |value cl.toBits| ≤ value ch.toBits / 2 ^ 53)
    (hA : value ch.toBits = 0 ∨ (1 / 2 ^ 60 ≤ value ch.toBits ∧ value sh.toBits ≤ 100 * value ch.toBits))
    (hB : value sh.toBits = 0 ∨ (1 / 2 ^ 60 ≤ value sh.toBits ∧
      2 ^ 53 * |value sl.toBits| + value ch.toBits * (1535 / 10 ^ 4) ≤ value sh.toBits * (69 / 10)))
    (hZ : value sh.toBits = 0 → 1 / 2 ^ 60 ≤ value ch.toBits ∧ 1 / 2 ^ 46 ≤ |value d.toBits|) :
    let R := sinTail d sh sl ch cl c130 c131 c132 c133 c134 c135 c136 c137
    Finite R.1.toBits ∧ Finite R.2.toBits ∧
      |value R.1.toBits + value R.2.toBits - (value sh.toBits + value sl.toBits +
          value d.toBits * ((value ch.toBits + value cl.toBits) * Ks (value d.toBits ^ 2) +
            value d.toBits * Kc (value d.toBits ^ 2) * (value sh.toBits + value sl.toBits)))| ≤
        |value d.toBits| / 2 ^ 71 + value sh.toBits / 2 ^ 100 + 1 / 2 ^ 1060 ∧
      |value R.2.toBits| ≤ |value R.1.toBits| / 2 ^ 50 := by
  intro R
  obtain ⟨⟨b130, b130'⟩, b131, b132, b133, ⟨b134, b134'⟩, b135, b136, b137, bc0, bs0⟩ := coef_bounds
  obtain ⟨f130, f131, f132, f133, f134, f135, f136, f137, fc0, fs0⟩ := coef_finite
  rw [← h130] at b130 b130' f130
  rw [← h131] at b131 f131
  rw [← h132] at b132 f132
  rw [← h133] at b133 f133
  rw [← h134] at b134 b134' f134
  rw [← h135] at b135 f135
  rw [← h136] at b136 f136
  rw [← h137] at b137 f137
  have hc0b := lit_bits _ fc0
  have hs0b := lit_bits _ fs0
  rw [← hc0b] at bc0 fc0
  rw [← hs0b] at bs0 fs0
  obtain ⟨D, hDd⟩ : ∃ v, v = value d.toBits := ⟨_, rfl⟩
  have hD' : |D| ≤ 1 / 2 := by rw [hDd]; exact hD
  -- the polynomials
  have hp := p_spec d c131 c132 c133 hd f131 f132 f133 hD b131 b132 b133
  have hq := q_spec d c135 c136 c137 hd f135 f136 f137 hD b135 b136 b137
  rw [← hDd] at hp hq
  have hQv : |D ^ 2 * (value c135.toBits + D ^ 2 * (value c136.toBits + D ^ 2 * value c137.toBits))| ≤
      617 / 10 ^ 9 := by
    have h1 := add_sq_le D _ _ _ _ hD' b136 b137
    have h2 := add_sq_le D _ _ _ _ hD' b135 h1
    have h3 := sq_mul_le D _ _ hD' h2
    linarith [(by norm_num : (2465 / 10 ^ 9 + (1 / 2 ^ 33 + 1 / 2 ^ 49 / 4) / 4 : ℝ) / 4 ≤ 617 / 10 ^ 9)]
  have hPv : |D ^ 2 * (value c131.toBits + D ^ 2 * (value c132.toBits + D ^ 2 * value c133.toBits))| ≤
      1 / 2 ^ 26 := by
    have h1 := add_sq_le D _ _ _ _ hD' b132 b133
    have h2 := add_sq_le D _ _ _ _ hD' b131 h1
    have h3 := sq_mul_le D _ _ hD' h2
    linarith [(by norm_num : (1 / 2 ^ 25 + (1 / 2 ^ 41 + 1 / 2 ^ 58 / 4) / 4 : ℝ) / 4 ≤ 1 / 2 ^ 26)]
  -- the products
  have hS := sin_part hF _ c134 (Float.ofBits 0x3C31A624B88C9448) ch cl _ hq hQv f134 b134 b134'
    fs0 bs0 hchf hclf hch0 hch1 hcl
  have hC := cos_part hF d _ c130 (Float.ofBits 0xBBD692B66E3CF6E8) sh sl _ hd hD hp hPv f130 b130
    b130' fc0 bc0 hshf hslf hsh0 hsh1 (by linarith [(by positivity : (0 : ℝ) ≤ value sh.toBits / 2 ^ 53)])
  obtain ⟨hS1, hS2, hSe, hSa, hSb, hSlo⟩ := hS
  obtain ⟨hC1, hC2, hCe, hCa, hCb⟩ := hC
  have h2 := combine_c2 _ _ hS1 hS2 hC1 hC2 (value ch.toBits) (value sh.toBits) _ _ hch0 hch1 hsh0 hsh1
    hSe hSa hSb hSlo hCe hCa hCb hA
  obtain ⟨h21, h22, h2e, h2a, h2b, h2lo⟩ := h2
  have hr := combine_r hF d sh sl _ hd hshf hslf h21 h22 (value ch.toBits) _ hD hch0 hch1 hsh0 hsh1
    hsl h2e h2a h2b h2lo hB hZ
  obtain ⟨hr1, hr2, hre, hrl⟩ := hr
  refine ⟨hr1, hr2, ?_, hrl⟩
  rw [← hDd] at hre ⊢
  have hKs : Ks (D ^ 2) = value c134.toBits + value (Float.ofBits 0x3C31A624B88C9448).toBits +
      D ^ 2 * (value c135.toBits + D ^ 2 * (value c136.toBits + D ^ 2 * value c137.toBits)) := by
    rw [Ks, h134, h135, h136, h137, hs0b]
  have hKc : Kc (D ^ 2) = value c130.toBits + value (Float.ofBits 0xBBD692B66E3CF6E8).toBits +
      D ^ 2 * (value c131.toBits + D ^ 2 * (value c132.toBits + D ^ 2 * value c133.toBits)) := by
    rw [Kc, h130, h131, h132, h133, hc0b]
  rw [hKs, hKc]
  exact hre

#print axioms sinTail_spec

end Verified.Examples.TgammaSinpidTail
