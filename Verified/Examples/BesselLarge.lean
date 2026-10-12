import Verified.Examples.BesselCase
import Verified.Examples.BesselPQ0
import Verified.Examples.BesselPQ1

/-!
The path from 2 of the four functions, with the two branches of `BesselCS` folded in.
`large_sub` and `large_add` take the rounded `P̂` and `Q̂` of one range, the pair `(cc, ss)` in its
two branches, and the numeric conditions of `BesselCase.case_sub` or `case_add` for each branch,
and bound the result against any `F` equal to the large-argument form, in units of any `M` at least
`0.7978 Pl / √x`.  `modulus_ge` supplies that `M` from `BesselPQ.modulus0` or `modulus1`.
`huge_pq0` and `huge_pq1` bound `|P - 1|` and `|Q|` from `2 ^ 129` on, for the path that drops them.
-/

namespace Verified.Examples.BesselLarge
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselPQRange BesselCombine
  BesselCase BesselCS BesselRatio BesselRatioEval Real
open LeanExe.ProofKit.Bessel (J0 J1 Y0 Y1)
open LeanExe.ProofKit.BesselPQ (P0 Q0 P1 Q1)

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

theorem abs_le_sqrt_two {A : ℝ} (h : A ^ 2 ≤ 2) : |A| ≤ 14143 / 10000 := by
  rw [← Real.sqrt_sq_eq_abs]
  calc √(A ^ 2) ≤ √2 := Real.sqrt_le_sqrt h
    _ ≤ 14143 / 10000 := by
      rw [show (14143 / 10000 : ℝ) = √((14143 / 10000) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)

theorem abs_le_one_plus {B : ℝ} (h : B ^ 2 ≤ 1 + 1 / 2 ^ 48) : |B| ≤ 1 + 1 / 2 ^ 48 := by
  rw [← Real.sqrt_sq_eq_abs]
  calc √(B ^ 2) ≤ √(1 + 1 / 2 ^ 48) := Real.sqrt_le_sqrt h
    _ ≤ 1 + 1 / 2 ^ 48 := by
      rw [show (1 + 1 / 2 ^ 48 : ℝ) = √((1 + 1 / 2 ^ 48) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)

/-- `M ≥ 0.7978 Pl / √x` for `M = √(J² + Y²) = √(2/(π x) (P² + Q²))`. -/
theorem modulus_ge {w J Y P Q Pl : ℝ} (hw : 0 < w) (hPl0 : 0 < Pl) (hPl : Pl ≤ P)
    (hmod : J ^ 2 + Y ^ 2 = 2 / (π * w) * (P ^ 2 + Q ^ 2)) :
    7978 / 10000 * Pl / √w ≤ √(J ^ 2 + Y ^ 2) := by
  rw [hmod]
  exact modulus_lower w P Q Pl hw hPl0 hPl

/-- The bracket `P A - Q B` in both branches. -/
theorem large_sub {p q c s xa : Float} {P Q A B F M eP eQ Pl Ph Qh K : ℝ}
    (hp : FApprox p P eP) (hq : FApprox q Q eQ) (hPl0 : 0 < Pl) (hPl : Pl ≤ P) (hPh : P ≤ Ph)
    (hQh : |Q| ≤ Qh) (hbr : Branches c s A B) (hAB : A ^ 2 + B ^ 2 = 2)
    (h1A : (Ph + eP) * (14143 / 10000 + 96 / 25 * 𝐮) < 2 ^ 1022)
    (h2A : (Qh + eQ) * (1 + 1 / 2 ^ 48 + 627 / 100 * 𝐮) < 2 ^ 1022)
    (hltA : Ph * (14143 / 10000) + Qh * (1 + 1 / 2 ^ 48) + (mulErr eP (96 / 25 * 𝐮) Ph (14143 / 10000) +
      mulErr eQ (627 / 100 * 𝐮) Qh (1 + 1 / 2 ^ 48)) < 2)
    (hKA : finErr (mulErr eP (96 / 25 * 𝐮) Ph (14143 / 10000) +
      mulErr eQ (627 / 100 * 𝐮) Qh (1 + 1 / 2 ^ 48) + 𝐮) (Ph * (14143 / 10000) + Qh * (1 + 1 / 2 ^ 48)) +
      1 / 2 ^ 500 ≤ K * 𝐮 * (7978 / 10000 * Pl))
    (h1B : (Ph + eP) * (1 + 1 / 2 ^ 48 + 627 / 100 * 𝐮) < 2 ^ 1022)
    (h2B : (Qh + eQ) * (14143 / 10000 + 96 / 25 * 𝐮) < 2 ^ 1022)
    (hltB : Ph * (1 + 1 / 2 ^ 48) + Qh * (14143 / 10000) + (mulErr eP (627 / 100 * 𝐮) Ph (1 + 1 / 2 ^ 48) +
      mulErr eQ (96 / 25 * 𝐮) Qh (14143 / 10000)) < 2)
    (hKB : finErr (mulErr eP (627 / 100 * 𝐮) Ph (1 + 1 / 2 ^ 48) +
      mulErr eQ (96 / 25 * 𝐮) Qh (14143 / 10000) + 𝐮) (Ph * (1 + 1 / 2 ^ 48) + Qh * (14143 / 10000)) +
      1 / 2 ^ 500 ≤ K * 𝐮 * (7978 / 10000 * Pl)) (hK0 : 0 ≤ K)
    (hxf : Finite xa.toBits) (hx2 : 2 ≤ value xa.toBits) (hxb : value xa.toBits ≤ 2 ^ 1024)
    (hF : F = (P * A - Q * B) / √(π * value xa.toBits))
    (hM : 7978 / 10000 * Pl / √(value xa.toBits) ≤ M) :
    Finite (Bessel.invsqrtpi * (p * c - q * s) / xa.sqrt).toBits ∧
      |value (Bessel.invsqrtpi * (p * c - q * s) / xa.sqrt).toBits - F| ≤ K * 𝐮 * M := by
  have hPm : |P| ≤ Ph := abs_le.mpr ⟨by linarith, hPh⟩
  rw [hF]
  rcases hbr with ⟨hc, hs, hA, hB2⟩ | ⟨hc, hs, hB, hA2⟩
  · exact case_sub hp hq hc hs hPm hQh (abs_le_sqrt_two (by nlinarith)) (abs_le_one_plus hB2)
      h1A h2A hltA hKA hK0 hxf hx2 hxb hM
  · exact case_sub hp hq hc hs hPm hQh (abs_le_one_plus hA2) (abs_le_sqrt_two (by nlinarith))
      h1B h2B hltB hKB hK0 hxf hx2 hxb hM

/-- The bracket `P B + Q A` in both branches. -/
theorem large_add {p q c s xa : Float} {P Q A B F M eP eQ Pl Ph Qh K : ℝ}
    (hp : FApprox p P eP) (hq : FApprox q Q eQ) (hPl0 : 0 < Pl) (hPl : Pl ≤ P) (hPh : P ≤ Ph)
    (hQh : |Q| ≤ Qh) (hbr : Branches c s A B) (hAB : A ^ 2 + B ^ 2 = 2)
    (h1A : (Ph + eP) * (1 + 1 / 2 ^ 48 + 627 / 100 * 𝐮) < 2 ^ 1022)
    (h2A : (Qh + eQ) * (14143 / 10000 + 96 / 25 * 𝐮) < 2 ^ 1022)
    (hltA : Ph * (1 + 1 / 2 ^ 48) + Qh * (14143 / 10000) + (mulErr eP (627 / 100 * 𝐮) Ph (1 + 1 / 2 ^ 48) +
      mulErr eQ (96 / 25 * 𝐮) Qh (14143 / 10000)) < 2)
    (hKA : finErr (mulErr eP (627 / 100 * 𝐮) Ph (1 + 1 / 2 ^ 48) +
      mulErr eQ (96 / 25 * 𝐮) Qh (14143 / 10000) + 𝐮) (Ph * (1 + 1 / 2 ^ 48) + Qh * (14143 / 10000)) +
      1 / 2 ^ 500 ≤ K * 𝐮 * (7978 / 10000 * Pl))
    (h1B : (Ph + eP) * (14143 / 10000 + 96 / 25 * 𝐮) < 2 ^ 1022)
    (h2B : (Qh + eQ) * (1 + 1 / 2 ^ 48 + 627 / 100 * 𝐮) < 2 ^ 1022)
    (hltB : Ph * (14143 / 10000) + Qh * (1 + 1 / 2 ^ 48) + (mulErr eP (96 / 25 * 𝐮) Ph (14143 / 10000) +
      mulErr eQ (627 / 100 * 𝐮) Qh (1 + 1 / 2 ^ 48)) < 2)
    (hKB : finErr (mulErr eP (96 / 25 * 𝐮) Ph (14143 / 10000) +
      mulErr eQ (627 / 100 * 𝐮) Qh (1 + 1 / 2 ^ 48) + 𝐮) (Ph * (14143 / 10000) + Qh * (1 + 1 / 2 ^ 48)) +
      1 / 2 ^ 500 ≤ K * 𝐮 * (7978 / 10000 * Pl)) (hK0 : 0 ≤ K)
    (hxf : Finite xa.toBits) (hx2 : 2 ≤ value xa.toBits) (hxb : value xa.toBits ≤ 2 ^ 1024)
    (hF : F = (P * B + Q * A) / √(π * value xa.toBits))
    (hM : 7978 / 10000 * Pl / √(value xa.toBits) ≤ M) :
    Finite (Bessel.invsqrtpi * (p * s + q * c) / xa.sqrt).toBits ∧
      |value (Bessel.invsqrtpi * (p * s + q * c) / xa.sqrt).toBits - F| ≤ K * 𝐮 * M := by
  have hPm : |P| ≤ Ph := abs_le.mpr ⟨by linarith, hPh⟩
  rw [hF]
  rcases hbr with ⟨hc, hs, hA, hB2⟩ | ⟨hc, hs, hB, hA2⟩
  · exact case_add hp hq hc hs hPm hQh (abs_le_sqrt_two (by nlinarith)) (abs_le_one_plus hB2)
      h1A h2A hltA hKA hK0 hxf hx2 hxb hM
  · exact case_add hp hq hc hs hPm hQh (abs_le_one_plus hA2) (abs_le_sqrt_two (by nlinarith))
      h1B h2B hltB hKB hK0 hxf hx2 hxb hM

/-- `R/S` of fdlibm's range from 8, at `z ≤ 2 ^ -250`. -/
theorem tiny_bounds :
    boundsOk (BesselPQ0.pr0.map ratOfWord) (1 :: BesselPQ0.ps0.map ratOfWord) (1 / 2 ^ 240) 0
        [1 / 2 ^ 250] = true ∧
      boundsOk (BesselPQ0.qr0.map ratOfWord) (1 :: BesselPQ0.qs0.map ratOfWord) (1 / 2 ^ 240) 0
        [1 / 2 ^ 250] = true ∧
      boundsOk (BesselPQ1.pr0.map ratOfWord) (1 :: BesselPQ1.ps0.map ratOfWord) (1 / 2 ^ 240) 0
        [1 / 2 ^ 250] = true ∧
      boundsOk (BesselPQ1.qr0.map ratOfWord) (1 :: BesselPQ1.qs0.map ratOfWord) (1 / 2 ^ 240) 0
        [1 / 2 ^ 250] = true := by
  decide +kernel

theorem tiny_ratio (R S : List ℚ) (h : boundsOk R S (1 / 2 ^ 240) 0 [1 / 2 ^ 250] = true)
    (w : ℝ) (hw : 2 ^ 125 ≤ w) : |eval R (1 / w ^ 2) / eval S (1 / w ^ 2)| ≤ 1 / 2 ^ 240 := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hz0 : (0 : ℝ) ≤ 1 / w ^ 2 := by positivity
  have hz1 : 1 / w ^ 2 ≤ 1 / 2 ^ 250 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    have := pow_le_pow_left₀ (by positivity) hw 2
    rw [← pow_mul] at this
    exact this
  have hb := bounds_sound R S (1 / 2 ^ 240) (1 / w ^ 2) 0 [1 / 2 ^ 250] (by simp) h
    (by push_cast; exact hz0) (by simp only [lastD]; push_cast; exact hz1)
  have := ratio_abs R S _ _ hb
  push_cast at this
  exact this

/-- `|P₀ - 1|` and `|Q₀|` from `2 ^ 129` on. -/
theorem huge_pq0 (w : ℝ) (hw : 2 ^ 129 ≤ w) :
    |P0 w - 1| ≤ 262 / 2 ^ 68 ∧ |Q0 w| ≤ 19 / 2 ^ 68 := by
  have hw8 : (((8 : ℚ)) : ℝ) ≤ w := by push_cast; linarith [show (8 : ℝ) ≤ 2 ^ 129 by norm_num]
  have hw0 : 0 < w := by linarith
  have h1 := BesselFd0b.pzero_8 w hw8
  have h2 := BesselFd0b.qzero_8 w hw8
  have hp := tiny_ratio _ _ tiny_bounds.1 w (by linarith [show (2 : ℝ) ^ 125 ≤ 2 ^ 129 by norm_num])
  have hq := tiny_ratio _ _ tiny_bounds.2.1 w (by linarith [show (2 : ℝ) ^ 125 ≤ 2 ^ 129 by norm_num])
  rw [show BesselPQ0.pr0.map ratOfWord = BesselFd0b.pR8 from (BesselPQ0.lists_0).1,
    show BesselPQ0.ps0.map ratOfWord = BesselFd0b.pS8 from (BesselPQ0.lists_0).2.1,
    eval_one_cons] at hp
  rw [show BesselPQ0.qr0.map ratOfWord = BesselFd0b.qR8 from (BesselPQ0.lists_0).2.2.1,
    show BesselPQ0.qs0.map ratOfWord = BesselFd0b.qS8 from (BesselPQ0.lists_0).2.2.2,
    eval_one_cons] at hq
  unfold pFd at h1
  unfold qFd at h2
  constructor
  · have := abs_sub_abs_le_abs_sub (P0 w - 1) (eval BesselFd0b.pR8 (1 / w ^ 2) /
      (1 + 1 / w ^ 2 * eval BesselFd0b.pS8 (1 / w ^ 2)))
    rw [show P0 w - 1 - eval BesselFd0b.pR8 (1 / w ^ 2) /
      (1 + 1 / w ^ 2 * eval BesselFd0b.pS8 (1 / w ^ 2)) = P0 w - (1 + eval BesselFd0b.pR8 (1 / w ^ 2) /
      (1 + 1 / w ^ 2 * eval BesselFd0b.pS8 (1 / w ^ 2))) by ring] at this
    have e : (1 : ℝ) / 2 ^ 240 + (261 / 2 ^ 68 + 1 / 2 ^ 70) ≤ 262 / 2 ^ 68 := by norm_num
    linarith
  · set ρ := eval BesselFd0b.qR8 (1 / w ^ 2) / (1 + 1 / w ^ 2 * eval BesselFd0b.qS8 (1 / w ^ 2))
    have hρ : |(ρ + ((-1 / 8 : ℚ) : ℝ)) / w| ≤ 1 / 2 ^ 120 := by
      rw [abs_div, abs_of_pos hw0, div_le_iff₀ hw0]
      have : |ρ + ((-1 / 8 : ℚ) : ℝ)| ≤ 1 := by
        have := abs_add_le ρ ((-1 / 8 : ℚ) : ℝ)
        have hc : |((-1 / 8 : ℚ) : ℝ)| ≤ 1 / 2 := by norm_num
        have e : (1 : ℝ) / 2 ^ 240 ≤ 1 / 2 := by norm_num
        linarith
      have e : (1 : ℝ) ≤ 1 / 2 ^ 120 * 2 ^ 129 := by norm_num
      nlinarith
    have := abs_sub_abs_le_abs_sub (Q0 w) ((ρ + ((-1 / 8 : ℚ) : ℝ)) / w)
    have e : (1 : ℝ) / 2 ^ 120 + (18 / 2 ^ 68 + 1 / 2 ^ 70) ≤ 19 / 2 ^ 68 := by norm_num
    linarith

/-- `|P₁ - 1|` and `|Q₁|` from `2 ^ 129` on. -/
theorem huge_pq1 (w : ℝ) (hw : 2 ^ 129 ≤ w) :
    |P1 w - 1| ≤ 283 / 2 ^ 68 ∧ |Q1 w| ≤ 21 / 2 ^ 68 := by
  have hw8 : (((8 : ℚ)) : ℝ) ≤ w := by push_cast; linarith [show (8 : ℝ) ≤ 2 ^ 129 by norm_num]
  have hw0 : 0 < w := by linarith
  have h1 := BesselFd1b.pone_8 w hw8
  have h2 := BesselFd1b.qone_8 w hw8
  have hp := tiny_ratio _ _ tiny_bounds.2.2.1 w (by linarith [show (2 : ℝ) ^ 125 ≤ 2 ^ 129 by norm_num])
  have hq := tiny_ratio _ _ tiny_bounds.2.2.2 w (by linarith [show (2 : ℝ) ^ 125 ≤ 2 ^ 129 by norm_num])
  rw [show BesselPQ1.pr0.map ratOfWord = BesselFd1b.pr8 from (BesselPQ1.lists_0).1,
    show BesselPQ1.ps0.map ratOfWord = BesselFd1b.ps8 from (BesselPQ1.lists_0).2.1,
    eval_one_cons] at hp
  rw [show BesselPQ1.qr0.map ratOfWord = BesselFd1b.qr8 from (BesselPQ1.lists_0).2.2.1,
    show BesselPQ1.qs0.map ratOfWord = BesselFd1b.qs8 from (BesselPQ1.lists_0).2.2.2,
    eval_one_cons] at hq
  unfold pFd at h1
  unfold qFd at h2
  constructor
  · have := abs_sub_abs_le_abs_sub (P1 w - 1) (eval BesselFd1b.pr8 (1 / w ^ 2) /
      (1 + 1 / w ^ 2 * eval BesselFd1b.ps8 (1 / w ^ 2)))
    rw [show P1 w - 1 - eval BesselFd1b.pr8 (1 / w ^ 2) /
      (1 + 1 / w ^ 2 * eval BesselFd1b.ps8 (1 / w ^ 2)) = P1 w - (1 + eval BesselFd1b.pr8 (1 / w ^ 2) /
      (1 + 1 / w ^ 2 * eval BesselFd1b.ps8 (1 / w ^ 2))) by ring] at this
    have e : (1 : ℝ) / 2 ^ 240 + (282 / 2 ^ 68 + 1 / 2 ^ 70) ≤ 283 / 2 ^ 68 := by norm_num
    linarith
  · set ρ := eval BesselFd1b.qr8 (1 / w ^ 2) / (1 + 1 / w ^ 2 * eval BesselFd1b.qs8 (1 / w ^ 2))
    have hρ : |(ρ + ((3 / 8 : ℚ) : ℝ)) / w| ≤ 1 / 2 ^ 120 := by
      rw [abs_div, abs_of_pos hw0, div_le_iff₀ hw0]
      have : |ρ + ((3 / 8 : ℚ) : ℝ)| ≤ 1 := by
        have := abs_add_le ρ ((3 / 8 : ℚ) : ℝ)
        have hc : |((3 / 8 : ℚ) : ℝ)| ≤ 1 / 2 := by norm_num
        have e : (1 : ℝ) / 2 ^ 240 ≤ 1 / 2 := by norm_num
        linarith
      have e : (1 : ℝ) ≤ 1 / 2 ^ 120 * 2 ^ 129 := by norm_num
      nlinarith
    have := abs_sub_abs_le_abs_sub (Q1 w) ((ρ + ((3 / 8 : ℚ) : ℝ)) / w)
    have e : (1 : ℝ) / 2 ^ 120 + (20 / 2 ^ 68 + 1 / 2 ^ 70) ≤ 21 / 2 ^ 68 := by norm_num
    linarith

#print axioms modulus_ge
#print axioms large_sub
#print axioms large_add
#print axioms tiny_bounds
#print axioms huge_pq0
#print axioms huge_pq1

end Verified.Examples.BesselLarge
