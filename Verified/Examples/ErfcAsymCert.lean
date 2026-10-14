import Verified.Examples.ErfcSeries
import Verified.Examples.ErfTailBase
import Verified.Examples.ErfcCast

/-!
The certificate of a polynomial `Z` in `1/x²` against `x erfcx x = x exp (x²) erfc x`, from a
model `p` of `erfcxN = erfcx/(2/√π)` on a piece `[a, b]` of the track `erf`
(`ErfTailPieces0` to `ErfTailPieces7`): `|erfcxN x - p (x - c)| ≤ s + eD (b - x)` and
`|p (x - c) - pm| ≤ pr` on `[a, b]`.  `certP` is `x^(2n) Z (1/x²) - sig x^(2n+1) p (x - c)` in the
variable `t = x - c`, with `sig` the middle of `[sLo, sHi]`, and `PolyBound.check` bounds it on
`[lo, hi]` by `E ≤ ε lo^(2n+1) (pm - pr)`.  `cert_sound` turns the check and the rational
conditions `CertCond` into `|Z (1/x²) - x erfcx x| ≤ ρ x erfcx x` on `[lo, hi]`.
-/

namespace Verified.Examples.ErfcAsymCert

open Real Set LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErf RealErfScaled ErfTailBase
  ErfcSeries

set_option exponentiation.threshold 4096

/-- The middle of `[sLo, sHi]`, within `2^-161` of `2/√π`. -/
def sig : ℚ := (sLo + sHi) / 2

theorem sig_close : |(sig : ℝ) - scale| ≤ 1 / 2 ^ 161 := by
  have h1 := scale_lo
  have h2 := scale_hi
  have hd : (sHi : ℝ) - sLo = 1 / 2 ^ 160 := by
    have : sHi - sLo = 1 / 2 ^ 160 := by decide +kernel
    qc this
  have hs : (sig : ℝ) = (sLo + sHi) / 2 := by unfold sig; push_cast; ring
  rw [hs, abs_le]
  constructor <;> linarith

/-- `x^(2n) Z (1/x²) - sig x^(2n+1) p (x - c)` in the variable `t = x - c`. -/
def certP (Z : List ℚ) (n : ℕ) (p : List ℚ) (c : ℚ) : List ℚ :=
  subP (shift c (hatP Z n)) (scaleP sig (mulP (powP (linP c) (2 * n + 1)) p))

theorem eval_certP (Z : List ℚ) (n : ℕ) (hZ : Z.length ≤ n + 1) (p : List ℚ) (c : ℚ) (x : ℝ)
    (hx : x ≠ 0) :
    eval (certP Z n p c) (x - c) =
      x ^ (2 * n) * eval Z (x ^ 2)⁻¹ - sig * (x ^ (2 * n + 1) * eval p (x - c)) := by
  rw [certP, eval_subP, eval_shift, eval_scaleP, eval_mulP, eval_powP, eval_linP, add_sub_cancel,
    eval_hatP Z n hZ x hx]

/-- The rational conditions of one certificate, with `D = s + eD (b - a)` the model's error. -/
def CertCond (n : ℕ) (a b s eD pm pr lo hi E ε ρ : ℚ) : Prop :=
  a ≤ lo ∧ lo ≤ hi ∧ hi ≤ b ∧ 0 < lo ∧ 0 ≤ s ∧ 0 ≤ eD ∧ 0 ≤ ε ∧
    0 < pm - pr - (s + eD * (b - a)) ∧ E ≤ ε * lo ^ (2 * n + 1) * (pm - pr) ∧
    ε + 1 / 2 ^ 161 ≤ ρ * sLo ∧
    (ε + 1 / 2 ^ 161) * (pm - pr) + sHi * (s + eD * (b - a)) ≤
      ρ * sLo * (pm - pr - (s + eD * (b - a)))

instance (n : ℕ) (a b s eD pm pr lo hi E ε ρ : ℚ) :
    Decidable (CertCond n a b s eD pm pr lo hi E ε ρ) := by
  unfold CertCond; infer_instance

theorem cert_sound (Z : List ℚ) (n : ℕ) (hZ : Z.length ≤ n + 1) (p : List ℚ)
    (a b c s eD pm pr lo hi E ε ρ : ℚ) (d : ℕ)
    (hmodel : ∀ x ∈ Icc (a : ℝ) b, |erfcxN x - eval p (x - c)| ≤ (s : ℝ) + eD * ((b : ℝ) - x))
    (hpc : check (subP p [pm]) (a - c) (b - c) pr 20 = true)
    (hck : check (certP Z n p c) (lo - c) (hi - c) E d = true)
    (hcond : CertCond n a b s eD pm pr lo hi E ε ρ) :
    ∀ x ∈ Icc (lo : ℝ) hi, |eval Z (x ^ 2)⁻¹ - x * erfcx x| ≤ ρ * (x * erfcx x) := by
  obtain ⟨h1, -, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hcond
  have q1 : (a : ℝ) ≤ lo := by qc h1
  have q3 : (hi : ℝ) ≤ b := by qc h3
  have q4 : (0 : ℝ) < lo := by qc h4
  have q5 : (0 : ℝ) ≤ s := by qc h5
  have q6 : (0 : ℝ) ≤ eD := by qc h6
  have q7 : (0 : ℝ) ≤ ε := by qc h7
  have q8 : (0 : ℝ) < pm - pr - (s + eD * (b - a)) := by qc h8
  have q9 : (E : ℝ) ≤ ε * lo ^ (2 * n + 1) * (pm - pr) := by qc h9
  have q10 : (ε : ℝ) + 1 / 2 ^ 161 ≤ ρ * sLo := by qc h10
  have q11 : ((ε : ℝ) + 1 / 2 ^ 161) * (pm - pr) + sHi * (s + eD * (b - a)) ≤
      ρ * sLo * (pm - pr - (s + eD * (b - a))) := by qc h11
  have hsl := scale_lo
  have hsh := scale_hi
  have hsig := sig_close
  have hsl0 : (0 : ℝ) < sLo := by
    have : (0 : ℚ) < sLo := by decide +kernel
    qc this
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le q4 hx.1
  have hxa : (a : ℝ) ≤ x := q1.trans hx.1
  have hxb : x ≤ (b : ℝ) := hx.2.trans q3
  have hab : (a : ℝ) ≤ b := hxa.trans hxb
  have hD0 : (0 : ℝ) ≤ s + eD * (b - a) := by
    have : (0 : ℝ) ≤ eD * (b - a) := mul_nonneg q6 (by linarith)
    linarith
  have hm : |erfcxN x - eval p (x - c)| ≤ s + eD * (b - a) := by
    refine (hmodel x ⟨hxa, hxb⟩).trans ?_
    have : (eD : ℝ) * (b - x) ≤ eD * (b - a) := mul_le_mul_of_nonneg_left (by linarith) q6
    linarith
  have hP : (pm : ℝ) - pr ≤ eval p (x - c) := by
    have h := check_sound _ _ _ _ _ hpc (x - c) (by push_cast; linarith) (by push_cast; linarith)
    rw [eval_subP] at h
    simp only [eval_cons, eval_nil, mul_zero, add_zero] at h
    linarith [(abs_le.mp h).1]
  have hw : (0 : ℝ) < pm - pr := by linarith
  have hP0 : 0 < eval p (x - c) := by linarith
  have hA := check_sound _ _ _ _ _ hck (x - c) (by push_cast; linarith [hx.1])
    (by push_cast; linarith [hx.2])
  rw [eval_certP Z n hZ p c x hx0.ne'] at hA
  have hxn : 0 < x ^ (2 * n) := pow_pos hx0 _
  have hE : (E : ℝ) ≤ ε * x * eval p (x - c) * x ^ (2 * n) := by
    refine q9.trans ?_
    have k1 : (lo : ℝ) ^ (2 * n + 1) ≤ x ^ (2 * n + 1) := pow_le_pow_left₀ q4.le hx.1 _
    have k2 : (lo : ℝ) ^ (2 * n + 1) * (pm - pr) ≤ x ^ (2 * n + 1) * eval p (x - c) :=
      mul_le_mul k1 hP hw.le (pow_pos hx0 _).le
    have k3 : (ε : ℝ) * (lo ^ (2 * n + 1) * (pm - pr)) ≤ ε * (x ^ (2 * n + 1) * eval p (x - c)) :=
      mul_le_mul_of_nonneg_left k2 q7
    calc (ε : ℝ) * lo ^ (2 * n + 1) * (pm - pr) = ε * (lo ^ (2 * n + 1) * (pm - pr)) := by ring
      _ ≤ ε * (x ^ (2 * n + 1) * eval p (x - c)) := k3
      _ = ε * x * eval p (x - c) * x ^ (2 * n) := by ring
  have hZ1 : |eval Z (x ^ 2)⁻¹ - sig * x * eval p (x - c)| ≤ ε * x * eval p (x - c) := by
    have e : x ^ (2 * n) * eval Z (x ^ 2)⁻¹ - sig * (x ^ (2 * n + 1) * eval p (x - c)) =
        (eval Z (x ^ 2)⁻¹ - sig * x * eval p (x - c)) * x ^ (2 * n) := by ring
    rw [e, abs_mul, abs_of_pos hxn] at hA
    exact le_of_mul_le_mul_right (hA.trans hE) hxn
  have hN0 : 0 ≤ erfcxN x := (erfcxN_pos x).le
  have hk : ((ε : ℝ) + 1 / 2 ^ 161) * eval p (x - c) + scale * (s + eD * (b - a)) ≤
      ρ * (scale * erfcxN x) := by
    have hPN : eval p (x - c) ≤ erfcxN x + (s + eD * (b - a)) := by
      linarith [(abs_le.mp hm).1]
    have hg : (pm : ℝ) - pr - (s + eD * (b - a)) ≤ erfcxN x := by
      linarith [(abs_le.mp hm).1]
    have hρ0 : (0 : ℝ) ≤ ρ := by
      by_contra hn
      have : (ρ : ℝ) * sLo < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hn) hsl0
      linarith [show (0 : ℝ) < 1 / 2 ^ 161 by positivity]
    have t1 : ((ε : ℝ) + 1 / 2 ^ 161) * eval p (x - c) ≤
        (ε + 1 / 2 ^ 161) * (erfcxN x + (s + eD * (b - a))) :=
      mul_le_mul_of_nonneg_left hPN (by positivity)
    have t2 : scale * (s + eD * (b - a)) ≤ sHi * (s + eD * (b - a)) :=
      mul_le_mul_of_nonneg_right hsh hD0
    have t3 : ρ * sLo * erfcxN x ≤ ρ * (scale * erfcxN x) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsl hN0) hρ0
    have t5 : ((ε : ℝ) + 1 / 2 ^ 161) * (erfcxN x - (pm - pr - (s + eD * (b - a)))) ≤
        ρ * sLo * (erfcxN x - (pm - pr - (s + eD * (b - a)))) :=
      mul_le_mul_of_nonneg_right q10 (by linarith)
    linarith
  have e : eval Z (x ^ 2)⁻¹ - x * erfcx x = (eval Z (x ^ 2)⁻¹ - sig * x * eval p (x - c)) +
      (sig - scale) * (x * eval p (x - c)) + scale * x * (eval p (x - c) - erfcxN x) := by
    rw [erfcx_eq]; ring
  rw [e]
  have b2 : |((sig : ℝ) - scale) * (x * eval p (x - c))| ≤ 1 / 2 ^ 161 * (x * eval p (x - c)) := by
    rw [abs_mul, abs_of_pos (mul_pos hx0 hP0)]
    exact mul_le_mul_of_nonneg_right hsig (mul_pos hx0 hP0).le
  have b3 : |scale * x * (eval p (x - c) - erfcxN x)| ≤ scale * x * (s + eD * (b - a)) := by
    rw [abs_mul, abs_of_pos (mul_pos scale_pos hx0), abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hm (mul_pos scale_pos hx0).le
  have t1 := abs_add_le ((eval Z (x ^ 2)⁻¹ - sig * x * eval p (x - c)) +
    (sig - scale) * (x * eval p (x - c))) (scale * x * (eval p (x - c) - erfcxN x))
  have t2 := abs_add_le (eval Z (x ^ 2)⁻¹ - sig * x * eval p (x - c))
    ((sig - scale) * (x * eval p (x - c)))
  rw [erfcx_eq]
  have hk' := mul_le_mul_of_nonneg_left hk hx0.le
  linarith

#print axioms sig_close
#print axioms eval_certP
#print axioms cert_sound

end Verified.Examples.ErfcAsymCert
