import Verified.Examples.BesselMillerBack

/-!
The last step of `jn`'s backward recurrence, from `i = 1` to `i = 0`, and the loop as a whole.
`binv_iter` carries `BesselMillerBack.BInv` from the start to `i = 1`.  The last step uses
`BesselMillerStep.bstep` with a bound `d` on `J₂/J₀` that the caller supplies (`last_step`):
`25/6` always, and `21/20` when `J₁ ≤ J₀ + 2^-40`.  The result is a scale `σ` with `b` within
`βL d n` of `σ J₀`, `a` within `βB (n - 2) 1 + 2 u` of `σ J₁`, and `t` within
`(6.1 + 1.01 (n - 1)) u` of `σ J_n` plus `2^-1074`, where `σ J_n ≤ 2^1018` (`J_n ≤ J₁` by
`Jn_le_one`).
-/

namespace Verified.Examples.BesselMillerLast
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselOrderN BesselRecur
  BesselStepF BesselJnTiny BesselSmallSigns BesselMillerReal BesselMillerCF BesselMillerFacts
  BesselMillerStep BesselMillerT BesselMillerLog BesselMillerBack

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The invariant from the start to `i = 1`. -/
theorem binv_iter (scale : Bool) (xa : Float) (hxf : Finite xa.toBits)
    (hw : 1 / 2 ^ 30 ≤ value xa.toBits) (hw2 : value xa.toBits < 2) (n : ℕ) (hn : 2 ≤ n)
    (hn2 : n ≤ 2 ^ 31) (init : Float × Float × Float × Float)
    (h0 : BInv scale (value xa.toBits) n 0 init) :
    ∀ m, m ≤ n - 2 → BInv scale (value xa.toBits) n m (lseq (fun _ s => bbody scale xa s) init m) := by
  intro m
  induction m with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hk
    exact binv_step scale xa hxf hw hw2 n hn2 k (by omega) _ (ih (by omega))

/-- The bound `d` of the last step's factor. -/
noncomputable def KL (d : ℝ) : ℝ :=
  (1 + d) * (203 / 100) * 𝐮 + d * (12 * 𝐮) * (1 + 2 * (12 * 𝐮)) + 101 / 100 * 𝐮

/-- The error bound of `b` after the last step. -/
noncomputable def βL (d : ℝ) (n : ℕ) : ℝ := KL d * (1 + βB (n - 2) 1) + βB (n - 2) 1

theorem KL_le (d : ℝ) (hd0 : 0 ≤ d) (hd5 : d ≤ 5) : 0 ≤ KL d ∧ KL d ≤ 80 * 𝐮 := by
  unfold KL
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  rw [hu]
  constructor
  · positivity
  · nlinarith

/-- `J_n ≤ J₁` for `n ≥ 1` and `0 < x < 2`. -/
theorem Jn_le_one (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) : ∀ n, 1 ≤ n → Jn n w ≤ Jn 1 w
  | 0 => fun h => absurd h (by omega)
  | 1 => fun _ => le_rfl
  | n + 2 => fun _ => by
    have h1 := J_decr w hw0 hw2 (n + 2) (by omega)
    have h2 := Jn_le_one w hw0 hw2 (n + 1) (by omega)
    have h3 := Jn_pos (n + 1) w hw0 hw2.le
    rw [show n + 2 - 1 = n + 1 from rfl] at h1
    linarith

set_option maxHeartbeats 4000000 in
/-- The last step, from `i = 1` to `i = 0`. -/
theorem last_step (scale : Bool) (xa : Float) (hxf : Finite xa.toBits)
    (hw : 1 / 2 ^ 30 ≤ value xa.toBits) (hw2 : value xa.toBits < 2) (n : ℕ) (hn : 2 ≤ n)
    (hn2 : n ≤ 2 ^ 31) (s : Float × Float × Float × Float)
    (hs : BInv scale (value xa.toBits) n (n - 2) s) (d : ℝ) (hd0 : 0 ≤ d) (hd5 : d ≤ 5)
    (hdJ : Jn 2 (value xa.toBits) ≤ d * Jn 0 (value xa.toBits)) :
    ∃ σ : ℝ, 0 < σ ∧
      FApprox (bbody scale xa s).2.1 (σ * Jn 0 (value xa.toBits))
        (βL d n * (σ * Jn 0 (value xa.toBits))) ∧
      FApprox (bbody scale xa s).1 (σ * Jn 1 (value xa.toBits))
        ((βB (n - 2) 1 + 2 * 𝐮) * (σ * Jn 1 (value xa.toBits))) ∧
      Finite (bbody scale xa s).2.2.1.toBits ∧
      |value (bbody scale xa s).2.2.1.toBits - σ * Jn n (value xa.toBits)| ≤
        Tb (n - 1) * (σ * Jn n (value xa.toBits)) + 1 / 2 ^ 1074 ∧
      1 / 2 ^ 64 ≤ σ * Jn 1 (value xa.toBits) ∧ 1 / 20 ≤ σ * Jn 0 (value xa.toBits) ∧
      σ * Jn n (value xa.toBits) ≤ 2 ^ 1018 := by
  set w := value xa.toBits with hwdef
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  have hx : FApprox xa w 0 := by rw [hwdef]; exact fapprox_exact xa hxf
  obtain ⟨σ, hσ, hdi, hb, ha, hr, htf, ht, hlow, hsf, hst⟩ := hs
  rw [show n - 1 - (n - 2) = 1 by omega] at hdi hb hr hlow
  rw [show n - (n - 2) = 2 by omega] at ha hr
  have hJ1 := Jn_pos 1 w hw0 hw2.le
  have hJ1' := hJ1.ne'
  have hJ0 := Jn_pos 0 w hw0 hw2.le
  have hJ2 := Jn_pos 2 w hw0 hw2.le
  have hJn := Jn_pos n w hw0 hw2.le
  have hsum := J_sum w hw0 1 le_rfl
  obtain ⟨hβ0, hβ1⟩ := βB_le (n - 2) 1 (by omega)
  obtain ⟨hT0, hT1⟩ := Tb_le (n - 2) (by omega)
  obtain ⟨hK0, hK1⟩ := KL_le d hd0 hd5
  have hB1 := abs_le.mp hb.2
  have ha1 := abs_le.mp ha.2
  have hσJ1 : 0 < σ * Jn 1 w := by positivity
  have hσJ0 : 0 < σ * Jn 0 w := by positivity
  have hσJ2 : 0 < σ * Jn 2 w := by positivity
  obtain ⟨hα0, hα1⟩ := αB_le (n - 2) (by omega)
  have hBlow : 1 / 4 ≤ value s.2.1.toBits := by nlinarith
  have hA0 : 0 < value s.1.toBits := by nlinarith
  have hJ1le : Jn 1 w ≤ 5 / 3 := by
    have := Jn_le 1 le_rfl w hw0.le hw2.le
    have : (w / 2) ^ 1 / ((1 : ℕ).factorial : ℝ) ≤ 1 := by
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]; linarith
    linarith
  have hJ0low : 1 / 5 ≤ Jn 0 w := by
    rw [Jn_zero]; exact LeanExe.ProofKit.BesselModulus.J0_small w (by rw [abs_of_pos hw0]; exact hw2.le)
  have hBm : value s.2.1.toBits * (2 * ((1 : ℕ) : ℝ) / w) ≤ 2 ^ 1020 := by
    have hlw : 2 * ((1 : ℕ) : ℝ) / w = lam w 1 := by unfold lam; ring
    rw [hlw]
    have hl0 : 0 ≤ lam w 1 := by unfold lam; positivity
    have hJ0u : Jn 0 w ≤ 7 / 3 := by
      have h := (Jn_bounds 0 w hw0.le hw2.le).2
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add,
        Nat.factorial_one] at h
      nlinarith
    have hJ2u : Jn 2 w ≤ 5 / 3 := by
      have := Jn_le 2 (by norm_num) w hw0.le hw2.le
      have h1 : (w / 2) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
      have h2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
      rw [h2] at this
      nlinarith
    have hlamJ : lam w 1 * Jn 1 w ≤ 4 := by
      have := hsum
      simp only [show (1 : ℕ) - 1 = 0 from rfl, show (1 : ℕ) + 1 = 2 from rfl] at this
      linarith
    cases hsc : scale
    · have hσb := hsf hsc
      have hBu : value s.2.1.toBits ≤ σ * Jn 1 w * (1 + 1 / 2 ^ 18) := by nlinarith
      have h2 : value s.2.1.toBits * lam w 1 ≤ σ * Jn 1 w * (1 + 1 / 2 ^ 18) * lam w 1 :=
        mul_le_mul_of_nonneg_right hBu hl0
      have h3 : σ * Jn 1 w * (1 + 1 / 2 ^ 18) * lam w 1 = σ * (lam w 1 * Jn 1 w) * (1 + 1 / 2 ^ 18) := by
        ring
      have h4 : σ * (lam w 1 * Jn 1 w) ≤ 2 ^ 1017 * 4 :=
        mul_le_mul hσb hlamJ (by positivity) (by positivity)
      nlinarith
    · have hB2 := hst hsc
      have hl63 : lam w 1 ≤ 2 ^ 31 := by
        unfold lam
        rw [div_le_iff₀ hw0]
        push_cast
        nlinarith
      have := mul_le_mul hB2 hl63 hl0 (by positivity)
      linarith [show (2 : ℝ) ^ 333 * 2 ^ 31 ≤ 2 ^ 1020 by norm_num]
  have hE : |value s.2.1.toBits * Jn (1 + 1) w - value s.1.toBits * Jn 1 w| ≤
      12 * 𝐮 * (value s.1.toBits * Jn 1 w) := by
    have : Er 1 = 12 * 𝐮 := by unfold Er; rw [if_pos rfl]
    rw [← this]; exact hr
  have hsum' : lam w 1 * Jn 1 w = Jn (1 - 1) w + Jn (1 + 1) w := hsum
  have hdJ' : Jn (1 + 1) w ≤ d * Jn (1 - 1) w := hdJ
  obtain ⟨hbf, hbe⟩ := bstep (a := s.1) (b := s.2.1) (di := s.2.2.2) (x := xa) 1 ha.1 hb.1 hdi hx
    hw hw2 le_rfl (by norm_num) rfl rfl hA0 (le_trans (by norm_num) hBlow) hBm rfl hJ1
    (by simpa using hJ0) (by simpa using hJ2) hsum' hdJ' hd0 hd5 hE (by rw [hu]; positivity)
    (by rw [hu]; norm_num)
  have hKe : (1 + d) * (203 / 100) * 𝐮 + d * (12 * 𝐮) * (1 + 2 * (12 * 𝐮)) + 101 / 100 * 𝐮 = KL d := rfl
  rw [hKe] at hbe
  simp only [show (1 : ℕ) - 1 = 0 from rfl] at hbe
  set Bp := value (s.2.1 * s.2.2.2 / xa - s.1).toBits with hBp
  have hbE : |Bp - σ * Jn 0 w| ≤ βL d n * (σ * Jn 0 w) :=
    b_err hJ1 hJ0 hσJ1 rfl (by field_simp) hK0 hβ0 hbe hb.2
  have hβL : βL d n ≤ 1 / 2 ^ 17 := by
    unfold βL
    have : KL d * (1 + βB (n - 2) 1) ≤ 80 * 𝐮 * 2 := mul_le_mul hK1 (by linarith) (by linarith) (by positivity)
    rw [hu] at this; linarith [show (80 : ℝ) * (1 / 2 ^ 53) * 2 + 1 / 2 ^ 18 ≤ 1 / 2 ^ 17 by norm_num]
  have hβL0 : 0 ≤ βL d n := by unfold βL; positivity
  have hBpu : Bp ≤ (1 + βL d n) * (σ * Jn 0 w) := by have := (abs_le.mp hbE).2; nlinarith
  have hBpl : (1 - βL d n) * (σ * Jn 0 w) ≤ Bp := by have := (abs_le.mp hbE).1; nlinarith
  have hJr := J_ratio w hw0 hw2.le 0
  have hl1 : lam w (0 + 1) ≤ 2 ^ 31 := by
    unfold lam; rw [div_le_iff₀ hw0]; push_cast; nlinarith
  have hJr2 : Jn 0 w ≤ 2 ^ 31 * Jn 1 w := le_trans hJr (mul_le_mul_of_nonneg_right hl1 hJ1.le)
  -- `σ J₀ ≥ 1/20`
  have hσJ0l : 1 / 20 ≤ σ * Jn 0 w := by
    nlinarith [mul_nonneg hσ.le (sub_nonneg.mpr hJ0low), mul_nonneg hσ.le (sub_nonneg.mpr hJ1le)]
  have hTbn : Tb (n - 1) = Tb (n - 2) + 101 / 100 * (1 / 2 ^ 53) := by
    unfold Tb; rw [show n - 1 = n - 2 + 1 by omega]; push_cast; rw [hu]; ring
  have hJn1 := Jn_le_one w hw0 hw2 n (by omega)
  have hσn1 : σ * Jn n w ≤ σ * Jn 1 w := mul_le_mul_of_nonneg_left hJn1 hσ.le
  have hσ334 : scale = true → σ * Jn 1 w ≤ 2 ^ 334 := by
    intro hsc
    have h1 := hst hsc
    have h2 := mul_le_mul_of_nonneg_right hβ1 hσJ1.le
    linarith [hB1.1]
  have hσ1018 : σ * Jn 1 w ≤ 2 ^ 1018 := by
    cases hsc : scale
    · have h1 := mul_le_mul (hsf hsc) hJ1le hJ1.le (by positivity)
      linarith [show (2 : ℝ) ^ 1017 * (5 / 3) ≤ 2 ^ 1018 by norm_num]
    · have h1 := hσ334 hsc
      linarith [show (2 : ℝ) ^ 334 ≤ 2 ^ 1018 by norm_num]
  unfold bbody
  split_ifs with hsc
  · -- the code scales by `b'`
    have hscale : scale = true := by
      cases scale
      · simp at hsc
      · rfl
    have hgt : value (Float.ofBits 0x54B249AD2594C37D).toBits < Bp := by
      have : (s.2.1 * s.2.2.2 / xa - s.1) > Float.ofBits 0x54B249AD2594C37D := by
        rw [hscale] at hsc; simpa using hsc
      exact (gt_c100 _ hbf).mp this
    obtain ⟨-, hc1, hc2⟩ := c100_facts
    have hBp332 : 2 ^ 332 ≤ Bp := by linarith
    have hBp0 : 0 < Bp := lt_of_lt_of_le (by positivity) hBp332
    have hdm := div_mag hb.1 hbf (show |value s.2.1.toBits| ≤ value s.2.1.toBits by
      rw [abs_of_pos (by linarith)]) hBp0 (show Bp ≤ |Bp| from le_abs_self _) (by
        rw [div_le_iff₀ hBp0]
        have : value s.2.1.toBits ≤ 2 ^ 1020 := by
          linarith [hst hscale, show (2 : ℝ) ^ 333 ≤ 2 ^ 1020 by norm_num]
        nlinarith)
    have hYB : 1 / 2 ^ 64 ≤ σ * Jn 1 w / Bp := by
      rw [le_div_iff₀ hBp0]
      have : Bp ≤ 2 * (2 ^ 31 * (σ * Jn 1 w)) := by
        have h1 : σ * Jn 0 w ≤ 2 ^ 31 * (σ * Jn 1 w) := by nlinarith
        nlinarith
      nlinarith
    refine ⟨σ / Bp, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hone := fapprox_one
      have hv1 : value (1.0 : Float).toBits = 1 := by have := abs_nonpos_iff.mp hone.2; linarith
      refine ⟨hone.1, ?_⟩
      rw [hv1, show σ / Bp * Jn 0 w = σ * Jn 0 w / Bp by ring]
      exact scale_b hBp0 hσJ0 hbE
    · refine ⟨hdm.1, ?_⟩
      rw [show σ / Bp * Jn 1 w = σ * Jn 1 w / Bp by ring]
      exact scale_a hBp0 hσJ1 hβ0 (by linarith [show (1 : ℝ) / 2 ^ 18 ≤ 1 by norm_num]) hYB hdm.2
        hb.2 (by rw [hu]; nlinarith)
    · exact (div_mag htf hbf (le_refl _) hBp0 (le_abs_self _) (hAm htf hBp0 hBp332)).1
    · have hdt := div_mag htf hbf (le_refl _) hBp0 (le_abs_self _) (hAm htf hBp0 hBp332)
      rw [show σ / Bp * Jn n w = σ * Jn n w / Bp by ring, hTbn]
      exact scale_t hBp332 (by positivity) hT0 hT1 ht hdt.2
    · rw [show σ / Bp * Jn 1 w = σ * Jn 1 w / Bp by ring]
      exact hYB
    · rw [show σ / Bp * Jn 0 w = σ * Jn 0 w / Bp by ring, le_div_iff₀ hBp0]
      nlinarith
    · rw [show σ / Bp * Jn n w = σ * Jn n w / Bp by ring, div_le_iff₀ hBp0]
      have h3 := mul_le_mul_of_nonneg_left hBp332 (by positivity : (0 : ℝ) ≤ 2 ^ 1018)
      linarith [hσ334 hscale, show (2 : ℝ) ^ 334 ≤ 2 ^ 1018 * 2 ^ 332 by norm_num]
  · refine ⟨σ, hσ, ⟨hbf, hbE⟩, fmono hb ?_, htf, ?_, ?_, hσJ0l, le_trans hσn1 hσ1018⟩
    · exact mul_le_mul_of_nonneg_right (by linarith) hσJ1.le
    · have : Tb (n - 2) ≤ Tb (n - 1) := by rw [hTbn]; linarith [show (0 : ℝ) ≤ 101 / 100 * (1 / 2 ^ 53) by positivity]
      have := mul_le_mul_of_nonneg_right this (show 0 ≤ σ * Jn n w by positivity)
      linarith
    · linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 / 2 by norm_num]

#print axioms Jn_le_one
#print axioms binv_iter
#print axioms last_step

end Verified.Examples.BesselMillerLast
