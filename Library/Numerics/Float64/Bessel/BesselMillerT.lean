import Library.Numerics.Float64.Bessel.BesselMillerDepth
import Library.Numerics.Float64.Bessel.BesselJnTiny

/-!
The evaluation of the continued fraction in `jn`'s backward recurrence: for the depth `K` of
`BesselMillerDepth.cf_depth`, the loop `t ← 1/(2 (n + K - j)/x - t)` for `j = 0, ..., K` computes
`F n` for `F = BesselMillerReal.cfrac x (n + K + 1)`.  Each step keeps a relative error of at most
`6 u` (`tstep`), since the fraction stays below `1/2` before the last step and `λ ≥ 2`
(`t_loop`).  With `BesselMillerReal.cf_error`, `tail_ratio`, and `Q K ≥ 9 · 10^8`, the result
lies within `6.1 u` of `J_n/J_(n-1)` (`t_value`).
-/

namespace Library.Numerics.Float64.Bessel.BesselMillerT
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselOrderN BesselRecur
  BesselMillerReal BesselMillerCF BesselStepF BesselJnTiny BesselSmallSigns

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- One step `1/(c/x - t)` of the fraction, with relative errors. -/
theorem tstep {c x t : Float} {C w L τ : ℝ} (hc : FApprox c C 0) (hx : FApprox x w 0) (hw : 0 < w)
    (hL : L = C / w) (hL2 : 2 ≤ L) (hLb : L ≤ 2 ^ 63) (ht : FApprox t τ (6 * 𝐮 * τ))
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) :
    FApprox (1.0 / (c / x - t)) (1 / (L - τ)) (6 * 𝐮 * (1 / (L - τ))) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hC : 0 ≤ C := by
    have : C = L * w := by rw [hL]; field_simp
    rw [this]; positivity
  have hq := fapprox_div hc hx C w (by rw [abs_of_nonneg hC]) (le_abs_self w) hw L
    (by rw [add_zero, sub_zero, hL]) (by linarith [show (2 : ℝ) ^ 63 < 2 ^ 1022 by norm_num])
  rw [← hL] at hq
  have hq' : FApprox (c / x) L (L / 2 ^ 53 + 1 / 2 ^ 1075) := fmono hq (by simp)
  have hm : 3 / 2 ≤ L - τ := by linarith
  set m := L - τ with hmdef
  have hm0 : 0 < m := by linarith
  have hD := fapprox_sub hq' ht (m * (1 + 1 / 2 ^ 40)) (by
    rw [abs_of_nonneg hm0.le, hu]
    nlinarith) (by nlinarith [show (2 : ℝ) ^ 63 * 2 < 2 ^ 1023 by norm_num])
  rw [← hmdef] at hD
  set eD := L / 2 ^ 53 + 1 / 2 ^ 1075 + 6 * 𝐮 * τ + m * (1 + 1 / 2 ^ 40) / 2 ^ 53 with heD
  -- `eD ≤ 4.34 u m`
  have heD' : eD ≤ 434 / 100 * 𝐮 * m := by
    rw [heD, hu]
    have h1 : L ≤ 4 / 3 * m := by rw [hmdef]; linarith
    have h2 : τ ≤ 1 / 3 * m := by rw [hmdef]; linarith
    have h3 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000 * m := by nlinarith
    nlinarith
  have heDm : eD < m := by
    have : 434 / 100 * 𝐮 * m < m := by rw [hu]; nlinarith
    linarith
  have hone : FApprox (1.0 : Float) 1 0 := fapprox_one
  have hr := fapprox_div hone hD 1 m (by norm_num) (le_of_eq (abs_of_pos hm0).symm) heDm
    (1 / (m - eD)) (by rw [add_zero]) (by
      have : m - eD ≥ 1 := by nlinarith
      rw [div_lt_iff₀ (by linarith)]
      nlinarith [show (1 : ℝ) < 2 ^ 1022 by norm_num])
  refine fmono hr ?_
  -- `(eD/m)/(m - eD) + 1/((m - eD) 2^53) + η ≤ 6 u/m`
  obtain ⟨E, hEdef⟩ : ∃ E, E = eD / m := ⟨_, rfl⟩
  have heq : eD = E * m := by rw [hEdef]; field_simp
  have hE : E ≤ 434 / 100 * 𝐮 := by rw [hEdef, div_le_iff₀ hm0]; linarith
  have heD0 : 0 ≤ eD := by rw [heD, hu]; positivity
  have hE0 : 0 ≤ E := by rw [hEdef]; exact div_nonneg heD0 hm0.le
  rw [heq]
  rw [hu] at hE ⊢
  have h1E : 0 < 1 - E := by linarith [show (434 : ℝ) / 100 * (1 / 2 ^ 53) < 1 by norm_num]
  have hm1 : m ≠ 0 := hm0.ne'
  have hm2 : m - E * m ≠ 0 := by nlinarith
  have hm3 : 1 - E ≠ 0 := h1E.ne'
  have e1 : (0 + 1 * (E * m) / m) / (m - E * m) + 1 / (m - E * m) / 2 ^ 53 =
      (E + 1 / 2 ^ 53) / (m * (1 - E)) := by
    field_simp
    ring
  rw [e1]
  have h2 : (E + 1 / 2 ^ 53) / (m * (1 - E)) ≤ 54 / 10 * (1 / 2 ^ 53) / m := by
    rw [div_le_div_iff₀ (by positivity) hm0]
    nlinarith
  have hm63 : m ≤ 2 ^ 63 := by linarith
  have h3 : (1 : ℝ) / 2 ^ 1075 ≤ 6 / 10 * (1 / 2 ^ 53) / m := by
    rw [le_div_iff₀ hm0]; nlinarith
  have e2 : 54 / 10 * (1 / 2 ^ 53) / m + 6 / 10 * (1 / 2 ^ 53) / m = 6 * (1 / 2 ^ 53) * (1 / m) := by
    ring
  linarith

/-- The body of the fraction's loop. -/
def fbody (n k : UInt64) (x : Float) (j : UInt64) (t : Float) : Float :=
  1.0 / ((2 * (n + k) - 2 * j).toFloat / x - t)

theorem word_c (n : UInt64) (K j : ℕ) (hn : n.toNat ≤ 2 ^ 31) (hK : K ≤ 13) (hj : j ≤ K) :
    (2 * (n + UInt64.ofNat K) - 2 * UInt64.ofNat j).toNat = 2 * (n.toNat + K - j) := by
  have hnl := n.toNat_lt
  rw [UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat',
    UInt64.toNat_ofNat']
  simp only [UInt64.reduceToNat, Nat.reducePow] at hnl ⊢
  omega

/-- The fraction's loop keeps a relative error of `6 u` and values in `[0, 1/2]`. -/
theorem t_loop (xa : Float) (n : UInt64) (K : ℕ) (hxf : Finite xa.toBits)
    (hw : 1 / 2 ^ 30 ≤ value xa.toBits) (hw2 : value xa.toBits < 2) (hn : 2 ≤ n.toNat)
    (hn2 : n.toNat ≤ 2 ^ 31) (hK : K ≤ 13) :
    ∀ i, i ≤ K →
      FApprox (lseq (fbody n (UInt64.ofNat K) xa) (0.0 : Float) i)
          (cfrac (value xa.toBits) (n.toNat + K + 1) (n.toNat + K + 1 - i))
          (6 * 𝐮 * cfrac (value xa.toBits) (n.toNat + K + 1) (n.toNat + K + 1 - i)) ∧
        0 ≤ cfrac (value xa.toBits) (n.toNat + K + 1) (n.toNat + K + 1 - i) ∧
        cfrac (value xa.toBits) (n.toNat + K + 1) (n.toNat + K + 1 - i) ≤ 1 / 2 := by
  set w := value xa.toBits with hwdef
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hx : FApprox xa w 0 := by rw [hwdef]; exact fapprox_exact xa hxf
  intro i
  induction i with
  | zero =>
    intro _
    have hc : cfrac w (n.toNat + K + 1) (n.toNat + K + 1 - 0) = 0 := by
      unfold cfrac; simp
    rw [hc]
    refine ⟨?_, le_rfl, by norm_num⟩
    have h0 : (0.0 : Float).toBits = 0 := rfl
    unfold FApprox Approx
    show Finite (0.0 : Float).toBits ∧ |value (0.0 : Float).toBits - 0| ≤ 6 * 𝐮 * 0
    rw [h0]
    have : value (0 : UInt64) = 0 := by
      rw [← ratOfWord_cast]
      have : ratOfWord 0 = 0 := by decide +kernel
      rw [this]; norm_num
    rw [this]
    exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num⟩
  | succ i ih =>
    intro hi
    obtain ⟨ht, hτ0, hτ⟩ := ih (by omega)
    set M := n.toNat + K + 1 with hM
    set p := M - (i + 1) with hp
    have hp1 : p + 1 = M - i := by omega
    have hpn : n.toNat + 1 ≤ p := by omega
    have hl : ∀ i', p ≤ i' → i' < M → 2 ≤ lam w i' := by
      intro i' h1 _
      have := lam_gt w hw0 hw2 i' (by omega)
      have : (2 : ℝ) ≤ i' := by exact_mod_cast (show 2 ≤ i' by omega)
      linarith
    have hcf := cf_step w hw0 M p (by omega) (by omega) hl
    rw [hp1] at hcf
    have hlp := lam_gt w hw0 hw2 p (by omega)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    have hLb := lam_le w hw p (by omega)
    have hword := word_c n K i hn2 hK (by omega)
    have hcw := toFloat_exact (2 * (n + UInt64.ofNat K) - 2 * UInt64.ofNat i) (by rw [hword]; omega)
    rw [hword] at hcw
    have hpv : p = n.toNat + K - i := by omega
    have hL : lam w p = ((2 * (n.toNat + K - i) : ℕ) : ℝ) / w := by
      unfold lam; rw [hpv]; push_cast <;> ring
    have hs := tstep hcw hx hw0 hL (by linarith) hLb ht hτ0 hτ
    rw [← hcf] at hs
    refine ⟨hs, ?_, ?_⟩
    · rw [hcf]; apply div_nonneg (by norm_num); linarith
    · rw [hcf, div_le_iff₀ (by linarith)]; linarith

/-- The fraction's value: within `6.1 u` of `J_n/J_(n-1)`. -/
theorem t_value (xa : Float) (n : UInt64) (K : ℕ) (hxf : Finite xa.toBits)
    (hw : 1 / 2 ^ 30 ≤ value xa.toBits) (hw2 : value xa.toBits < 2) (hn : 2 ≤ n.toNat)
    (hn2 : n.toNat ≤ 2 ^ 31) (hK1 : 1 ≤ K) (hK : K ≤ 13)
    (hQ : 900000000 ≤ Q (value xa.toBits) n.toNat K) :
    FApprox (LeanExe.loop (UInt64.ofNat K + 1) (0.0 : Float) (fbody n (UInt64.ofNat K) xa))
      (Jn n.toNat (value xa.toBits) / Jn (n.toNat - 1) (value xa.toBits))
      (61 / 10 * 𝐮 * (Jn n.toNat (value xa.toBits) / Jn (n.toNat - 1) (value xa.toBits))) := by
  set w := value xa.toBits with hwdef
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hx : FApprox xa w 0 := by rw [hwdef]; exact fapprox_exact xa hxf
  have hKw : (UInt64.ofNat K + 1).toNat = K + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']; simp only [UInt64.reduceToNat, Nat.reducePow]; omega
  rw [loop_lseq, hKw]
  obtain ⟨ht, hτ0, hτ⟩ := t_loop xa n K hxf hw hw2 hn hn2 hK K le_rfl
  set M := n.toNat + K + 1 with hM
  rw [show M - K = n.toNat + 1 by omega] at ht hτ0 hτ
  have hword := word_c n K K hn2 hK le_rfl
  rw [show n.toNat + K - K = n.toNat by omega] at hword
  have hcw := toFloat_exact (2 * (n + UInt64.ofNat K) - 2 * UInt64.ofNat K) (by rw [hword]; omega)
  rw [hword] at hcw
  have hL : lam w n.toNat = ((2 * n.toNat : ℕ) : ℝ) / w := by unfold lam; push_cast <;> ring
  have hlg := lam_gt w hw0 hw2 n.toNat (by omega)
  have hnr : (2 : ℝ) ≤ n.toNat := by exact_mod_cast hn
  have hLb := lam_le w hw n.toNat (by omega)
  have hs := tstep hcw hx hw0 hL (by linarith) hLb ht hτ0 hτ
  have hl : ∀ i', n.toNat ≤ i' → i' < M → 2 ≤ lam w i' := by
    intro i' h1 _
    have := lam_gt w hw0 hw2 i' (by omega)
    have : (2 : ℝ) ≤ i' := by exact_mod_cast (show 2 ≤ i' by omega)
    linarith
  have hcf := cf_step w hw0 M n.toNat (by omega) (by omega) hl
  rw [← hcf] at hs
  have e : lseq (fbody n (UInt64.ofNat K) xa) (0.0 : Float) (K + 1) =
      1.0 / ((2 * (n + UInt64.ofNat K) - 2 * UInt64.ofNat K).toFloat / xa -
        lseq (fbody n (UInt64.ofNat K) xa) (0.0 : Float) K) := rfl
  rw [e]
  -- the fraction against `r = J_n/J_(n-1)`
  have hcv : cfrac w M n.toNat = kern w n.toNat M / kern w (n.toNat - 1) M := by
    unfold cfrac; rw [if_pos (by omega)]
  have hJ1 := Jn_pos (n.toNat - 1) w hw0 hw2.le
  have hJn := Jn_pos n.toNat w hw0 hw2.le
  have hJM := Jn_pos M w hw0 hw2.le
  have hQd : kern w (n.toNat - 1) M = Q w n.toNat K := rfl
  have hQ0 : 0 < kern w (n.toNat - 1) M := by rw [hQd]; linarith
  have hce := cf_error w hw0.ne' n.toNat M (by omega)
  have htr := tail_ratio w hw0 hw2.le n.toNat K hn
  have hkl := (kern_le_prod w hw0 n.toNat (by omega) (fun i hi => by
    have := lam_gt w hw0 hw2 i (by omega)
    have : (2 : ℝ) ≤ i := by exact_mod_cast (show 2 ≤ i by omega)
    linarith) K).2.1
  rw [show n.toNat + K + 1 = M from rfl] at htr hkl
  -- `J_M Q ≤ 2.4 J_n`
  have hJQ : Jn M w * kern w (n.toNat - 1) M ≤ 12 / 5 * Jn n.toNat w := by
    have := mul_le_mul_of_nonneg_left hkl hJM.le
    linarith
  set r := Jn n.toNat w / Jn (n.toNat - 1) w with hr
  have hr0 : 0 < r := div_pos hJn hJ1
  set Qk := kern w (n.toNat - 1) M with hQkdef
  have hQk : 900000000 ≤ Qk := le_of_le_of_eq hQ hQd.symm
  have hcfv : cfrac w M n.toNat = r - Jn M w / (Jn (n.toNat - 1) w * Qk) := by
    rw [hcv, hr]
    field_simp
    linarith
  have hgap : Jn M w / (Jn (n.toNat - 1) w * Qk) ≤ 3 / 100 * 𝐮 * r := by
    rw [hr, div_le_iff₀ (by positivity)]
    have : 3 / 100 * 𝐮 * (Jn n.toNat w / Jn (n.toNat - 1) w) * (Jn (n.toNat - 1) w * Qk) =
        3 / 100 * 𝐮 * Jn n.toNat w * Qk := by field_simp
    rw [this, hu]
    have hQ2 : 12 / 5 ≤ 3 / 100 * (1 / 2 ^ 53) * Qk * Qk := by nlinarith
    nlinarith
  have hgap0 : 0 ≤ Jn M w / (Jn (n.toNat - 1) w * Qk) := by positivity
  refine ⟨hs.1, ?_⟩
  have h1 := hs.2
  rw [hcfv] at h1
  have := abs_sub_le (value (1.0 / ((2 * (n + UInt64.ofNat K) - 2 * UInt64.ofNat K).toFloat / xa -
    lseq (fbody n (UInt64.ofNat K) xa) (0.0 : Float) K)).toBits)
    (r - Jn M w / (Jn (n.toNat - 1) w * Qk)) r
  rw [show r - Jn M w / (Jn (n.toNat - 1) w * Qk) - r = -(Jn M w / (Jn (n.toNat - 1) w * Qk)) by ring,
    abs_neg, abs_of_nonneg hgap0] at this
  have h6 : 6 * 𝐮 * (r - Jn M w / (Jn (n.toNat - 1) w * Qk)) ≤ 6 * 𝐮 * r := by
    have : (0 : ℝ) ≤ 6 * 𝐮 := by rw [hu]; positivity
    nlinarith
  rw [hu] at hgap h6 h1 ⊢
  linarith

#print axioms tstep
#print axioms t_value

end Library.Numerics.Float64.Bessel.BesselMillerT
