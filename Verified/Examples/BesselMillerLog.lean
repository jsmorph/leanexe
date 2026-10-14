import Verified.Examples.BesselMillerDepth
import Verified.Examples.LogNearAll
import Verified.Examples.TrigSinCos
import Verified.Examples.BesselSmallJ0

/-!
The scaling flag of `jn`'s backward recurrence.  The code computes `tmp = n · log |(2/x) · n|` and
skips the scaling when `tmp < 709.782712893383973096`.  From `LogNearAll.log_near` and the
roundings of the three operations, `tmp` below that constant gives `n ln(2n/x) ≤ 709.783`
(`flag_log`), so `(2n/x)^n ≤ e^709.783 < 2^1024 · 1.001`.  With
`J_(n-1) ≥ (x/2)^(n-1)/(3 (n-1)!)` and `m! ≤ m^m/2^(m-1)` (`factorial_le`), this bounds
`1/J_(n-1)` by `2^1017` (`flag_bound`), which keeps the unscaled recurrence finite.
-/

namespace Verified.Examples.BesselMillerLog
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselOrderN BesselRecur
  BesselMillerReal BesselMillerCF BesselMillerDepth BesselStepF BesselSmallSigns

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- `m! ≤ m^m/2^(m-1)` for `m ≥ 1`. -/
theorem factorial_le (m : ℕ) (hm : 1 ≤ m) : (m.factorial : ℝ) * 2 ^ (m - 1) ≤ (m : ℝ) ^ m := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; norm_num
    · have ih' := ih h
      have hk : (1 : ℝ) ≤ k := by exact_mod_cast h
      -- `2 k^k ≤ (k + 1)^k` from Bernoulli's inequality
      have hb : 2 * (k : ℝ) ^ k ≤ ((k : ℝ) + 1) ^ k := by
        have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / k by
          have : (0 : ℝ) ≤ 1 / k := by positivity
          linarith) k
        have e : (1 : ℝ) + k * (1 / k) = 2 := by field_simp; ring
        rw [e] at h1
        have e2 : ((k : ℝ) + 1) ^ k = (k : ℝ) ^ k * (1 + 1 / k) ^ k := by
          rw [← mul_pow]; congr 1; field_simp
        rw [e2]
        have : (0 : ℝ) ≤ (k : ℝ) ^ k := by positivity
        nlinarith
      rw [Nat.factorial_succ, show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
      push_cast
      have hp : (0 : ℝ) ≤ ((k : ℝ) + 1) := by positivity
      calc ((k : ℝ) + 1) * (k.factorial : ℝ) * (2 ^ (k - 1) * 2)
          = ((k : ℝ) + 1) * 2 * ((k.factorial : ℝ) * 2 ^ (k - 1)) := by ring
        _ ≤ ((k : ℝ) + 1) * 2 * (k : ℝ) ^ k := by
            apply mul_le_mul_of_nonneg_left ih' (by positivity)
        _ ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ k := by nlinarith
        _ = ((k : ℝ) + 1) ^ (k + 1) := by ring

/-- `J_m ≥ (x/2)^m/(3 m!)` for `m ≥ 1` and `0 ≤ x ≤ 2`. -/
theorem Jn_ge (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    (x / 2) ^ m / (3 * (m.factorial : ℝ)) ≤ Jn m x := by
  have hb := (Jn_bounds m x hx0 hx2).1
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hf1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * m.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hz : x ^ 2 / 4 ≤ 1 := by nlinarith
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 4 / 3 * (x ^ 2 / 4) / ((m + 1).factorial : ℝ) ≤ 2 / 3 * (1 / (m.factorial : ℝ)) := by
    rw [hf1, div_le_iff₀ (by positivity)]
    have e : 2 / 3 * (1 / (m.factorial : ℝ)) * (((m : ℝ) + 1) * m.factorial) = 2 / 3 * ((m : ℝ) + 1) := by
      field_simp
    rw [e]; nlinarith
  have hp : 0 ≤ (x / 2) ^ m := by positivity
  calc (x / 2) ^ m / (3 * (m.factorial : ℝ)) = (x / 2) ^ m * (1 / (m.factorial : ℝ) - 2 / 3 * (1 / (m.factorial : ℝ))) := by
        field_simp; ring
    _ ≤ (x / 2) ^ m * (1 / (m.factorial : ℝ) - 4 / 3 * (x ^ 2 / 4) / ((m + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hp
    _ ≤ Jn m x := hb

/-- From `n ln(2n/x) ≤ 709.783` to `1/J_(n-1) ≤ 2^1017`. -/
theorem flag_bound (w : ℝ) (hw : 0 < w) (hw2 : w < 2) (n : ℕ) (hn : 12 ≤ n)
    (hlog : (n : ℝ) * Real.log (2 * n / w) ≤ 709783 / 1000) :
    1 / Jn (n - 1) w ≤ 2 ^ 1017 := by
  have hnr : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hJ := Jn_ge (n - 1) (by omega) w hw.le hw2.le
  have hJp := Jn_pos (n - 1) w hw hw2.le
  have hfac := factorial_le (n - 1) (by omega)
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [show 1 ≤ n by omega]; ring
  rw [hn1] at hfac
  -- `(2n/w)^n ≤ e^709.783 ≤ 2^1024 · 2`
  have hpow : (2 * n / w) ^ n ≤ 2 ^ 1025 := by
    have hpos : 0 < 2 * (n : ℝ) / w := by positivity
    have h1 : (2 * (n : ℝ) / w) ^ n = Real.exp (n * Real.log (2 * n / w)) := by
      rw [← Real.log_rpow hpos, Real.exp_log (by positivity), Real.rpow_natCast]
    rw [h1]
    have h2 : Real.exp (n * Real.log (2 * n / w)) ≤ Real.exp (709783 / 1000) := Real.exp_le_exp.mpr hlog
    have h3 : Real.exp (709783 / 1000) ≤ 2 ^ 1025 := by
      have hl2 := Real.log_two_gt_d9
      have : (709783 / 1000 : ℝ) ≤ 1025 * Real.log 2 := by linarith
      calc Real.exp (709783 / 1000) ≤ Real.exp (1025 * Real.log 2) := Real.exp_le_exp.mpr this
        _ = 2 ^ 1025 := by
          rw [show (1025 : ℝ) * Real.log 2 = Real.log (2 ^ 1025) by
            rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
    linarith
  -- `1/J_(n-1) ≤ 3 (n-1)! (2/w)^(n-1) ≤ 3 (2n/w)^(n-1)/2^(n-2)`
  have hf0 : (0 : ℝ) < (n - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hw2' : 0 < w / 2 := by positivity
  have hinv : 1 / Jn (n - 1) w ≤ 3 * ((n - 1).factorial : ℝ) * (2 / w) ^ (n - 1) := by
    rw [div_le_iff₀ hJp]
    have e : (w / 2) ^ (n - 1) / (3 * ((n - 1).factorial : ℝ)) * (3 * ((n - 1).factorial : ℝ) * (2 / w) ^ (n - 1)) = 1 := by
      rw [show (2 / w) ^ (n - 1) = ((w / 2) ^ (n - 1))⁻¹ by rw [← inv_pow, inv_div]]
      field_simp
    have := mul_le_mul_of_nonneg_right hJ (show (0 : ℝ) ≤ 3 * ((n - 1).factorial : ℝ) * (2 / w) ^ (n - 1) by
      positivity)
    linarith
  have hfac2 : ((n - 1).factorial : ℝ) ≤ ((n : ℝ) - 1) ^ (n - 1) / 2 ^ (n - 1 - 1) := by
    rw [le_div_iff₀ (by positivity)]; exact hfac
  have hmono : ((n : ℝ) - 1) ^ (n - 1) ≤ (n : ℝ) ^ (n - 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hp2 : (2 : ℝ) ^ (n - 1 - 1) ≥ 2 ^ 10 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpow' : (2 * n / w) ^ (n - 1) * (2 * n / w) = (2 * n / w) ^ n := by
    rw [← pow_succ, show n - 1 + 1 = n by omega]
  have hge : (2 : ℝ) ≤ 2 * n / w := by rw [le_div_iff₀ hw]; nlinarith
  have hcomb : (n : ℝ) ^ (n - 1) * (2 / w) ^ (n - 1) = (2 * n / w) ^ (n - 1) := by
    rw [← mul_pow]; congr 1; ring
  calc 1 / Jn (n - 1) w ≤ 3 * ((n - 1).factorial : ℝ) * (2 / w) ^ (n - 1) := hinv
    _ ≤ 3 * (((n : ℝ) - 1) ^ (n - 1) / 2 ^ (n - 1 - 1)) * (2 / w) ^ (n - 1) := by
        gcongr
    _ ≤ 3 * ((n : ℝ) ^ (n - 1) / 2 ^ 10) * (2 / w) ^ (n - 1) := by
        gcongr
    _ = 3 / 2 ^ 10 * (2 * n / w) ^ (n - 1) := by rw [← hcomb]; ring
    _ ≤ 3 / 2 ^ 10 * ((2 * n / w) ^ n / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [← hpow', le_div_iff₀ (by norm_num)]
        have : 0 ≤ (2 * n / w) ^ (n - 1) := by positivity
        nlinarith
    _ ≤ 3 / 2 ^ 10 * (2 ^ 1025 / 2) := by gcongr
    _ ≤ 2 ^ 1017 := by norm_num

theorem c709_facts : Finite (Float.ofBits 0x40862E42FEFA39EF).toBits ∧
    value (Float.ofBits 0x40862E42FEFA39EF).toBits ≤ 709782713 / 1000000 := by
  have hfin : Finite (0x40862E42FEFA39EF : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
  have h := fapprox_ofBits _ hfin
  have hv := abs_nonpos_iff.mp h.2
  have hq : value (0x40862E42FEFA39EF : UInt64) = ratOfWord 0x40862E42FEFA39EF :=
    (ratOfWord_cast _).symm
  have h1 : ratOfWord 0x40862E42FEFA39EF ≤ (709782713 / 1000000 : ℚ) := by decide +kernel
  have h1' : (ratOfWord 0x40862E42FEFA39EF : ℝ) ≤ 709782713 / 1000000 := by
    have h2 := (Rat.cast_le (K := ℝ)).mpr h1
    have e : (((709782713 / 1000000 : ℚ)) : ℝ) = 709782713 / 1000000 := by push_cast; ring
    rw [e] at h2
    exact h2
  exact ⟨h.1, by linarith⟩

set_option maxHeartbeats 2000000 in
/-- When the code skips the scaling, `n ln(2n/x) ≤ 709.783`. -/
theorem flag_log (xa : Float) (n : UInt64) (hxf : Finite xa.toBits)
    (hw : 1 / 2 ^ 30 ≤ value xa.toBits) (hw2 : value xa.toBits < 2) (hn : 2 ≤ n.toNat)
    (hn2 : n.toNat ≤ 2 ^ 31)
    (hlt : n.toFloat * Log.logWith Log.logTable Log.logTable2 ((2.0 / xa) * n.toFloat).abs <
      Float.ofBits 0x40862E42FEFA39EF) :
    (n.toNat : ℝ) * Real.log (2 * n.toNat / value xa.toBits) ≤ 709783 / 1000 := by
  set w := value xa.toBits with hwdef
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hnr : (2 : ℝ) ≤ n.toNat := by exact_mod_cast hn
  have hnr2 : (n.toNat : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hn2
  have hH := (wh_facts xa n hxf hw hw2 hn hn2).2
  have hnf := toFloat_exact n (by omega)
  have h2w : 2 / w ≤ 2 ^ 31 := by rw [div_le_iff₀ hw0]; nlinarith
  have h2w1 : 1 ≤ 2 / w := by rw [le_div_iff₀ hw0]; linarith
  -- `v = h ⊗ n`
  have hv := fapprox_mul hH hnf (2 / w) (n.toNat : ℝ) (by rw [abs_of_pos (by positivity)])
    (by rw [abs_of_nonneg (by positivity)]) ((2 / w + 2 * 𝐮 * (2 / w)) * ((n.toNat : ℝ) + 0)) le_rfl
    (by rw [hu]; nlinarith)
  set V := 2 * (n.toNat : ℝ) / w with hV
  have hVe : 2 / w * (n.toNat : ℝ) = V := by rw [hV]; ring
  rw [hVe] at hv
  have hV4 : 2 ≤ V := by rw [hV, le_div_iff₀ hw0]; nlinarith
  have hverr : |value ((2.0 / xa) * n.toFloat).toBits - V| ≤ 4 * 𝐮 * V := by
    refine le_trans hv.2 ?_
    have e : 2 * 𝐮 * (2 / w) * (n.toNat : ℝ) + 2 / w * 0 + 2 * 𝐮 * (2 / w) * 0 +
        (2 / w + 2 * 𝐮 * (2 / w)) * ((n.toNat : ℝ) + 0) / 2 ^ 53 + 1 / 2 ^ 1075 =
        2 * 𝐮 * V + V * (1 + 2 * 𝐮) / 2 ^ 53 + 1 / 2 ^ 1075 := by
      rw [hV]; ring
    rw [e, hu]
    have : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 60 * V := by nlinarith
    nlinarith
  have hvpos : 0 < value ((2.0 / xa) * n.toFloat).toBits := by
    have := (abs_le.mp hverr).1; rw [hu] at this; nlinarith
  -- `|v|` and its logarithm
  set va := ((2.0 / xa) * n.toFloat).abs with hva
  have hab := F64Bits.toBits_abs ((2.0 / xa) * n.toFloat)
  have hvaf : Finite va.toBits := by rw [hva, hab]; exact TrigSinCos.abs_finite _ hv.1
  have hvav : value va.toBits = value ((2.0 / xa) * n.toFloat).toBits := by
    rw [hva, hab, TrigSinCos.abs_value, abs_of_pos hvpos]
  have hL : FApprox (Log.logWith Log.logTable Log.logTable2 va) (Real.log (value va.toBits))
      (LogNearAll.logErr (Real.log (value va.toBits))) :=
    LogNearAll.log_near va hvaf (by rw [hvav]; exact hvpos)
  rw [hvav] at hL
  set vv := value ((2.0 / xa) * n.toFloat).toBits with hvv
  have hvv1 : 1 ≤ vv := by have := (abs_le.mp hverr).1; rw [hu] at this; nlinarith
  have hl0 : 0 ≤ Real.log vv := Real.log_nonneg hvv1
  have hlv : Real.log vv ≤ vv := by have := Real.log_le_sub_one_of_pos (by linarith : 0 < vv); linarith
  have hvvb : vv ≤ 2 ^ 63 := by
    have := (abs_le.mp hverr).2
    have : V ≤ 2 ^ 62 := by rw [hV, div_le_iff₀ hw0]; nlinarith
    rw [hu] at *; nlinarith
  unfold LogNearAll.logErr at hL
  rw [abs_of_nonneg hl0] at hL
  -- `tmp = n ⊗ L`
  have hLb : |Real.log vv| ≤ Real.log vv := le_of_eq (abs_of_nonneg hl0)
  have ht := fapprox_mul hnf hL (n.toNat : ℝ) (Real.log vv) (by rw [abs_of_nonneg (by positivity)]) hLb
    (((n.toNat : ℝ) + 0) * (Real.log vv + (6 / 5 * 𝐮 * Real.log vv + 1 / 2 ^ 59))) le_rfl (by
      rw [hu]
      have hl63 : Real.log vv ≤ 63 := by
        have h1 := Real.log_le_log (by linarith) hvvb
        rw [Real.log_pow] at h1
        have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        push_cast at h1
        nlinarith
      have : 6 / 5 * (1 / 2 ^ 53) * Real.log vv ≤ 1 := by nlinarith
      nlinarith)
  have htf := ht.1
  have hlt' := (BesselSmallJ0.flt_iff _ _ htf c709_facts.1).mp hlt
  have hC := c709_facts.2
  have hterr := (abs_le.mp ht.2).1
  -- `n ln v ≤ 709.78275`
  have hnl : (n.toNat : ℝ) * Real.log vv ≤ 70978272 / 100000 := by
    rw [hu] at hterr
    have h1 : 0 ≤ (n.toNat : ℝ) * Real.log vv := by positivity
    have h2 : (n.toNat : ℝ) * (1 / 2 ^ 59) ≤ 1 / 2 ^ 28 := by
      have := mul_le_mul_of_nonneg_right hnr2 (show (0 : ℝ) ≤ 1 / 2 ^ 59 by positivity)
      linarith [show (2 : ℝ) ^ 31 * (1 / 2 ^ 59) = 1 / 2 ^ 28 by norm_num]
    nlinarith
  -- `ln (2n/x) ≤ ln v + 3.3 u`
  have hratio : Real.log V ≤ Real.log vv + 1 / 2 ^ 50 := by
    have hvl : V * (1 - 4 * 𝐮) ≤ vv := by have := (abs_le.mp hverr).1; linarith
    have h1 : Real.log (V / vv) = Real.log V - Real.log vv :=
      Real.log_div (by linarith) (by linarith)
    have h2 := Real.log_le_sub_one_of_pos (show 0 < V / vv by positivity)
    have h3 : V / vv ≤ 1 + 1 / 2 ^ 50 := by
      rw [div_le_iff₀ (by linarith)]
      rw [hu] at hvl
      linarith
    linarith
  have := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ n.toNat by positivity)
  have hn51 : (n.toNat : ℝ) * (1 / 2 ^ 50) ≤ 1 / 2 ^ 19 := by
    have := mul_le_mul_of_nonneg_right hnr2 (show (0 : ℝ) ≤ 1 / 2 ^ 50 by positivity)
    linarith [show (2 : ℝ) ^ 31 * (1 / 2 ^ 50) = 1 / 2 ^ 19 by norm_num]
  have e : (n.toNat : ℝ) * (Real.log vv + 1 / 2 ^ 50) =
      (n.toNat : ℝ) * Real.log vv + (n.toNat : ℝ) * (1 / 2 ^ 50) := by ring
  linarith [show (70978272 : ℝ) / 100000 + 1 / 2 ^ 19 ≤ 709783 / 1000 by norm_num]

#print axioms factorial_le
#print axioms flag_bound
#print axioms flag_log

end Verified.Examples.BesselMillerLog
