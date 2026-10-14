import Verified.Examples.LgammaSinpi

/-!
`Lgamma.asSinpipid` with its two branches stated apart (`asSinpipid_abs`): within `3/256` of an
integer the polynomial `z + z³ nearPoly (z²)` gives `2^-72` relative, and elsewhere
`TgammaSinpid.asSinpid_gen` gives `1.14 · 2^-71` absolute.  `LgammaSinpi.asSinpipid_spec` merges
both into `2^-63` relative, which the reflection of the fast path cannot use next to the zeros of
`ln |Γ|` between -6 and -2, where the absolute bound is about `2^-69` relative.
-/

namespace Verified.Examples.LgammaSinpiAbs
open CodeLib.IEEE64 LeanExe.ProofKit TgammaFloor TgammaLogdTab TgammaSinpidTab TgammaSinpidRed TgammaSinpid
  LgammaSinpiNear LgammaSinpi
open Verified.Examples.Tgamma (entry roundEven)

set_option exponentiation.threshold 4096

set_option maxHeartbeats 1000000 in
/-- **`asSinpipid` near the integers and away from them**, for `x = n/2^53` with `0 < n < 2^53`:
within `2^-72` of `s = sin (π x)/π` relative, or at least `3/256` from the integers and within
`1.14 · 2^-71` of `s`, with the low part at most `2^-50` of the high part. -/
theorem asSinpipid_abs (hF : FmaSpec.FmaNearest) (hS : LgammaApprox.SinpiFact) (x : Float) (n : ℕ)
    (hn0 : 0 < n) (hn : n < 2 ^ 53) (hx : Finite x.toBits) (hv : value x.toBits = n / 2 ^ 53) :
    Finite (Lgamma.asSinpipid Lgamma.sinpiTable x).1.toBits ∧
      Finite (Lgamma.asSinpipid Lgamma.sinpiTable x).2.toBits ∧
      |value (Lgamma.asSinpipid Lgamma.sinpiTable x).2.toBits| ≤
        |value (Lgamma.asSinpipid Lgamma.sinpiTable x).1.toBits| / 2 ^ 50 ∧
      (|value (Lgamma.asSinpipid Lgamma.sinpiTable x).1.toBits +
          value (Lgamma.asSinpipid Lgamma.sinpiTable x).2.toBits -
          Real.sin (Real.pi * value x.toBits) / Real.pi| ≤
        Real.sin (Real.pi * value x.toBits) / Real.pi / 2 ^ 72 ∨
      (3 / 256 ≤ 1 / 2 - |value x.toBits - 1 / 2| ∧
        |value (Lgamma.asSinpipid Lgamma.sinpiTable x).1.toBits +
          value (Lgamma.asSinpipid Lgamma.sinpiTable x).2.toBits -
          Real.sin (Real.pi * value x.toBits) / Real.pi| ≤ 114 / 100 / 2 ^ 71)) := by
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hS
  obtain ⟨k, hk64, hky, -, -, hdb⟩ := red_spec x n hn0 hn hx hv
  obtain ⟨hbf, hbv, hzf, hzv⟩ := half_parts x n hn0 hn hx hv
  obtain ⟨R, hRd⟩ : ∃ R, R = Lgamma.asSinpipid Lgamma.sinpiTable x := ⟨_, rfl⟩
  rw [← hRd]
  have hR : R = if 64 - UInt64.ofNat k < 2 then
      nearTail (0.5 - (x - 0.5).abs) (entry Lgamma.sinpiTable 138) (entry Lgamma.sinpiTable 139)
        (entry Lgamma.sinpiTable 140) (entry Lgamma.sinpiTable 141) (entry Lgamma.sinpiTable 142)
      else Tgamma.asSinpid Lgamma.sinpiTable x := by
    rw [hRd, asSinpipid_eq]; dsimp only; rw [hky]
  have hX : |(n : ℝ) / 2 ^ 53 - 1 / 2| ≤ 1 / 2 - 1 / 2 ^ 53 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have h2 : (n : ℝ) ≤ 2 ^ 53 - 1 := by
      have h3 : n + 1 ≤ 2 ^ 53 := by omega
      have h4 : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ 53 : ℕ) : ℝ) := by exact_mod_cast h3
      push_cast at h4
      linarith
    rw [abs_le]; constructor
    · have : (1 : ℝ) / 2 ^ 53 ≤ n / 2 ^ 53 := by gcongr
      linarith
    · have : (n : ℝ) / 2 ^ 53 ≤ (2 ^ 53 - 1) / 2 ^ 53 := by gcongr
      have e : ((2 : ℝ) ^ 53 - 1) / 2 ^ 53 = 1 - 1 / 2 ^ 53 := by field_simp
      linarith
  rw [hv]
  rcases (show 63 ≤ k ∨ k ≤ 62 by omega) with hk | hk
  · -- within `3/256` of an integer
    have hc : 64 - UInt64.ofNat k < 2 := by
      rw [ix_sub k hk64, UInt64.lt_iff_toNat_lt, ofNat_toNat _ (by omega)]
      simp only [UInt64.reduceToNat]; omega
    rw [hR, ite_eq_left hc]
    have hnear := nearOK_lgamma
    unfold nearOK at hnear
    simp only [Bool.and_eq_true] at hnear
    obtain ⟨⟨⟨⟨f138, f139⟩, f140⟩, f141⟩, f142⟩ := hnear
    have ek : ∀ (k : UInt64) (i : ℕ), k.toNat = i → finW Lgamma.sinpiTable[i]! = true →
        (entry Lgamma.sinpiTable k).toBits = Lgamma.sinpiTable[i]! := by
      intro k i hki hf
      rw [entry_bits _ _ (by rw [hki]; exact finW_spec _ hf), hki]
    have e138 := ek 138 138 rfl f138
    have e139 := ek 139 139 rfl f139
    have e140 := ek 140 140 rfl f140
    have e141 := ek 141 141 rfl f141
    have e142 := ek 142 142 rfl f142
    have hZ1 : 1 / 2 - |(n : ℝ) / 2 ^ 53 - 1 / 2| ≤ 3 / 256 := by
      have := (abs_le.mp hdb).2
      have hk' : (63 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    obtain ⟨Z, hZd⟩ : ∃ v, v = 1 / 2 - |(n : ℝ) / 2 ^ 53 - 1 / 2| := ⟨_, rfl⟩
    rw [← hZd] at hzv hZ1
    have hZ0 : 1 / 2 ^ 53 ≤ Z := by rw [hZd]; linarith
    have hN := near_spec hF (0.5 - (x - 0.5).abs) (entry Lgamma.sinpiTable 138)
      (entry Lgamma.sinpiTable 139) (entry Lgamma.sinpiTable 140) (entry Lgamma.sinpiTable 141)
      (entry Lgamma.sinpiTable 142) hzf (by rw [hzv]; exact hZ0) (by rw [hzv]; exact hZ1)
      (by rw [e138]; exact finW_spec _ f138) (by rw [e139]; exact finW_spec _ f139)
      (by rw [e140]; exact finW_spec _ f140) (by rw [e141]; exact finW_spec _ f141)
      (by rw [e142]; exact finW_spec _ f142)
      (by
        have h := word_bounds Lgamma.sinpiTable[138]! (-1645 / 1000) (-1644 / 1000) (by decide +kernel)
        rw [e138]; push_cast at h; constructor <;> linarith [h.1, h.2])
      (by
        have h := word_bounds Lgamma.sinpiTable[139]! (-1 / 2 ^ 54) (1 / 2 ^ 54) (by decide +kernel)
        rw [e139, abs_le]; push_cast at h; constructor <;> linarith [h.1, h.2])
      (by
        have h := word_bounds Lgamma.sinpiTable[140]! (-82 / 100) (82 / 100) (by decide +kernel)
        rw [e140, abs_le]; push_cast at h; constructor <;> linarith [h.1, h.2])
      (by
        have h := word_bounds Lgamma.sinpiTable[141]! (-20 / 100) (20 / 100) (by decide +kernel)
        rw [e141, abs_le]; push_cast at h; constructor <;> linarith [h.1, h.2])
      (by
        have h := word_bounds Lgamma.sinpiTable[142]! (-3 / 100) (3 / 100) (by decide +kernel)
        rw [e142, abs_le]; push_cast at h; constructor <;> linarith [h.1, h.2])
    obtain ⟨hN1, hN2, hNe, hNl⟩ := hN
    refine ⟨hN1, hN2, hNl, Or.inl ?_⟩
    rw [hzv, e138, e139, e140, e141, e142] at hNe
    have hK := hT4 Z (by rw [abs_le]; constructor <;> linarith)
    rw [nearPoly_eq, abs_of_pos (by linarith : (0 : ℝ) < Z)] at hK
    rw [sin_eq_near, ← hZd]
    have hs : 2 * Z / (315 / 100) ≤ Real.sin (Real.pi * Z) / Real.pi := by
      have hZn : 0 ≤ Z := by linarith
      have h1 := Real.mul_le_sin (x := Real.pi * Z) (mul_nonneg Real.pi_pos.le hZn) (by
        have := mul_le_mul_of_nonneg_left (show Z ≤ 1 / 2 by linarith) Real.pi_pos.le
        linarith)
      rw [← mul_assoc, div_mul_cancel₀ 2 Real.pi_ne_zero] at h1
      rw [le_div_iff₀ Real.pi_pos]
      have h2 := mul_le_mul_of_nonneg_left Real.pi_lt_d2.le
        (show (0 : ℝ) ≤ 2 * Z / (315 / 100) by positivity)
      have h3 : 2 * Z / (315 / 100) * 3.15 = 2 * Z := by norm_num
      linarith
    have h2 := abs_add_le (value (nearTail (0.5 - (x - 0.5).abs) (entry Lgamma.sinpiTable 138)
        (entry Lgamma.sinpiTable 139) (entry Lgamma.sinpiTable 140) (entry Lgamma.sinpiTable 141)
        (entry Lgamma.sinpiTable 142)).1.toBits + value (nearTail (0.5 - (x - 0.5).abs)
        (entry Lgamma.sinpiTable 138) (entry Lgamma.sinpiTable 139) (entry Lgamma.sinpiTable 140)
        (entry Lgamma.sinpiTable 141) (entry Lgamma.sinpiTable 142)).2.toBits -
        (Z + Z ^ 3 * ((value Lgamma.sinpiTable[138]! + value Lgamma.sinpiTable[139]!) +
          Z ^ 2 * (value Lgamma.sinpiTable[140]! + Z ^ 2 * (value Lgamma.sinpiTable[141]! +
            Z ^ 2 * value Lgamma.sinpiTable[142]!)))))
      ((Z + Z ^ 3 * ((value Lgamma.sinpiTable[138]! + value Lgamma.sinpiTable[139]!) +
          Z ^ 2 * (value Lgamma.sinpiTable[140]! + Z ^ 2 * (value Lgamma.sinpiTable[141]! +
            Z ^ 2 * value Lgamma.sinpiTable[142]!)))) - Real.sin (Real.pi * Z) / Real.pi)
    rw [show ∀ a b c : ℝ, a - b + (b - c) = a - c from fun a b c => by ring, abs_sub_comm
      ((Z + Z ^ 3 * ((value Lgamma.sinpiTable[138]! + value Lgamma.sinpiTable[139]!) +
          Z ^ 2 * (value Lgamma.sinpiTable[140]! + Z ^ 2 * (value Lgamma.sinpiTable[141]! +
            Z ^ 2 * value Lgamma.sinpiTable[142]!)))))] at h2
    linarith
  · -- the table
    have hc : ¬ (64 - UInt64.ofNat k < 2) := by
      rw [ix_sub k hk64, UInt64.lt_iff_toNat_lt, ofNat_toNat _ (by omega)]
      simp only [UInt64.reduceToNat]; omega
    rw [hR, ite_eq_right hc]
    have hst : ∀ k ≤ 64, |value Lgamma.sinpiTable[2 * k]! + value Lgamma.sinpiTable[2 * k + 1]! -
        1 / Real.pi * Real.sin (k * Real.pi / 128)| ≤ 1 / 2 ^ 100 := by
      intro k hk
      have h := hT1 k hk
      simp only [LgammaApprox.stpi, LgammaApprox.q, Rat.cast_add, PolyBound.ratOfWord_cast] at h
      rw [one_div_mul_eq_div]; exact h
    have hs : ∀ d : ℝ, |d| ≤ 1 / 2 →
        |Real.sin (Real.pi * d / 128) - d * Ks (d ^ 2)| ≤ 1 / 2 ^ 73 * |d| := by
      intro d hd; have h := hT2 d hd; rw [sinKernel_eq] at h; exact h
    have hcc : ∀ d : ℝ, |d| ≤ 1 / 2 →
        |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * Kc (d ^ 2))| ≤ 1 / 2 ^ 76 * d ^ 2 := by
      intro d hd; have h := hT3 d hd; rw [cosKernel_eq] at h; exact h
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := asSinpid_gen hF Lgamma.sinpiTable sinTabOK_lgamma (1 / Real.pi)
      (1 / 2 ^ 100) (1 / 2 ^ 73) (1 / 2 ^ 76) hst hs hcc x n hn0 hn hx hv
    refine ⟨h1, h2, h4, Or.inr ⟨?_, ?_⟩⟩
    · have := (abs_le.mp hdb).1
      have hk' : (k : ℝ) ≤ 62 := by exact_mod_cast hk
      linarith
    rw [hv] at h3 h5
    have hy : 3 / 2 ≤ 64 - 128 * |(n : ℝ) / 2 ^ 53 - 1 / 2| := by
      have := (abs_le.mp hdb).1
      have hk' : (k : ℝ) ≤ 62 := by exact_mod_cast hk
      linarith
    rw [min_eq_left (by linarith), one_mul, one_div_mul_eq_div] at h3
    linarith [(by norm_num : (81 / 80 * (1 / 2 ^ 100) + (1 + 1 / 2 ^ 50) * (1 / 2 ^ 73 / 2 +
      1 / 2 ^ 76 / 4) + 1 / 2 ^ 71 : ℝ) + 1 / 2 ^ 1060 ≤ 114 / 100 / 2 ^ 71)]

#print axioms asSinpipid_abs

end Verified.Examples.LgammaSinpiAbs
