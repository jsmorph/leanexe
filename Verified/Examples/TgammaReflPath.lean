import Verified.Examples.TgammaRefl9

/-!
**The path of `tgammaWith` from `-184` to `-3`** within one step of `Γ x` for every finite
non-integer `x` in that range (`reflPath_within`), from `FmaSpec.FmaNearest`,
`TgammaAsym1.LogdSpec`, `TgammaApprox.StirlingFact`, `TgammaApprox.ExpFact`,
`TgammaRefl4.SinpidSpec`, `TgammaRefl4.SubnormalGap`, and the accurate path at the same input.
-/

namespace Verified.Examples.TgammaReflPath
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaFloor TgammaRefl1
  TgammaRefl2 TgammaRefl4 TgammaRefl8 TgammaRefl9

set_option exponentiation.threshold 4096

/-- **The path below `-3`** within one step. -/
theorem reflPath_within (hF : FmaSpec.FmaNearest) (hLog : TgammaAsym1.LogdSpec)
    (hS : TgammaApprox.StirlingFact) (hE : TgammaApprox.ExpFact) (hSin : SinpidSpec)
    (hGap : SubnormalGap) (dbTab accTab : Array UInt64) (x : Float) (hx : Finite x.toBits)
    (h1 : -184 < value x.toBits) (h2 : value x.toBits < -3) (hint : ∀ n : ℤ, value x.toBits ≠ n)
    (hacc : F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (accurate accTab dbTab x).toBits) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (TgammaBranches.reflPath dbTab accTab logdTable sinpidTable expdTable asymTable x).toBits := by
  rw [refl_gen]
  dsimp only
  -- `1 - x`
  obtain ⟨hlf1, hlf2, hlsum, hllb, hl4, hl186⟩ := refl_front x hx h1 h2
  generalize fastTwoSum (-x) 1.0 = F at hlf1 hlf2 hlsum hllb hl4 hl186 ⊢
  obtain ⟨lh, ll⟩ := F
  dsimp only at hlf1 hlf2 hlsum hllb hl4 hl186 ⊢
  -- `log Γ (1 - x)`
  obtain ⟨hLf1, hLf2, hLe, hLl, hL1, hL2⟩ := TgammaAsym6.asLgammaAsym_spec hF hLog hS lh ll hlf1
    hlf2 hl4 hl186 (by rw [hlsum]; linarith) (by rw [hlsum]; linarith) hllb
  rw [hlsum] at hLe
  generalize asLgammaAsym logdTable asymTable lh ll = L at hLf1 hLf2 hLe hLl hL1 hL2 ⊢
  obtain ⟨lh2, ll2⟩ := L
  dsimp only at hLf1 hLf2 hLe hLl hL1 hL2 ⊢
  -- its exponential
  obtain ⟨E, hE15, he, hf1, hf2, hex, -, hh1, hh2⟩ :=
    TgammaExpdSpec.asExpd_spec hF hE lh2 ll2 hLf1 hLf2 hL1 hL2 hLl
  have hlow := TgammaExpLow.asExpd_low hF lh2 ll2 hLf1 hLf2 hL1 hL2 hLl
  generalize asExpd expdTable lh2 ll2 = R at he hf1 hf2 hex hh1 hh2 hlow ⊢
  obtain ⟨h, l, e⟩ := R
  dsimp only at he hf1 hf2 hex hh1 hh2 hlow ⊢
  subst he
  -- the fractional part and its sine
  obtain ⟨hff, hfv, hdf, hdv, hd0, hd1⟩ := refl_dx x hx h1 h2 hint
  obtain ⟨k, hk⟩ := grid x.toBits 1 (by norm_num)
    (by rw [abs_of_neg (show value x.toBits < 0 by linarith)]; norm_num; linarith)
  rw [show 52 - 1 = 51 from rfl] at hk
  have hj : Int.fract (value x.toBits) = ((k - ⌊value x.toBits⌋ * 2 ^ 51 : ℤ) : ℝ) / 2 ^ 51 := by
    rw [← Int.self_sub_floor, hk]
    push_cast
    field_simp
    ring
  obtain ⟨hn0, hn1, hnv⟩ := fract_grid _ _ hj hd0 hd1
  obtain ⟨hsf1, hsf2, hse, hslb⟩ := hSin (x - floorF x) _ hn0 hn1 hdf (by rw [hdv]; exact hnv)
  rw [hdv] at hse
  generalize asSinpid sinpidTable (x - floorF x) = Sn at hsf1 hsf2 hse hslb ⊢
  obtain ⟨sh, sl⟩ := Sn
  dsimp only at hsf1 hsf2 hse hslb ⊢
  have hs50 : 1 / 2 ^ 50 ≤ Real.sin (Real.pi * Int.fract (value x.toBits)) :=
    sin_lower _ (k - ⌊value x.toBits⌋ * 2 ^ 51) hj hd0 hd1
  -- the product
  have hh0 : 0 < value h.toBits := by linarith
  have hha : |value h.toBits| ≤ 5 / 2 := abs_le.mpr ⟨by linarith, hh2⟩
  have hsha : |value sh.toBits| ≤ 2 := by
    have h3 := abs_sub_abs_le_abs_sub (value sh.toBits + value sl.toBits)
      (Real.sin (Real.pi * Int.fract (value x.toBits)))
    have h4 := abs_add_le (value sh.toBits + value sl.toBits) (-value sl.toBits)
    rw [add_neg_cancel_right, abs_neg] at h4
    have h5 := Real.sin_le_one (Real.pi * Int.fract (value x.toBits))
    have h6 := Real.abs_sin_le_one (Real.pi * Int.fract (value x.toBits))
    linarith
  have hsla : |value sl.toBits| ≤ 1 := by linarith
  have hla : |value l.toBits| ≤ 1 := by linarith
  obtain ⟨hpf1, hpf2, hme, hmlow, -⟩ := mulDD_spec hF sh sl h l hsf1 hsf2 hf1 hf2
    (|value h.toBits| * |value sh.toBits|) (|value h.toBits| * |value sl.toBits|)
    (|value l.toBits| * |value sh.toBits|) (|value l.toBits| * |value sl.toBits|)
    le_rfl le_rfl le_rfl le_rfl
    (by nlinarith [abs_nonneg (value h.toBits), abs_nonneg (value sh.toBits)])
    (by nlinarith [abs_nonneg (value h.toBits), abs_nonneg (value sh.toBits),
      abs_nonneg (value l.toBits), abs_nonneg (value sl.toBits)])
  have hmA := fapprox_mul (fapprox_self h hf1) (fapprox_self sh hsf1) |value h.toBits|
    |value sh.toBits| le_rfl le_rfl (|value h.toBits| * |value sh.toBits|) (by simp)
    (by nlinarith [abs_nonneg (value h.toBits), abs_nonneg (value sh.toBits)])
  have hmap := hmA.2
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hmap
  have hph1 : (mulDD sh sl h l).1 = h * sh := rfl
  rw [← hph1] at hmap
  generalize mulDD sh sl h l = M at hpf1 hpf2 hme hmlow hmap ⊢
  obtain ⟨ph, pl⟩ := M
  dsimp only at hpf1 hpf2 hme hmlow hmap ⊢
  obtain ⟨hsh0, hph53, hph3, hpl36, hpl18, hD⟩ := refl_core1 _ _ _ _ _ _ _ hs50
    (Real.sin_le_one _) hh1 hh2 hlow hse hslb hme hmlow hmap
  -- the quotient by `π`
  obtain ⟨hpwf1, hpwf2, hp1a, hp1b, hp2, hPc⟩ := pi_words
  have hph0 : 0 < value ph.toBits := lt_of_lt_of_le (by positivity) hph53
  have hpha : |value ph.toBits| = value ph.toBits := abs_of_pos hph0
  obtain ⟨hrhf, hrlf, hR68, hrl32⟩ := pi_div hF ph pl _ _ hpf1 hpf2 hpwf1 hpwf2
    (by rw [hpha]; exact hph53) (by rw [hpha]; exact hph3) (by rw [hpha]; exact hpl36)
    (by linarith) (by linarith) (by linarith [(by norm_num : (1104 / 1000 : ℝ) / 2 ^ 53 ≤ 1 / 2 ^ 52)])
  obtain ⟨-, -, -, hrh49⟩ := pi_head ph _ hpf1 hpwf1 (by rw [hpha]; exact hph53)
    (by rw [hpha]; exact hph3) (abs_le.mpr ⟨by linarith, by linarith⟩)
  generalize 1.0 / ph * Float.ofBits 0x400921FB54442D18 = rh0 at hrhf hrlf hR68 hrl32 hrh49 ⊢
  generalize 1.0 / ph * (Float.ofBits 0x3CA1A62633145C07 - pl * rh0 -
    Fma.fma rh0 ph (-Float.ofBits 0x400921FB54442D18)) = rl0 at hrlf hR68 hrl32 ⊢
  -- the real analysis
  obtain ⟨hE1, hG0, hGt, hr1, hr2, hRT, hrhT, hbig, hGs⟩ := refl_core2 (value x.toBits)
    (value lh2.toBits + value ll2.toBits) (value h.toBits) (value l.toBits) (value sh.toBits)
    (value sl.toBits) (value ph.toBits) (value pl.toBits)
    (value (Float.ofBits 0x400921FB54442D18).toBits) (value (Float.ofBits 0x3CA1A62633145C07).toBits)
    (value rh0.toBits) (value rl0.toBits) E h2 hint hLe hex hh1 hh2 hlow hs50 hse hslb hsh0 hph53
    hpl18 hD hp1a hp2 hPc hrh49 hR68
  have hxa : |value x.toBits| ≤ 184 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hbig' : -170 ≤ value (floorF x).toBits → 1 / 2 ^ 1019 ≤ |Real.Gamma (value x.toBits)| := by
    intro h3
    rw [hfv] at h3
    exact hbig (by exact_mod_cast h3)
  have hgap' : value (floorF x).toBits < -170 →
      |Real.Gamma (value x.toBits)| ≤ 1 / 2 ^ 1022 * (1 - 1 / 2 ^ 48) ∨
        1 / 2 ^ 1022 * (1 + 1 / 2 ^ 48) ≤ |Real.Gamma (value x.toBits)| := by
    intro h3
    rw [hfv] at h3
    have h4 : (⌊value x.toBits⌋ : ℝ) ≤ -171 := by
      have : ⌊value x.toBits⌋ < -170 := by exact_mod_cast h3
      have : ⌊value x.toBits⌋ ≤ -171 := by omega
      exact_mod_cast this
    have h5 := Int.lt_floor_add_one (value x.toBits)
    exact refl_gap hGap x h1 (by linarith)
  have hP : (0 : ℝ) < 2 ^ E := by positivity
  have hGPa : |Real.Gamma (value x.toBits) * 2 ^ E| = |Real.Gamma (value x.toBits)| * 2 ^ E := by
    rw [abs_mul, abs_of_pos hP]
  -- the sign
  rw [refl_odd x hx h1 h2]
  by_cases ho : Odd ⌊value x.toBits⌋
  · rw [decide_eq_true ho, ite_eq_left rfl, ite_eq_left rfl]
    rw [ite_eq_left ho] at hGs
    have hGv : Real.Gamma (value x.toBits) * 2 ^ E = -(|Real.Gamma (value x.toBits)| * 2 ^ E) := by
      conv_lhs => rw [hGs]
      ring
    obtain ⟨hnf1, hnv1⟩ := neg_float rh0 hrhf
    obtain ⟨hnf2, hnv2⟩ := neg_float rl0 hrlf
    apply tail_within dbTab accTab x (floorF x) (-rh0) (-rl0) E _ hx hxa hff hnf1 hnf2
      hE1 hE15 hG0 hGt (by rw [hnv1, abs_neg]; exact hr1) (by rw [hnv1, abs_neg]; exact hr2)
    · rw [hnv1, hnv2, hGPa, hGv]
      rw [show -value rh0.toBits + -value rl0.toBits - -(|Real.Gamma (value x.toBits)| * 2 ^ E) =
        -(value rh0.toBits + value rl0.toBits - |Real.Gamma (value x.toBits)| * 2 ^ E) by ring,
        abs_neg]
      exact hRT
    · rw [hnv1, hGPa, hGv]
      rw [show -value rh0.toBits - -(|Real.Gamma (value x.toBits)| * 2 ^ E) =
        -(value rh0.toBits - |Real.Gamma (value x.toBits)| * 2 ^ E) by ring, abs_neg]
      exact hrhT
    · rw [hnv1, hnv2, abs_neg, abs_neg]; exact hrl32
    · exact hbig'
    · exact hgap'
    · exact hacc
  · rw [decide_eq_false ho, ite_eq_right (by simp), ite_eq_right (by simp)]
    rw [ite_eq_right ho, one_mul] at hGs
    have hGv : Real.Gamma (value x.toBits) * 2 ^ E = |Real.Gamma (value x.toBits)| * 2 ^ E := by
      conv_lhs => rw [hGs]
    apply tail_within dbTab accTab x (floorF x) rh0 rl0 E _ hx hxa hff hrhf hrlf
      hE1 hE15 hG0 hGt hr1 hr2
    · rw [hGPa, hGv]
      exact hRT
    · rw [hGPa, hGv]
      exact hrhT
    · exact hrl32
    · exact hbig'
    · exact hgap'
    · exact hacc

#print axioms reflPath_within

end Verified.Examples.TgammaReflPath
