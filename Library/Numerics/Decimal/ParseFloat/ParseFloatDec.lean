import Library.Numerics.Decimal.ParseFloat.ParseFloatRound
import Library.Numerics.Arithmetic.Uscale.UscaleDiv

/-!
`ParseFloat.decRound` gives the nearest-even encoding of a positive decimal `V · 10 ^ q`, where
`V` is the integer `D` of the kept digits, or `D + 1/2` when a dropped digit is nonzero.
`exact_path` proves the exact branch for any numerator `n` and denominator `d`: the shifts make the
quotient `⌊n · 2 ^ sn / (d · 2 ^ sd)⌋` a word of `p + 2` or `p + 3` bits, `Library.Numerics.Arithmetic.Uscale.Uscale.scaledQuot_spec`
gives it with the remainder flag, and `ParseFloatRound.roundUnits_spec` rounds it.  `decRound_spec`
adds the saturations: from `10 ^ emax` on the value lies beyond the overflow threshold, and below
`10 ^ -emin` it lies below half the least subnormal.
-/

namespace Library.Numerics.Decimal.ParseFloat.ParseFloatDec
open ParseFloat Library.Numerics.Arithmetic.Uscale.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.Shared.StrconvGrid ParseFloatRound

set_option exponentiation.threshold 4096

theorem one_limb (c : UInt64) (hc : c.toNat < 2 ^ 32) :
    Limbs (LeanExe.build 1 fun _ => c) ∧ val (LeanExe.build 1 fun _ => c) = c.toNat ∧
      (LeanExe.build 1 fun _ => c).size = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; simp [LeanExe.build] at hx; rw [hx]; exact hc
  · simp [val, LeanExe.build, valL]
  · simp [LeanExe.build]

/-- The exact branch of `decRound`: the encoding of `n / d` scaled by `2 ^ nu`. -/
theorem exact_path (f : Fmt) (p F nu : UInt64) (n d : Array UInt64)
    (hp : p.toNat = f.p) (hF : F.toNat = f.F) (hp60 : f.p ≤ 60)
    (hlim : f.F * 2 ^ (f.p - 1) < 2 ^ 63) (hnu : nu.toNat ≤ 2 ^ 40)
    (hn : Limbs n) (hd : Limbs d) (hns : n.size ≤ 2 ^ 20) (hds : d.size ≤ 2 ^ 20)
    (hn0 : 0 < val n) (hd0 : 0 < val d) :
    (roundUnits p F
      (scaledQuot n d
        (if bitLen n ≤ bitLen d + p + 2 then bitLen d + p + 2 - bitLen n else 0)
        (if bitLen n ≤ bitLen d + p + 2 then 0 else bitLen n - bitLen d - p - 2) (p + 3)).1
      (scaledQuot n d
        (if bitLen n ≤ bitLen d + p + 2 then bitLen d + p + 2 - bitLen n else 0)
        (if bitLen n ≤ bitLen d + p + 2 then 0 else bitLen n - bitLen d - p - 2) (p + 3)).2
      (0x4000000000000000 + nu +
        (if bitLen n ≤ bitLen d + p + 2 then 0 else bitLen n - bitLen d - p - 2) -
        (if bitLen n ≤ bitLen d + p + 2 then bitLen d + p + 2 - bitLen n else 0))).toNat =
      refPos f ((val n : ℝ) / val d * 2 ^ nu.toNat) := by
  have hfp := f.hp
  have hbn := bitLen_spec n hn (by omega)
  have hbd := bitLen_spec d hd (by omega)
  set bn := Nat.size (val n) with hbndef
  set bd := Nat.size (val d) with hbddef
  have hbn32 : bn ≤ 2 ^ 26 := by
    have := val_lt n hn
    have : bn ≤ 32 * n.size := Nat.size_le.mpr this
    omega
  have hbd32 : bd ≤ 2 ^ 26 := by
    have := val_lt d hd
    have : bd ≤ 32 * d.size := Nat.size_le.mpr this
    omega
  have hbn1 : 1 ≤ bn := Nat.pos_of_ne_zero (fun h => by rw [Nat.size_eq_zero] at h; omega)
  have hbd1 : 1 ≤ bd := Nat.pos_of_ne_zero (fun h => by rw [Nat.size_eq_zero] at h; omega)
  have hn1 : 2 ^ (bn - 1) ≤ val n := Nat.lt_size.mp (by omega)
  have hn2 : val n < 2 ^ bn := Nat.lt_size_self _
  have hd1 : 2 ^ (bd - 1) ≤ val d := Nat.lt_size.mp (by omega)
  have hd2 : val d < 2 ^ bd := Nat.lt_size_self _
  have hdp : (bitLen d + p + 2).toNat = bd + f.p + 2 := by
    rw [toNat_add' _ _ (by rw [toNat_add' _ _ (by rw [hbd, hp]; omega), hbd, hp]; simp; omega),
      toNat_add' _ _ (by rw [hbd, hp]; omega), hbd, hp]; rfl
  -- the shifts
  set sn : ℕ := if bn ≤ bd + f.p + 2 then bd + f.p + 2 - bn else 0 with hsndef
  set sd : ℕ := if bn ≤ bd + f.p + 2 then 0 else bn - bd - f.p - 2 with hsddef
  have hcond : (bitLen n ≤ bitLen d + p + 2) ↔ bn ≤ bd + f.p + 2 := by
    rw [UInt64.le_iff_toNat_le, hbn, hdp]
  have hsnw : (if bitLen n ≤ bitLen d + p + 2 then bitLen d + p + 2 - bitLen n else 0).toNat =
      sn := by
    by_cases hc : bn ≤ bd + f.p + 2
    · rw [if_pos (hcond.mpr hc), toNat_sub' _ _ (by rw [hdp, hbn]; exact hc), hdp, hbn, hsndef,
        if_pos hc]
    · rw [if_neg (fun h => hc (hcond.mp h)), hsndef, if_neg hc]; rfl
  have hsdw : (if bitLen n ≤ bitLen d + p + 2 then 0 else bitLen n - bitLen d - p - 2).toNat =
      sd := by
    by_cases hc : bn ≤ bd + f.p + 2
    · rw [if_pos (hcond.mpr hc), hsddef, if_pos hc]; rfl
    · rw [if_neg (fun h => hc (hcond.mp h)), hsddef, if_neg hc]
      have h1 : (bitLen n - bitLen d).toNat = bn - bd := by
        rw [toNat_sub' _ _ (by rw [hbn, hbd]; omega), hbn, hbd]
      have h2 : (bitLen n - bitLen d - p).toNat = bn - bd - f.p := by
        rw [toNat_sub' _ _ (by rw [h1, hp]; omega), h1, hp]
      rw [toNat_sub' _ _ (by rw [h2]; simp; omega), h2]; rfl
  generalize (if bitLen n ≤ bitLen d + p + 2 then bitLen d + p + 2 - bitLen n else 0) = snw
    at hsnw ⊢
  generalize (if bitLen n ≤ bitLen d + p + 2 then 0 else bitLen n - bitLen d - p - 2) = sdw
    at hsdw ⊢
  -- the quotient lies in `[2 ^ (p + 1), 2 ^ (p + 3))`
  have hb3 : (p + 3).toNat = f.p + 3 := by rw [toNat_add' _ _ (by rw [hp]; simp; omega), hp]; rfl
  have hlo : val d * 2 ^ sd * 2 ^ (f.p + 1) < val n * 2 ^ sn := by
    by_cases hc : bn ≤ bd + f.p + 2
    · have e1 : sn = bd + f.p + 2 - bn := by rw [hsndef, if_pos hc]
      have e2 : sd = 0 := by rw [hsddef, if_pos hc]
      rw [e2, pow_zero, mul_one]
      calc val d * 2 ^ (f.p + 1) < 2 ^ bd * 2 ^ (f.p + 1) :=
            Nat.mul_lt_mul_of_pos_right hd2 (by positivity)
        _ = 2 ^ (bn - 1) * 2 ^ sn := by rw [← pow_add, ← pow_add, e1]; congr 1; omega
        _ ≤ val n * 2 ^ sn := Nat.mul_le_mul_right _ hn1
    · have e1 : sn = 0 := by rw [hsndef, if_neg hc]
      have e2 : sd = bn - bd - f.p - 2 := by rw [hsddef, if_neg hc]
      rw [e1, pow_zero, mul_one]
      calc val d * 2 ^ sd * 2 ^ (f.p + 1) < 2 ^ bd * 2 ^ sd * 2 ^ (f.p + 1) := by
            apply Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hd2 (by positivity))
            positivity
        _ = 2 ^ (bn - 1) := by rw [← pow_add, ← pow_add, e2]; congr 1; omega
        _ ≤ val n := hn1
  have hhi : val n * 2 ^ sn < val d * 2 ^ sd * 2 ^ (f.p + 3) := by
    by_cases hc : bn ≤ bd + f.p + 2
    · have e1 : sn = bd + f.p + 2 - bn := by rw [hsndef, if_pos hc]
      have e2 : sd = 0 := by rw [hsddef, if_pos hc]
      rw [e2, pow_zero, mul_one]
      calc val n * 2 ^ sn < 2 ^ bn * 2 ^ sn := Nat.mul_lt_mul_of_pos_right hn2 (by positivity)
        _ = 2 ^ (bd - 1) * 2 ^ (f.p + 3) := by rw [← pow_add, ← pow_add, e1]; congr 1; omega
        _ ≤ val d * 2 ^ (f.p + 3) := Nat.mul_le_mul_right _ hd1
    · have e1 : sn = 0 := by rw [hsndef, if_neg hc]
      have e2 : sd = bn - bd - f.p - 2 := by rw [hsddef, if_neg hc]
      rw [e1, pow_zero, mul_one]
      calc val n < 2 ^ bn := hn2
        _ = 2 ^ (bd - 1) * 2 ^ sd * 2 ^ (f.p + 3) := by
            rw [← pow_add, ← pow_add, e2]; congr 1; omega
        _ ≤ val d * 2 ^ sd * 2 ^ (f.p + 3) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hd1)
  have hsn30 : sn < 2 ^ 30 := by rw [hsndef]; split_ifs <;> omega
  have hsd30 : sd < 2 ^ 30 := by rw [hsddef]; split_ifs <;> omega
  obtain ⟨q1, q2⟩ := scaledQuot_spec n d snw sdw (p + 3) hn hd (by omega) (by omega)
    (by rw [hsnw]; exact hsn30) (by rw [hsdw]; exact hsd30) (by rw [hb3]; omega) hd0
    (by rw [hsnw, hsdw, hb3]; exact hhi)
  rw [hsnw, hsdw] at q1 q2
  generalize scaledQuot n d snw sdw (p + 3) = r at q1 q2 ⊢
  set N := val n * 2 ^ sn with hN
  set M := val d * 2 ^ sd with hM
  have hM0 : 0 < M := by positivity
  have hu1 : 2 ^ (f.p + 1) ≤ r.1.toNat := by
    rw [q1]; exact (Nat.le_div_iff_mul_le hM0).mpr (by rw [mul_comm]; exact hlo.le)
  have hu2 : r.1.toNat < 2 ^ (f.p + 3) := by
    rw [q1]; exact (Nat.div_lt_iff_lt_mul hM0).mpr (by rw [mul_comm]; exact hhi)
  -- the fraction below the quotient
  set φ : ℝ := (N : ℝ) / M - r.1.toNat with hφ
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hNM : (N : ℝ) = r.1.toNat * M + (N % M : ℕ) := by
    rw [q1]; exact_mod_cast (Nat.div_add_mod' N M).symm
  have hφ' : φ = ((N % M : ℕ) : ℝ) / M := by
    rw [hφ, hNM]; field_simp; ring
  have hφ0 : 0 ≤ φ := by rw [hφ']; positivity
  have hφ1 : φ < 1 := by
    rw [hφ', div_lt_one hMr]; exact_mod_cast Nat.mod_lt N hM0
  have hst : r.2 = decide (0 < φ) := by
    rw [q2, hφ']
    by_cases h0 : N % M = 0
    · simp [h0]
    · have : (0 : ℝ) < ((N % M : ℕ) : ℝ) / M := by
        apply div_pos _ hMr; exact_mod_cast Nat.pos_of_ne_zero h0
      simp [h0, this]
  -- the biased exponent
  have hb1 : (0x4000000000000000 + nu).toNat = 2 ^ 62 + nu.toNat := by
    rw [toNat_add' _ _ (by rw [bias_toNat]; omega), bias_toNat]
  have hb2 : (0x4000000000000000 + nu + sdw).toNat = 2 ^ 62 + nu.toNat + sd := by
    rw [toNat_add' _ _ (by rw [hb1, hsdw]; omega), hb1, hsdw]
  have htb : (0x4000000000000000 + nu + sdw - snw).toNat = 2 ^ 62 + nu.toNat + sd - sn := by
    rw [toNat_sub' _ _ (by rw [hb2, hsnw]; omega), hb2, hsnw]
  have hu63 : r.1.toNat < 2 ^ 63 :=
    lt_of_lt_of_le hu2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [roundUnits_spec f p F r.1 _ r.2 φ hp hF hp60 hlim hu63 (by rw [htb]; omega)
    (by rw [htb]; omega) hφ0 hφ1 hst (fun _ => by
      have : f.p + 1 < Nat.size r.1.toNat := Nat.lt_size.mpr hu1
      omega)]
  congr 1
  have hval : (r.1.toNat : ℝ) + φ = (N : ℝ) / M := by rw [hφ]; ring
  have ht : ((2 ^ 62 + nu.toNat + sd - sn : ℕ) : ℤ) - 2 ^ 62 = (nu.toNat : ℤ) + sd - sn := by
    omega
  rw [htb, hval, ht, zpow_sub₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, zpow_natCast,
    zpow_natCast, hN, hM]
  have h1 : (0 : ℝ) < 2 ^ sn := by positivity
  have h2 : (0 : ℝ) < 2 ^ sd := by positivity
  have h3 : (0 : ℝ) < val d := by exact_mod_cast hd0
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

#print axioms exact_path

theorem decRound_eq (p F nu emax emin : UInt64) (D : Array UInt64) (kept qb : UInt64)
    (sticky : Bool) (n d : Array UInt64)
    (hn : n = if qb ≥ 0x4000000000000000 then
        mulPow10 (if sticky then mulSmall D 2 1 else D) (qb - 0x4000000000000000)
      else if sticky then mulSmall D 2 1 else D)
    (hd : d = if qb ≥ 0x4000000000000000 then LeanExe.build 1 fun _ => if sticky then 2 else 1
      else mulPow10 (LeanExe.build 1 fun _ => if sticky then 2 else 1) (0x4000000000000000 - qb)) :
    decRound p F nu emax emin D kept qb sticky =
      if kept == 0 then 0
      else if qb + kept ≥ 0x4000000000000001 + emax then F <<< (p - 1)
      else if qb + kept + emin ≤ 0x4000000000000000 then 0
      else roundUnits p F
        (scaledQuot n d
          (if bitLen n ≤ bitLen d + p + 2 then bitLen d + p + 2 - bitLen n else 0)
          (if bitLen n ≤ bitLen d + p + 2 then 0 else bitLen n - bitLen d - p - 2) (p + 3)).1
        (scaledQuot n d
          (if bitLen n ≤ bitLen d + p + 2 then bitLen d + p + 2 - bitLen n else 0)
          (if bitLen n ≤ bitLen d + p + 2 then 0 else bitLen n - bitLen d - p - 2) (p + 3)).2
        (0x4000000000000000 + nu +
          (if bitLen n ≤ bitLen d + p + 2 then 0 else bitLen n - bitLen d - p - 2) -
          (if bitLen n ≤ bitLen d + p + 2 then bitLen d + p + 2 - bitLen n else 0)) := by
  subst hn hd; rfl

/-- `decRound` gives the nearest-even encoding of `V · 10 ^ (qb - 2 ^ 62)` units of `2 ^ -nu`,
where `V` is the value of the kept digits `D`, plus one half when `sticky`. -/
theorem decRound_spec (f : Fmt) (p F nu emax emin : UInt64) (D : Array UInt64)
    (kept qb : UInt64) (sticky : Bool)
    (hp : p.toNat = f.p) (hF : F.toNat = f.F) (hp60 : f.p ≤ 60)
    (hlim : f.F * 2 ^ (f.p - 1) < 2 ^ 63)
    (hnu : nu.toNat ≤ 2000) (hemax : emax.toNat ≤ 2000) (hemin : emin.toNat ≤ 2000)
    (hD : Limbs D) (hDs : D.size ≤ 2 ^ 10) (hk : kept.toNat ≤ 2000)
    (hD1 : kept.toNat = 0 ∨ 10 ^ (kept.toNat - 1) ≤ val D) (hD2 : val D < 10 ^ kept.toNat)
    (hst : sticky = true → kept.toNat ≠ 0)
    (hqb1 : 2 ^ 62 - 2 ^ 40 ≤ qb.toNat) (hqb2 : qb.toNat ≤ 2 ^ 62 + 2 ^ 40)
    (hmax : threshold f ≤ (10 : ℝ) ^ emax.toNat * 2 ^ nu.toNat)
    (hmin : 2 * ((10 : ℝ) ^ emin.toNat)⁻¹ * 2 ^ nu.toNat ≤ 1) :
    (decRound p F nu emax emin D kept qb sticky).toNat =
      refPos f ((if sticky then (2 * (val D : ℝ) + 1) / 2 else val D) *
        (10 : ℝ) ^ ((qb.toNat : ℤ) - 2 ^ 62) * 2 ^ nu.toNat) := by
  have hfp := f.hp
  set K := kept.toNat with hKdef
  set q : ℤ := (qb.toNat : ℤ) - 2 ^ 62 with hqdef
  set V : ℝ := if sticky then (2 * (val D : ℝ) + 1) / 2 else val D with hVdef
  have h10 : (0 : ℝ) < (10 : ℝ) ^ q := zpow_pos (by norm_num) q
  have h2nu : (0 : ℝ) < 2 ^ nu.toNat := by positivity
  rw [decRound_eq p F nu emax emin D kept qb sticky _ _ rfl rfl]
  by_cases hk0 : K = 0
  · have hk0' : (kept == 0) = true := by
      simp only [beq_iff_eq]; exact UInt64.toNat_inj.mp (by rw [← hKdef, hk0]; rfl)
    rw [if_pos hk0']
    have hsf : sticky = false := by
      cases hsc : sticky
      · rfl
      · exact absurd hk0 (hst hsc)
    have hv0 : val D = 0 := by rw [hk0] at hD2; simpa using hD2
    have hV0 : V = 0 := by rw [hVdef, hsf, hv0]; simp
    rw [hV0, zero_mul, zero_mul, Library.Numerics.Decimal.Shared.StrconvOfScientific.refPos_small f 0 le_rfl (by norm_num)]
    rfl
  have hk0' : (kept == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hk0; rw [hKdef, h]; rfl
  rw [if_neg (by simp [hk0'])]
  have hDK : 10 ^ (K - 1) ≤ val D := hD1.resolve_left hk0
  have hVlo : (val D : ℝ) ≤ V := by
    rw [hVdef]; split_ifs
    · have : (0 : ℝ) ≤ val D := by positivity
      linarith
    · exact le_rfl
  have hVhi : V < (10 : ℝ) ^ K := by
    have : ((val D + 1 : ℕ) : ℝ) ≤ ((10 ^ K : ℕ) : ℝ) := by exact_mod_cast hD2
    push_cast at this
    rw [hVdef]; split_ifs <;> linarith
  have hqk : (qb + kept).toNat = qb.toNat + K := by rw [toNat_add' _ _ (by omega)]
  -- beyond the overflow threshold
  by_cases hhi : qb.toNat + K ≥ 2 ^ 62 + 1 + emax.toNat
  · rw [if_pos (UInt64.le_iff_toNat_le.mpr (by
      rw [hqk, toNat_add' _ _ (by simp; omega)]; simpa using hhi))]
    have hFs : (F <<< (p - 1)).toNat = limit f := by
      have h1' : (p - 1).toNat = f.p - 1 := by rw [toNat_sub' _ _ (by rw [hp]; simp; omega), hp]; rfl
      rw [shl_word _ _ (by rw [h1']; omega) (by
        rw [h1', hF]; have : 1 ≤ 2 ^ (f.p - 1) := Nat.one_le_two_pow; nlinarith), h1', hF]
      unfold limit half; rfl
    rw [hFs]
    symm
    unfold refPos
    rw [if_pos]
    refine le_trans hmax ?_
    apply mul_le_mul_of_nonneg_right _ h2nu.le
    calc (10 : ℝ) ^ emax.toNat = (10 : ℝ) ^ (((K - 1 : ℕ) : ℤ) + (emax.toNat - (K - 1 : ℕ) : ℤ)) := by
          rw [← zpow_natCast]; congr 1; ring
      _ ≤ (10 : ℝ) ^ (((K - 1 : ℕ) : ℤ) + q) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = ((10 ^ (K - 1) : ℕ) : ℝ) * 10 ^ q := by
          rw [zpow_add₀ (by norm_num), zpow_natCast]; push_cast; ring
      _ ≤ V * 10 ^ q := by
          apply mul_le_mul_of_nonneg_right _ h10.le
          exact le_trans (by exact_mod_cast hDK) hVlo
  rw [if_neg (fun h => hhi (by
    have := UInt64.le_iff_toNat_le.mp h
    rw [hqk, toNat_add' _ _ (by simp; omega)] at this; simpa using this))]
  -- below half the least subnormal
  have hqke : (qb + kept + emin).toNat = qb.toNat + K + emin.toNat := by
    rw [toNat_add' _ _ (by rw [hqk]; omega), hqk]
  by_cases hlo : qb.toNat + K + emin.toNat ≤ 2 ^ 62
  · rw [if_pos (UInt64.le_iff_toNat_le.mpr (by rw [hqke, bias_toNat]; exact hlo))]
    symm
    rw [Library.Numerics.Decimal.Shared.StrconvOfScientific.refPos_small f _ (by positivity)]
    · rfl
    have hval : V * 10 ^ q < ((10 : ℝ) ^ emin.toNat)⁻¹ := by
      calc V * 10 ^ q < (10 : ℝ) ^ K * 10 ^ q := mul_lt_mul_of_pos_right hVhi h10
        _ = (10 : ℝ) ^ ((K : ℤ) + q) := by rw [zpow_add₀ (by norm_num), zpow_natCast]
        _ ≤ (10 : ℝ) ^ (-(emin.toNat : ℤ)) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = ((10 : ℝ) ^ emin.toNat)⁻¹ := by rw [zpow_neg, zpow_natCast]
    calc 2 * (V * 10 ^ q * 2 ^ nu.toNat) = 2 * (V * 10 ^ q) * 2 ^ nu.toNat := by ring
      _ < 2 * ((10 : ℝ) ^ emin.toNat)⁻¹ * 2 ^ nu.toNat := by
          apply mul_lt_mul_of_pos_right _ h2nu; linarith
      _ ≤ 1 := hmin
  rw [if_neg (fun h => hlo (by
    have := UInt64.le_iff_toNat_le.mp h; rwa [hqke, bias_toNat] at this))]
  push Not at hhi hlo
  -- the exact rounding
  set c : UInt64 := if sticky then 2 else 1 with hcdef
  have hc : c.toNat = if sticky then 2 else 1 := by rw [hcdef]; split_ifs <;> rfl
  obtain ⟨c1, c2, c3⟩ := one_limb c (by rw [hc]; split_ifs <;> norm_num)
  set D' := if sticky then mulSmall D 2 1 else D with hD'def
  have hD' : Limbs D' ∧ val D' = (if sticky then 2 * val D + 1 else val D) ∧ D'.size ≤ 2 ^ 10 + 1 := by
    rw [hD'def]
    split_ifs
    · obtain ⟨a1, a2, a3⟩ := mulSmall_spec D 2 1 hD (by omega) (by decide) (by decide)
      exact ⟨a1, by rw [a2]; simp; ring, by omega⟩
    · exact ⟨hD, rfl, by omega⟩
  obtain ⟨d1, d2, d3⟩ := hD'
  have hVq : V = (val D' : ℝ) / (c.toNat : ℝ) := by
    rw [hVdef, d2, hc]; split_ifs <;> push_cast <;> ring
  have hc0 : (0 : ℝ) < c.toNat := by rw [hc]; split_ifs <;> norm_num
  have hD'0 : 0 < val D' := by
    rw [d2]; have := Nat.one_le_pow (K - 1) 10 (by norm_num); split_ifs <;> omega
  have hcpos : 0 < val (LeanExe.build 1 fun _ => c) := by rw [c2, hc]; split_ifs <;> norm_num
  by_cases hq0 : 2 ^ 62 ≤ qb.toNat
  · have hqbw : qb ≥ 0x4000000000000000 := UInt64.le_iff_toNat_le.mpr (by rw [bias_toNat]; exact hq0)
    have hk' : (qb - 0x4000000000000000).toNat = qb.toNat - 2 ^ 62 := by
      rw [toNat_sub' _ _ (by rw [bias_toNat]; exact hq0), bias_toNat]
    obtain ⟨m1, m2, m3⟩ := mulPow10_spec D' (qb - 0x4000000000000000) d1 (by omega)
      (by rw [hk']; omega)
    simp only [if_pos hqbw]
    rw [exact_path f p F nu _ _ hp hF hp60 hlim (by omega) m1 c1 (by rw [m3, hk']; omega)
      (by rw [c3]; norm_num) (by rw [m2]; exact Nat.mul_pos hD'0 (by positivity)) hcpos]
    refine congrArg (refPos f) ?_
    rw [m2, c2, hk', hVq]
    have hqe : q = ((qb.toNat - 2 ^ 62 : ℕ) : ℤ) := by rw [hqdef]; omega
    rw [hqe, zpow_natCast]
    push_cast
    field_simp
  · have hqbw : ¬ qb ≥ 0x4000000000000000 := fun h => hq0 (by
      have := UInt64.le_iff_toNat_le.mp h; rwa [bias_toNat] at this)
    have hk' : (0x4000000000000000 - qb).toNat = 2 ^ 62 - qb.toNat := by
      rw [toNat_sub' _ _ (by rw [bias_toNat]; omega), bias_toNat]
    obtain ⟨m1, m2, m3⟩ := mulPow10_spec _ (0x4000000000000000 - qb) c1 (by rw [c3]; norm_num)
      (by rw [hk']; omega)
    simp only [if_neg hqbw]
    rw [exact_path f p F nu _ _ hp hF hp60 hlim (by omega) d1 m1 (by omega)
      (by rw [m3, c3, hk']; omega) hD'0 (by rw [m2]; exact Nat.mul_pos hcpos (by positivity))]
    refine congrArg (refPos f) ?_
    rw [m2, c2, hk', hVq]
    have hqe : q = -((2 ^ 62 - qb.toNat : ℕ) : ℤ) := by rw [hqdef]; omega
    rw [hqe, zpow_neg, zpow_natCast]
    push_cast
    field_simp

#print axioms decRound_spec

end Library.Numerics.Decimal.ParseFloat.ParseFloatDec
