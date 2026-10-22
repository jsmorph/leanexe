import Library.Numerics.Float64.Log.LogMain

/-!
The error of `Log.log` on its main path as a distance, for proofs that combine the result with
further arithmetic.  `LogCoreStep.core_within` puts the sum before the final rounding within
`1.83 · 2 ^ -60` of `log X` and converts that bound to one representable step.  `core_near` stops
before the conversion: the result lies within `u |log X| + 2 ^ -59` of `log X`, with `u = 2 ^ -53`,
for every argument word that reaches `Log.logCore`.  `normal_near` and `subnormal_near` carry the
bound to `Log.log` on positive normal arguments outside `[15/16, 1 + 265/4096)` and on positive
subnormal arguments, following `LogMain.log_normal_within` and `LogMain.log_subnormal_within`.
-/

namespace Library.Numerics.Float64.Log.LogNearMain
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack LogCoreBits LogCoreFinal LogTables PolyBound
  LogCoreStep LogMain

set_option exponentiation.threshold 4096

/-- `Log.logCore` as a distance from `log X` on every argument word that reaches it. -/
theorem core_near (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616) :
    Finite (Log.logCore Log.logTable Log.logTable2 ix).toBits ∧
      |value (Log.logCore Log.logTable Log.logTable2 ix).toBits -
          Real.log (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075))| ≤
        unitRoundoff64 * |Real.log (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075))| + 1 / 2 ^ 59 := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  obtain ⟨e, n, he, hn, hz, hi, hk, hlow, hhigh, hZ1, hZ2⟩ := core_index ix E f hE1 hE2 hf hix
  have he1 : 1 ≤ e := by omega
  obtain ⟨hf1, hf2, hf3, hf4, hinvpos, -, hcinv, hlo_r, hhi_r, hchi1, hchi2, hgchi, hglc, hcloq,
    hlcq⟩ := checked_entries ⟨n, hn⟩
  obtain ⟨hc0, hlogc⟩ := log_center ⟨n, hn⟩
  simp only at hf1 hf2 hf3 hf4 hinvpos hcinv hlo_r hhi_r hchi1 hchi2 hgchi hglc hcloq hlcq hc0 hlogc
  -- the word of `z`
  have hzexp : Wasm.IEEE64.exponent (zOf ix) = e := by
    simp only [Wasm.IEEE64.exponent, hz]
    rcases he with rfl | rfl <;> omega
  have hzfrac : Wasm.IEEE64.fraction (zOf ix) = f := by
    simp only [Wasm.IEEE64.fraction, hz]
    omega
  have hzsign : Wasm.IEEE64.sign (zOf ix) = false := by
    simp only [Wasm.IEEE64.sign, hz, decide_eq_false_iff_not, not_le]
    rcases he with rfl | rfl <;> omega
  have hzf : Finite (zOf ix) := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hzexp, bne_iff_ne, ne_eq]
    omega
  have hzv : value (zOf ix) = ((2 : ℝ) ^ 52 + f) * 2 ^ (e - 1) / 2 ^ 1074 := by
    rw [F64Magnitude.normal_value _ hzsign (by omega), hzexp, hzfrac]
  have hgz : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue (zOf ix) := by
    simp only [Wasm.IEEE64.scaledValue, hzsign, Bool.false_eq_true, ite_false,
      Wasm.IEEE64.scaledMagnitude, hzexp, hzfrac]
    rcases he with rfl | rfl
    · exact ⟨(2 ^ 52 + f : Nat), by push_cast; ring⟩
    · exact ⟨(2 * (2 ^ 52 + f) : Nat), by push_cast; ring⟩
  rw [core_word ix n hn hi hzf]
  -- the table values
  have vinv : value Log.logTable[2 * n]! = (invcQ n : ℝ) := by rw [invcQ, ratOfWord_cast]
  have vlc : value Log.logTable[2 * n + 1]! = (logcQ n : ℝ) := by rw [logcQ, ratOfWord_cast]
  have vchi : value Log.logTable2[2 * n]! = (chiQ n : ℝ) := by rw [chiQ, ratOfWord_cast]
  have vclo : value Log.logTable2[2 * n + 1]! = (cloQ n : ℝ) := by rw [cloQ, ratOfWord_cast]
  have hcenter : value Log.logTable2[2 * n]! + value Log.logTable2[2 * n + 1]! =
      (centerQ n : ℝ) := by
    rw [vchi, vclo, centerQ, Rat.cast_add]
  have hinvR : 0 < value Log.logTable[2 * n]! := by
    rw [vinv]
    exact_mod_cast hinvpos
  have hcloR : |value Log.logTable2[2 * n + 1]!| ≤ 1 / 2 ^ 50 := by
    have h := rat_le_real hcloq
    rw [qabs_cast, ← vclo] at h
    exact h.trans (by norm_num)
  have hlcR : |value Log.logTable[2 * n + 1]!| ≤ 3 / 8 := by
    have h := rat_le_real hlcq
    rw [qabs_cast, ← vlc] at h
    exact h.trans (by norm_num)
  have hchiR1 : (1 : ℝ) / 2 ≤ value Log.logTable2[2 * n]! := by
    have h := rat_le_real hchi1
    rw [← vchi] at h
    exact le_trans (by norm_num) h
  have hchiR2 : value Log.logTable2[2 * n]! ≤ 3 / 2 := by
    have h := rat_le_real hchi2
    rw [← vchi] at h
    exact h.trans (by norm_num)
  have hcinvR : |(centerQ n : ℝ) * value Log.logTable[2 * n]! - 1| ≤ 1 / 2 ^ 100 := by
    have h := rat_le_real hcinv
    rw [qabs_cast] at h
    push_cast at h
    rw [vinv]
    exact h.trans (by norm_num)
  -- the reduced argument
  have hre : |(value (zOf ix) - (centerQ n : ℝ)) * value Log.logTable[2 * n]!| ≤ 39 / 10000 := by
    have h1 : ((lowQ n : ℝ) - (centerQ n : ℝ)) * value Log.logTable[2 * n]! ≤
        (value (zOf ix) - (centerQ n : ℝ)) * value Log.logTable[2 * n]! :=
      mul_le_mul_of_nonneg_right (by rw [hzv]; linarith) hinvR.le
    have h2 : (value (zOf ix) - (centerQ n : ℝ)) * value Log.logTable[2 * n]! ≤
        ((highQ n : ℝ) - (centerQ n : ℝ)) * value Log.logTable[2 * n]! :=
      mul_le_mul_of_nonneg_right (by rw [hzv]; linarith) hinvR.le
    have h3 := rat_le_real hlo_r
    have h4 := rat_le_real hhi_r
    push_cast at h3 h4
    rw [← vinv] at h3 h4
    rw [abs_le]
    constructor <;> linarith
  have hzc : |value (zOf ix) - value Log.logTable2[2 * n]!| ≤ 1 := by
    rw [abs_le, hzv]
    constructor <;> linarith
  have aR := reduced_error (zOf ix) Log.logTable2[2 * n]! Log.logTable2[2 * n + 1]!
    Log.logTable[2 * n]! hzf hf3 hf4 hf1 hgz (Int.dvd_of_emod_eq_zero hgchi)
    hzc hcloR hinvR (by rw [hcenter]; exact hre)
  rw [hcenter] at aR
  have hRb : |value (Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub (zOf ix)
      Log.logTable2[2 * n]!) Log.logTable2[2 * n + 1]!) Log.logTable[2 * n]!)| ≤ 1 / 256 := by
    have := aR.abs_le hre
    norm_num at this ⊢ <;> linarith
  -- `k`
  have hkd := kd_value (kOf ix) (E - e) (by omega) (by omega) (by rw [hk])
  have hk1075 : |E - (e : Int)| ≤ 1075 := by
    rw [abs_le]
    constructor <;> omega
  obtain ⟨hresf, hres⟩ := final_error _ (kdOf (kOf ix)).toBits Log.logTable[2 * n + 1]! (E - e)
    aR.1 hRb hkd.1 hkd.2 hk1075 hf2 hlcR (Int.dvd_of_emod_eq_zero hglc)
    (Real.log (((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (E - 1075)))
  have hT := target_close (E - e) hk1075 (value (zOf ix)) (centerQ n : ℝ) (value Log.logTable[2 * n]!)
    _ (value Log.logTable[2 * n + 1]!) (by rw [hzv]; positivity) hc0 hcinvR hre aR.2 hRb
    (by rw [vlc]; exact hlogc)
  rw [log_split E e he1 f, ← hzv] at hres ⊢
  refine ⟨hresf, ?_⟩
  have hb : (1 + unitRoundoff64) * (5 / 4 / 2 ^ 61 + (1075 / 2 ^ 91 + 1 / 2 ^ 64 +
      1 / 256 * ((17 / 32) / 2 ^ 54) + (1 / 2 ^ 60 + 1 / 2 ^ 100) / (995 / 1000))) ≤
      1 / 2 ^ 59 := by
    norm_num [hu]
  have hu0 : (0 : ℝ) ≤ 1 + unitRoundoff64 := by norm_num [hu]
  have hT' := mul_le_mul_of_nonneg_left (add_le_add_left hT (5 / 4 / 2 ^ 61)) hu0
  linarith

theorem normal_near (x : Float) (hf : Finite x.toBits)
    (hs : Wasm.IEEE64.sign x.toBits = false) (he : 1 ≤ Wasm.IEEE64.exponent x.toBits)
    (hnear : x.toBits.toNat < 4606619468846596096 ∨ 4607473789381378048 ≤ x.toBits.toNat) :
    Finite (Log.log x).toBits ∧ |value (Log.log x).toBits - Real.log (value x.toBits)| ≤
      unitRoundoff64 * |Real.log (value x.toBits)| + 1 / 2 ^ 59 := by
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hfin : Wasm.IEEE64.exponent x.toBits ≠ 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hf
    exact hf
  have hN : x.toBits.toNat = Wasm.IEEE64.exponent x.toBits * 4503599627370496 +
      Wasm.IEEE64.fraction x.toBits := by
    simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Nat.reducePow] at he hfin ⊢
    simp only [Nat.reducePow] at hlt
    omega
  have hfrac : Wasm.IEEE64.fraction x.toBits < 4503599627370496 := by
    simp only [Wasm.IEEE64.fraction]
    omega
  have hlo : 4503599627370496 ≤ x.toBits.toNat := by omega
  have hhi : x.toBits.toNat < 9218868437227405312 := by
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    simp only [Nat.reducePow] at hlt
    omega
  rw [Log.log, LogBranches.normal_selected _ _ x hlo hhi hnear, normal_form _ hs he]
  apply core_near x.toBits (Wasm.IEEE64.exponent x.toBits)
    (Wasm.IEEE64.fraction x.toBits) (by omega) (by omega) hfrac
  have : x.toBits.toNat < 18446744073709551616 := by omega
  rw [hN]
  push_cast
  omega

/-- `Log.log` on a positive subnormal argument, which the code scales by `2 ^ 52` into the main
path. -/
theorem subnormal_near (x : Float) (hlo : 0 < x.toBits.toNat)
    (hhi : x.toBits.toNat < 4503599627370496) :
    Finite (Log.log x).toBits ∧ |value (Log.log x).toBits - Real.log (value x.toBits)| ≤
      unitRoundoff64 * |Real.log (value x.toBits)| + 1 / 2 ^ 59 := by
  rw [Log.log, LogBranches.subnormal_selected _ _ x hlo hhi]
  have hcn : Wasm.IEEE64.isNaN 0x4330000000000000 = false := by decide
  have hw : (x * Float.ofBits 0x4330000000000000).toBits =
      Wasm.IEEE64.mul x.toBits 0x4330000000000000 := by
    rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits, hcn]
    rfl
  rw [hw]
  have hxe : Wasm.IEEE64.exponent x.toBits = 0 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have hxfr : Wasm.IEEE64.fraction x.toBits = x.toBits.toNat := by
    simp only [Wasm.IEEE64.fraction]
    omega
  have hxf : Finite x.toBits := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hxe]
    decide
  have hxs : Wasm.IEEE64.sign x.toBits = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    omega
  have hxm : Wasm.IEEE64.scaledMagnitude x.toBits = x.toBits.toNat * 2 ^ 0 := by
    simp only [Wasm.IEEE64.scaledMagnitude, hxe, hxfr, beq_self_eq_true, ↓reduceIte]
    ring
  have hcf : Finite (0x4330000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  have hcm : Wasm.IEEE64.scaledMagnitude (0x4330000000000000 : UInt64) = 1 * 2 ^ 1126 := by
    decide +kernel
  have hcs : Wasm.IEEE64.sign (0x4330000000000000 : UInt64) = false := by decide
  have hcv : value (0x4330000000000000 : UInt64) = 2 ^ 52 := by
    have h : PolyBound.ratOfWord 0x4330000000000000 = 2 ^ 52 := by decide +kernel
    rw [← PolyBound.ratOfWord_cast, h]
    norm_num
  obtain ⟨hwf, hwv, hwm, hws⟩ := F64ExactProduct.mul_exact_scaled x.toBits _ hxf hcf
    x.toBits.toNat 1 0 1126 hxm hcm (by omega) (by norm_num) (by norm_num)
  rw [hxs, hcs, hcv] at *
  simp only [bne_self_eq_false] at hws
  generalize hwdef : Wasm.IEEE64.mul x.toBits 0x4330000000000000 = w at hwf hwv hwm hws ⊢
  obtain ⟨e, he⟩ : ∃ e, Wasm.IEEE64.exponent w = e := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, Wasm.IEEE64.fraction w = f := ⟨_, rfl⟩
  have hflt : f < 4503599627370496 := by
    rw [← hf]
    simp only [Wasm.IEEE64.fraction]
    omega
  have hwlt : w.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hws
    exact hws
  have he1 : 1 ≤ e := by
    by_contra h0
    have he0 : e = 0 := by omega
    have hsm : Wasm.IEEE64.scaledMagnitude w = f := by
      simp only [Wasm.IEEE64.scaledMagnitude, he, hf, he0, beq_self_eq_true, ↓reduceIte]
    rw [hsm] at hwm
    have : 4503599627370496 ≤ x.toBits.toNat * 1 * 2 ^ (0 + 1126 - 1074) := by
      simp only [Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, mul_one]
      omega
    omega
  have hsm : Wasm.IEEE64.scaledMagnitude w = (2 ^ 52 + f) * 2 ^ (e - 1) := by
    have hne : (e == 0) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    simp only [Wasm.IEEE64.scaledMagnitude, he, hf, hne, Bool.false_eq_true, ↓reduceIte]
  have he52 : e ≤ 52 := by
    rw [hsm] at hwm
    simp only [Nat.reduceAdd, Nat.reduceSub, mul_one] at hwm
    have h1 : 2 ^ 52 * 2 ^ (e - 1) ≤ (2 ^ 52 + f) * 2 ^ (e - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : x.toBits.toNat * 2 ^ 52 < 2 ^ 52 * 2 ^ 52 :=
      Nat.mul_lt_mul_of_pos_right (by simp only [Nat.reducePow]; omega) (by positivity)
    have h3 : 2 ^ (e - 1) < 2 ^ 52 := by
      have : 2 ^ 52 * 2 ^ (e - 1) < 2 ^ 52 * 2 ^ 52 := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
    omega
  have hwN : w.toNat = e * 4503599627370496 + f := by
    rw [← he, ← hf]
    simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Nat.reducePow]
    simp only [Nat.reducePow] at hwlt
    omega
  have hwv' := normal_form w hws (by rw [he]; exact he1)
  rw [he, hf] at hwv'
  have hxv : value x.toBits = ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (((e : Int) - 52) - 1075) := by
    have h52 : (2 : ℝ) ^ (((e : Int) - 52) - 1075) * 2 ^ 52 = (2 : ℝ) ^ ((e : Int) - 1075) := by
      rw [← zpow_natCast (2 : ℝ) 52, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      push_cast
      ring
    have h2 : value x.toBits * 2 ^ 52 = ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ ((e : Int) - 1075) := by
      rw [← hwv, hwv']
    rw [← h52, ← mul_assoc] at h2
    exact mul_right_cancel₀ (by positivity) h2
  rw [hxv]
  have hsh : ((52 : UInt64) <<< 52).toNat = 52 * 4503599627370496 := by decide
  apply core_near (w - (52 : UInt64) <<< 52) ((e : Int) - 52) f (by omega) (by omega) hflt
  rw [UInt64.toNat_sub, hsh, hwN]
  have : e * 4503599627370496 + f < 18446744073709551616 := by omega
  push_cast
  omega

#print axioms core_near
#print axioms normal_near
#print axioms subnormal_near

end Library.Numerics.Float64.Log.LogNearMain
