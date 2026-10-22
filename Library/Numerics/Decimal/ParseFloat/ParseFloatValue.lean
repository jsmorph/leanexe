import Library.Numerics.Decimal.ParseFloat.ParseFloatHexParse
import Library.Numerics.Decimal.ParseFloat.ParseFloatDec
import Library.Numerics.Decimal.Shared.StrconvTruncate

/-!
From the scanners' outputs to the value of the significand.  For the digits `L = i ++ f` with `z`
leading zeros and `kept` kept digits, `dec_parts` and `hex_parts` split the value of `L` into the
kept digits `D` times a power of the base plus the dropped digits `R`, with `R` below that power,
positive exactly when a dropped digit is nonzero, and `D` of `kept` digits with a nonzero first
digit.  `dec_value` proves that `decRound` on the scanner's outputs is the reference of
`decValue L · 10 ^ (e - nf)`: with no dropped nonzero digit the two values are equal, otherwise
`kept` is the format's count and the truncation theorem applies, and an exponent beyond `10 ^ 11`
in magnitude puts both values beyond the overflow threshold or below half the least subnormal.
`hex_value` proves the same for `roundUnits` and `hexValue L · 2 ^ (e - 4 nf)`.
-/

namespace Library.Numerics.Decimal.ParseFloat.ParseFloatValue
open ParseFloat Library.Numerics.Arithmetic.Uscale.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.Shared.StrconvGrid Library.Numerics.Decimal.Shared.StrconvGrammar Library.Numerics.Decimal.Shared.StrconvDecode ParseFloatRound
  ParseFloatScan ParseFloatDigits ParseFloatDec StrconvOfScientific

set_option exponentiation.threshold 4096

/-! ### The significant digits -/

theorem zeros_take (L : List UInt8) :
    ∀ b ∈ L.take (L.takeWhile (· == 0x30)).length, b = 0x30 := by
  have hp : L.takeWhile (· == (0x30 : UInt8)) = L.take (L.takeWhile (· == 0x30)).length :=
    List.prefix_iff_eq_take.mp (List.takeWhile_prefix _)
  rw [← hp]
  intro b hb
  have := takeWhile_all (· == (0x30 : UInt8)) L b hb
  simpa using this

theorem first_digit (L : List UInt8) (h : (L.takeWhile (· == 0x30)).length < L.length) :
    byteAt L (L.takeWhile (· == 0x30)).length ≠ 0x30 := by
  have := takeWhile_stop (· == (0x30 : UInt8)) L h
  simpa using this

theorem rest_zero (L : List UInt8) (a : ℕ) :
    (∀ b ∈ L.drop a, b = 0x30) ↔ ∀ k, a ≤ k → k < L.length → byteAt L k = 0x30 := by
  constructor
  · intro h k hk1 hk2
    have e : byteAt L k = byteAt (L.drop a) (k - a) := by rw [byteAt_drop]; congr 1; omega
    rw [e]; exact h _ (byteAt_mem _ _ (by rw [List.length_drop]; omega))
  · intro h b hb
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    rw [← byteAt_lt _ _ hj, byteAt_drop]
    rw [List.length_drop] at hj
    exact h _ (by omega) (by omega)

/-- The common facts of both splits: lengths and the first kept digit. -/
theorem split_facts (L : List UInt8) (K z kept : ℕ)
    (hz : z = (L.takeWhile (· == 0x30)).length) (hkept : kept = min (L.length - z) K) :
    z ≤ L.length ∧ L.drop z = (L.drop z).take kept ++ L.drop (z + kept) ∧
      (L.drop (z + kept)).length = L.length - z - kept ∧ ((L.drop z).take kept).length = kept ∧
      (kept ≠ 0 → ∃ k', kept = k' + 1 ∧ byteAt L z ≠ 0x30 ∧
        (L.drop z).take kept = byteAt L z :: (L.drop (z + 1)).take k' ∧
        ((L.drop (z + 1)).take k').length = k') := by
  have hzL : z ≤ L.length := by rw [hz]; exact (List.takeWhile_prefix _).length_le
  refine ⟨hzL, ?_, by rw [List.length_drop]; omega, by rw [List.length_take, List.length_drop]; omega,
    ?_⟩
  · rw [← List.drop_drop, List.take_append_drop]
  · intro hk0
    obtain ⟨k', hk'⟩ : ∃ k', kept = k' + 1 := ⟨kept - 1, by omega⟩
    have hzlt : z < L.length := by omega
    have hcons : L.drop z = byteAt L z :: L.drop (z + 1) := by
      rw [byteAt_lt _ _ hzlt]; exact List.drop_eq_getElem_cons hzlt
    refine ⟨k', hk', ?_, by rw [hcons, hk', List.take_succ_cons], ?_⟩
    · have := first_digit L (by rw [← hz]; exact hzlt); rwa [← hz] at this
    · rw [List.length_take, List.length_drop]; omega

theorem dec_parts (L : List UInt8) (hL : ∀ b ∈ L, isDigit b = true) (K z kept : ℕ)
    (hz : z = (L.takeWhile (· == 0x30)).length) (hkept : kept = min (L.length - z) K) :
    decValue L = decValue ((L.drop z).take kept) * 10 ^ (L.length - z - kept) +
        decValue (L.drop (z + kept)) ∧
      decValue (L.drop (z + kept)) < 10 ^ (L.length - z - kept) ∧
      (0 < decValue (L.drop (z + kept)) ↔
        ∃ k, z + kept ≤ k ∧ k < L.length ∧ byteAt L k ≠ 0x30) ∧
      decValue ((L.drop z).take kept) < 10 ^ kept ∧
      (kept = 0 ∨ 10 ^ (kept - 1) ≤ decValue ((L.drop z).take kept)) := by
  obtain ⟨hzL, hsplit, hRlen, hTlen, hfirst⟩ := split_facts L K z kept hz hkept
  have h0 : decValue L = decValue (L.drop z) :=
    decValue_zeros L z (by rw [hz]; exact zeros_take L)
  have hTd : ∀ b ∈ (L.drop z).take kept, isDigit b = true :=
    fun b hb => hL b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  have hRd : ∀ b ∈ L.drop (z + kept), isDigit b = true := fun b hb => hL b (List.mem_of_mem_drop hb)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]; conv_lhs => rw [hsplit]
    rw [decValue_append, hRlen]
  · have := decValue_lt _ hRd; rwa [hRlen] at this
  · rw [Nat.pos_iff_ne_zero, Ne, decValue_eq_zero _ hRd, rest_zero]
    constructor
    · intro h; by_contra hc; push_neg at hc; exact h (fun k h1 h2 => hc k h1 h2)
    · rintro ⟨k, h1, h2, h3⟩ h; exact h3 (h k h1 h2)
  · have := decValue_lt _ hTd; rwa [hTlen] at this
  · by_cases hk0 : kept = 0
    · exact Or.inl hk0
    right
    obtain ⟨k', hk', hb, htake, hlen⟩ := hfirst hk0
    rw [htake, hk', Nat.add_sub_cancel]
    have hge := decValue_ge (byteAt L z) ((L.drop (z + 1)).take k') (by
      intro c hc
      rcases List.mem_cons.mp hc with h | h
      · rw [h]; exact hL _ (byteAt_mem _ _ (by omega))
      · exact hL c (List.mem_of_mem_drop (List.mem_of_mem_take h))) hb
    rwa [hlen] at hge

theorem hex_parts (L : List UInt8) (hL : ∀ b ∈ L, isHexDigit b = true) (K z kept : ℕ)
    (hz : z = (L.takeWhile (· == 0x30)).length) (hkept : kept = min (L.length - z) K) :
    hexValue L = hexValue ((L.drop z).take kept) * 16 ^ (L.length - z - kept) +
        hexValue (L.drop (z + kept)) ∧
      hexValue (L.drop (z + kept)) < 16 ^ (L.length - z - kept) ∧
      (0 < hexValue (L.drop (z + kept)) ↔
        ∃ k, z + kept ≤ k ∧ k < L.length ∧ byteAt L k ≠ 0x30) ∧
      hexValue ((L.drop z).take kept) < 16 ^ kept ∧
      (kept = 0 ∨ 16 ^ (kept - 1) ≤ hexValue ((L.drop z).take kept)) := by
  obtain ⟨hzL, hsplit, hRlen, hTlen, hfirst⟩ := split_facts L K z kept hz hkept
  have h0 : hexValue L = hexValue (L.drop z) :=
    hexValue_zeros L z (by rw [hz]; exact zeros_take L)
  have hTd : ∀ b ∈ (L.drop z).take kept, isHexDigit b = true :=
    fun b hb => hL b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  have hRd : ∀ b ∈ L.drop (z + kept), isHexDigit b = true :=
    fun b hb => hL b (List.mem_of_mem_drop hb)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]; conv_lhs => rw [hsplit]
    rw [hexValue_append, hRlen]
  · have := hexValue_lt _ hRd; rwa [hRlen] at this
  · rw [Nat.pos_iff_ne_zero, Ne, hexValue_eq_zero _ hRd, rest_zero]
    constructor
    · intro h; by_contra hc; push_neg at hc; exact h (fun k h1 h2 => hc k h1 h2)
    · rintro ⟨k, h1, h2, h3⟩ h; exact h3 (h k h1 h2)
  · have := hexValue_lt _ hTd; rwa [hTlen] at this
  · by_cases hk0 : kept = 0
    · exact Or.inl hk0
    right
    obtain ⟨k', hk', hb, htake, hlen⟩ := hfirst hk0
    rw [htake, hk', Nat.add_sub_cancel]
    have hge := hexValue_ge (byteAt L z) ((L.drop (z + 1)).take k') (by
      intro c hc
      rcases List.mem_cons.mp hc with h | h
      · rw [h]; exact hL _ (byteAt_mem _ _ (by omega))
      · exact hL c (List.mem_of_mem_drop (List.mem_of_mem_take h))) hb
    rwa [hlen] at hge

theorem min_lt (a K : ℕ) (h : min a K < a) : min a K = K := by omega

/-! ### Values beyond the range -/

theorem big_value (f : Fmt) (b : ℝ) (hb : 1 ≤ b) (nu emax : ℕ)
    (hmax : threshold f ≤ b ^ emax * 2 ^ nu) (V : ℝ) (hV : 1 ≤ V) (X : ℤ) (hX : (emax : ℤ) ≤ X) :
    threshold f ≤ V * b ^ X * 2 ^ nu := by
  have h1 : b ^ emax ≤ b ^ X := by rw [← zpow_natCast]; exact zpow_le_zpow_right₀ hb hX
  have h2 : (0 : ℝ) < b ^ X := zpow_pos (by linarith) X
  have h3 : (0 : ℝ) < 2 ^ nu := by positivity
  calc threshold f ≤ b ^ emax * 2 ^ nu := hmax
    _ ≤ b ^ X * 2 ^ nu := mul_le_mul_of_nonneg_right h1 h3.le
    _ ≤ V * b ^ X * 2 ^ nu := mul_le_mul_of_nonneg_right (le_mul_of_one_le_left h2.le hV) h3.le

theorem small_value (b : ℝ) (hb : 1 ≤ b) (nu emin : ℕ) (hmin : 2 * (b ^ emin)⁻¹ * 2 ^ nu ≤ 1)
    (V : ℝ) (M : ℕ) (hV : V < b ^ M) (X : ℤ) (hX : (M : ℤ) + X ≤ -(emin : ℤ)) :
    2 * (V * b ^ X * 2 ^ nu) < 1 := by
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; norm_num at hb
  have h2 : (0 : ℝ) < b ^ X := zpow_pos (by linarith) X
  have h3 : (0 : ℝ) < 2 ^ nu := by positivity
  have h4 : V * b ^ X < b ^ M * b ^ X := mul_lt_mul_of_pos_right hV h2
  have h5 : b ^ M * b ^ X ≤ (b ^ emin)⁻¹ := by
    rw [← zpow_natCast b M, ← zpow_add₀ hb0, ← zpow_natCast b emin, ← zpow_neg]
    exact zpow_le_zpow_right₀ hb hX
  have h6 := mul_lt_mul_of_pos_right (lt_of_lt_of_le h4 h5) h3
  calc 2 * (V * b ^ X * 2 ^ nu) < 2 * ((b ^ emin)⁻¹ * 2 ^ nu) := by linarith
    _ = 2 * (b ^ emin)⁻¹ * 2 ^ nu := by ring
    _ ≤ 1 := hmin

/-! ### Decimals -/

/-- `decRound` on the scanner's outputs is the reference of `decValue L · 10 ^ (e - nf)`. -/
theorem dec_value (f : Fmt) (p F nu emax emin : UInt64) (K : ℕ)
    (hp : p.toNat = f.p) (hF : F.toNat = f.F) (hp60 : f.p ≤ 60)
    (hlim : f.F * 2 ^ (f.p - 1) < 2 ^ 63)
    (hnu : nu.toNat ≤ 2000) (hemax : emax.toNat ≤ 2000) (hemin : emin.toNat ≤ 2000)
    (hmax : threshold f ≤ (10 : ℝ) ^ emax.toNat * 2 ^ nu.toNat)
    (hmin : 2 * ((10 : ℝ) ^ emin.toNat)⁻¹ * 2 ^ nu.toNat ≤ 1)
    (hK : 1 ≤ K) (hK2 : K ≤ 2000)
    (htr : ∀ D : ℕ, 10 ^ (K - 1) ≤ D → ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ j : ℤ,
      refPos f ((D + θ) * 10 ^ j * 2 ^ nu.toNat) = refPos f ((D + 1 / 2) * 10 ^ j * 2 ^ nu.toNat))
    (L : List UInt8) (hL : ∀ b ∈ L, isDigit b = true) (hLlen : L.length < 2 ^ 32)
    (nf : ℕ) (hnf : nf ≤ L.length) (e : ℤ)
    (D : Array UInt64) (kept qb : UInt64) (sticky : Bool) (hD : Limbs D)
    (hval : val D = decValue ((L.drop (L.takeWhile (· == 0x30)).length).take
      (min (L.length - (L.takeWhile (· == 0x30)).length) K)))
    (hsize : D.size = (min (L.length - (L.takeWhile (· == 0x30)).length) K + 8) / 9)
    (hkept : kept.toNat = min (L.length - (L.takeWhile (· == 0x30)).length) K)
    (hqb : (qb.toNat : ℤ) = 2 ^ 62 + satE e - nf +
      ((L.length - (L.takeWhile (· == 0x30)).length -
        min (L.length - (L.takeWhile (· == 0x30)).length) K : ℕ)))
    (hst : sticky = true ↔ ∃ k, (L.takeWhile (· == 0x30)).length +
      min (L.length - (L.takeWhile (· == 0x30)).length) K ≤ k ∧ k < L.length ∧
        byteAt L k ≠ 0x30) :
    (decRound p F nu emax emin D kept qb sticky).toNat =
      refPos f ((decValue L : ℝ) * 10 ^ (e - nf) * 2 ^ nu.toNat) := by
  generalize hz : (L.takeWhile (· == 0x30)).length = z at hval hsize hkept hqb hst
  generalize hkp : min (L.length - z) K = kp at hval hsize hkept hqb hst
  obtain ⟨hV, hRlt, hRpos, hDlt, hDge⟩ := dec_parts L hL K z kp hz.symm hkp.symm
  generalize hR : decValue (L.drop (z + kp)) = R at hV hRlt hRpos
  generalize hd : L.length - z - kp = d at hV hRlt hqb
  have hzL : z ≤ L.length := by rw [← hz]; exact (List.takeWhile_prefix _).length_le
  have hkp1 : kp ≤ L.length - z := by rw [← hkp]; exact min_le_left _ _
  have hkp2 : kp ≤ K := by rw [← hkp]; exact min_le_right _ _
  have hkp3 : kp < L.length - z → kp = K := by intro h; rw [← hkp] at h ⊢; exact min_lt _ _ h
  have hV' : decValue L = val D * 10 ^ d + R := by rw [hV, hval]
  have hdpos : sticky = true → 0 < d := by
    intro h; obtain ⟨k, h1, h2, _⟩ := hst.mp h; omega
  have hkpK : sticky = true → kp = K := by
    intro h; have := hdpos h; exact hkp3 (Nat.lt_of_sub_pos (by rw [hd]; exact this))
  have hsat1 : -(10 : ℤ) ^ 11 ≤ satE e := by unfold satE; omega
  have hsat2 : satE e ≤ 10 ^ 11 := by unfold satE; omega
  rw [decRound_spec f p F nu emax emin D kept qb sticky hp hF hp60 hlim hnu hemax hemin hD
    (by rw [hsize]; omega) (by rw [hkept]; omega) (by rw [hkept, hval]; exact hDge)
    (by rw [hkept, hval]; exact hDlt) (by intro h; rw [hkept, hkpK h]; omega)
    (by omega) (by omega) hmax hmin]
  have hDv : (val D : ℝ) < 10 ^ kp := by rw [hval]; exact_mod_cast hDlt
  have hDv1 : (val D : ℝ) + 1 ≤ 10 ^ kp := by rw [hval]; exact_mod_cast hDlt
  have hD'0 : (0 : ℝ) ≤ (if sticky then (2 * (val D : ℝ) + 1) / 2 else val D) := by
    split_ifs <;> positivity
  have hD'lt : (if sticky then (2 * (val D : ℝ) + 1) / 2 else val D) < 10 ^ kp := by
    split_ifs
    · linarith
    · exact hDv
  have hpos : ∀ X : ℤ, (0 : ℝ) ≤ (if sticky then (2 * (val D : ℝ) + 1) / 2 else val D) *
      10 ^ X * 2 ^ nu.toNat := fun X =>
    mul_nonneg (mul_nonneg hD'0 (zpow_pos (by norm_num) X).le) (by positivity)
  have hreal : (decValue L : ℝ) * 10 ^ (e - nf) =
      ((val D : ℝ) + (R : ℝ) / 10 ^ d) * 10 ^ (e - nf + d) := by
    rw [hV']
    push_cast
    rw [zpow_add₀ (by norm_num), zpow_natCast]
    have : (10 : ℝ) ^ d ≠ 0 := by positivity
    field_simp <;> ring
  by_cases hlo : e < -(10 ^ 11)
  · have hs : satE e = -(10 ^ 11) := by unfold satE; omega
    have hA : refPos f ((if sticky then (2 * (val D : ℝ) + 1) / 2 else val D) *
        10 ^ ((qb.toNat : ℤ) - 2 ^ 62) * 2 ^ nu.toNat) = 0 :=
      refPos_small f _ (hpos _)
        (small_value 10 (by norm_num) nu.toNat emin.toNat hmin _ kp hD'lt _ (by omega))
    have hB : refPos f ((decValue L : ℝ) * 10 ^ (e - nf) * 2 ^ nu.toNat) = 0 :=
      refPos_small f _ (by positivity)
        (small_value 10 (by norm_num) nu.toNat emin.toNat hmin _ L.length
          (by exact_mod_cast decValue_lt L hL) _ (by omega))
    rw [hA, hB]
  by_cases hhi : 10 ^ 11 < e
  · have hs : satE e = 10 ^ 11 := by unfold satE; omega
    by_cases hz0 : decValue L = 0
    · have hR0 : R = 0 := by omega
      have hD0 : val D = 0 := by
        rcases Nat.mul_eq_zero.mp (show val D * 10 ^ d = 0 by omega) with h | h
        · exact h
        · exact absurd h (pow_ne_zero _ (by norm_num))
      have hs0 : sticky = false := by
        cases hsc : sticky
        · rfl
        · have := hRpos.mpr (hst.mp hsc); omega
      simp only [hs0, Bool.false_eq_true, ite_false, hD0, hz0, Nat.cast_zero, zero_mul]
    have hV1 : (1 : ℝ) ≤ decValue L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz0
    have hD1 : (1 : ℝ) ≤ (if sticky then (2 * (val D : ℝ) + 1) / 2 else val D) := by
      cases hsc : sticky
      · have hR0 : R = 0 := by
          by_contra h; have := hst.mpr (hRpos.mp (Nat.pos_of_ne_zero h)); rw [hsc] at this
          exact absurd this (by decide)
        have : val D ≠ 0 := by intro h; apply hz0; rw [hV', h, hR0]; simp
        simp only [Bool.false_eq_true, ite_false]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
      · simp only [ite_true]
        rcases hDge with h1 | h1
        · have := hkpK hsc; omega
        · have : (1 : ℝ) ≤ val D := by
            rw [hval]; exact_mod_cast le_trans (Nat.one_le_pow _ _ (by norm_num)) h1
          linarith
    rw [refPos_large f _ (big_value f 10 (by norm_num) nu.toNat emax.toNat hmax _ hD1 _ (by omega)),
      refPos_large f _ (big_value f 10 (by norm_num) nu.toNat emax.toNat hmax _ hV1 _ (by omega))]
  have hs : satE e = e := by unfold satE; omega
  have hq : (qb.toNat : ℤ) - 2 ^ 62 = e - nf + d := by omega
  rw [hq, hreal]
  cases hsc : sticky
  · have hR0 : R = 0 := by
      by_contra h; have := hst.mpr (hRpos.mp (Nat.pos_of_ne_zero h)); rw [hsc] at this
      exact absurd this (by decide)
    simp only [Bool.false_eq_true, ite_false, hR0, Nat.cast_zero, zero_div, add_zero]
  · have hRp : 0 < R := hRpos.mpr (hst.mp hsc)
    have hDge' : 10 ^ (K - 1) ≤ val D := by
      rw [hval]
      rcases hDge with h | h
      · have := hkpK hsc; omega
      · calc 10 ^ (K - 1) = 10 ^ (kp - 1) := by rw [hkpK hsc]
          _ ≤ _ := h
    have hθ0 : (0 : ℝ) < (R : ℝ) / 10 ^ d := div_pos (by exact_mod_cast hRp) (by positivity)
    have hθ1 : (R : ℝ) / 10 ^ d < 1 := by
      rw [div_lt_one (by positivity)]; exact_mod_cast hRlt
    simp only [ite_true]
    rw [htr (val D) hDge' _ hθ0 hθ1 (e - nf + d)]
    refine congrArg (refPos f) ?_
    ring

/-! ### Hexadecimal significands -/

/-- `roundUnits` on the scanner's outputs is the reference of `hexValue L · 2 ^ (e - 4 nf)`. -/
theorem hex_value (f : Fmt) (p F : UInt64) (nu emax emin : ℕ)
    (hp : p.toNat = f.p) (hF : F.toNat = f.F) (hp55 : f.p ≤ 55)
    (hlim : f.F * 2 ^ (f.p - 1) < 2 ^ 63)
    (hnu : nu ≤ 2000) (hemax : emax ≤ 2000) (hemin : emin ≤ 2000)
    (hmax : threshold f ≤ (2 : ℝ) ^ emax * 2 ^ nu)
    (hmin : 2 * ((2 : ℝ) ^ emin)⁻¹ * 2 ^ nu ≤ 1)
    (L : List UInt8) (hL : ∀ b ∈ L, isHexDigit b = true) (hLlen : L.length < 2 ^ 32)
    (nf : ℕ) (hnf : nf ≤ L.length) (e : ℤ) (u tb : UInt64) (sticky : Bool)
    (hu : u.toNat = hexValue ((L.drop (L.takeWhile (· == 0x30)).length).take
      (min (L.length - (L.takeWhile (· == 0x30)).length) 15)))
    (hst : sticky = true ↔ ∃ k, (L.takeWhile (· == 0x30)).length +
      min (L.length - (L.takeWhile (· == 0x30)).length) 15 ≤ k ∧ k < L.length ∧
        byteAt L k ≠ 0x30)
    (htb : (tb.toNat : ℤ) = 2 ^ 62 + satE e - 4 * nf +
      4 * ((L.length - (L.takeWhile (· == 0x30)).length -
        min (L.length - (L.takeWhile (· == 0x30)).length) 15 : ℕ)) + nu) :
    (roundUnits p F u sticky tb).toNat =
      refPos f ((hexValue L : ℝ) * 2 ^ (e - 4 * nf) * 2 ^ nu) := by
  generalize hz : (L.takeWhile (· == 0x30)).length = z at hu hst htb
  generalize hkp : min (L.length - z) 15 = kp at hu hst htb
  obtain ⟨hV, hRlt, hRpos, hUlt, hUge⟩ := hex_parts L hL 15 z kp hz.symm hkp.symm
  generalize hR : hexValue (L.drop (z + kp)) = R at hV hRlt hRpos
  generalize hd : L.length - z - kp = d at hV hRlt htb
  have hzL : z ≤ L.length := by rw [← hz]; exact (List.takeWhile_prefix _).length_le
  have hkp1 : kp ≤ L.length - z := by rw [← hkp]; exact min_le_left _ _
  have hkp2 : kp ≤ 15 := by rw [← hkp]; exact min_le_right _ _
  have hkp3 : kp < L.length - z → kp = 15 := by intro h; rw [← hkp] at h ⊢; exact min_lt _ _ h
  have hV' : hexValue L = u.toNat * 16 ^ d + R := by rw [hV, hu]
  have hsat1 : -(10 : ℤ) ^ 11 ≤ satE e := by unfold satE; omega
  have hsat2 : satE e ≤ 10 ^ 11 := by unfold satE; omega
  have h16 : (16 : ℝ) ^ d = 2 ^ (4 * d) := by rw [pow_mul]; norm_num
  have hd0 : (0 : ℝ) < 16 ^ d := by positivity
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = (R : ℝ) / 16 ^ d := ⟨_, rfl⟩
  have hφ0 : 0 ≤ φ := by rw [hφ]; positivity
  have hφ1 : φ < 1 := by rw [hφ, div_lt_one hd0]; exact_mod_cast hRlt
  have hR0 : sticky = false → R = 0 := by
    intro hsc
    by_contra h; have := hst.mpr (hRpos.mp (Nat.pos_of_ne_zero h)); rw [hsc] at this
    exact absurd this (by decide)
  have hs : sticky = decide (0 < φ) := by
    rw [hφ]
    cases hsc : sticky
    · symm; rw [decide_eq_false_iff_not, not_lt, hR0 hsc]; simp
    · symm; rw [decide_eq_true_iff]
      have := hRpos.mpr (hst.mp hsc)
      exact div_pos (by exact_mod_cast this) hd0
  have hukp : u.toNat < 16 ^ 15 := by
    rw [hu]; exact lt_of_lt_of_le hUlt (Nat.pow_le_pow_right (by norm_num) hkp2)
  have hsb : sticky = true → f.p + 2 ≤ Nat.size u.toNat := by
    intro h
    obtain ⟨k, h1, h2, _⟩ := hst.mp h
    have h3 : kp + z < L.length := by rw [Nat.add_comm]; exact lt_of_le_of_lt h1 h2
    have hkp15 : kp = 15 := hkp3 (Nat.lt_sub_of_add_lt h3)
    have hge : 2 ^ 56 ≤ u.toNat := by
      rw [hu]
      rcases hUge with h0 | h0
      · omega
      · have : 2 ^ 56 ≤ 16 ^ (kp - 1) := by rw [hkp15]; norm_num
        omega
    have : ¬ Nat.size u.toNat ≤ 56 := by
      rw [Nat.size_le]; omega
    omega
  rw [roundUnits_spec f p F u tb sticky φ hp hF (by omega) hlim
    (lt_of_lt_of_le hukp (by norm_num)) (by omega) (by omega) hφ0 hφ1 hs hsb]
  have hu0 : (0 : ℝ) ≤ (u.toNat : ℝ) + φ := add_nonneg (Nat.cast_nonneg _) hφ0
  have hreal : (hexValue L : ℝ) * 2 ^ (e - 4 * nf) * 2 ^ nu =
      ((u.toNat : ℝ) + φ) * 2 ^ (e - 4 * nf + 4 * d) * 2 ^ nu := by
    rw [hV', hφ]
    push_cast
    rw [zpow_add₀ (by norm_num), show ((4 : ℤ) * (d : ℤ)) = ((4 * d : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, ← h16]
    field_simp <;> ring
  have hT : (tb.toNat : ℤ) - 2 ^ 62 = (satE e - 4 * nf + 4 * d) + nu := by omega
  rw [hT, zpow_add₀ two_ne_zero, zpow_natCast, ← mul_assoc, hreal]
  have hpos : ∀ X : ℤ, (0 : ℝ) ≤ ((u.toNat : ℝ) + φ) * 2 ^ X * 2 ^ nu := fun X =>
    mul_nonneg (mul_nonneg hu0 (zpow_pos (by norm_num) X).le) (by positivity)
  by_cases hlo : e < -(10 ^ 11)
  · have hs' : satE e = -(10 ^ 11) := by unfold satE; omega
    have hU1 : (u.toNat : ℝ) + φ < 2 ^ (4 * kp) := by
      have : (u.toNat : ℝ) + 1 ≤ 16 ^ kp := by rw [hu]; exact_mod_cast hUlt
      rw [pow_mul]; norm_num; linarith
    have hH : (hexValue L : ℝ) < 2 ^ (4 * L.length) := by
      rw [pow_mul]; norm_num; exact_mod_cast hexValue_lt L hL
    have hA : refPos f (((u.toNat : ℝ) + φ) * 2 ^ (satE e - 4 * nf + 4 * d) * 2 ^ nu) = 0 :=
      refPos_small f _ (hpos _) (small_value 2 (by norm_num) nu emin hmin _ (4 * kp) hU1 _
        (by omega))
    have hB : refPos f (((u.toNat : ℝ) + φ) * 2 ^ (e - 4 * nf + 4 * d) * 2 ^ nu) = 0 := by
      rw [← hreal]
      exact refPos_small f _ (by positivity) (small_value 2 (by norm_num) nu emin hmin _
        (4 * L.length) hH (e - 4 * nf) (by omega))
    rw [hA, hB]
  by_cases hhi : 10 ^ 11 < e
  · have hs' : satE e = 10 ^ 11 := by unfold satE; omega
    by_cases hz0 : hexValue L = 0
    · have hRz : R = 0 := by omega
      have hU0 : u.toNat = 0 := by
        rcases Nat.mul_eq_zero.mp (show u.toNat * 16 ^ d = 0 by omega) with h | h
        · exact h
        · exact absurd h (pow_ne_zero _ (by norm_num))
      have e1 : ((u.toNat : ℝ) + φ) = 0 := by rw [hU0, hφ, hRz]; simp
      rw [e1]
      simp only [zero_mul]
    have hH1 : (1 : ℝ) ≤ hexValue L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz0
    have hU1 : (1 : ℝ) ≤ (u.toNat : ℝ) + φ := by
      have hu1 : u.toNat ≠ 0 := by
        intro h0
        rcases hUge with h | h
        · apply hz0
          have hRz : R = 0 := by
            rw [← hR]
            apply (hexValue_eq_zero _ (fun b hb => hL b (List.mem_of_mem_drop hb))).mpr
            intro b hb; rw [List.drop_eq_nil_of_le (by omega)] at hb; simp at hb
          rw [hV', h0, hRz]; simp
        · rw [← hu, h0] at h; exact absurd h (Nat.not_le.mpr (by positivity))
      have : (1 : ℝ) ≤ u.toNat := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hu1
      linarith
    rw [refPos_large f _ (big_value f 2 (by norm_num) nu emax hmax _ hU1 _ (by omega)), ← hreal,
      refPos_large f _ (big_value f 2 (by norm_num) nu emax hmax _ hH1 _ (by omega))]
  have hs' : satE e = e := by unfold satE; omega
  rw [hs']

#print axioms dec_parts
#print axioms hex_parts
#print axioms dec_value
#print axioms hex_value

end Library.Numerics.Decimal.ParseFloat.ParseFloatValue
