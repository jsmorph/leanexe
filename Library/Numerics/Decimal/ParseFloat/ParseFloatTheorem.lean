import Library.Numerics.Decimal.ParseFloat.ParseFloatValue
import Library.Numerics.Decimal.ParseFloat.ParseFloatFast

/-!
The parsers' theorems.  `decode_eq` writes `Library.Numerics.Decimal.Shared.StrconvDecode.decode` as one chain of conditions on
the rest `r` of the string after its sign: the special words, the hexadecimal prefix with
`ParseFloatHexParse.hexBranch`, and `ParseFloatDecParse.decBranch`.  The scanner computes the same
conditions (`sign_scan`, `special_scan`, `hex_scan`), the branches' values come from
`ParseFloatValue.hex_value`, `ParseFloatValue.dec_value`, and `ParseFloatFast.fastPath_spec`, and
the sign is the bit `2 ^ 63` (`2 ^ 31`) set by OR, which is Talos's `negate` on a nonnegative
word (`sign_or64`, `sign_or32`).  `parse64_spec` and `parse32_spec` state the results for every
string of fewer than `2 ^ 32` bytes through `decode`, and `parse64_accept`, `parse64_reject`,
`parse32_accept`, and `parse32_reject` through the grammar by `derives_iff_decode`.
-/

namespace Library.Numerics.Decimal.ParseFloat.ParseFloatTheorem
open ParseFloat Library.Numerics.Arithmetic.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.Shared.StrconvGrid Library.Numerics.Decimal.Shared.StrconvWords Library.Numerics.Decimal.Shared.StrconvGrammar Library.Numerics.Decimal.Shared.StrconvDecode
  Library.Numerics.Decimal.Shared.StrconvRound ParseFloatRound ParseFloatScan ParseFloatDigits ParseFloatDec ParseFloatDecParse
  ParseFloatHexParse ParseFloatFast ParseFloatValue Library.Numerics.Decimal.Shared.StrconvOfScientific Library.Numerics.Decimal.Shared.StrconvTruncate

set_option exponentiation.threshold 4096

/-! ### Words -/

theorem refPos_le (f : Fmt) (y : ℝ) : refPos f y ≤ limit f := by
  unfold refPos
  split_ifs
  · exact le_rfl
  · exact (Classical.choose_spec (exists_nearest_even f y)).1.1.le

theorem negate64 (w : UInt64) (hw : w.toNat < 2 ^ 63) :
    (Wasm.IEEE64.negate w).toNat = 2 ^ 63 + w.toNat := by
  have hs : Wasm.IEEE64.sign w = false := decide_eq_false (by omega)
  unfold Wasm.IEEE64.negate Wasm.IEEE64.encodeFinite Wasm.IEEE64.exponent Wasm.IEEE64.fraction
  rw [hs, Bool.not_false, ite_eq_left rfl, ofNat_toNat _ (by omega)]
  omega

theorem negate32 (w : UInt32) (hw : w.toNat < 2 ^ 31) :
    (Wasm.IEEE32.negate w).toNat = 2 ^ 31 + w.toNat := by
  have hs : Wasm.IEEE32.sign w = false := decide_eq_false (by omega)
  have hsz : UInt32.size = 2 ^ 32 := rfl
  unfold Wasm.IEEE32.negate Wasm.IEEE32.encodeFinite Wasm.IEEE32.exponent Wasm.IEEE32.fraction
  rw [hs, Bool.not_false, ite_eq_left rfl, UInt32.toNat_ofNat_of_lt' (by omega)]
  omega

/-- Setting the sign bit of a nonnegative binary64 word by OR is `withSign64`. -/
theorem sign_or64 (neg : Bool) (w : UInt64) (hw : w.toNat < 2 ^ 63) :
    ((if neg then (0x8000000000000000 : UInt64) else 0) ||| w) = withSign64 neg w := by
  apply UInt64.toNat_inj.mp
  unfold withSign64
  cases neg
  · simp only [Bool.false_eq_true, ite_false]
    rw [UInt64.toNat_or, UInt64.toNat_zero, Nat.zero_or]
  · simp only [ite_true]
    rw [negate64 w hw, UInt64.toNat_or, show (0x8000000000000000 : UInt64).toNat = 1 <<< 63 from rfl,
      ← Nat.shiftLeft_add_eq_or_of_lt hw, Nat.shiftLeft_eq, one_mul]

/-- Setting the sign bit of a nonnegative binary32 pattern by OR is `withSign32`. -/
theorem sign_or32 (neg : Bool) (w : UInt64) (hw : w.toNat < 2 ^ 31) :
    ((if neg then (0x80000000 : UInt64) else 0) ||| w) =
      (withSign32 neg (UInt32.ofNat w.toNat)).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hsz : UInt32.size = 2 ^ 32 := rfl
  have hx : (UInt32.ofNat w.toNat).toNat = w.toNat := UInt32.toNat_ofNat_of_lt' (by omega)
  rw [UInt32.toNat_toUInt64]
  unfold withSign32
  cases neg
  · simp only [Bool.false_eq_true, ite_false]
    rw [UInt64.toNat_or, UInt64.toNat_zero, Nat.zero_or, hx]
  · simp only [ite_true]
    rw [negate32 _ (by rw [hx]; exact hw), hx, UInt64.toNat_or,
      show (0x80000000 : UInt64).toNat = 1 <<< 31 from rfl,
      ← Nat.shiftLeft_add_eq_or_of_lt hw, Nat.shiftLeft_eq, one_mul]

theorem limit64 (y : ℝ) : refPos b64 y < 2 ^ 63 :=
  lt_of_le_of_lt (refPos_le b64 y) (by rw [limit_b64]; norm_num)

theorem limit32 (y : ℝ) : refPos b32 y < 2 ^ 31 :=
  lt_of_le_of_lt (refPos_le b32 y) (by rw [limit_b32]; norm_num)

/-! ### Bytes -/

theorem plus_word (b : UInt8) : (b.toUInt64 == 0x2B) = decide (b = 0x2B) := by
  revert b; apply ParseFloatScan.byte_cases; decide +kernel

theorem zero_eq_word (b : UInt8) : (b.toUInt64 == 0x30) = decide (b = 0x30) := by
  revert b; apply ParseFloatScan.byte_cases; decide +kernel

theorem x_word (b : UInt8) : ((b.toUInt64 ||| 0x20) == 0x78) = decide (b ∈ ascii "xX") := by
  revert b; apply ParseFloatScan.byte_cases; decide +kernel

theorem band_decide (g : Bool) (Q : Prop) [Decidable Q] : ((g && decide Q) = true) = (g = true ∧ Q) := by
  simp

/-! ### The scanner's conditions -/

/-- The sign: `parse64`'s flag of a minus sign and its first position after the sign. -/
theorem sign_scan (general : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32) :
    ∃ i0, i0 ≤ 1 ∧ i0 ≤ s.length ∧ s.drop i0 = (decodeSign general s).2 ∧
      (limb (words s) 0 == 0x2D) = (decodeSign general s).1 ∧
      (if ((decodeSign general s).1 || (general && limb (words s) 0 == 0x2B)) = true then
        (1 : UInt64) else 0) = UInt64.ofNat i0 := by
  have h0 : limb (words s) 0 = (byteAt s 0).toUInt64 := by rw [limb_words s 0 hs]; rfl
  rw [h0]
  cases s with
  | nil =>
    refine ⟨0, by norm_num, le_rfl, rfl, ?_, ?_⟩
    · rfl
    · cases general <;> rfl
  | cons b t =>
    rw [byteAt_cons_zero, minus_word, plus_word]
    by_cases h1 : b = 0x2D
    · subst h1
      exact ⟨1, le_rfl, by simp, rfl, rfl, rfl⟩
    · by_cases h2 : general = true ∧ b = 0x2B
      · obtain ⟨hg, hb⟩ := h2
        subst hg hb
        exact ⟨1, le_rfl, by simp, rfl, rfl, rfl⟩
      · have hd : decodeSign general (b :: t) = (false, b :: t) := by
          simp only [decodeSign, h1, ite_false, h2]
        rw [hd]
        refine ⟨0, by norm_num, by simp, rfl, decide_eq_false h1, ?_⟩
        rw [ite_eq_right]
        · rfl
        · simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq]
          exact h2

theorem special_scan (s : List UInt8) (hs : s.length < 2 ^ 32) (i0 : ℕ) (hi0 : i0 ≤ s.length) :
    (matchLower (words s) (UInt64.ofNat i0) 3 0x666E69 ||
        matchLower (words s) (UInt64.ofNat i0) 8 0x7974696E69666E69) =
      decide ((s.drop i0).map lower = ascii "inf" ∨ (s.drop i0).map lower = ascii "infinity") ∧
    matchLower (words s) (UInt64.ofNat i0) 3 0x6E616E = decide ((s.drop i0).map lower = ascii "nan") := by
  rw [show (3 : UInt64) = UInt64.ofNat 3 from rfl, show (8 : UInt64) = UInt64.ofNat 8 from rfl,
    matchLower_spec s i0 3 _ hi0 (by norm_num) hs, matchLower_spec s i0 8 _ hi0 (by norm_num) hs,
    matchLower_spec s i0 3 _ hi0 (by norm_num) hs, unpack_inf, unpack_infinity, unpack_nan,
    Bool.decide_or]
  exact ⟨rfl, rfl⟩

theorem hex_scan (general : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32) (i0 : ℕ)
    (hi0 : i0 ≤ s.length) :
    (general && limb (words s) (UInt64.ofNat i0) == 0x30 &&
        (limb (words s) (UInt64.ofNat i0 + 1) ||| 0x20) == 0x78) =
      (general && decide ((s.drop i0).take 2 = ascii "0x" ∨ (s.drop i0).take 2 = ascii "0X")) := by
  have h1 : (UInt64.ofNat i0 + 1).toNat = i0 + 1 := by
    rw [toNat_add' _ _ (by rw [ofNat_toNat _ (by omega)]; simp; omega), ofNat_toNat _ (by omega)]
    rfl
  rw [limb_words s _ hs, limb_words s _ hs, h1, ofNat_toNat _ (by omega), zero_eq_word, x_word,
    Bool.and_assoc]
  congr 1
  have e0 : byteAt s i0 = byteAt (s.drop i0) 0 := by rw [byteAt_drop, add_zero]
  have e1 : byteAt s (i0 + 1) = byteAt (s.drop i0) 1 := by rw [byteAt_drop]
  rw [e0, e1]
  generalize s.drop i0 = r
  match r with
  | [] => rfl
  | [a] =>
    simp only [byteAt_cons_zero, List.take]
    have : byteAt [a] 1 = 0 := byteAt_ge _ _ (by simp)
    rw [this]
    simp [ascii_0x, ascii_0X, show ascii "xX" = [0x78, 0x58] from rfl]
  | a :: b :: t =>
    simp only [byteAt_cons_zero, List.take]
    have : byteAt (a :: b :: t) 1 = b := by simp [byteAt]
    rw [this]
    simp only [ascii_0x, ascii_0X, show ascii "xX" = [0x78, 0x58] from rfl, List.cons.injEq,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, and_true, or_false]
    by_cases ha : a = 0x30 <;> simp [ha]

/-! ### The decoder as one chain of conditions -/

theorem decode_eq (general : Bool) (s : List UInt8) :
    decode general s =
      if general = true ∧ (((decodeSign general s).2).map lower = ascii "inf" ∨
          ((decodeSign general s).2).map lower = ascii "infinity") then
        some (.inf (decodeSign general s).1)
      else if general = true ∧ ((decodeSign general s).2).map lower = ascii "nan" then some .nan
      else if general = true ∧ (((decodeSign general s).2).take 2 = ascii "0x" ∨
          ((decodeSign general s).2).take 2 = ascii "0X") then
        (hexBranch (((decodeSign general s).2).drop 2)).map fun t =>
          .hex (decodeSign general s).1 (hexValue (t.1 ++ t.2.1)) (t.2.2 - 4 * t.2.1.length)
      else
        (decBranch general (decodeSign general s).2).map fun t =>
          .dec (decodeSign general s).1 (decValue (t.1 ++ t.2.1)) (t.2.2 - t.2.1.length) := by
  unfold decode
  simp only []
  split_ifs with h1 h2 h3 h4
  · rfl
  · rfl
  · unfold hexBranch
    rcases decodeSig isHexDigit (List.drop 2 (decodeSign general s).2) with _ | ⟨i, f, x⟩
    · rfl
    · dsimp only
      rcases decodeExp (ascii "pP") x with _ | e <;> rfl
  · unfold decBranch
    rw [ite_eq_left h4]
    rcases decodeSig isDigit (decodeSign general s).2 with _ | ⟨i, f, x⟩
    · rfl
    · dsimp only
      rcases decodeOptExp (ascii "eE") x with _ | e <;> rfl
  · unfold decBranch
    rw [ite_eq_right h4]
    rcases decodeJson (decodeSign general s).2 with _ | ⟨i, f, x⟩
    · rfl
    · dsimp only
      rcases decodeOptExp (ascii "eE") x with _ | e <;> rfl

/-! ### Results -/

/-- The parser's result for the decoder's number, or the rejection. -/
noncomputable def res64 : Option Num → Bool × UInt64
  | some n => (true, round64 n)
  | none => (false, 0)

/-- The binary32 parser's result for the decoder's number, or the rejection. -/
noncomputable def res32 : Option Num → Bool × UInt64
  | some n => (true, (round32 n).toUInt64)
  | none => (false, 0)

theorem threshold64 : threshold b64 ≤ (10 : ℝ) ^ (309 : UInt64).toNat * 2 ^ (1074 : UInt64).toNat := by
  show threshold b64 ≤ (10 : ℝ) ^ 309 * 2 ^ 1074
  unfold threshold; simp only [b64]; norm_num

theorem small64 : 2 * ((10 : ℝ) ^ (325 : UInt64).toNat)⁻¹ * 2 ^ (1074 : UInt64).toNat ≤ 1 := by
  show 2 * ((10 : ℝ) ^ 325)⁻¹ * 2 ^ 1074 ≤ 1
  norm_num

theorem threshold32 : threshold b32 ≤ (10 : ℝ) ^ (39 : UInt64).toNat * 2 ^ (149 : UInt64).toNat := by
  show threshold b32 ≤ (10 : ℝ) ^ 39 * 2 ^ 149
  unfold threshold; simp only [b32]; norm_num

theorem small32 : 2 * ((10 : ℝ) ^ (46 : UInt64).toNat)⁻¹ * 2 ^ (149 : UInt64).toNat ≤ 1 := by
  show 2 * ((10 : ℝ) ^ 46)⁻¹ * 2 ^ 149 ≤ 1
  norm_num

/-- The hexadecimal branch of `parse64`. -/
theorem hex64 (neg : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32) (j : ℕ) (hj : j ≤ s.length) :
    (if (hexParse 1074 (words s) (UInt64.ofNat j)).1 = true then
        (true, (if neg = true then (0x8000000000000000 : UInt64) else 0) |||
          roundUnits 53 2047 (hexParse 1074 (words s) (UInt64.ofNat j)).2.1
            (hexParse 1074 (words s) (UInt64.ofNat j)).2.2.1
            (hexParse 1074 (words s) (UInt64.ofNat j)).2.2.2)
      else (false, 0)) =
    res64 ((hexBranch (s.drop j)).map fun t =>
      .hex neg (hexValue (t.1 ++ t.2.1)) (t.2.2 - 4 * t.2.1.length)) := by
  obtain ⟨hflag, hval⟩ := hexParse_spec 1074 (by norm_num) s hs j hj
  rw [show (1074 : UInt64) = UInt64.ofNat 1074 from rfl]
  rcases hb : hexBranch (s.drop j) with _ | ⟨i, f, e⟩
  · rw [hb] at hflag
    rw [ite_eq_right (by rw [hflag]; decide)]
    rfl
  · rw [hb] at hflag
    obtain ⟨hd, hlen, hu, hst, htb⟩ := hval i f e hb
    rw [ite_eq_left (by rw [hflag]; rfl)]
    simp only [Option.map_some, res64]
    have hw := hex_value b64 53 2047 1074 1024 1075 rfl rfl (by norm_num [b64]) (by norm_num [b64])
      (by norm_num) (by norm_num) (by norm_num)
      (by unfold threshold; simp only [b64]; norm_num) (by norm_num)
      (i ++ f) hd (by omega) f.length (by simp) e _ _ _ hu hst htb
    have hw' : roundUnits 53 2047 (hexParse (UInt64.ofNat 1074) (words s) (UInt64.ofNat j)).2.1
        (hexParse (UInt64.ofNat 1074) (words s) (UInt64.ofNat j)).2.2.1
        (hexParse (UInt64.ofNat 1074) (words s) (UInt64.ofNat j)).2.2.2 =
        UInt64.ofNat (refPos b64 ((hexValue (i ++ f) : ℝ) * 2 ^ (e - 4 * f.length) * 2 ^ 1074)) := by
      apply UInt64.toNat_inj.mp
      rw [hw, ofNat_toNat _ (lt_trans (limit64 _) (by norm_num))]
    rw [hw', sign_or64 neg _ (by rw [ofNat_toNat _ (lt_trans (limit64 _) (by norm_num))]; exact limit64 _)]
    simp only [round64, ref64]

/-- An exponent within 22 of the bias after the digit counts is not saturated. -/
theorem fast_exp (e : ℤ) (nf d L qbn : ℕ) (hL : L < 2 ^ 32) (hnf : nf ≤ L) (hd : d ≤ L)
    (hq : (qbn : ℤ) = 2 ^ 62 + satE e - nf + d) (h1 : 2 ^ 62 - 22 ≤ qbn) (h2 : qbn ≤ 2 ^ 62 + 22) :
    satE e = e := by
  unfold satE at hq ⊢
  omega

/-- The decimal branch of `parse64`. -/
theorem dec64 (general neg : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32) (j : ℕ)
    (hj : j ≤ s.length) :
    (if (!(decParse general 768 (words s) (UInt64.ofNat j)).1) = true then (false, 0)
      else if (!(decParse general 768 (words s) (UInt64.ofNat j)).2.2.2.2 &&
          bitLen (decParse general 768 (words s) (UInt64.ofNat j)).2.1 ≤ 53 &&
          0x3FFFFFFFFFFFFFEA ≤ (decParse general 768 (words s) (UInt64.ofNat j)).2.2.2.1 &&
          (decParse general 768 (words s) (UInt64.ofNat j)).2.2.2.1 ≤ 0x4000000000000016) = true then
        (true, (if neg = true then (0x8000000000000000 : UInt64) else 0) |||
          fastPath (decParse general 768 (words s) (UInt64.ofNat j)).2.1
            (decParse general 768 (words s) (UInt64.ofNat j)).2.2.2.1)
      else (true, (if neg = true then (0x8000000000000000 : UInt64) else 0) |||
          decRound 53 2047 1074 309 325 (decParse general 768 (words s) (UInt64.ofNat j)).2.1
            (decParse general 768 (words s) (UInt64.ofNat j)).2.2.1
            (decParse general 768 (words s) (UInt64.ofNat j)).2.2.2.1
            (decParse general 768 (words s) (UInt64.ofNat j)).2.2.2.2)) =
    res64 ((decBranch general (s.drop j)).map fun t =>
      .dec neg (decValue (t.1 ++ t.2.1)) (t.2.2 - t.2.1.length)) := by
  obtain ⟨hflag, hval⟩ := decParse_spec general 768 (by norm_num) s hs j hj
  rw [show (768 : UInt64) = UInt64.ofNat 768 from rfl]
  rcases hb : decBranch general (s.drop j) with _ | ⟨i, f, e⟩
  · rw [hb] at hflag
    rw [ite_eq_left (by rw [hflag]; rfl)]
    rfl
  rw [hb] at hflag
  obtain ⟨hd, hlen, hD, hv, hsize, hkept, hqb, hst⟩ := hval i f e hb
  rw [ite_eq_right (by rw [hflag]; simp)]
  simp only [Option.map_some, res64]
  set d := decParse general (UInt64.ofNat 768) (words s) (UInt64.ofNat j) with hdd
  have hgoal : ∀ w : UInt64,
      w = UInt64.ofNat (refPos b64 ((decValue (i ++ f) : ℝ) * 10 ^ (e - f.length) * 2 ^ 1074)) →
      (true, (if neg = true then (0x8000000000000000 : UInt64) else 0) ||| w) =
        (true, round64 (.dec neg (decValue (i ++ f)) (e - f.length))) := by
    intro w hw
    rw [hw, sign_or64 neg _ (by rw [ofNat_toNat _ (lt_trans (limit64 _) (by norm_num))]; exact limit64 _),
      round64_dec]
  have hround := dec_value b64 53 2047 1074 309 325 768 rfl rfl (by norm_num [b64])
    (by norm_num [b64]) (by decide) (by decide) (by decide) threshold64 small64
    (by norm_num) (by norm_num)
    (fun D hD θ h0 h1 j' => truncate64 D hD θ h0 h1 j')
    (i ++ f) hd (by omega) f.length (by simp) e d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 hD hv hsize
    hkept hqb hst
  generalize (if neg = true then (0x8000000000000000 : UInt64) else 0) = S at hgoal ⊢
  split_ifs with hfast
  · apply hgoal
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hfast
    obtain ⟨⟨⟨hs0, hbl⟩, hq1⟩, hq2⟩ := hfast
    -- the fast path's value
    have hbl' : val d.2.1 < 2 ^ 53 := by
      have := bitLen_spec d.2.1 hD (by rw [hsize]; omega)
      rw [UInt64.le_iff_toNat_le] at hbl
      rw [this] at hbl
      exact Nat.size_le.mp (by exact hbl)
    rw [UInt64.le_iff_toNat_le] at hq1 hq2
    rw [fastPath_spec d.2.1 hD (by rw [hsize]; omega) hbl' d.2.2.2.1 (by exact hq1) (by exact hq2)]
    -- no dropped nonzero digit: the kept digits are the value
    generalize hz : ((i ++ f).takeWhile (· == 0x30)).length = z at hv hsize hkept hqb hst
    generalize hkp : min ((i ++ f).length - z) 768 = kp at hv hsize hkept hqb hst
    obtain ⟨hV, _, hRpos, _, _⟩ := dec_parts (i ++ f) hd 768 z kp hz.symm hkp.symm
    have hR0 : decValue ((i ++ f).drop (z + kp)) = 0 := by
      by_contra h
      have := hst.mpr (hRpos.mp (Nat.pos_of_ne_zero h))
      rw [hs0] at this; exact absurd this (by decide)
    rw [hR0, add_zero, ← hv] at hV
    have hsat : satE e = e := fast_exp e f.length ((i ++ f).length - z - kp) (i ++ f).length
      d.2.2.2.1.toNat (lt_of_le_of_lt (le_trans (Nat.le_add_left _ _) hlen) hs) (by simp)
      (le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)) hqb
      (by rw [show (0x3FFFFFFFFFFFFFEA : UInt64).toNat = 2 ^ 62 - 22 from rfl] at hq1; exact hq1)
      (by rw [show (0x4000000000000016 : UInt64).toNat = 2 ^ 62 + 22 from rfl] at hq2; exact hq2)
    have hq : (d.2.2.2.1.toNat : ℤ) - 2 ^ 62 =
        e - f.length + ((i ++ f).length - z - kp : ℕ) := by
      rw [hqb, hsat]; ring
    refine congrArg (fun y => UInt64.ofNat (refPos b64 y)) ?_
    rw [hq, hV]
    push_cast
    rw [zpow_add₀ (by norm_num), zpow_natCast]
    ring
  · apply hgoal
    apply UInt64.toNat_inj.mp
    rw [hround, ofNat_toNat _ (lt_trans (limit64 _) (by norm_num))]
    rfl

/-- The hexadecimal branch of `parse32`. -/
theorem hex32 (neg : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32) (j : ℕ) (hj : j ≤ s.length) :
    (if (hexParse 149 (words s) (UInt64.ofNat j)).1 = true then
        (true, (if neg = true then (0x80000000 : UInt64) else 0) |||
          roundUnits 24 255 (hexParse 149 (words s) (UInt64.ofNat j)).2.1
            (hexParse 149 (words s) (UInt64.ofNat j)).2.2.1
            (hexParse 149 (words s) (UInt64.ofNat j)).2.2.2)
      else (false, 0)) =
    res32 ((hexBranch (s.drop j)).map fun t =>
      .hex neg (hexValue (t.1 ++ t.2.1)) (t.2.2 - 4 * t.2.1.length)) := by
  obtain ⟨hflag, hval⟩ := hexParse_spec 149 (by norm_num) s hs j hj
  rw [show (149 : UInt64) = UInt64.ofNat 149 from rfl]
  rcases hb : hexBranch (s.drop j) with _ | ⟨i, f, e⟩
  · rw [hb] at hflag
    rw [ite_eq_right (by rw [hflag]; decide)]
    rfl
  · rw [hb] at hflag
    obtain ⟨hd, hlen, hu, hst, htb⟩ := hval i f e hb
    rw [ite_eq_left (by rw [hflag]; rfl)]
    simp only [Option.map_some, res32]
    have hw := hex_value b32 24 255 149 128 150 rfl rfl (by norm_num [b32]) (by norm_num [b32])
      (by norm_num) (by norm_num) (by norm_num)
      (by unfold threshold; simp only [b32]; norm_num) (by norm_num)
      (i ++ f) hd (by omega) f.length (by simp) e _ _ _ hu hst htb
    rw [sign_or32 neg _ (by rw [hw]; exact limit32 _), hw]
    simp only [round32, ref32]

/-- The decimal branch of `parse32`. -/
theorem dec32 (general neg : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32) (j : ℕ)
    (hj : j ≤ s.length) :
    (if (!(decParse general 113 (words s) (UInt64.ofNat j)).1) = true then (false, 0)
      else (true, (if neg = true then (0x80000000 : UInt64) else 0) |||
          decRound 24 255 149 39 46 (decParse general 113 (words s) (UInt64.ofNat j)).2.1
            (decParse general 113 (words s) (UInt64.ofNat j)).2.2.1
            (decParse general 113 (words s) (UInt64.ofNat j)).2.2.2.1
            (decParse general 113 (words s) (UInt64.ofNat j)).2.2.2.2)) =
    res32 ((decBranch general (s.drop j)).map fun t =>
      .dec neg (decValue (t.1 ++ t.2.1)) (t.2.2 - t.2.1.length)) := by
  obtain ⟨hflag, hval⟩ := decParse_spec general 113 (by norm_num) s hs j hj
  rw [show (113 : UInt64) = UInt64.ofNat 113 from rfl]
  rcases hb : decBranch general (s.drop j) with _ | ⟨i, f, e⟩
  · rw [hb] at hflag
    rw [ite_eq_left (by rw [hflag]; rfl)]
    rfl
  rw [hb] at hflag
  obtain ⟨hd, hlen, hD, hv, hsize, hkept, hqb, hst⟩ := hval i f e hb
  rw [ite_eq_right (by rw [hflag]; simp)]
  simp only [Option.map_some, res32]
  have hround := dec_value b32 24 255 149 39 46 113 rfl rfl (by norm_num [b32])
    (by norm_num [b32]) (by decide) (by decide) (by decide) threshold32 small32
    (by norm_num) (by norm_num)
    (fun D hD θ h0 h1 j' => truncate32 D hD θ h0 h1 j')
    (i ++ f) hd (by omega) f.length (by simp) e _ _ _ _ hD hv hsize hkept hqb hst
  rw [sign_or32 neg _ (by rw [hround]; exact limit32 _), hround, round32_dec]
  rfl

theorem key_and (g : Bool) (Q : Prop) [Decidable Q] : (g && decide Q) = true ↔ (g = true ∧ Q) := by
  simp

theorem drop_two (s : List UInt8) (i0 : ℕ)
    (h : (s.drop i0).take 2 = ascii "0x" ∨ (s.drop i0).take 2 = ascii "0X") :
    i0 + 2 ≤ s.length ∧ (s.drop i0).drop 2 = s.drop (i0 + 2) := by
  refine ⟨?_, by rw [List.drop_drop]⟩
  have h2 : ((s.drop i0).take 2).length = 2 := by rcases h with h | h <;> rw [h] <;> rfl
  rw [List.length_take, List.length_drop] at h2
  omega

/-- `parse64` returns the reference word of the number that `decode` reads, or the rejection. -/
theorem parse64_spec (general : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32) :
    parse64 general (words s) = res64 (decode general s) := by
  obtain ⟨i0, hi01, hi0, hr, hneg, hi0w⟩ := sign_scan general s hs
  obtain ⟨hsp1, hsp2⟩ := special_scan s hs i0 hi0
  have hhx := hex_scan general s hs i0 hi0
  have hi2 : UInt64.ofNat i0 + 2 = UInt64.ofNat (i0 + 2) := by
    apply UInt64.toNat_inj.mp
    rw [toNat_add' _ _ (by rw [ofNat_toNat _ (by omega)]; simp; omega), ofNat_toNat _ (by omega),
      ofNat_toNat _ (by omega)]
    rfl
  rw [decode_eq, ← hr]
  unfold parse64
  simp only [hneg, hi0w, hsp1, hsp2, hhx, hi2]
  by_cases h1 : general = true ∧ ((s.drop i0).map lower = ascii "inf" ∨
      (s.drop i0).map lower = ascii "infinity")
  · rw [ite_eq_left ((key_and _ _).mpr h1), ite_eq_left h1]
    simp only [res64, round64]
    rw [sign_or64 _ _ (by decide)]
  rw [ite_eq_right (fun h => h1 ((key_and _ _).mp h)), ite_eq_right h1]
  by_cases h2 : general = true ∧ (s.drop i0).map lower = ascii "nan"
  · rw [ite_eq_left ((key_and _ _).mpr h2), ite_eq_left h2]
    rfl
  rw [ite_eq_right (fun h => h2 ((key_and _ _).mp h)), ite_eq_right h2]
  by_cases h3 : general = true ∧ ((s.drop i0).take 2 = ascii "0x" ∨
      (s.drop i0).take 2 = ascii "0X")
  · rw [ite_eq_left ((key_and _ _).mpr h3), ite_eq_left h3]
    obtain ⟨hj, hd⟩ := drop_two s i0 h3.2
    rw [hd]
    exact hex64 _ s hs (i0 + 2) hj
  rw [ite_eq_right (fun h => h3 ((key_and _ _).mp h)), ite_eq_right h3]
  exact dec64 general _ s hs i0 hi0

/-- `parse32` returns the binary32 reference pattern of the number that `decode` reads, or the
rejection. -/
theorem parse32_spec (general : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32) :
    parse32 general (words s) = res32 (decode general s) := by
  obtain ⟨i0, hi01, hi0, hr, hneg, hi0w⟩ := sign_scan general s hs
  obtain ⟨hsp1, hsp2⟩ := special_scan s hs i0 hi0
  have hhx := hex_scan general s hs i0 hi0
  have hi2 : UInt64.ofNat i0 + 2 = UInt64.ofNat (i0 + 2) := by
    apply UInt64.toNat_inj.mp
    rw [toNat_add' _ _ (by rw [ofNat_toNat _ (by omega)]; simp; omega), ofNat_toNat _ (by omega),
      ofNat_toNat _ (by omega)]
    rfl
  rw [decode_eq, ← hr]
  unfold parse32
  simp only [hneg, hi0w, hsp1, hsp2, hhx, hi2]
  by_cases h1 : general = true ∧ ((s.drop i0).map lower = ascii "inf" ∨
      (s.drop i0).map lower = ascii "infinity")
  · rw [ite_eq_left ((key_and _ _).mpr h1), ite_eq_left h1]
    simp only [res32, round32]
    rw [sign_or32 _ _ (by decide)]
    rfl
  rw [ite_eq_right (fun h => h1 ((key_and _ _).mp h)), ite_eq_right h1]
  by_cases h2 : general = true ∧ (s.drop i0).map lower = ascii "nan"
  · rw [ite_eq_left ((key_and _ _).mpr h2), ite_eq_left h2]
    rfl
  rw [ite_eq_right (fun h => h2 ((key_and _ _).mp h)), ite_eq_right h2]
  by_cases h3 : general = true ∧ ((s.drop i0).take 2 = ascii "0x" ∨
      (s.drop i0).take 2 = ascii "0X")
  · rw [ite_eq_left ((key_and _ _).mpr h3), ite_eq_left h3]
    obtain ⟨hj, hd⟩ := drop_two s i0 h3.2
    rw [hd]
    exact hex32 _ s hs (i0 + 2) hj
  rw [ite_eq_right (fun h => h3 ((key_and _ _).mp h)), ite_eq_right h3]
  exact dec32 general _ s hs i0 hi0

/-! ### The theorems of the specification -/

/-- `parse64` on the bytes of a number of the grammar returns the binary64 word of
roundTiesToEven applied to it.  The hypothesis on the length excludes no input of the compiled
module, whose 4 GiB memory holds fewer than `2 ^ 29` one-byte words. -/
theorem parse64_accept (general : Bool) (s : List UInt8) (n : Num) (hs : s.length < 2 ^ 32)
    (h : Derives general s n) : parse64 general (words s) = (true, round64 n) := by
  rw [parse64_spec general s hs, (derives_iff_decode general s n).mp h]
  rfl

/-- `parse64` rejects a string that is no number of the grammar. -/
theorem parse64_reject (general : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32)
    (h : ∀ n, ¬ Derives general s n) : parse64 general (words s) = (false, 0) := by
  rw [parse64_spec general s hs]
  cases hd : decode general s with
  | none => rfl
  | some n => exact absurd ((derives_iff_decode general s n).mpr hd) (h n)

/-- `parse32` on the bytes of a number of the grammar returns the binary32 pattern of
roundTiesToEven applied to it in the low 32 bits.  The hypothesis on the length excludes no input
of the compiled module. -/
theorem parse32_accept (general : Bool) (s : List UInt8) (n : Num) (hs : s.length < 2 ^ 32)
    (h : Derives general s n) : parse32 general (words s) = (true, (round32 n).toUInt64) := by
  rw [parse32_spec general s hs, (derives_iff_decode general s n).mp h]
  rfl

/-- `parse32` rejects a string that is no number of the grammar. -/
theorem parse32_reject (general : Bool) (s : List UInt8) (hs : s.length < 2 ^ 32)
    (h : ∀ n, ¬ Derives general s n) : parse32 general (words s) = (false, 0) := by
  rw [parse32_spec general s hs]
  cases hd : decode general s with
  | none => rfl
  | some n => exact absurd ((derives_iff_decode general s n).mpr hd) (h n)

#print axioms decode_eq
#print axioms hex64
#print axioms dec64
#print axioms parse64_accept
#print axioms parse64_reject
#print axioms parse32_accept
#print axioms parse32_reject

end Library.Numerics.Decimal.ParseFloat.ParseFloatTheorem
