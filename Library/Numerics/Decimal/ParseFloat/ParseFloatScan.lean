import Library.Numerics.Decimal.ParseFloat.ParseFloatRound
import Library.Numerics.Decimal.Shared.StrconvDecode

/-!
The parsers' scanner against the decoder's splits of a list.  For a string `s` of bytes held as
`words s`, `limb_words` reads byte `j` as `byteAt s j`, the byte classes of the words agree with
those of `StrconvGrammar` on every byte (checked over the 256 bytes) and are false on the 0 read
past the end, and `span_spec` shows that `span` from position `i` stops after the bytes of
`(s.drop i).takeWhile` of the class.  `matchLower_spec` reads the test for `inf`, `infinity`, and
`nan`, and `expPart_spec` the exponent: its flag is `decodeExpDigits` succeeding, its sign is the
sign of the decoded value, and its value is the decoded magnitude saturated at `10 ^ 11`.
-/

namespace Library.Numerics.Decimal.ParseFloat.ParseFloatScan
open ParseFloat Library.Numerics.Arithmetic.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.Shared.StrconvGrammar Library.Numerics.Decimal.Shared.StrconvDecode ParseFloatRound

/-! ### Bytes -/

/-- Byte `j` of `s`, 0 past the end. -/
def byteAt (s : List UInt8) (j : ℕ) : UInt8 := (s[j]?).getD 0

theorem byteAt_lt (s : List UInt8) (j : ℕ) (h : j < s.length) : byteAt s j = s[j] := by
  simp [byteAt, List.getElem?_eq_getElem h]

theorem byteAt_ge (s : List UInt8) (j : ℕ) (h : s.length ≤ j) : byteAt s j = 0 := by
  simp [byteAt, List.getElem?_eq_none h]

theorem byteAt_drop (s : List UInt8) (i k : ℕ) : byteAt (s.drop i) k = byteAt s (i + k) := by
  simp [byteAt, List.getElem?_drop]

theorem byteAt_append (l₁ l₂ : List UInt8) (k : ℕ) :
    byteAt (l₁ ++ l₂) (l₁.length + k) = byteAt l₂ k := by
  simp [byteAt, List.getElem?_append_right]

theorem byteAt_cons_zero (b : UInt8) (t : List UInt8) : byteAt (b :: t) 0 = b := by
  simp [byteAt]

theorem byteAt_mem (s : List UInt8) (j : ℕ) (h : j < s.length) : byteAt s j ∈ s := by
  rw [byteAt_lt s j h]; exact List.getElem_mem _

theorem words_size (s : List UInt8) : (words s).size = s.length := by simp [words]

theorem words_size64 (s : List UInt8) (hs : s.length < 2 ^ 32) :
    (words s).size.toUInt64.toNat = s.length := by
  rw [size_toUInt64 _ (by rw [words_size]; omega), words_size]

theorem limb_words (s : List UInt8) (j : UInt64) (hs : s.length < 2 ^ 32) :
    limb (words s) j = (byteAt s j.toNat).toUInt64 := by
  unfold limb
  have hsz := words_size64 s hs
  by_cases h : j.toNat < s.length
  · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hsz]; exact h)]
    have hj : j.toNat < (words s).size := by rw [words_size]; exact h
    rw [getElem!_pos (words s) j.toNat hj, byteAt_lt s _ h]
    simp [words]
  · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hsz]; exact h), byteAt_ge s _ (by omega)]
    rfl

theorem byte_cases (P : UInt8 → Prop) (h : ∀ n, n < 256 → P (UInt8.ofNat n)) (b : UInt8) :
    P b := by
  have := h b.toNat b.toNat_lt
  simpa using this

theorem isDigitW_byte (b : UInt8) : isDigitW b.toUInt64 = isDigit b := by
  revert b; apply byte_cases; decide +kernel

theorem isHexW_byte (b : UInt8) : isHexW b.toUInt64 = isHexDigit b := by
  revert b; apply byte_cases; decide +kernel

theorem lowerW_byte (b : UInt8) : lowerW b.toUInt64 = (lower b).toUInt64 := by
  revert b; apply byte_cases; decide +kernel

theorem hexValW_byte (b : UInt8) (h : isHexDigit b = true) :
    (hexValW b.toUInt64).toNat = hexDigitValue b := by
  revert b h; apply byte_cases; decide +kernel

theorem digit_val (b : UInt8) (h : isDigit b = true) :
    (b.toUInt64 - 0x30).toNat = b.toNat - 0x30 := by
  revert b h; apply byte_cases; decide +kernel

/-- The class of `span`'s test. -/
def cls (hex : Bool) (b : UInt8) : Bool := if hex then isHexDigit b else isDigit b

theorem cls_word (hex : Bool) (b : UInt8) :
    (if hex then isHexW b.toUInt64 else isDigitW b.toUInt64) = cls hex b := by
  cases hex <;> simp [cls, isHexW_byte, isDigitW_byte]

/-! ### Spans -/

theorem takeWhile_get (p : UInt8 → Bool) (l : List UInt8) (k : ℕ)
    (hk : k < (l.takeWhile p).length) : p (byteAt l k) = true := by
  have h1 : k < l.length := lt_of_lt_of_le hk (List.takeWhile_prefix p).length_le
  have : byteAt l k = (l.takeWhile p)[k] := by
    rw [byteAt_lt l k h1]; exact ((List.takeWhile_prefix p).getElem hk).symm
  rw [this]
  exact takeWhile_all p l _ (List.getElem_mem hk)

theorem takeWhile_stop (p : UInt8 → Bool) (l : List UInt8)
    (hk : (l.takeWhile p).length < l.length) :
    p (byteAt l (l.takeWhile p).length) = false := by
  have hs := dropWhile_stops p l
  have hl := (List.takeWhile_append_dropWhile (p := p) (l := l))
  have hd : l.dropWhile p ≠ [] := by
    intro h; rw [h, List.append_nil] at hl
    have := congrArg List.length hl; omega
  obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil hd
  have hb := hs b t hbt
  have e : l = l.takeWhile p ++ b :: t := by rw [← hbt]; exact hl.symm
  have : byteAt l (l.takeWhile p).length = b := by
    have h2 := byteAt_append (l.takeWhile p) (b :: t) 0
    rw [add_zero, byteAt_cons_zero, ← e] at h2
    exact h2
  rw [this, hb]

theorem span_spec (s : List UInt8) (hex : Bool) (i : ℕ) (hi : i ≤ s.length)
    (hs : s.length < 2 ^ 32) :
    (span (words s) hex (UInt64.ofNat i)).toNat =
      i + ((s.drop i).takeWhile (cls hex)).length := by
  set m := ((s.drop i).takeWhile (cls hex)).length with hm
  have hml : i + m ≤ s.length := by
    have := (List.takeWhile_prefix (cls hex) (l := s.drop i)).length_le
    simp at this; omega
  have hsz := words_size64 s hs
  unfold span LeanExe.repeatWhile
  have key : ∀ fuel j, i ≤ j → j ≤ i + m → i + m - j ≤ fuel →
      (LeanExe.repeatWhile.go (fun j => decide (j < (words s).size.toUInt64) &&
          (if hex then isHexW (limb (words s) j) else isDigitW (limb (words s) j))) (fun j => j + 1)
        fuel (UInt64.ofNat j)).toNat = i + m := by
    intro fuel
    induction fuel with
    | zero =>
      intro j h1 h2 h3
      simp only [LeanExe.repeatWhile.go]
      rw [ofNat_toNat _ (by omega)]; omega
    | succ k ih =>
      intro j h1 h2 h3
      simp only [LeanExe.repeatWhile.go]
      have hjn : (UInt64.ofNat j).toNat = j := ofNat_toNat _ (by omega)
      have hlimb : limb (words s) (UInt64.ofNat j) = (byteAt s j).toUInt64 := by
        rw [limb_words s _ hs, hjn]
      rw [hlimb, cls_word]
      by_cases hj : j < i + m
      · have hc : (decide (UInt64.ofNat j < (words s).size.toUInt64) &&
            cls hex (byteAt s j)) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rw [UInt64.lt_iff_toNat_lt, hjn, hsz]; omega
          · have := takeWhile_get (cls hex) (s.drop i) (j - i) (by omega)
            rwa [byteAt_drop, show i + (j - i) = j by omega] at this
        rw [if_pos hc]
        have := ih (j + 1) (by omega) (by omega) (by omega)
        rwa [show UInt64.ofNat j + 1 = UInt64.ofNat (j + 1) by
          apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hjn, ofNat_toNat _ (by omega)]; simp
          omega] at *
      · have hje : j = i + m := by omega
        have hc : (decide (UInt64.ofNat j < (words s).size.toUInt64) &&
            cls hex (byteAt s j)) = false := by
          by_cases hjl : j < s.length
          · have hlt : m < (s.drop i).length := by simp; omega
            have := takeWhile_stop (cls hex) (s.drop i) hlt
            rw [← hm, byteAt_drop, ← hje] at this
            simp [this]
          · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
            left; rw [UInt64.lt_iff_toNat_lt, hjn, hsz]; exact hjl
        rw [if_neg (by simp [hc]), hjn]; exact hje
  exact key _ i le_rfl (by omega) (by rw [hsz]; omega)

/-! ### Words of special names -/

/-- The `len` bytes packed in `w`, least significant first. -/
def unpack (w : UInt64) (len : ℕ) : List UInt8 :=
  (List.range len).map fun k => ((w >>> (8 * UInt64.ofNat k)) &&& 0xFF).toUInt8

theorem unpack_inf : unpack 0x666E69 3 = ascii "inf" := by decide
theorem unpack_infinity : unpack 0x7974696E69666E69 8 = ascii "infinity" := by decide
theorem unpack_nan : unpack 0x6E616E 3 = ascii "nan" := by decide

theorem mask_byte (x : UInt64) : ((x &&& 0xFF).toUInt8).toUInt64 = x &&& 0xFF := by
  apply UInt64.toNat_inj.mp
  rw [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_and]
  have : x.toNat &&& (0xFF : UInt64).toNat < 256 := by
    rw [show (0xFF : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  exact Nat.mod_eq_of_lt this

theorem matchLower_spec (s : List UInt8) (i len : ℕ) (w : UInt64) (hi : i ≤ s.length)
    (hlen : len ≤ 8) (hs : s.length < 2 ^ 32) :
    matchLower (words s) (UInt64.ofNat i) (UInt64.ofNat len) w =
      decide ((s.drop i).map lower = unpack w len) := by
  have hsz := words_size64 s hs
  have hin : (UInt64.ofNat i).toNat = i := ofNat_toNat _ (by omega)
  have hln : (UInt64.ofNat len).toNat = len := ofNat_toNat _ (by omega)
  unfold matchLower
  have hdiff : ((words s).size.toUInt64 - UInt64.ofNat i == UInt64.ofNat len) =
      decide (s.length - i = len) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h; have := congrArg UInt64.toNat h
      rw [toNat_sub' _ _ (by rw [hsz, hin]; exact hi), hsz, hin, hln] at this; exact this
    · intro h; apply UInt64.toNat_inj.mp
      rw [toNat_sub' _ _ (by rw [hsz, hin]; exact hi), hsz, hin, hln]; exact h
  rw [hdiff]
  by_cases hl : s.length - i = len
  · rw [decide_eq_true hl, Bool.true_and]
    have hloop := loop_inv (UInt64.ofNat len) true
      (fun k ok => ok && lowerW (limb (words s) (UInt64.ofNat i + k)) ==
        ((w >>> (8 * k)) &&& 0xFF))
      (fun k ok => ok = decide (∀ j, j < k → lower (byteAt s (i + j)) = byteAt (unpack w len) j))
      (by simp)
      (by
        intro k ok hk hok
        rw [hln] at hk
        have hkn : (UInt64.ofNat k).toNat = k := ofNat_toNat _ (by omega)
        have hlimb : limb (words s) (UInt64.ofNat i + UInt64.ofNat k) =
            (byteAt s (i + k)).toUInt64 := by
          rw [limb_words s _ hs, toNat_add' _ _ (by rw [hin, hkn]; omega), hin, hkn]
        rw [hlimb, lowerW_byte, hok]
        have hun : byteAt (unpack w len) k = ((w >>> (8 * UInt64.ofNat k)) &&& 0xFF).toUInt8 := by
          rw [byteAt_lt _ _ (by simp [unpack]; omega)]
          simp [unpack]
        have heq : ((lower (byteAt s (i + k))).toUInt64 == ((w >>> (8 * UInt64.ofNat k)) &&& 0xFF)) =
            decide (lower (byteAt s (i + k)) = byteAt (unpack w len) k) := by
          rw [hun, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
          constructor
          · intro h; apply UInt8.toUInt64_inj.mp; rw [h, mask_byte]
          · intro h; rw [h, mask_byte]
        rw [heq, Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2⟩ j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
          · exact h1 j h
          · rw [h]; exact h2
        · intro h; exact ⟨fun j hj => h j (by omega), h k (by omega)⟩)
    rw [hln] at hloop
    rw [hloop, decide_eq_decide]
    have hlen1 : ((s.drop i).map lower).length = len := by simp; omega
    have hlen2 : (unpack w len).length = len := by simp [unpack]
    constructor
    · intro h
      apply List.ext_getElem (by rw [hlen1, hlen2])
      intro j h1 h2
      have := h j (by rw [hlen1] at h1; exact h1)
      rw [byteAt_lt _ _ h2] at this
      simp only [List.getElem_map, List.getElem_drop]
      rw [← this, byteAt_lt _ _ (by simp at h1; omega)]
    · intro h j hj
      have h1 : j < ((s.drop i).map lower).length := by rw [hlen1]; exact hj
      have := congrArg (fun l => byteAt l j) h
      rw [byteAt_lt _ _ h1] at this
      simp only [List.getElem_map, List.getElem_drop] at this
      rw [byteAt_lt _ _ (by simp at h1; omega)]
      exact this
  · rw [decide_eq_false hl, Bool.false_and]
    symm
    rw [decide_eq_false_iff_not]
    intro h
    have := congrArg List.length h
    simp [unpack] at this
    omega

/-! ### Exponents -/

/-- A decimal exponent saturated at `±10 ^ 11`. -/
def satE (v : ℤ) : ℤ := max (-(10 ^ 11)) (min v (10 ^ 11))

theorem decValue_snoc (l : List UInt8) (b : UInt8) :
    decValue (l ++ [b]) = 10 * decValue l + (b.toNat - 0x30) := by
  simp [decValue, List.foldl_append]

theorem expDigits_spec (s : List UInt8) (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ s.length)
    (hs : s.length < 2 ^ 32) (hd : ∀ t, j ≤ t → t < k → isDigit (byteAt s t) = true) :
    (expDigits (words s) (UInt64.ofNat j) (UInt64.ofNat k)).toNat =
      min (decValue ((s.drop j).take (k - j))) (10 ^ 11) := by
  have hjn : (UInt64.ofNat j).toNat = j := ofNat_toNat _ (by omega)
  have hkn : (UInt64.ofNat k).toNat = k := ofNat_toNat _ (by omega)
  have hkj : (UInt64.ofNat k - UInt64.ofNat j).toNat = k - j := by
    rw [toNat_sub' _ _ (by rw [hjn, hkn]; exact hjk), hjn, hkn]
  unfold expDigits
  have hloop := loop_inv (UInt64.ofNat k - UInt64.ofNat j) (0 : UInt64)
    (fun t acc => min (10 * acc + (limb (words s) (UInt64.ofNat j + t) - 0x30)) 100000000000)
    (fun t acc => acc.toNat = min (decValue ((s.drop j).take t)) (10 ^ 11)) (by simp [decValue])
    (by
      intro t acc ht hacc
      rw [hkj] at ht
      have htn : (UInt64.ofNat t).toNat = t := ofNat_toNat _ (by omega)
      have hb : limb (words s) (UInt64.ofNat j + UInt64.ofNat t) = (byteAt s (j + t)).toUInt64 := by
        rw [limb_words s _ hs, toNat_add' _ _ (by rw [hjn, htn]; omega), hjn, htn]
      have hdig := hd (j + t) (by omega) (by omega)
      rw [hb]
      have hdv := digit_val _ hdig
      have hdl : (byteAt s (j + t)).toNat - 0x30 < 10 := by
        revert hdig; generalize byteAt s (j + t) = b; revert b; apply byte_cases; decide +kernel
      have htake : (s.drop j).take (t + 1) = (s.drop j).take t ++ [byteAt s (j + t)] := by
        rw [List.take_succ, List.getElem?_drop]
        rw [List.getElem?_eq_getElem (by omega)]
        rw [byteAt_lt _ _ (show j + t < s.length by omega)]
        simp
      rw [htake, decValue_snoc]
      have hacc' : acc.toNat ≤ 10 ^ 11 := by rw [hacc]; exact min_le_right _ _
      have hmul : (10 * acc + ((byteAt s (j + t)).toUInt64 - 0x30)).toNat =
          10 * acc.toNat + ((byteAt s (j + t)).toNat - 0x30) := by
        rw [toNat_add' _ _ (by rw [toNat_mul' _ _ (by simp; omega), hdv]; simp; omega),
          toNat_mul' _ _ (by simp; omega), hdv]; rfl
      rw [UInt64.toNat_min, hmul, hacc, show (100000000000 : UInt64).toNat = 10 ^ 11 from rfl]
      rcases le_total (decValue ((s.drop j).take t)) (10 ^ 11) with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h]
        rw [min_eq_right (by omega), min_eq_right (by omega)])
  rw [hkj] at hloop
  exact hloop

theorem takeWhile_len_eq (p : UInt8 → Bool) (l : List UInt8) :
    (l.takeWhile p).length = l.length ↔ l.all p = true := by
  induction l with
  | nil => simp
  | cons b t ih =>
    by_cases hb : p b = true
    · rw [List.takeWhile_cons_of_pos hb]; simp [hb, ih]
    · rw [List.takeWhile_cons_of_neg hb]; simp [hb]

theorem takeWhile_len_pos (p : UInt8 → Bool) (b : UInt8) (t : List UInt8) :
    0 < ((b :: t).takeWhile p).length ↔ p b = true := by
  by_cases hb : p b = true
  · rw [List.takeWhile_cons_of_pos hb]; simp [hb]
  · rw [List.takeWhile_cons_of_neg hb]; simp [hb]

theorem satE_neg (d : ℕ) : satE (-(d : ℤ)) = -(min d (10 ^ 11) : ℕ) := by
  unfold satE; push_cast; omega

theorem satE_pos (d : ℕ) : satE (d : ℤ) = (min d (10 ^ 11) : ℕ) := by
  unfold satE; push_cast; omega

theorem cls_false : cls false = isDigit := by funext b; rfl

/-- A run of digits from `j`: `span` ends it, and `expDigits` reads its saturated value. -/
theorem digit_run (s : List UInt8) (hs : s.length < 2 ^ 32) (j : ℕ) (hj : j ≤ s.length) :
    (span (words s) false (UInt64.ofNat j)).toNat = j + ((s.drop j).takeWhile isDigit).length ∧
      (expDigits (words s) (UInt64.ofNat j) (span (words s) false (UInt64.ofNat j))).toNat =
        min (decValue ((s.drop j).takeWhile isDigit)) (10 ^ 11) := by
  have hsp := span_spec s false j hj hs
  rw [cls_false] at hsp
  set m := ((s.drop j).takeWhile isDigit).length with hm
  have hml : j + m ≤ s.length := by
    have := (List.takeWhile_prefix isDigit (l := s.drop j)).length_le
    simp at this; omega
  refine ⟨hsp, ?_⟩
  have hspw : span (words s) false (UInt64.ofNat j) = UInt64.ofNat (j + m) := by
    apply UInt64.toNat_inj.mp; rw [hsp, ofNat_toNat _ (by omega)]
  rw [hspw, expDigits_spec s j (j + m) (by omega) hml hs (fun t h1 h2 => by
    have := takeWhile_get isDigit (s.drop j) (t - j) (by omega)
    rwa [byteAt_drop, show j + (t - j) = t by omega] at this)]
  rw [show j + m - j = m by omega]
  congr 2
  have := (List.takeWhile_prefix isDigit (l := s.drop j))
  obtain ⟨u, hu⟩ := this
  conv_lhs => rw [← hu]
  rw [hm, List.take_left]

theorem sign_word (b : UInt8) :
    (b.toUInt64 == 0x2D || b.toUInt64 == 0x2B) = decide (b = 0x2D ∨ b = 0x2B) := by
  revert b; apply byte_cases; decide +kernel

theorem minus_word (b : UInt8) : (b.toUInt64 == 0x2D) = decide (b = 0x2D) := by
  revert b; apply byte_cases; decide +kernel

theorem expPart_spec (s : List UInt8) (i : ℕ) (hi : i ≤ s.length) (hs : s.length < 2 ^ 32) :
    ((expPart (words s) (UInt64.ofNat i)).1 = true ↔
        (decodeExpDigits (s.drop i)).isSome = true) ∧
      ∀ v, decodeExpDigits (s.drop i) = some v →
        (if (expPart (words s) (UInt64.ofNat i)).2.1 then
            (2 ^ 62 : ℤ) - (expPart (words s) (UInt64.ofNat i)).2.2.toNat
          else 2 ^ 62 + (expPart (words s) (UInt64.ofNat i)).2.2.toNat) = 2 ^ 62 + satE v := by
  have hsz := words_size64 s hs
  have hin : (UInt64.ofNat i).toNat = i := ofNat_toNat _ (by omega)
  have hc : limb (words s) (UInt64.ofNat i) = (byteAt s i).toUInt64 := by
    rw [limb_words s _ hs, hin]
  set c := byteAt s i with hcdef
  set j : ℕ := if c = 0x2D ∨ c = 0x2B then i + 1 else i with hjdef
  have hj : j ≤ s.length := by
    rw [hjdef]; split_ifs with h
    · by_contra hn
      have : i = s.length := by omega
      rw [hcdef, byteAt_ge s i (by omega)] at h
      rcases h with h | h <;> exact absurd h (by decide)
    · exact hi
  have hjw : (if limb (words s) (UInt64.ofNat i) == 0x2D || limb (words s) (UInt64.ofNat i) == 0x2B
      then UInt64.ofNat i + 1 else UInt64.ofNat i) = UInt64.ofNat j := by
    rw [hc, sign_word, hjdef]
    split_ifs with h1 h2 h2
    · apply UInt64.toNat_inj.mp
      rw [toNat_add' _ _ (by rw [hin]; simp; omega), hin, ofNat_toNat _ (by omega)]; rfl
    · exact absurd (of_decide_eq_true h1) h2
    · exact absurd (decide_eq_true h2) h1
    · rfl
  have hexp : expPart (words s) (UInt64.ofNat i) =
      (decide (UInt64.ofNat j < span (words s) false (UInt64.ofNat j)) &&
          (span (words s) false (UInt64.ofNat j) == (words s).size.toUInt64),
        c.toUInt64 == 0x2D, expDigits (words s) (UInt64.ofNat j)
          (span (words s) false (UInt64.ofNat j))) := by
    unfold expPart
    simp only [hjw]
    rw [hc]
  rw [hexp]
  dsimp only
  obtain ⟨hk, hval⟩ := digit_run s hs j hj
  set m := ((s.drop j).takeWhile isDigit).length with hm
  have hall := takeWhile_len_eq isDigit (s.drop j)
  have hjn : (UInt64.ofNat j).toNat = j := ofNat_toNat _ (by omega)
  have hvalid : (decide (UInt64.ofNat j < span (words s) false (UInt64.ofNat j)) &&
      (span (words s) false (UInt64.ofNat j) == (words s).size.toUInt64)) =
      decide (s.drop j ≠ [] ∧ (s.drop j).all isDigit = true) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, UInt64.lt_iff_toNat_lt, hjn, hk]
    constructor
    · rintro ⟨h1, h2⟩
      have h2' := congrArg UInt64.toNat h2
      rw [hk, hsz] at h2'
      refine ⟨fun h => by rw [h] at hm; simp at hm; omega, hall.mp (by simp; omega)⟩
    · rintro ⟨h1, h2⟩
      have := hall.mpr h2
      have hr : 0 < (s.drop j).length := List.length_pos_iff.mpr h1
      simp at this hr
      refine ⟨by omega, UInt64.toNat_inj.mp (by rw [hk, hsz]; omega)⟩
  have htake : (s.drop j).all isDigit = true → (s.drop j).takeWhile isDigit = s.drop j := by
    intro h
    obtain ⟨u, hu⟩ := List.takeWhile_prefix isDigit (l := s.drop j)
    have hl := hall.mpr h
    have : u = [] := by
      have := congrArg List.length hu; simp at this hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [this, List.append_nil] at hu; exact hu
  rcases hdr : s.drop i with _ | ⟨b, rest⟩
  · -- the end of the string
    have hin' : i = s.length := by
      have := congrArg List.length hdr; simp at this; omega
    have hc0 : c = 0 := by rw [hcdef]; exact byteAt_ge _ _ (by omega)
    have hji : j = i := by rw [hjdef, hc0]; simp
    refine ⟨?_, fun v hv => by simp [decodeExpDigits] at hv⟩
    rw [hvalid, hji, hdr]; simp [decodeExpDigits]
  have hcb : c = b := by
    rw [hcdef]
    have := congrArg (fun l => byteAt l 0) hdr
    simp only [byteAt_drop, add_zero, byteAt_cons_zero] at this; exact this
  have hrest : s.drop (i + 1) = rest := by rw [← List.drop_drop, hdr]; rfl
  by_cases hsg : b = 0x2D ∨ b = 0x2B
  · have hj1 : j = i + 1 := by rw [hjdef, if_pos (by rw [hcb]; exact hsg)]
    have hdj : s.drop j = rest := by rw [hj1, hrest]
    rw [hdj] at hvalid htake hval
    refine ⟨?_, fun v hv => ?_⟩
    · rw [hvalid]
      rcases hsg with h | h <;> subst h <;>
        simp only [decodeExpDigits, ite_true, show ((0x2B : UInt8) = 0x2D) = False by decide,
          ite_false] <;> split_ifs <;> simp_all
    · have hrd : rest ≠ [] ∧ rest.all isDigit = true := by
        rcases hsg with h | h <;> subst h <;>
          simp only [decodeExpDigits, ite_true, show ((0x2B : UInt8) = 0x2D) = False by decide,
            ite_false] at hv <;> split_ifs at hv with hh <;> simp_all
      rw [hval, htake hrd.2, hcb, minus_word]
      rcases hsg with h | h <;> subst h
      · simp only [decodeExpDigits, ite_true, if_pos hrd, Option.some.injEq] at hv
        subst hv
        simp only [decide_true, ite_true]
        rw [satE_neg]; push_cast; ring
      · simp only [decodeExpDigits, show ((0x2B : UInt8) = 0x2D) = False by decide, ite_false,
          ite_true, if_pos hrd, Option.some.injEq] at hv
        subst hv
        simp only [show ((0x2B : UInt8) = 0x2D) = False by decide, decide_false,
          Bool.false_eq_true, ite_false]
        rw [satE_pos]
  · push Not at hsg
    have hji : j = i := by rw [hjdef, if_neg (by rw [hcb]; push Not; exact hsg)]
    have hdj : s.drop j = b :: rest := by rw [hji, hdr]
    rw [hdj] at hvalid htake hval
    refine ⟨?_, fun v hv => ?_⟩
    · rw [hvalid]
      simp only [decodeExpDigits, show (b = 0x2D) = False from propext ⟨hsg.1, False.elim⟩,
        show (b = 0x2B) = False from propext ⟨hsg.2, False.elim⟩, ite_false]
      split_ifs <;> simp_all
    · simp only [decodeExpDigits, show (b = 0x2D) = False from propext ⟨hsg.1, False.elim⟩,
        show (b = 0x2B) = False from propext ⟨hsg.2, False.elim⟩, ite_false] at hv
      split_ifs at hv with hh
      · simp only [Option.some.injEq] at hv
        subst hv
        rw [hval, htake hh, hcb, minus_word, decide_eq_false hsg.1]
        simp only [Bool.false_eq_true, ite_false]
        rw [satE_pos]

#print axioms limb_words
#print axioms span_spec
#print axioms matchLower_spec
#print axioms expDigits_spec
#print axioms digit_run
#print axioms expPart_spec

end Library.Numerics.Decimal.ParseFloat.ParseFloatScan
