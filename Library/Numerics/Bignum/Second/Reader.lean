module

public import Library.Numerics.Bignum.Second.Read

@[expose] public section

/-!
The readers of text of the second iteration.  `intOfTextDC` has the program of the first
iteration's `intOfText` with `decimalValueDC` in place of `decimalValue`, so it returns what
`intOfText` returns on every array, with the same statuses (`intOfTextDC_eq_intOfText`), and
therefore `readSpec`.  `natOfTextDCWith` reads the grammar without the sign: on a text that does
not start with `-`, it tests what `intOfText` tests with no sign and returns the magnitude, and a
text that starts with `-` fails its test of digits (`natOfTextDCWith_eq_intOfText`).  The
specification `natReadSpec` stands in the same relation to `readSpec` (`natReadSpec_eq`).
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open Library.Numerics.Decimal.Int64Text (digitsValue isDigitWord isDigitWord_iff isDigitW
  magnitude magnitude_cons digitsValue_pos denote denote_minus denote_plain denote_zero
  getElem!_of_toList toList_cons_of_size isDigitWord_ne48 magnitude_some)

/-- The integer reader of the second iteration returns what the first iteration's returns. -/
theorem intOfTextDC_eq_intOfText (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    intOfTextDC s = intOfText s := by
  have hn : s.size.toUInt64.toNat = s.size :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  unfold intOfTextDC intOfText
  lift_lets
  intro n neg start count
  have hn' : n.toNat = s.size := hn
  have hstart : start.toNat ≤ 1 := by
    show (if neg then (1 : UInt64) else 0).toNat ≤ 1; split <;> simp
  by_cases h0 : n = 0
  · have h0' : (n == 0) = true := by rw [h0]; rfl
    rw [if_pos h0', if_pos h0']
  have h0' : ¬ (n == 0) = true := by simpa using h0
  rw [if_neg h0', if_neg h0']
  have hn1 : 1 ≤ n.toNat := by
    have : n.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    omega
  have hcount : count.toNat = n.toNat - start.toNat := by
    show (n - start).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]
      show (if neg then (1 : UInt64) else 0).toNat ≤ n.toNat; split <;> simp <;> omega)]
  by_cases hc0 : count = 0
  · have hc0' : (count == 0) = true := by rw [hc0]; rfl
    rw [if_pos hc0', if_pos hc0']
  have hc0' : ¬ (count == 0) = true := by simpa using hc0
  rw [if_neg hc0', if_neg hc0']
  have hc1 : 1 ≤ count.toNat := by
    have : count.toNat ≠ 0 := fun h => hc0 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    omega
  by_cases hok : (allDigits s start count && (s[start.toNat]! != 48 || (count == 1 && !neg))) = true
  · rw [if_pos hok, if_pos hok]
    have hsz : start.toNat + count.toNat = s.size := by rw [hcount]; omega
    have hall := allDigits_spec s start count (by omega) hsz
    have hdig : ∀ w ∈ s.toList.drop start.toNat, isDigitWord w = true := by
      rw [Bool.and_eq_true, hall] at hok
      exact List.all_eq_true.mp hok.1
    show (true, (⟨neg, decimalValueDC karaThreshold readBase s start count⟩ : BigInt)) =
      (true, ⟨neg, decimalValue s start count⟩)
    rw [decimalValueDC_eq_decimalValue _ _ s start count hs hsz hc1 hdig]
  · rw [if_neg hok, if_neg hok]

/-- The integer reader of the second iteration returns the specification's result. -/
theorem intOfTextDC_eq (s : Array UInt64) (hs : s.size < 2 ^ 32) : intOfTextDC s = readSpec s := by
  rw [intOfTextDC_eq_intOfText s hs, intOfText_eq s hs]

/-- The first word of an array that starts with `-`. -/
theorem toList_of_minus {s : Array UInt64} (h : s[(0 : UInt64).toNat]! = 45) :
    ∃ t, s.toList = 45 :: t := by
  have hs : s.size ≠ 0 := by
    intro h0
    rw [getElem!_neg s _ (by simp [h0])] at h
    exact absurd h (by decide)
  obtain ⟨a, t, hl⟩ := toList_cons_of_size s hs
  have : s[(0 : UInt64).toNat]! = a := by
    rw [getElem!_of_toList s _ (by simp; omega)]; simp [hl]
  exact ⟨t, by rw [hl, ← this, h]⟩

/-- The natural reader of the second iteration on a text that starts with `-` rejects it, and on
any other text returns the flag and the magnitude of the first iteration's integer reader. -/
theorem natOfTextDCWith_eq_intOfText (t E : UInt64) (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    natOfTextDCWith t E s = if s[(0 : UInt64).toNat]! = 45 then (false, #[])
      else ((intOfText s).1, (intOfText s).2.mag) := by
  have hn : s.size.toUInt64.toNat = s.size :=
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  have hall := allDigits_spec s 0 s.size.toUInt64 (by omega) (by rw [hn]; simp)
  unfold natOfTextDCWith intOfText
  lift_lets
  intro n neg start count
  have hn' : n.toNat = s.size := hn
  by_cases h0 : n = 0
  · have h0' : (n == 0) = true := by rw [h0]; rfl
    rw [if_pos h0', if_pos h0']; split <;> rfl
  have h0' : ¬ (n == 0) = true := by simpa using h0
  rw [if_neg h0', if_neg h0']
  have hn1 : 1 ≤ n.toNat := by
    have : n.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    omega
  by_cases h45 : s[(0 : UInt64).toNat]! = 45
  · rw [if_pos h45]
    obtain ⟨r, hr⟩ := toList_of_minus h45
    have hfalse : allDigits s 0 n = false := by
      show allDigits s 0 s.size.toUInt64 = false
      rw [hall, show (0 : UInt64).toNat = 0 from rfl, List.drop_zero, hr]
      simp only [List.all_cons, Bool.and_eq_false_iff]
      left; decide
    rw [if_neg (by rw [hfalse]; simp)]
  · rw [if_neg h45]
    have hneg : neg = false := by
      show (s[(0 : UInt64).toNat]! == 45) = false; simpa using h45
    have hst : start = 0 := by show (if neg then (1 : UInt64) else 0) = 0; rw [hneg]; rfl
    have hcn : count = n := by show n - start = n; rw [hst]; exact UInt64.sub_zero n
    have hc0 : ¬ (count == 0) = true := by rw [hcn]; exact h0'
    rw [if_neg hc0, hcn, hst, hneg]
    simp only [Bool.not_false, Bool.and_true]
    by_cases hok : (allDigits s 0 n && (s[(0 : UInt64).toNat]! != 48 || n == 1)) = true
    · rw [if_pos hok, if_pos hok]
      have hdig : ∀ w ∈ s.toList.drop (0 : UInt64).toNat, isDigitWord w = true := by
        rw [Bool.and_eq_true] at hok
        have h1 : allDigits s 0 s.size.toUInt64 = true := hok.1
        rw [hall] at h1
        exact List.all_eq_true.mp h1
      show (true, decimalValueDC t E s 0 n) = (true, decimalValue s 0 n)
      rw [decimalValueDC_eq_decimalValue t E s 0 n hs (by rw [hn']; simp) hn1 hdig]
    · rw [if_neg hok, if_neg hok]

/-- `natReadSpec` rejects a text that starts with `-` and on any other text returns the flag and
the magnitude of `readSpec`. -/
theorem natReadSpec_eq (s : Array UInt64) :
    natReadSpec s = if s[(0 : UInt64).toNat]! = 45 then (false, #[])
      else ((readSpec s).1, (readSpec s).2.mag) := by
  unfold natReadSpec readSpec
  by_cases h45 : s[(0 : UInt64).toNat]! = 45
  · rw [if_pos h45]
    obtain ⟨r, hr⟩ := toList_of_minus h45
    rw [hr, denote_minus _ (by simp) (by simp), List.tail_cons]
    cases hm : magnitude r with
    | none => simp [limbsOf_zero]
    | some v =>
      obtain ⟨d, rest, hdr, hd1, -, -, hv⟩ := magnitude_some hm
      have hpos : 0 < v := by rw [hv, hdr]; exact digitsValue_pos hd1
      simp only [Option.map_some]
      rw [if_neg (by omega), limbsOf_zero]
  · rw [if_neg h45]
    have h45' : ¬ s.toList.head? = some 45 := by
      intro h
      by_cases hs0 : s.size = 0
      · simp [List.eq_nil_of_length_eq_zero (by simpa using hs0 : s.toList.length = 0)] at h
      · obtain ⟨a, t, hl⟩ := toList_cons_of_size s hs0
        rw [hl] at h
        have : s[(0 : UInt64).toNat]! = a := by
          rw [getElem!_of_toList s _ (by simp; omega)]; simp [hl]
        simp at h
        exact h45 (this.trans h)
    by_cases h48 : s.toList = [48]
    · rw [h48, denote_zero]
      simp [BigInt.ofInt]
    · rw [denote_plain _ h48 h45']
      cases magnitude s.toList with
      | none => simp [BigInt.ofInt, limbsOf_zero]
      | some v => simp [BigInt.ofInt]

/-- The natural reader of the second iteration returns the specification's result. -/
theorem natOfTextDCWith_eq (t E : UInt64) (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    natOfTextDCWith t E s = natReadSpec s := by
  rw [natOfTextDCWith_eq_intOfText t E s hs, natReadSpec_eq, intOfText_eq s hs]

theorem natOfTextDC_eq (s : Array UInt64) (hs : s.size < 2 ^ 32) : natOfTextDC s = natReadSpec s :=
  natOfTextDCWith_eq _ _ s hs

/-- The limbs that the natural reader returns are canonical. -/
theorem natOfTextDC_canonical (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    Canonical (natOfTextDC s).2 := by
  rw [natOfTextDC_eq s hs]
  unfold natReadSpec
  split
  · split <;> exact canonical_limbsOf _
  · exact canonical_limbsOf _

/-- The integer that the integer reader returns is canonical. -/
theorem intOfTextDC_canonical (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    (intOfTextDC s).2.Canonical := by
  rw [intOfTextDC_eq s hs]
  unfold readSpec
  split <;> exact canonical_ofInt _

end Library.Numerics.Bignum
