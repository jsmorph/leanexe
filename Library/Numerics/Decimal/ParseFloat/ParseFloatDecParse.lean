import Library.Numerics.Decimal.ParseFloat.ParseFloatDigits

/-!
`ParseFloat.decParse` against the decoder.  For the rest `r = s.drop i0` of a string after its
sign, `decBranch general r` is the decoder's decimal branch: the significand split by
`decodeSig` (general grammar) or `decodeJson` (RFC 8259) and the optional exponent.  `dec_split`
names the positions that both compute: the integer digits end at `i1`, a point may follow, the
fraction digits end at `i2`, and the exponent part is `s.drop i2`.  `decParse_spec` proves that
`decParse`'s flag is the decoder's success, and that its limbs, count, biased exponent, and sticky
flag are those of the significand's digits `L = i ++ f`: the first `kept` digits after the leading
zeros, the exponent of the last kept digit with the exponent saturated at `10 ^ 11`, and whether
a dropped digit is nonzero.
-/

namespace Library.Numerics.Decimal.ParseFloat.ParseFloatDecParse
open ParseFloat Library.Numerics.Arithmetic.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.Shared.StrconvGrammar Library.Numerics.Decimal.Shared.StrconvDecode ParseFloatRound ParseFloatScan
  ParseFloatDigits

/-- The decoder's decimal branch: the integer digits, the fraction digits, and the exponent. -/
def decBranch (general : Bool) (r : List UInt8) : Option (List UInt8 × List UInt8 × ℤ) :=
  match (if general = true then decodeSig isDigit r else decodeJson r) with
  | some (i, f, x) => (decodeOptExp (ascii "eE") x).map fun e => (i, f, e)
  | none => none

theorem dropWhile_eq_drop (p : UInt8 → Bool) (l : List UInt8) :
    l.dropWhile p = l.drop (l.takeWhile p).length := by
  have h := List.takeWhile_append_dropWhile (p := p) (l := l)
  calc l.dropWhile p = (l.takeWhile p ++ l.dropWhile p).drop (l.takeWhile p).length := by
        rw [List.drop_left]
    _ = l.drop (l.takeWhile p).length := by rw [h]

theorem digit_ge_one (c : UInt8) (h : isDigit c = true) : (0x31 ≤ c) ↔ c ≠ 0x30 := by
  revert c; apply ParseFloatScan.byte_cases; decide +kernel

theorem digit_json1 (c : UInt8) (h : isDigit c = true) :
    (decide (c = 0x30 ∧ ([] : List UInt8) = []) || decide (0x31 ≤ c)) = true := by
  revert c; apply ParseFloatScan.byte_cases; decide +kernel

theorem jsonIntOk_iff (i : List UInt8) (h : ∀ b ∈ i, isDigit b = true) :
    jsonIntOk i = true ↔ i.length = 1 ∨ (1 < i.length ∧ byteAt i 0 ≠ 0x30) := by
  match i, h with
  | [], _ => simp [jsonIntOk]
  | [c], h =>
    have hc := h c (by simp)
    simp only [List.length_singleton, true_or, iff_true]
    exact digit_json1 c hc
  | c :: d :: ds, h =>
    have hc := h c (by simp)
    have h1 : jsonIntOk (c :: d :: ds) = decide (0x31 ≤ c) := by
      simp [jsonIntOk]
    rw [h1, decide_eq_true_iff, digit_ge_one c hc, byteAt_cons_zero]
    simp

/-- The positions of a decimal significand after its sign. -/
theorem dec_split (s : List UInt8) (i0 : ℕ) (hi0 : i0 ≤ s.length) (general : Bool) :
    let iL := (s.drop i0).takeWhile isDigit
    let i1 := i0 + iL.length
    let pt := decide (byteAt s i1 = 0x2E)
    let fL := if pt then (s.drop (i1 + 1)).takeWhile isDigit else []
    let i2 := if pt then i1 + 1 + fL.length else i1
    i2 ≤ s.length ∧ s.drop i1 = (s.drop i0).dropWhile isDigit ∧
    (if general = true then decodeSig isDigit (s.drop i0) else decodeJson (s.drop i0)) =
      if (if general = true then iL.length + fL.length ≠ 0
          else jsonIntOk iL = true ∧ (pt = true → fL ≠ [])) then some (iL, fL, s.drop i2)
      else none := by
  intro iL i1 pt fL i2
  have hiLp : iL.length ≤ s.length - i0 := by
    have := (List.takeWhile_prefix isDigit (l := s.drop i0)).length_le
    rw [List.length_drop] at this; exact this
  have hd1 : (s.drop i0).dropWhile isDigit = s.drop i1 := by
    rw [dropWhile_eq_drop, List.drop_drop]
  have hi1 : i1 ≤ s.length := by show i0 + iL.length ≤ s.length; omega
  have hptlt : pt = true → i1 < s.length := by
    intro h; by_contra hc
    have : byteAt s i1 = 0 := byteAt_ge _ _ (by omega)
    have h' : byteAt s i1 = 0x2E := of_decide_eq_true h
    rw [this] at h'; exact absurd h' (by decide)
  have hi2 : i2 ≤ s.length := by
    by_cases hpt : pt = true
    · have hfl : fL = (s.drop (i1 + 1)).takeWhile isDigit := by
        show (if pt then _ else []) = _; rw [ite_eq_left hpt]
      have hfp : fL.length ≤ s.length - (i1 + 1) := by
        rw [hfl]
        have := (List.takeWhile_prefix isDigit (l := s.drop (i1 + 1))).length_le
        rw [List.length_drop] at this; exact this
      have := hptlt hpt
      show (if pt then i1 + 1 + fL.length else i1) ≤ s.length
      rw [ite_eq_left hpt]; omega
    · show (if pt then i1 + 1 + fL.length else i1) ≤ s.length
      rw [ite_eq_right hpt]; exact hi1
  refine ⟨hi2, hd1.symm, ?_⟩
  by_cases hpt : pt = true
  · -- a point follows the integer digits
    have hlt := hptlt hpt
    have hb : byteAt s i1 = 0x2E := of_decide_eq_true hpt
    have hcons : s.drop i1 = 0x2E :: s.drop (i1 + 1) := by
      rw [← hb, byteAt_lt _ _ hlt]; exact List.drop_eq_getElem_cons hlt
    have hfl : fL = (s.drop (i1 + 1)).takeWhile isDigit := by
      show (if pt then _ else []) = _; rw [ite_eq_left hpt]
    have hx : ((s.drop (i1 + 1)).dropWhile isDigit) = s.drop i2 := by
      show _ = s.drop (if pt then i1 + 1 + fL.length else i1)
      rw [ite_eq_left hpt, dropWhile_eq_drop, List.drop_drop, hfl]
    have hiff : iL ++ fL ≠ [] ↔ iL.length + fL.length ≠ 0 := by
      constructor
      · intro h h'; apply h; apply List.eq_nil_of_length_eq_zero; rw [List.length_append]; exact h'
      · intro h h'; apply h; have := congrArg List.length h'; simpa using this
    cases general with
    | true =>
      show decodeSig isDigit (s.drop i0) = _
      simp only [ite_true]
      unfold decodeSig
      rw [hd1, hcons]
      dsimp only
      rw [ite_eq_left rfl, ← hfl, hx]
      by_cases hne : iL.length + fL.length ≠ 0
      · rw [ite_eq_left (hiff.mpr hne), ite_eq_left hne]
      · rw [ite_eq_right (fun h => hne (hiff.mp h)), ite_eq_right hne]
    | false =>
      show decodeJson (s.drop i0) = _
      simp only [Bool.false_eq_true, ite_false]
      unfold decodeJson
      rw [hd1, hcons]
      dsimp only
      by_cases hj : jsonIntOk iL = true
      · rw [ite_eq_left hj, ite_eq_left rfl, ← hfl, hx]
        by_cases hf : fL ≠ []
        · rw [ite_eq_left hf, ite_eq_left ⟨hj, fun _ => hf⟩]
        · rw [ite_eq_right hf, ite_eq_right (fun h => hf (h.2 hpt))]
      · rw [ite_eq_right hj, ite_eq_right (fun h => hj h.1)]
  · -- no point
    have hfl : fL = [] := by show (if pt then _ else []) = _; rw [ite_eq_right hpt]
    have hi2' : i2 = i1 := by show (if pt then _ else i1) = i1; rw [ite_eq_right hpt]
    rw [hfl, hi2']
    have hnp : ∀ b t, s.drop i1 = b :: t → b ≠ 0x2E := by
      intro b t hr h
      apply hpt
      have := congrArg (fun l => byteAt l 0) hr
      simp only [byteAt_drop, add_zero, byteAt_cons_zero] at this
      exact decide_eq_true (this.trans h)
    have hiff : iL ≠ [] ↔ iL.length + ([] : List UInt8).length ≠ 0 := by
      simp [List.length_eq_zero_iff]
    cases general with
    | true =>
      show decodeSig isDigit (s.drop i0) = _
      simp only [ite_true]
      unfold decodeSig
      rw [hd1]
      rcases hr : s.drop i1 with _ | ⟨b, t⟩
      · dsimp only
        by_cases hne : iL.length + ([] : List UInt8).length ≠ 0
        · rw [ite_eq_left (hiff.mpr hne), ite_eq_left hne]
        · rw [ite_eq_right (fun h => hne (hiff.mp h)), ite_eq_right hne]
      · dsimp only
        rw [ite_eq_right (hnp b t hr)]
        by_cases hne : iL.length + ([] : List UInt8).length ≠ 0
        · rw [ite_eq_left (hiff.mpr hne), ite_eq_left hne]
        · rw [ite_eq_right (fun h => hne (hiff.mp h)), ite_eq_right hne]
    | false =>
      show decodeJson (s.drop i0) = _
      simp only [Bool.false_eq_true, ite_false]
      unfold decodeJson
      rw [hd1]
      by_cases hj : jsonIntOk iL = true
      · rw [ite_eq_left hj, ite_eq_left ⟨hj, fun h => absurd h hpt⟩]
        rcases hr : s.drop i1 with _ | ⟨b, t⟩
        · rfl
        · dsimp only
          rw [ite_eq_right (hnp b t hr)]
      · rw [ite_eq_right hj, ite_eq_right (fun h => hj h.1)]

theorem e_word (b : UInt8) : ((b.toUInt64 ||| 0x20) == 0x65) = decide (b ∈ ascii "eE") := by
  revert b; apply ParseFloatScan.byte_cases; decide +kernel

theorem point_word (b : UInt8) : (b.toUInt64 == 0x2E) = decide (b = 0x2E) := by
  revert b; apply ParseFloatScan.byte_cases; decide +kernel

theorem zero_word (b : UInt8) : (b.toUInt64 != 0x30) = decide (b ≠ 0x30) := by
  revert b; apply ParseFloatScan.byte_cases; decide +kernel

/-- `decParse` computes the decoder's decimal branch: its flag is the branch's success, and its
limbs, count, biased exponent, and sticky flag describe the digits of the significand. -/
theorem decParse_spec (general : Bool) (K : ℕ) (hK : K ≤ 2000) (s : List UInt8)
    (hs : s.length < 2 ^ 32) (i0 : ℕ) (hi0 : i0 ≤ s.length) :
    (decParse general (UInt64.ofNat K) (words s) (UInt64.ofNat i0)).1 =
        (decBranch general (s.drop i0)).isSome ∧
      ∀ i f e, decBranch general (s.drop i0) = some (i, f, e) →
        (∀ b ∈ i ++ f, isDigit b = true) ∧ i0 + (i ++ f).length ≤ s.length ∧
        Limbs (decParse general (UInt64.ofNat K) (words s) (UInt64.ofNat i0)).2.1 ∧
        val (decParse general (UInt64.ofNat K) (words s) (UInt64.ofNat i0)).2.1 =
          decValue (((i ++ f).drop ((i ++ f).takeWhile (· == 0x30)).length).take
            (min ((i ++ f).length - ((i ++ f).takeWhile (· == 0x30)).length) K)) ∧
        (decParse general (UInt64.ofNat K) (words s) (UInt64.ofNat i0)).2.1.size =
          (min ((i ++ f).length - ((i ++ f).takeWhile (· == 0x30)).length) K + 8) / 9 ∧
        (decParse general (UInt64.ofNat K) (words s) (UInt64.ofNat i0)).2.2.1.toNat =
          min ((i ++ f).length - ((i ++ f).takeWhile (· == 0x30)).length) K ∧
        ((decParse general (UInt64.ofNat K) (words s) (UInt64.ofNat i0)).2.2.2.1.toNat : ℤ) =
          2 ^ 62 + ParseFloatScan.satE e - f.length +
            ((i ++ f).length - ((i ++ f).takeWhile (· == 0x30)).length -
              min ((i ++ f).length - ((i ++ f).takeWhile (· == 0x30)).length) K : ℕ) ∧
        ((decParse general (UInt64.ofNat K) (words s) (UInt64.ofNat i0)).2.2.2.2 = true ↔
          ∃ k, ((i ++ f).takeWhile (· == 0x30)).length +
              min ((i ++ f).length - ((i ++ f).takeWhile (· == 0x30)).length) K ≤ k ∧
            k < (i ++ f).length ∧ byteAt (i ++ f) k ≠ 0x30) := by
  obtain ⟨hi2le, hd1, hsplit⟩ := dec_split s i0 hi0 general
  set iL := (s.drop i0).takeWhile isDigit with hiL
  set ni := iL.length with hni
  set i1 := i0 + ni with hi1
  set pt := decide (byteAt s i1 = 0x2E) with hpt
  set fL := if pt then (s.drop (i1 + 1)).takeWhile isDigit else [] with hfL
  set nf := fL.length with hnf
  set i2 := if pt then i1 + 1 + nf else i1 with hi2
  set L := iL ++ fL with hL
  have hsz := words_size64 s hs
  have hiLp : ni ≤ s.length - i0 := by
    have := (List.takeWhile_prefix isDigit (l := s.drop i0)).length_le
    rw [List.length_drop] at this; exact this
  have hi1le : i1 ≤ s.length := by omega
  have hiLd : ∀ b ∈ iL, isDigit b = true := takeWhile_all isDigit _
  have hfLd : ∀ b ∈ fL, isDigit b = true := by
    intro b hb
    rw [hfL] at hb
    split_ifs at hb
    · exact takeWhile_all isDigit _ b hb
    · simp at hb
  have hLd : ∀ b ∈ L, isDigit b = true := by
    intro b hb; rcases List.mem_append.mp hb with h | h
    · exact hiLd b h
    · exact hfLd b h
  have hptlt : pt = true → i1 < s.length := by
    intro h; by_contra hc
    have : byteAt s i1 = 0 := byteAt_ge _ _ (by omega)
    rw [hpt, this] at h; exact absurd (of_decide_eq_true h) (by decide)
  have hLlen : L.length = ni + nf := by rw [hL, List.length_append]
  have hi2eq : i2 = i0 + L.length + (if pt then 1 else 0) := by
    by_cases hp : pt = true
    · rw [hi2, ite_eq_left hp, ite_eq_left hp]; omega
    · have h0 : nf = 0 := by rw [hnf, hfL, ite_eq_right hp, List.length_nil]
      rw [hi2, ite_eq_right hp, ite_eq_right hp]; omega
  -- the positions of the digits
  have hreads : Reads s i0 ni L := by
    intro k hk
    unfold dpos
    by_cases hkn : k < ni
    · rw [ite_eq_left hkn, hL, ← byteAt_drop]
      have h1 : byteAt (s.drop i0) k = byteAt iL k := by
        rw [byteAt_lt _ _ (by rw [List.length_drop]; omega), byteAt_lt _ _ hkn]
        exact ((List.takeWhile_prefix isDigit).getElem hkn).symm
      rw [h1, byteAt_lt _ _ hkn, byteAt_lt _ _ (by rw [List.length_append]; omega)]
      simp [List.getElem_append_left hkn]
    · rw [ite_eq_right hkn]
      have hk' : k - ni < nf := by rw [hL, List.length_append] at hk; omega
      have hptt : pt = true := by
        by_contra h; rw [hnf, hfL, ite_eq_right h] at hk'; simp at hk'
      have hfl : fL = (s.drop (i1 + 1)).takeWhile isDigit := by rw [hfL, ite_eq_left hptt]
      have : byteAt L k = byteAt fL (k - ni) := by
        have e := byteAt_append iL fL (k - ni)
        rw [← hni, show ni + (k - ni) = k by omega] at e
        rw [hL]; exact e
      rw [this, show i0 + k + 1 = (i1 + 1) + (k - ni) by omega, ← byteAt_drop]
      have hk'' : k - ni < ((s.drop (i1 + 1)).takeWhile isDigit).length := by
        rw [← hfl, ← hnf]; exact hk'
      have hfp : ((s.drop (i1 + 1)).takeWhile isDigit).length ≤ (s.drop (i1 + 1)).length :=
        (List.takeWhile_prefix isDigit).length_le
      rw [hfl, byteAt_lt _ _ hk'', byteAt_lt _ _ (by omega)]
      exact ((List.takeWhile_prefix isDigit).getElem hk'').symm
  have hbound : i0 + L.length + 1 ≤ s.length + 1 := by
    have := hi2le; rw [hi2eq] at this; split_ifs at this <;> omega
  have hnis : ni ≤ s.length := by omega
  -- the words
  have hN : ∀ k, k ≤ s.length + 1 → (UInt64.ofNat k).toNat = k := fun k hk =>
    ofNat_toNat _ (by omega)
  have hw0 : (UInt64.ofNat i0).toNat = i0 := hN i0 (by omega)
  have hone : (1 : UInt64).toNat = 1 := rfl
  have hzero : (0 : UInt64).toNat = 0 := rfl
  have hw1 : span (words s) false (UInt64.ofNat i0) = UInt64.ofNat i1 := by
    have h1 : (span (words s) false (UInt64.ofNat i0)).toNat = i0 + ni := (digit_run s hs i0 hi0).1
    have h2 := hN i1 (by omega)
    apply UInt64.toNat_inj.mp; omega
  have hw2 : (limb (words s) (UInt64.ofNat i1) == 0x2E) = pt := by
    rw [limb_words s _ hs, hN i1 (by omega), point_word, hpt]
  have hw3 : (if pt = true then span (words s) false (UInt64.ofNat i1 + 1) else UInt64.ofNat i1) =
      UInt64.ofNat i2 := by
    by_cases hp : pt = true
    · have hlt := hptlt hp
      have h2 : i2 = i1 + 1 + nf := by rw [hi2, ite_eq_left hp]
      have hfl : fL = (s.drop (i1 + 1)).takeWhile isDigit := by rw [hfL, ite_eq_left hp]
      have e1 : UInt64.ofNat i1 + 1 = UInt64.ofNat (i1 + 1) := by
        have a1 := hN i1 (by omega)
        have a2 := hN (i1 + 1) (by omega)
        have a3 := toNat_add' (UInt64.ofNat i1) 1 (by omega)
        apply UInt64.toNat_inj.mp; omega
      have h3 : (span (words s) false (UInt64.ofNat (i1 + 1))).toNat = i1 + 1 + nf := by
        rw [(digit_run s hs (i1 + 1) (by omega)).1, hnf, hfl]
      have e2 := hN i2 (by omega)
      rw [ite_eq_left hp, e1]
      apply UInt64.toNat_inj.mp; omega
    · rw [ite_eq_right hp, hi2, ite_eq_right hp]
  have hw4 : UInt64.ofNat i1 - UInt64.ofNat i0 = UInt64.ofNat ni := by
    have e1 := hN i1 (by omega)
    have e2 := hN ni (by omega)
    have e3 := toNat_sub' (UInt64.ofNat i1) (UInt64.ofNat i0) (by omega)
    apply UInt64.toNat_inj.mp; omega
  have hw5 : (if pt = true then UInt64.ofNat i2 - UInt64.ofNat i1 - 1 else 0) = UInt64.ofNat nf := by
    by_cases hp : pt = true
    · have h2 : i2 = i1 + 1 + nf := by rw [hi2, ite_eq_left hp]
      have e1 := hN i1 (by omega)
      have e2 := hN i2 (by omega)
      have e4 := hN nf (by omega)
      have e3 := toNat_sub' (UInt64.ofNat i2) (UInt64.ofNat i1) (by omega)
      have e5 := toNat_sub' (UInt64.ofNat i2 - UInt64.ofNat i1) 1 (by omega)
      rw [ite_eq_left hp]
      apply UInt64.toNat_inj.mp; omega
    · have h0 : nf = 0 := by rw [hnf, hfL, ite_eq_right hp, List.length_nil]
      have e4 := hN nf (by omega)
      rw [ite_eq_right hp]
      apply UInt64.toNat_inj.mp; omega
  have hw6 : UInt64.ofNat i2 + 1 = UInt64.ofNat (i2 + 1) := by
    have e1 := hN i2 (by omega)
    have e2 := hN (i2 + 1) (by omega)
    have e3 := toNat_add' (UInt64.ofNat i2) 1 (by omega)
    apply UInt64.toNat_inj.mp; omega
  have hw7 : UInt64.ofNat ni + UInt64.ofNat nf = UInt64.ofNat L.length := by
    have e1 := hN ni (by omega)
    have e2 := hN nf (by omega)
    have e3 := hN L.length (by omega)
    have e4 := toNat_add' (UInt64.ofNat ni) (UInt64.ofNat nf) (by omega)
    apply UInt64.toNat_inj.mp; omega
  set z := (L.takeWhile (· == 0x30)).length with hz
  have hzL : z ≤ L.length := (List.takeWhile_prefix _).length_le
  have hw8 : leadingZeros (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat L.length) =
      UInt64.ofNat z := by
    have e1 : (leadingZeros (words s) (UInt64.ofNat i0) (UInt64.ofNat ni)
        (UInt64.ofNat L.length)).toNat = z := leadingZeros_spec s hs i0 ni L hreads hbound hnis
    have e2 := hN z (by omega)
    apply UInt64.toNat_inj.mp; omega
  set kept := min (L.length - z) K with hkept
  have hw9 : min (UInt64.ofNat L.length - UInt64.ofNat z) (UInt64.ofNat K) = UInt64.ofNat kept := by
    have e1 := hN L.length (by omega)
    have e2 := hN z (by omega)
    have e3 := hN kept (by omega)
    have e4 : (UInt64.ofNat K).toNat = K := ofNat_toNat _ (by omega)
    have e5 := toNat_sub' (UInt64.ofNat L.length) (UInt64.ofNat z) (by omega)
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_min]; omega
  have hw10 : UInt64.ofNat z + UInt64.ofNat kept = UInt64.ofNat (z + kept) := by
    have e1 := hN z (by omega)
    have e2 := hN kept (by omega)
    have e3 := hN (z + kept) (by omega)
    have e4 := toNat_add' (UInt64.ofNat z) (UInt64.ofNat kept) (by omega)
    apply UInt64.toNat_inj.mp; omega
  have hdp : decParse general (UInt64.ofNat K) (words s) (UInt64.ofNat i0) =
      ((if general = true then UInt64.ofNat L.length != 0
          else (UInt64.ofNat ni == 1 || (1 < UInt64.ofNat ni &&
              limb (words s) (UInt64.ofNat i0) != 0x30)) && (!pt || UInt64.ofNat nf != 0)) &&
        (UInt64.ofNat i2 == (words s).size.toUInt64 ||
          ((limb (words s) (UInt64.ofNat i2) ||| 0x20) == 0x65 &&
            (expPart (words s) (UInt64.ofNat (i2 + 1))).1)),
       digitsVal (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat z) (UInt64.ofNat kept),
       UInt64.ofNat kept,
       (if UInt64.ofNat i2 != (words s).size.toUInt64 &&
            (expPart (words s) (UInt64.ofNat (i2 + 1))).2.1 then
          0x4000000000000000 - (expPart (words s) (UInt64.ofNat (i2 + 1))).2.2
        else if UInt64.ofNat i2 == (words s).size.toUInt64 then 0x4000000000000000
        else 0x4000000000000000 + (expPart (words s) (UInt64.ofNat (i2 + 1))).2.2) -
          UInt64.ofNat nf + (UInt64.ofNat L.length - UInt64.ofNat z - UInt64.ofNat kept),
       anyNonzero (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat (z + kept))
         (UInt64.ofNat L.length)) := by
    unfold decParse
    simp only [hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10]
  rw [hdp]
  dsimp only
  -- the decoder's branch
  have hbranch : decBranch general (s.drop i0) =
      if (if general = true then ni + nf ≠ 0 else jsonIntOk iL = true ∧ (pt = true → fL ≠ []))
      then (decodeOptExp (ascii "eE") (s.drop i2)).map (fun e => (iL, fL, e))
      else none := by
    unfold decBranch; rw [hsplit]; split_ifs <;> rfl
  have hflag1 : (if general = true then UInt64.ofNat L.length != 0
      else (UInt64.ofNat ni == 1 || (1 < UInt64.ofNat ni &&
          limb (words s) (UInt64.ofNat i0) != 0x30)) && (!pt || UInt64.ofNat nf != 0)) =
      decide (if general = true then ni + nf ≠ 0
        else jsonIntOk iL = true ∧ (pt = true → fL ≠ [])) := by
    have hl := hN L.length (by omega)
    have hni' := hN ni (by omega)
    have hnf' := hN nf (by omega)
    cases general with
    | true =>
      simp only [ite_true]
      rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
      constructor
      · intro h h'; apply h; apply UInt64.toNat_inj.mp; rw [hzero]; omega
      · intro h h'; apply h; have := congrArg UInt64.toNat h'; rw [hzero] at this; omega
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
        Bool.not_eq_true', bne_iff_ne, ne_eq]
      rw [jsonIntOk_iff iL hiLd]
      have hn1 : (UInt64.ofNat ni = 1) ↔ ni = 1 := by
        constructor
        · intro h; have := congrArg UInt64.toNat h; rw [hone] at this; omega
        · intro h; apply UInt64.toNat_inj.mp; rw [hone]; omega
      have hn2 : (1 < UInt64.ofNat ni) ↔ 1 < ni := by
        rw [UInt64.lt_iff_toNat_lt, hone, hni']
      have hn3 : (UInt64.ofNat nf = 0) ↔ nf = 0 := by
        constructor
        · intro h; have := congrArg UInt64.toNat h; rw [hzero] at this; omega
        · intro h; apply UInt64.toNat_inj.mp; rw [hzero]; omega
      have hb0 : 1 ≤ ni → (limb (words s) (UInt64.ofNat i0) = 0x30 ↔ byteAt iL 0 = 0x30) := by
        intro h
        rw [limb_words s _ hs, hw0]
        have : byteAt s i0 = byteAt iL 0 := by
          have e1 : byteAt s i0 = byteAt (s.drop i0) 0 := by rw [byteAt_drop, add_zero]
          rw [e1, byteAt_lt _ _ (by rw [List.length_drop]; omega), byteAt_lt _ _ (by omega)]
          have h0 : 0 < ((s.drop i0).takeWhile isDigit).length := by rw [← hiL, ← hni]; omega
          exact ((List.takeWhile_prefix isDigit).getElem h0).symm
        rw [this]
        constructor
        · intro h'; exact UInt8.toUInt64_inj.mp (h'.trans rfl)
        · intro h'; rw [h']; rfl
      have hfne : fL ≠ [] ↔ nf ≠ 0 := by
        rw [hnf, ne_eq, ne_eq, List.length_eq_zero_iff]
      rw [hn1, hn2, hn3]
      constructor
      · rintro ⟨h1, h2⟩
        have h2' : pt = true → fL ≠ [] := by
          intro hp
          rcases h2 with h2 | h2
          · rw [h2] at hp; exact absurd hp (by decide)
          · exact hfne.mpr h2
        refine ⟨?_, h2'⟩
        rcases h1 with h1 | ⟨h1, h1'⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, fun h => h1' ((hb0 (by omega)).mpr h)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · rcases h1 with h1 | ⟨h1, h1'⟩
          · exact Or.inl h1
          · exact Or.inr ⟨h1, fun h => h1' ((hb0 (by omega)).mp h)⟩
        · by_cases hp : pt = true
          · right; exact hfne.mp (h2 hp)
          · left; simpa using hp
  have hexpflag : (UInt64.ofNat i2 == (words s).size.toUInt64 ||
      ((limb (words s) (UInt64.ofNat i2) ||| 0x20) == 0x65 &&
        (expPart (words s) (UInt64.ofNat (i2 + 1))).1)) =
      (decodeOptExp (ascii "eE") (s.drop i2)).isSome := by
    by_cases hi2n : i2 = s.length
    · have h1 : (UInt64.ofNat i2 == (words s).size.toUInt64) = true := by
        rw [beq_iff_eq]; apply UInt64.toNat_inj.mp
        rw [hN i2 (by omega), hsz]; exact hi2n
      rw [h1, Bool.true_or, List.drop_eq_nil_of_le (by omega)] <;> rfl
    · have hlt : i2 < s.length := by omega
      have h1 : (UInt64.ofNat i2 == (words s).size.toUInt64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq]; intro h; apply hi2n
        have := congrArg UInt64.toNat h; rwa [hN i2 (by omega), hsz] at this
      have hcons : s.drop i2 = byteAt s i2 :: s.drop (i2 + 1) := by
        rw [byteAt_lt _ _ hlt]; exact List.drop_eq_getElem_cons hlt
      rw [h1, Bool.false_or, hcons, limb_words s _ hs, hN i2 (by omega), e_word, decodeOptExp,
        ite_eq_right (List.cons_ne_nil _ _), decodeExp]
      have hep := (expPart_spec s (i2 + 1) (by omega) hs).1
      by_cases hm : byteAt s i2 ∈ ascii "eE"
      · rw [decide_eq_true hm, Bool.true_and, ite_eq_left hm, Bool.eq_iff_iff]
        exact hep
      · rw [decide_eq_false hm, Bool.false_and, ite_eq_right hm] <;> rfl
  refine ⟨?_, ?_⟩
  · rw [hflag1, hexpflag, hbranch]
    by_cases hv : (if general = true then ni + nf ≠ 0
        else jsonIntOk iL = true ∧ (pt = true → fL ≠ []))
    · rw [decide_eq_true hv, Bool.true_and, ite_eq_left hv, Option.isSome_map]
    · rw [decide_eq_false hv, Bool.false_and, ite_eq_right hv] <;> rfl
  intro i f e hbr
  rw [hbranch] at hbr
  by_cases hv : (if general = true then ni + nf ≠ 0
      else jsonIntOk iL = true ∧ (pt = true → fL ≠ []))
  swap
  · rw [ite_eq_right hv] at hbr; cases hbr
  rw [ite_eq_left hv] at hbr
  rcases hopt : decodeOptExp (ascii "eE") (s.drop i2) with _ | e'
  · rw [hopt] at hbr; simp at hbr
  rw [hopt] at hbr
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hbr
  obtain ⟨rfl, rfl, he⟩ := hbr
  rw [← he, ← hL, ← hz, ← hkept]
  obtain ⟨d1, d2, d3⟩ := digitsVal_spec s hs i0 ni L hreads hbound hnis hLd z kept (by omega)
  refine ⟨hLd, by omega, d1, d2, d3, hN kept (by omega), ?_,
    anyNonzero_spec s hs i0 ni L hreads hbound hnis (z + kept) L.length (by omega) le_rfl⟩
  -- the biased exponent of the last kept digit
  set E := expPart (words s) (UInt64.ofNat (i2 + 1)) with hE
  have htail : (UInt64.ofNat L.length - UInt64.ofNat z - UInt64.ofNat kept).toNat =
      L.length - z - kept := by
    have e1 := hN L.length (by omega)
    have e2 := hN z (by omega)
    have e3 := hN kept (by omega)
    have e4 := toNat_sub' (UInt64.ofNat L.length) (UInt64.ofNat z) (by omega)
    have e5 := toNat_sub' (UInt64.ofNat L.length - UInt64.ofNat z) (UInt64.ofNat kept) (by omega)
    omega
  have hfinal : ∀ W : UInt64, 2 ^ 62 - 2 ^ 40 ≤ W.toNat → W.toNat ≤ 2 ^ 62 + 2 ^ 40 →
      ((W - UInt64.ofNat nf + (UInt64.ofNat L.length - UInt64.ofNat z - UInt64.ofNat kept)).toNat
        : ℤ) = W.toNat - nf + ((L.length - z - kept : ℕ) : ℤ) := by
    intro W h1 h2
    have e1 := hN nf (by omega)
    have e2 := toNat_sub' W (UInt64.ofNat nf) (by omega)
    have e3 := toNat_add' (W - UInt64.ofNat nf)
      (UInt64.ofNat L.length - UInt64.ofNat z - UInt64.ofNat kept) (by omega)
    omega
  have hsize : (words s).size.toUInt64 = UInt64.ofNat s.length := by
    apply UInt64.toNat_inj.mp; rw [hsz, hN s.length (by omega)]
  by_cases hi2n : i2 = s.length
  · have h1 : (UInt64.ofNat i2 == (words s).size.toUInt64) = true := by
      rw [beq_iff_eq, hsize, hi2n]
    have h1' : (UInt64.ofNat i2 != (words s).size.toUInt64) = false := by
      rw [bne, h1, Bool.not_true]
    have he0 : e' = 0 := by
      rw [List.drop_eq_nil_of_le (by omega)] at hopt
      simp only [decodeOptExp, ite_true, Option.some.injEq] at hopt
      exact hopt.symm
    have hs0 : ParseFloatScan.satE 0 = 0 := by unfold ParseFloatScan.satE; omega
    rw [h1', Bool.false_and, ite_eq_right (show ¬(false = true) by decide), ite_eq_left h1,
      hfinal 0x4000000000000000 (by rw [bias_toNat]; omega) (by rw [bias_toNat]; omega),
      bias_toNat, he0, hs0]
    omega
  · have hlt : i2 < s.length := by omega
    have h1 : (UInt64.ofNat i2 == (words s).size.toUInt64) = false := by
      rw [beq_eq_false_iff_ne, ne_eq, hsize]; intro h; apply hi2n
      have := congrArg UInt64.toNat h; rwa [hN i2 (by omega), hN s.length (by omega)] at this
    have h1' : (UInt64.ofNat i2 != (words s).size.toUInt64) = true := by
      rw [bne, h1, Bool.not_false]
    have hcons : s.drop i2 = byteAt s i2 :: s.drop (i2 + 1) := by
      rw [byteAt_lt _ _ hlt]; exact List.drop_eq_getElem_cons hlt
    rw [hcons, decodeOptExp, ite_eq_right (List.cons_ne_nil _ _), decodeExp] at hopt
    by_cases hm : byteAt s i2 ∈ ascii "eE"
    swap
    · rw [ite_eq_right hm] at hopt; cases hopt
    rw [ite_eq_left hm] at hopt
    have hval := (expPart_spec s (i2 + 1) (by omega) hs).2 e' hopt
    rw [← hE] at hval
    have hsat1 : -(10 : ℤ) ^ 11 ≤ ParseFloatScan.satE e' := by unfold ParseFloatScan.satE; omega
    have hsat2 : ParseFloatScan.satE e' ≤ 10 ^ 11 := by unfold ParseFloatScan.satE; omega
    rw [h1', Bool.true_and]
    by_cases hneg : E.2.1 = true
    · rw [ite_eq_left hneg] at hval ⊢
      have hle : E.2.2.toNat ≤ 10 ^ 11 := by omega
      have hW : (0x4000000000000000 - E.2.2).toNat = 2 ^ 62 - E.2.2.toNat := by
        rw [toNat_sub' _ _ (by rw [bias_toNat]; omega), bias_toNat]
      rw [hfinal _ (by rw [hW]; omega) (by rw [hW]; omega), hW]
      omega
    · rw [ite_eq_right hneg] at hval
      rw [ite_eq_right hneg, h1, ite_eq_right (show ¬(false = true) by decide)]
      have hle : E.2.2.toNat ≤ 10 ^ 11 := by omega
      have hW : (0x4000000000000000 + E.2.2).toNat = 2 ^ 62 + E.2.2.toNat := by
        rw [toNat_add' _ _ (by rw [bias_toNat]; omega), bias_toNat]
      rw [hfinal _ (by rw [hW]; omega) (by rw [hW]; omega), hW]
      omega

#print axioms dec_split
#print axioms decParse_spec

end Library.Numerics.Decimal.ParseFloat.ParseFloatDecParse
