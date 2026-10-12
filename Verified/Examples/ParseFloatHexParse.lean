import Verified.Examples.ParseFloatDecParse

/-!
`ParseFloat.hexParse` against the decoder.  For the rest `r = s.drop i0` of a string after its
sign and `0x`, `hexBranch r` is the decoder's hexadecimal branch: the significand split by
`decodeSig isHexDigit` and the required binary exponent.  `sig_split` names the positions of a
significand of the general grammar for any digit class.  `hexParse_spec` proves that `hexParse`'s
flag is the branch's success, and that its value, sticky flag, and biased exponent are those of the
significand's digits `L = i ++ f`: the first 15 digits after the leading zeros, whether a dropped
digit is nonzero, and the binary exponent of the last kept digit, with the exponent saturated at
`10 ^ 11`, plus `nu`.
-/

namespace Verified.Examples.ParseFloatHexParse
open ParseFloat Uscale UscaleTheorem StrconvGrammar StrconvDecode ParseFloatRound ParseFloatScan
  ParseFloatDigits ParseFloatDecParse

/-- The decoder's hexadecimal branch: the integer digits, the fraction digits, and the binary
exponent. -/
def hexBranch (r : List UInt8) : Option (List UInt8 × List UInt8 × ℤ) :=
  match decodeSig isHexDigit r with
  | some (i, f, x) => (decodeExp (ascii "pP") x).map fun e => (i, f, e)
  | none => none

/-- The positions of a significand of the general grammar with digit class `p`. -/
theorem sig_split (p : UInt8 → Bool) (s : List UInt8) (i0 : ℕ) (hi0 : i0 ≤ s.length) :
    let iL := (s.drop i0).takeWhile p
    let i1 := i0 + iL.length
    let pt := decide (byteAt s i1 = 0x2E)
    let fL := if pt then (s.drop (i1 + 1)).takeWhile p else []
    let i2 := if pt then i1 + 1 + fL.length else i1
    i2 ≤ s.length ∧
    decodeSig p (s.drop i0) =
      if iL.length + fL.length ≠ 0 then some (iL, fL, s.drop i2) else none := by
  intro iL i1 pt fL i2
  have hiLp : iL.length ≤ s.length - i0 := by
    have := (List.takeWhile_prefix p (l := s.drop i0)).length_le
    rw [List.length_drop] at this; exact this
  have hd1 : (s.drop i0).dropWhile p = s.drop i1 := by
    rw [dropWhile_eq_drop, List.drop_drop]
  have hi1 : i1 ≤ s.length := by show i0 + iL.length ≤ s.length; omega
  have hptlt : pt = true → i1 < s.length := by
    intro h; by_contra hc
    have : byteAt s i1 = 0 := byteAt_ge _ _ (by omega)
    have h' : byteAt s i1 = 0x2E := of_decide_eq_true h
    rw [this] at h'; exact absurd h' (by decide)
  have hi2 : i2 ≤ s.length := by
    by_cases hpt : pt = true
    · have hfl : fL = (s.drop (i1 + 1)).takeWhile p := by
        show (if pt then _ else []) = _; rw [ite_eq_left hpt]
      have hfp : fL.length ≤ s.length - (i1 + 1) := by
        rw [hfl]
        have := (List.takeWhile_prefix p (l := s.drop (i1 + 1))).length_le
        rw [List.length_drop] at this; exact this
      have := hptlt hpt
      show (if pt then i1 + 1 + fL.length else i1) ≤ s.length
      rw [ite_eq_left hpt]; omega
    · show (if pt then i1 + 1 + fL.length else i1) ≤ s.length
      rw [ite_eq_right hpt]; exact hi1
  refine ⟨hi2, ?_⟩
  unfold decodeSig
  rw [hd1]
  by_cases hpt : pt = true
  · have hlt := hptlt hpt
    have hb : byteAt s i1 = 0x2E := of_decide_eq_true hpt
    have hcons : s.drop i1 = 0x2E :: s.drop (i1 + 1) := by
      rw [← hb, byteAt_lt _ _ hlt]; exact List.drop_eq_getElem_cons hlt
    have hfl : fL = (s.drop (i1 + 1)).takeWhile p := by
      show (if pt then _ else []) = _; rw [ite_eq_left hpt]
    have hx : ((s.drop (i1 + 1)).dropWhile p) = s.drop i2 := by
      show _ = s.drop (if pt then i1 + 1 + fL.length else i1)
      rw [ite_eq_left hpt, dropWhile_eq_drop, List.drop_drop, hfl]
    have hiff : iL ++ fL ≠ [] ↔ iL.length + fL.length ≠ 0 := by
      constructor
      · intro h h'; apply h; apply List.eq_nil_of_length_eq_zero; rw [List.length_append]; exact h'
      · intro h h'; apply h; have := congrArg List.length h'; simpa using this
    rw [hcons]
    dsimp only
    rw [ite_eq_left rfl, ← hfl, hx]
    by_cases hne : iL.length + fL.length ≠ 0
    · rw [ite_eq_left (hiff.mpr hne), ite_eq_left hne]
    · rw [ite_eq_right (fun h => hne (hiff.mp h)), ite_eq_right hne]
  · have hfl : fL = [] := by show (if pt then _ else []) = _; rw [ite_eq_right hpt]
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

theorem p_word (b : UInt8) : ((b.toUInt64 ||| 0x20) == 0x70) = decide (b ∈ ascii "pP") := by
  revert b; apply ParseFloatScan.byte_cases; decide +kernel

theorem cls_true : cls true = isHexDigit := by funext b; rfl

/-- `hexParse` computes the decoder's hexadecimal branch: its flag is the branch's success, and
its value, sticky flag, and biased exponent describe the digits of the significand. -/
theorem hexParse_spec (nu : ℕ) (hnu : nu ≤ 2000) (s : List UInt8) (hs : s.length < 2 ^ 32)
    (i0 : ℕ) (hi0 : i0 ≤ s.length) :
    (hexParse (UInt64.ofNat nu) (words s) (UInt64.ofNat i0)).1 = (hexBranch (s.drop i0)).isSome ∧
      ∀ i f e, hexBranch (s.drop i0) = some (i, f, e) →
        (∀ b ∈ i ++ f, isHexDigit b = true) ∧
        (hexParse (UInt64.ofNat nu) (words s) (UInt64.ofNat i0)).2.1.toNat =
          hexValue (((i ++ f).drop ((i ++ f).takeWhile (· == 0x30)).length).take
            (min ((i ++ f).length - ((i ++ f).takeWhile (· == 0x30)).length) 15)) ∧
        ((hexParse (UInt64.ofNat nu) (words s) (UInt64.ofNat i0)).2.2.1 = true ↔
          ∃ k, ((i ++ f).takeWhile (· == 0x30)).length +
              min ((i ++ f).length - ((i ++ f).takeWhile (· == 0x30)).length) 15 ≤ k ∧
            k < (i ++ f).length ∧ byteAt (i ++ f) k ≠ 0x30) ∧
        ((hexParse (UInt64.ofNat nu) (words s) (UInt64.ofNat i0)).2.2.2.toNat : ℤ) =
          2 ^ 62 + ParseFloatScan.satE e - 4 * f.length +
            4 * ((i ++ f).length - ((i ++ f).takeWhile (· == 0x30)).length -
              min ((i ++ f).length - ((i ++ f).takeWhile (· == 0x30)).length) 15 : ℕ) + nu := by
  obtain ⟨hi2le, hsplit⟩ := sig_split isHexDigit s i0 hi0
  set iL := (s.drop i0).takeWhile isHexDigit with hiL
  set ni := iL.length with hni
  set i1 := i0 + ni with hi1
  set pt := decide (byteAt s i1 = 0x2E) with hpt
  set fL := if pt then (s.drop (i1 + 1)).takeWhile isHexDigit else [] with hfL
  set nf := fL.length with hnf
  set i2 := if pt then i1 + 1 + nf else i1 with hi2
  set L := iL ++ fL with hL
  have hsz := words_size64 s hs
  have hiLp : ni ≤ s.length - i0 := by
    have := (List.takeWhile_prefix isHexDigit (l := s.drop i0)).length_le
    rw [List.length_drop] at this; exact this
  have hi1le : i1 ≤ s.length := by omega
  have hiLd : ∀ b ∈ iL, isHexDigit b = true := takeWhile_all isHexDigit _
  have hfLd : ∀ b ∈ fL, isHexDigit b = true := by
    intro b hb
    rw [hfL] at hb
    split_ifs at hb
    · exact takeWhile_all isHexDigit _ b hb
    · simp at hb
  have hLd : ∀ b ∈ L, isHexDigit b = true := by
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
        exact ((List.takeWhile_prefix isHexDigit).getElem hkn).symm
      rw [h1, byteAt_lt _ _ hkn, byteAt_lt _ _ (by rw [List.length_append]; omega)]
      simp [List.getElem_append_left hkn]
    · rw [ite_eq_right hkn]
      have hk' : k - ni < nf := by rw [hL, List.length_append] at hk; omega
      have hptt : pt = true := by
        by_contra h; rw [hnf, hfL, ite_eq_right h] at hk'; simp at hk'
      have hfl : fL = (s.drop (i1 + 1)).takeWhile isHexDigit := by rw [hfL, ite_eq_left hptt]
      have : byteAt L k = byteAt fL (k - ni) := by
        have e := byteAt_append iL fL (k - ni)
        rw [← hni, show ni + (k - ni) = k by omega] at e
        rw [hL]; exact e
      rw [this, show i0 + k + 1 = (i1 + 1) + (k - ni) by omega, ← byteAt_drop]
      have hk'' : k - ni < ((s.drop (i1 + 1)).takeWhile isHexDigit).length := by
        rw [← hfl, ← hnf]; exact hk'
      have hfp : ((s.drop (i1 + 1)).takeWhile isHexDigit).length ≤ (s.drop (i1 + 1)).length :=
        (List.takeWhile_prefix isHexDigit).length_le
      rw [hfl, byteAt_lt _ _ hk'', byteAt_lt _ _ (by omega)]
      exact ((List.takeWhile_prefix isHexDigit).getElem hk'').symm
  have hbound : i0 + L.length + 1 ≤ s.length + 1 := by
    have := hi2le; rw [hi2eq] at this; split_ifs at this <;> omega
  have hnis : ni ≤ s.length := by omega
  -- the words
  have hN : ∀ k, k ≤ s.length + 1 → (UInt64.ofNat k).toNat = k := fun k hk =>
    ofNat_toNat _ (by omega)
  have hw0 : (UInt64.ofNat i0).toNat = i0 := hN i0 (by omega)
  have hone : (1 : UInt64).toNat = 1 := rfl
  have hfour : (4 : UInt64).toNat = 4 := rfl
  have hrun : ∀ j, j ≤ s.length → (span (words s) true (UInt64.ofNat j)).toNat =
      j + ((s.drop j).takeWhile isHexDigit).length := by
    intro j hj; rw [span_spec s true j hj hs, cls_true]
  have hw1 : span (words s) true (UInt64.ofNat i0) = UInt64.ofNat i1 := by
    have h1 : (span (words s) true (UInt64.ofNat i0)).toNat = i0 + ni := hrun i0 hi0
    have h2 := hN i1 (by omega)
    apply UInt64.toNat_inj.mp; omega
  have hw2 : (limb (words s) (UInt64.ofNat i1) == 0x2E) = pt := by
    rw [limb_words s _ hs, hN i1 (by omega), point_word, hpt]
  have hw3 : (if pt = true then span (words s) true (UInt64.ofNat i1 + 1) else UInt64.ofNat i1) =
      UInt64.ofNat i2 := by
    by_cases hp : pt = true
    · have hlt := hptlt hp
      have h2 : i2 = i1 + 1 + nf := by rw [hi2, ite_eq_left hp]
      have hfl : fL = (s.drop (i1 + 1)).takeWhile isHexDigit := by rw [hfL, ite_eq_left hp]
      have e1 : UInt64.ofNat i1 + 1 = UInt64.ofNat (i1 + 1) := by
        have a1 := hN i1 (by omega)
        have a2 := hN (i1 + 1) (by omega)
        have a3 := toNat_add' (UInt64.ofNat i1) 1 (by omega)
        apply UInt64.toNat_inj.mp; omega
      have h3 : (span (words s) true (UInt64.ofNat (i1 + 1))).toNat = i1 + 1 + nf := by
        rw [hrun (i1 + 1) (by omega), hnf, hfl]
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
      have hzero : (0 : UInt64).toNat = 0 := rfl
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
  set kept := min (L.length - z) 15 with hkept
  have hw9 : min (UInt64.ofNat L.length - UInt64.ofNat z) 15 = UInt64.ofNat kept := by
    have e1 := hN L.length (by omega)
    have e2 := hN z (by omega)
    have e3 := hN kept (by omega)
    have e4 : (15 : UInt64).toNat = 15 := rfl
    have e5 := toNat_sub' (UInt64.ofNat L.length) (UInt64.ofNat z) (by omega)
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_min]; omega
  have hw10 : UInt64.ofNat z + UInt64.ofNat kept = UInt64.ofNat (z + kept) := by
    have e1 := hN z (by omega)
    have e2 := hN kept (by omega)
    have e3 := hN (z + kept) (by omega)
    have e4 := toNat_add' (UInt64.ofNat z) (UInt64.ofNat kept) (by omega)
    apply UInt64.toNat_inj.mp; omega
  have hhp : hexParse (UInt64.ofNat nu) (words s) (UInt64.ofNat i0) =
      (UInt64.ofNat L.length != 0 && (limb (words s) (UInt64.ofNat i2) ||| 0x20) == 0x70 &&
          (expPart (words s) (UInt64.ofNat (i2 + 1))).1,
       hexVal (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat z) (UInt64.ofNat kept),
       anyNonzero (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat (z + kept))
         (UInt64.ofNat L.length),
       (if (expPart (words s) (UInt64.ofNat (i2 + 1))).2.1 then
          0x4000000000000000 - (expPart (words s) (UInt64.ofNat (i2 + 1))).2.2
        else 0x4000000000000000 + (expPart (words s) (UInt64.ofNat (i2 + 1))).2.2) -
          4 * UInt64.ofNat nf +
          4 * (UInt64.ofNat L.length - UInt64.ofNat z - UInt64.ofNat kept) + UInt64.ofNat nu) := by
    unfold hexParse
    simp only [hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10]
  rw [hhp]
  dsimp only
  -- the decoder's branch
  have hbranch : hexBranch (s.drop i0) =
      if ni + nf ≠ 0 then (decodeExp (ascii "pP") (s.drop i2)).map (fun e => (iL, fL, e))
      else none := by
    unfold hexBranch; rw [hsplit]; split_ifs <;> rfl
  have hflag1 : (UInt64.ofNat L.length != 0) = decide (ni + nf ≠ 0) := by
    have hl := hN L.length (by omega)
    have hzero : (0 : UInt64).toNat = 0 := rfl
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
    constructor
    · intro h h'; apply h; apply UInt64.toNat_inj.mp; rw [hzero]; omega
    · intro h h'; apply h; have := congrArg UInt64.toNat h'; rw [hzero] at this; omega
  have hexpflag : ((limb (words s) (UInt64.ofNat i2) ||| 0x20) == 0x70 &&
        (expPart (words s) (UInt64.ofNat (i2 + 1))).1) =
      (decodeExp (ascii "pP") (s.drop i2)).isSome := by
    rw [limb_words s _ hs, hN i2 (by omega), p_word]
    by_cases hlt : i2 < s.length
    · have hcons : s.drop i2 = byteAt s i2 :: s.drop (i2 + 1) := by
        rw [byteAt_lt _ _ hlt]; exact List.drop_eq_getElem_cons hlt
      rw [hcons, decodeExp]
      have hep := (expPart_spec s (i2 + 1) (by omega) hs).1
      by_cases hm : byteAt s i2 ∈ ascii "pP"
      · rw [decide_eq_true hm, Bool.true_and, ite_eq_left hm, Bool.eq_iff_iff]
        exact hep
      · rw [decide_eq_false hm, Bool.false_and, ite_eq_right hm] <;> rfl
    · rw [byteAt_ge _ _ (by omega), List.drop_eq_nil_of_le (by omega)]
      rfl
  refine ⟨?_, ?_⟩
  · rw [hflag1, Bool.and_assoc, hexpflag, hbranch]
    by_cases hv : ni + nf ≠ 0
    · rw [decide_eq_true hv, Bool.true_and, ite_eq_left hv, Option.isSome_map]
    · rw [decide_eq_false hv, Bool.false_and, ite_eq_right hv] <;> rfl
  intro i f e hbr
  rw [hbranch] at hbr
  by_cases hv : ni + nf ≠ 0
  swap
  · rw [ite_eq_right hv] at hbr; cases hbr
  rw [ite_eq_left hv] at hbr
  rcases hopt : decodeExp (ascii "pP") (s.drop i2) with _ | e'
  · rw [hopt] at hbr; simp at hbr
  rw [hopt] at hbr
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hbr
  obtain ⟨rfl, rfl, he⟩ := hbr
  rw [← he, ← hL, ← hz, ← hkept]
  refine ⟨hLd, hexVal_spec s hs i0 ni L hreads hbound hnis hLd z kept (by omega) (by omega),
    anyNonzero_spec s hs i0 ni L hreads hbound hnis (z + kept) L.length (by omega) le_rfl, ?_⟩
  -- the biased exponent of the last kept digit
  have hlt : i2 < s.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at hopt
    simp [decodeExp] at hopt
  have hcons : s.drop i2 = byteAt s i2 :: s.drop (i2 + 1) := by
    rw [byteAt_lt _ _ hlt]; exact List.drop_eq_getElem_cons hlt
  rw [hcons, decodeExp] at hopt
  by_cases hm : byteAt s i2 ∈ ascii "pP"
  swap
  · rw [ite_eq_right hm] at hopt; cases hopt
  rw [ite_eq_left hm] at hopt
  have hval := (expPart_spec s (i2 + 1) (by omega) hs).2 e' hopt
  set E := expPart (words s) (UInt64.ofNat (i2 + 1)) with hE
  have hsat1 : -(10 : ℤ) ^ 11 ≤ ParseFloatScan.satE e' := by unfold ParseFloatScan.satE; omega
  have hsat2 : ParseFloatScan.satE e' ≤ 10 ^ 11 := by unfold ParseFloatScan.satE; omega
  have htail : (UInt64.ofNat L.length - UInt64.ofNat z - UInt64.ofNat kept).toNat =
      L.length - z - kept := by
    have e1 := hN L.length (by omega)
    have e2 := hN z (by omega)
    have e3 := hN kept (by omega)
    have e4 := toNat_sub' (UInt64.ofNat L.length) (UInt64.ofNat z) (by omega)
    have e5 := toNat_sub' (UInt64.ofNat L.length - UInt64.ofNat z) (UInt64.ofNat kept) (by omega)
    omega
  have hfinal : ∀ W : UInt64, 2 ^ 62 - 2 ^ 40 ≤ W.toNat → W.toNat ≤ 2 ^ 62 + 2 ^ 40 →
      ((W - 4 * UInt64.ofNat nf + 4 * (UInt64.ofNat L.length - UInt64.ofNat z - UInt64.ofNat kept)
        + UInt64.ofNat nu).toNat : ℤ) =
        W.toNat - 4 * nf + 4 * ((L.length - z - kept : ℕ) : ℤ) + nu := by
    intro W h1 h2
    have e1 := hN nf (by omega)
    have e6 : (UInt64.ofNat nu).toNat = nu := ofNat_toNat _ (by omega)
    have e2 := toNat_mul' 4 (UInt64.ofNat nf) (by rw [hfour, e1]; omega)
    have e3 := toNat_mul' 4 (UInt64.ofNat L.length - UInt64.ofNat z - UInt64.ofNat kept)
      (by rw [hfour, htail]; omega)
    have e4 := toNat_sub' W (4 * UInt64.ofNat nf) (by rw [e2, hfour, e1]; omega)
    have e5 := toNat_add' (W - 4 * UInt64.ofNat nf)
      (4 * (UInt64.ofNat L.length - UInt64.ofNat z - UInt64.ofNat kept))
      (by rw [e4, e3, e2, hfour, e1, htail]; omega)
    have e7 := toNat_add' (W - 4 * UInt64.ofNat nf +
      4 * (UInt64.ofNat L.length - UInt64.ofNat z - UInt64.ofNat kept)) (UInt64.ofNat nu)
      (by rw [e5, e4, e3, e2, hfour, e1, htail, e6]; omega)
    rw [e7, e5, e4, e3, e2, hfour, e1, htail, e6]
    omega
  by_cases hneg : E.2.1 = true
  · rw [ite_eq_left hneg] at hval ⊢
    have hle : E.2.2.toNat ≤ 10 ^ 11 := by omega
    have hW : (0x4000000000000000 - E.2.2).toNat = 2 ^ 62 - E.2.2.toNat := by
      rw [toNat_sub' _ _ (by rw [bias_toNat]; omega), bias_toNat]
    rw [hfinal _ (by rw [hW]; omega) (by rw [hW]; omega), hW]
    omega
  · rw [ite_eq_right hneg] at hval ⊢
    have hle : E.2.2.toNat ≤ 10 ^ 11 := by omega
    have hW : (0x4000000000000000 + E.2.2).toNat = 2 ^ 62 + E.2.2.toNat := by
      rw [toNat_add' _ _ (by rw [bias_toNat]; omega), bias_toNat]
    rw [hfinal _ (by rw [hW]; omega) (by rw [hW]; omega), hW]
    omega

#print axioms sig_split
#print axioms hexParse_spec

end Verified.Examples.ParseFloatHexParse
