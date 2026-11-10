import Demos.Rcv.Read
import Library.Numerics.Decimal.Int64Text.Inverse
import Mathlib.Data.Nat.BitIndices
import Mathlib.Tactic

/-!
Lemmas about the canonical file's forms that the theorems of the reader and of the printer share.
`decimal` is the library's `digitWords` of `Library.Numerics.Decimal.Int64Text` with bytes for
words, so `number_decimal` and `decimal_of_number`, the inverse statements of the decimal form,
follow from the library's `magnitude_digitWords` and `digitWords_of_magnitude`.  `text` is
`intercalate` of the lines and an empty last line, so `List.splitOn_intercalate` splits a written
file into its lines.  The candidates that a position word marks are its `Nat.bitIndices` shifted by
one, which gives the field of a word and the word of a field.
-/

namespace Demos.Rcv.Spec

open Demos.Rcv
open Library.Numerics.Decimal.Int64Text (digitWords digitWords_small digitWords_snoc
  magnitude magnitude_digitWords digitWords_of_magnitude isDigitWord)

/-! ## Decimal numbers -/

theorem char_byte (c : Char) : c.toNat.toUInt8.toUInt64 = c.toUInt8.toUInt64 := rfl

/-- The library's digits of `v` are the bytes of `decimal v` as words. -/
theorem digitWords_eq (v : Nat) : digitWords v = (decimal v).map UInt8.toUInt64 := by
  simp only [digitWords, decimal, ascii, Nat.toString_eq_repr, Nat.toList_repr, List.map_map]
  rfl

theorem map_toUInt64_injective {a b : List UInt8} (h : a.map UInt8.toUInt64 = b.map UInt8.toUInt64) :
    a = b :=
  List.map_injective_iff.mpr (fun x y hxy => UInt8.toUInt64_inj.mp hxy) h

theorem isDigit_eq (x : UInt8) : isDigit x = isDigitWord x.toUInt64 := by
  simp only [isDigit, isDigitWord, UInt8.le_iff_toNat_le, UInt64.le_iff_toNat_le,
    UInt8.toNat_toUInt64]
  rfl

theorem digitsValue_eq (bs : List UInt8) :
    digitsValue bs = Library.Numerics.Decimal.Int64Text.digitsValue (bs.map UInt8.toUInt64) := by
  simp only [digitsValue, Library.Numerics.Decimal.Int64Text.digitsValue, List.foldl_map,
    UInt8.toNat_toUInt64]

/-- A number other than `0` is a `magnitude` of the library. -/
theorem number_eq_magnitude (d : UInt8) (ds : List UInt8) (h : d ≠ 0x30) :
    number (d :: ds) = magnitude ((d :: ds).map UInt8.toUInt64) := by
  have hd : d.toUInt64 ≠ 48 := fun e => h (UInt8.toUInt64_inj.mp e)
  have hfun : isDigit = fun x : UInt8 => isDigitWord x.toUInt64 := funext isDigit_eq
  simp only [number, List.map_cons, magnitude, List.all_cons, hfun, List.all_map,
    digitsValue_eq]
  have hiff : (49 ≤ d.toUInt64 && d.toUInt64 ≤ 57) = isDigitWord d.toUInt64 := by
    simp only [isDigitWord, UInt64.le_iff_toNat_le]
    have : d.toUInt64.toNat ≠ 48 := fun e => hd (UInt64.toNat_inj.mp (by simpa using e))
    by_cases h1 : 48 ≤ d.toUInt64.toNat <;> by_cases h2 : d.toUInt64.toNat ≤ 57 <;>
      simp_all <;> omega
  have hne : (d != 0x30) = true := by simpa using h
  simp only [hne, Bool.true_or, Bool.and_true, hiff, Function.comp_def]

theorem decimal_zero : decimal 0 = [0x30] := rfl

theorem number_zero : number [0x30] = some 0 := rfl

/-- The decimal form of `v` reads as `v`. -/
theorem number_decimal (v : Nat) : number (decimal v) = some v := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rfl
  · obtain ⟨d, ds, hds⟩ : ∃ d ds, decimal v = d :: ds := by
      cases h : decimal v with
      | nil =>
        have := magnitude_digitWords hv
        rw [digitWords_eq, h] at this
        simp [magnitude] at this
      | cons d ds => exact ⟨d, ds, rfl⟩
    have hm := magnitude_digitWords hv
    rw [digitWords_eq, hds] at hm
    have hd : d ≠ 0x30 := by
      intro e
      subst e
      simp [magnitude] at hm
    rw [hds, number_eq_magnitude d ds hd, hm]

/-- The bytes that read as `v` are its decimal form. -/
theorem decimal_of_number {bs : List UInt8} {v : Nat} (h : number bs = some v) : decimal v = bs := by
  match bs, h with
  | d :: ds, h =>
    by_cases hd : d = 0x30
    · subst hd
      have hds : ds = [] := by
        simp only [number] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, bne_self_eq_false, Bool.false_or, List.isEmpty_iff] at hc
          exact hc.2
        · exact absurd h (by simp)
      subst hds
      have : v = 0 := by simpa [number_zero] using h.symm
      subst this
      rfl
    · rw [number_eq_magnitude d ds hd] at h
      exact map_toUInt64_injective (by rw [← digitWords_eq]; exact digitWords_of_magnitude _ v h)

theorem decimal_injective {a b : Nat} (h : decimal a = decimal b) : a = b := by
  have ha := number_decimal a
  rw [h, number_decimal b] at ha
  exact (Option.some.inj ha).symm

/-- Every byte of a decimal form is a digit. -/
theorem decimal_digit {v : Nat} {x : UInt8} (hx : x ∈ decimal v) : isDigit x = true := by
  have h := number_decimal v
  cases hd : decimal v with
  | nil => rw [hd] at h; simp [number] at h
  | cons d ds =>
    rw [hd] at h hx
    simp only [number] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true] at hc
      exact hc.1 x hx
    · exact absurd h (by simp)

theorem decimal_ne_nil (v : Nat) : decimal v ≠ [] := by
  intro h
  have := number_decimal v
  rw [h] at this
  simp [number] at this

/-- A byte that is not a digit is not in a decimal form. -/
theorem not_mem_decimal {v : Nat} {x : UInt8} (hx : isDigit x = false) : x ∉ decimal v :=
  fun h => by rw [decimal_digit h] at hx; exact absurd hx (by decide)

/-- Pieces that read as numbers are the decimal forms of the numbers. -/
theorem map_decimal_of_forall₂ {ps : List (List UInt8)} {is : List Nat}
    (h : List.Forall₂ (fun a b => number a = some b) ps is) : is.map decimal = ps := by
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [List.map_cons, decimal_of_number hab, ih]

/-! ## Lines and separators -/

theorem text_eq (ls : List (List UInt8)) : text ls = [lf].intercalate (ls ++ [[]]) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    have h : text (l :: ls) = l ++ [lf] ++ text ls := by simp [text, lf]
    rw [h, ih, List.cons_append, List.intercalate_cons_of_ne_nil (by simp)]

/-- A text whose lines hold no LF splits at LF into its lines and the empty piece after the last
LF. -/
theorem splitOn_text {ls : List (List UInt8)} (h : ∀ l ∈ ls, lf ∉ l) :
    (text ls).splitOn lf = ls ++ [[]] := by
  rw [text_eq]
  refine List.splitOn_intercalate lf ?_ (by simp)
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact h l hl
  · rw [List.mem_singleton.mp hl]
    simp

/-- A list of the pieces that `splitOn` gives joins back to the list. -/
theorem intercalate_splitOn' (sep : UInt8) (l : List UInt8) :
    [sep].intercalate (l.splitOn sep) = l := List.intercalate_splitOn sep

theorem spaced_eq (parts : List (List UInt8)) : spaced parts = [sp].intercalate parts := rfl

theorem spaced_two (a b : List UInt8) : spaced [a, b] = a ++ sp :: b := by
  simp [spaced, sp]

theorem spaced_cons_cons (a b : List UInt8) (rest : List (List UInt8)) :
    spaced (a :: b :: rest) = a ++ sp :: spaced (b :: rest) := by
  simp [spaced, sp]

/-- `after` on a list with the prefix. -/
theorem after_append (p r : List UInt8) : after p (p ++ r) = some r := by
  simp [after]

/-- A list on which `after` succeeds is the prefix and the rest. -/
theorem eq_of_after {p bs r : List UInt8} (h : after p bs = some r) : bs = p ++ r := by
  unfold after at h
  split at h
  · rename_i hp
    have hp' : p <+: bs := by simpa using hp
    obtain ⟨t, rfl⟩ := hp'
    simp at h
    rw [← h]
  · exact absurd h (by simp)

/-! ## Lists of options -/

/-- `mapM` succeeds on `l` with the result `r` exactly when `f` succeeds on each element with the
element of `r` at its place. -/
theorem mapM_some_iff {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r ↔ List.Forall₂ (fun a b => f a = some b) l r
  | [], r => by
    cases r <;> simp
  | a :: l, r => by
    have ih := mapM_some_iff f l
    rw [List.mapM_cons]
    cases r with
    | nil =>
      constructor
      · intro h
        cases hfa : f a <;> cases hl : l.mapM f <;> simp [hfa, hl] at h
      · intro h
        cases h
    | cons b r =>
      rw [List.forall₂_cons, ← ih r]
      cases hfa : f a <;> cases hl : l.mapM f <;> simp [hfa, hl]

/-- `mapM` of `f` over the images of `g` gives the images of `h` when `f (g a) = some (h a)`. -/
theorem mapM_map_some {α β γ : Type} (f : β → Option γ) (g : α → β) (h : α → γ) (l : List α)
    (hf : ∀ a ∈ l, f (g a) = some (h a)) : (l.map g).mapM f = some (l.map h) := by
  rw [mapM_some_iff]
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
    exact List.Forall₂.cons (hf a List.mem_cons_self)
      (ih fun x hx => hf x (List.mem_cons_of_mem a hx))

/-! ## Marks of a position word -/

/-- The bits of a number below `2 ^ 63`, in increasing order, are its bit indices. -/
theorem filter_testBit_eq (m : Nat) (h : m < 2 ^ 63) :
    (List.range 63).filter (fun j => m.testBit j) = m.bitIndices := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact List.Pairwise.filter _ List.pairwise_lt_range
  · exact List.sortedLT_iff_pairwise.mp Nat.bitIndices_sorted
  · intro a
    simp only [List.mem_filter, List.mem_range, Nat.mem_bitIndices]
    constructor
    · exact fun h' => h'.2
    · intro hb
      refine ⟨?_, hb⟩
      have := Nat.ge_two_pow_of_testBit hb
      by_contra hlt
      have : 2 ^ 63 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
      omega

/-- The candidates that a word without bit 63 marks are its bit indices plus one. -/
theorem marks_eq (w : UInt64) (h : w.toNat < 2 ^ 63) : marks w = w.toNat.bitIndices.map (· + 1) := by
  rw [marks, filter_testBit_eq _ h]

/-- An increasing list of numbers is pairwise increasing. -/
theorem increasing_iff (l : List Nat) : increasing l = true ↔ l.Pairwise (· < ·) := by
  induction l with
  | nil => simp [increasing]
  | cons a l ih =>
    cases l with
    | nil => simp [increasing]
    | cons b l =>
      simp only [increasing, Bool.and_eq_true, decide_eq_true_eq, ih, List.pairwise_cons,
        List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨hab, hb, hp⟩
        exact ⟨⟨hab, fun x hx => Nat.lt_trans hab (hb x hx)⟩, hb, hp⟩
      · rintro ⟨⟨hab, _⟩, hb, hp⟩
        exact ⟨hab, hb, hp⟩

/-! ## Fields of position words -/

theorem ascii_bar : ascii "|" = [bar] := rfl

theorem ascii_star : ascii "*" = [0x2A] := rfl

theorem testBit63_of_lt {m : Nat} (h : m < 2 ^ 63) : m.testBit 63 = false :=
  Nat.testBit_lt_two_pow h

theorem unnamedOvervote_toNat : unnamedOvervote.toNat = 2 ^ 63 := rfl

/-- The field of a word without bit 63: its marks in decimal, separated by `|`. -/
theorem field_eq {w : UInt64} (h : w.toNat < 2 ^ 63) :
    field w = [bar].intercalate (w.toNat.bitIndices.map fun j => decimal (j + 1)) := by
  rw [field, testBit63_of_lt h, marks_eq w h, ascii_bar, List.map_map]
  rfl

theorem decimal_no_bar (v : Nat) : bar ∉ decimal v := not_mem_decimal (by decide)

theorem decimal_no_sp (v : Nat) : sp ∉ decimal v := not_mem_decimal (by decide)

theorem decimal_no_lf (v : Nat) : lf ∉ decimal v := not_mem_decimal (by decide)

theorem decimal_no_comma (v : Nat) : comma ∉ decimal v := not_mem_decimal (by decide)

/-- The sum of `2 ^ j` over the bit indices of a list below `n` is below `2 ^ n`. -/
theorem sum_lt_of_bits {L : List Nat} (hs : L.Pairwise (· < ·)) {n : Nat} (hL : ∀ j ∈ L, j < n) :
    (L.map fun j => 2 ^ j).sum < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hb := Nat.bitIndices_sum_map_two_pow (List.sortedLT_iff_pairwise.mpr hs)
  by_contra hc
  have hmem : i ∈ (L.map fun j => 2 ^ j).sum.bitIndices := Nat.mem_bitIndices.mpr (by simpa using hc)
  rw [hb] at hmem
  have := hL i hmem
  omega

/-- The field of a valid word reads back as the word. -/
theorem parsePosition_field {n : Nat} (hn : n ≤ 63) {w : UInt64} (hw : ValidWord n w) :
    parsePosition n (field w) = some w := by
  rcases hw with rfl | rfl | ⟨hpos, hlt⟩
  · rfl
  · rfl
  · have h63 : w.toNat < 2 ^ 63 :=
      Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hn)
    set L := w.toNat.bitIndices with hL
    have hsorted : L.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp Nat.bitIndices_sorted
    have hbits : ∀ j ∈ L, j < n := by
      intro j hj
      have := Nat.ge_two_pow_of_testBit (Nat.mem_bitIndices.mp hj)
      by_contra hc
      have : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hsum : (L.map fun j => 2 ^ j).sum = w.toNat := Nat.sum_map_two_pow_bitIndices _
    obtain ⟨j0, L', hL'⟩ : ∃ j0 L', L = j0 :: L' := by
      cases hc : L with
      | nil => rw [hc] at hsum; simp at hsum; omega
      | cons j0 L' => exact ⟨j0, L', rfl⟩
    rw [field_eq h63, ← hL]
    have hpieces : (L.map fun j => decimal (j + 1)) ≠ [] := by simp [hL']
    have hne : [bar].intercalate (L.map fun j => decimal (j + 1)) ≠ [] := by
      rw [hL', List.map_cons]
      cases hd : decimal (j0 + 1) with
      | nil => exact absurd hd (decimal_ne_nil _)
      | cons x xs => cases L' <;> simp
    have hfirst : ∀ x xs, [bar].intercalate (L.map fun j => decimal (j + 1)) = x :: xs →
        isDigit x = true := by
      intro x xs hx
      rw [hL', List.map_cons] at hx
      cases hd : decimal (j0 + 1) with
      | nil => exact absurd hd (decimal_ne_nil _)
      | cons y ys =>
        rw [hd] at hx
        have hxy : x = y := by cases L' <;> simp_all
        rw [hxy]
        exact decimal_digit (by rw [hd]; exact List.mem_cons_self)
    have hnstar : [bar].intercalate (L.map fun j => decimal (j + 1)) ≠ ascii "*" := by
      intro he
      have := hfirst 0x2A [] (by rw [he]; rfl)
      exact absurd this (by decide)
    have hsplit : ([bar].intercalate (L.map fun j => decimal (j + 1))).splitOn bar =
        L.map fun j => decimal (j + 1) := by
      refine List.splitOn_intercalate bar ?_ hpieces
      intro l hl
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
      exact decimal_no_bar _
    have hmap : (L.map fun j => decimal (j + 1)).mapM number = some (L.map (· + 1)) := by
      have := mapM_map_some number (fun j => decimal (j + 1)) (· + 1) L
        (fun j _ => number_decimal (j + 1))
      exact this
    simp only [parsePosition, hne, hnstar, ite_false, hsplit, hmap]
    have hall : ((L.map (· + 1)).all fun i : Nat => 1 ≤ i && i ≤ n) = true := by
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, Bool.and_eq_true,
        decide_eq_true_eq]
      exact fun j hj => ⟨by omega, by have := hbits j hj; omega⟩
    have hinc : increasing (L.map (· + 1)) = true := by
      rw [increasing_iff, List.pairwise_map]
      exact hsorted.imp (by omega)
    have hval : ((L.map (· + 1)).map fun i : Nat => (2 : Nat) ^ (i - 1)).sum = w.toNat := by
      rw [List.map_map, ← hsum]
      congr 1
    simp only [hall, hinc, Bool.and_self, ite_true, hval, UInt64.ofNat_toNat]

/-- A field that reads as a word is the word's field, and the word is valid. -/
theorem field_of_parsePosition {n : Nat} (hn : n ≤ 63) {f : List UInt8} {w : UInt64}
    (h : parsePosition n f = some w) : field w = f ∧ ValidWord n w := by
  unfold parsePosition at h
  split at h
  · rename_i hf
    subst hf
    cases h
    exact ⟨rfl, Or.inl rfl⟩
  · split at h
    · rename_i _ hf
      subst hf
      cases h
      exact ⟨rfl, Or.inr (Or.inl rfl)⟩
    · rename_i hf0 hfs
      split at h
      · rename_i is his
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
          obtain ⟨hin, hinc⟩ := hc
          rw [increasing_iff] at hinc
          have hpieces := (mapM_some_iff number _ _).mp his
          set L := is.map (· - 1) with hL
          have hLs : L.Pairwise (· < ·) := by
            rw [hL, List.pairwise_map]
            refine hinc.imp_of_mem ?_
            intro a b ha hb hab
            have := hin a ha
            have := hin b hb
            omega
          have hbits : ∀ j ∈ L, j < n := by
            intro j hj
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
            have := hin i hi
            omega
          have hsumeq : (is.map fun i : Nat => (2 : Nat) ^ (i - 1)) = L.map fun j => 2 ^ j := by
            rw [hL, List.map_map]
            rfl
          have hlt := sum_lt_of_bits hLs hbits
          have hlt64 : (L.map fun j => 2 ^ j).sum < 2 ^ 64 :=
            Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
          have hw : (UInt64.ofNat (is.map fun i : Nat => (2 : Nat) ^ (i - 1)).sum).toNat =
              (L.map fun j => 2 ^ j).sum := by
            rw [hsumeq]
            exact UInt64.toNat_ofNat_of_lt' hlt64
          have hbitsw : (UInt64.ofNat (is.map fun i : Nat => (2 : Nat) ^ (i - 1)).sum).toNat.bitIndices
              = L := by
            rw [hw]
            exact Nat.bitIndices_sum_map_two_pow (List.sortedLT_iff_pairwise.mpr hLs)
          have h63 : (UInt64.ofNat (is.map fun i : Nat => (2 : Nat) ^ (i - 1)).sum).toNat < 2 ^ 63 := by
            rw [hw]
            exact Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hn)
          have his_ne : is ≠ [] := by
            intro he
            subst he
            have := hpieces.length_eq
            simp at this
          refine ⟨?_, Or.inr (Or.inr ⟨?_, by rw [hw]; exact hlt⟩)⟩
          · rw [field_eq h63, hbitsw]
            conv_rhs => rw [← List.intercalate_splitOn (xs := f) bar]
            congr 1
            rw [hL, List.map_map]
            have hfor : ∀ i ∈ is, ((fun j => decimal (j + 1)) ∘ fun x => x - 1) i = decimal i := by
              intro i hi
              have := hin i hi
              simp only [Function.comp_apply]
              congr 1
              omega
            rw [List.map_congr_left hfor]
            exact map_decimal_of_forall₂ hpieces
          · rw [hw]
            obtain ⟨i, rest, rfl⟩ := List.exists_cons_of_ne_nil his_ne
            have hi := hin i List.mem_cons_self
            simp only [hL, List.map_cons, List.sum_cons]
            have : 0 < 2 ^ (i - 1) := Nat.two_pow_pos _
            omega
        · exact absurd h (by simp)
      · exact absurd h (by simp)

end Demos.Rcv.Spec
