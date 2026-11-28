module

public import Library.Numerics.Bignum.Canonical
public import Library.Numerics.Decimal.Int64Text.Inverse

@[expose] public section

/-!
The specification's reader and printer are inverse, as Int64Text's `expectedRead_print` and
`expectedPrint_of_read` state for `Int64`, here for every integer.  `printSpec_toList` writes the
text of `z` as `-` for a negative `z` and the digit words of `|z|`, through Lean's
`Int.repr_eq_ite` and `Nat.toList_repr`.  `denote_print` reads it back, and `print_of_denote`
shows that every text the grammar accepts is the printer's text of the integer it denotes, so the
grammar's texts are exactly the printer's texts.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.Decimal.Int64Text
open Library.Numerics.Decimal.Shared.StrconvGrammar (words ascii)

/-- The text of `z` is its sign and the digits of its magnitude. -/
theorem printSpec_toList (z : ℤ) :
    (printSpec z).toList = (if z < 0 then [45] else []) ++ digitWords z.natAbs := by
  have h : (toString z).toList = (Int.repr z).toList := rfl
  have hmap : (printSpec z).toList = (toString z).toList.map fun c => c.toUInt8.toUInt64 := by
    simp [printSpec, words, ascii]
  have hminus : ("-" : String).toList = ['-'] := by decide
  rw [hmap, h, Int.repr_eq_ite]
  by_cases hz : 0 ≤ z
  · rw [ite_eq_left hz, ite_eq_right (by omega), Nat.toList_repr, List.nil_append, digitWords,
      show z.toNat = z.natAbs by omega]
  · rw [ite_eq_right hz, ite_eq_left (by omega), String.toList_append, hminus, Nat.toList_repr,
      List.map_append, digitWords, show (-z).toNat = z.natAbs by omega]
    rfl

theorem printSpec_size (z : ℤ) :
    (printSpec z).size = (if z < 0 then 1 else 0) + (digitWords z.natAbs).length := by
  rw [← Array.length_toList, printSpec_toList, List.length_append]
  split <;> rfl

/-- The grammar reads the printer's text of `z` as `z`. -/
theorem denote_print (z : ℤ) : denote (printSpec z).toList = some z := by
  obtain ⟨hdig, hval, d, rest, hdr, hpos⟩ := digitWords_facts z.natAbs
  have hd := hdig d (by rw [hdr]; exact List.mem_cons_self)
  rw [isDigitWord_iff] at hd
  rw [printSpec_toList]
  by_cases hneg : z < 0
  · have hm : 0 < z.natAbs := by omega
    rw [ite_eq_left hneg, denote_minus ([45] ++ digitWords z.natAbs) (by simp) (by simp)]
    simp only [List.tail_cons, List.singleton_append, magnitude_digitWords hm, Option.map_some]
    rw [Int.ofNat_natAbs_of_nonpos (by omega), Int.neg_neg]
  · rw [ite_eq_right hneg, List.nil_append]
    by_cases hz : z = 0
    · rw [hz]
      simp [digitWords_zero, denote]
    · have hm : 0 < z.natAbs := by omega
      have h48 : digitWords z.natAbs ≠ [48] := by
        intro h
        have := hval
        rw [h] at this
        simp [digitsValue] at this
        omega
      have h45 : ¬ (digitWords z.natAbs).head? = some 45 := by
        rw [hdr]
        intro h
        simp only [List.head?_cons, Option.some.injEq] at h
        rw [h] at hd
        simp at hd
      rw [denote_plain _ h48 h45, magnitude_digitWords hm]
      simp only [Option.map_some]
      rw [Int.natAbs_of_nonneg (by omega)]

/-- Every text that the grammar accepts is the printer's text of the integer it denotes. -/
theorem print_of_denote {s : Array UInt64} {z : ℤ} (hn : denote s.toList = some z) :
    printSpec z = s := by
  apply Array.toList_inj.mp
  rw [printSpec_toList]
  by_cases h48 : s.toList = [48]
  · have h0 : z = 0 := by
      rw [h48, denote_zero] at hn
      exact (Option.some.inj hn).symm
    subst h0
    rw [h48]
    simp [digitWords_zero]
  · by_cases h45 : s.toList.head? = some 45
    · rw [denote_minus _ h48 h45] at hn
      obtain ⟨v, hv, hvn⟩ := Option.map_eq_some_iff.mp hn
      obtain ⟨d, rest, hds, hd1, -, -, hval⟩ := magnitude_some hv
      have hpos : 0 < v := by rw [hval, hds]; exact digitsValue_pos hd1
      have hcons : s.toList = 45 :: s.toList.tail := by
        cases hs : s.toList with
        | nil => rw [hs] at h45; simp at h45
        | cons a t => rw [hs] at h45; simp at h45; rw [h45]; rfl
      rw [← hvn, ite_eq_left (by omega), Int.natAbs_neg, Int.natAbs_natCast,
        digitWords_of_magnitude _ v hv]
      conv_rhs => rw [hcons]
      rfl
    · rw [denote_plain _ h48 h45] at hn
      obtain ⟨v, hv, hvn⟩ := Option.map_eq_some_iff.mp hn
      rw [← hvn, ite_eq_right (by omega), Int.natAbs_natCast, digitWords_of_magnitude _ v hv]
      rfl

/-- The reader of the specification returns `(true, z)` on the text of `z`. -/
theorem readSpec_print (z : ℤ) : readSpec (printSpec z) = (true, .ofInt z) := by
  unfold readSpec
  rw [denote_print]

/-- Every text that the specification's reader accepts is the printer's text of its integer. -/
theorem print_of_readSpec {s : Array UInt64} {x : BigInt} (h : readSpec s = (true, x)) :
    ∃ z, x = .ofInt z ∧ printSpec z = s := by
  unfold readSpec at h
  split at h
  · rename_i z hz
    exact ⟨z, (Prod.mk.inj h).2.symm, print_of_denote hz⟩
  · exact absurd (Prod.mk.inj h).1 (by decide)

/-- The specification's reader rejects every array that is no printer's text. -/
theorem readSpec_reject {s : Array UInt64} (h : ∀ z, printSpec z ≠ s) :
    readSpec s = (false, .ofInt 0) := by
  unfold readSpec
  split
  · rename_i z hz
    exact absurd (print_of_denote hz) (h z)
  · rfl

end Library.Numerics.Bignum
