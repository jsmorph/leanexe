module

public import Demos.BignumCalc.MessageEq
public import Demos.BignumCalc.MessageBound
public import Verified.BoundFacts
import all Init.Data.Repr
import all Init.Data.Int.Repr

@[expose] public section

/-!
# The calculator's allocation bounds

`calcLine_bound_le` bounds the generated allocation bound of `calcLine` in the calculator's module
by `400 n + 4096` bytes for a message of `n ≤ 65,536` bytes: the operands' copies, the text export's
closed form from `Export.lean` through the equations of `MessageBound.lean`, and the line, whose
text has at most `n + 4` bytes.  `calcWords_bound_le` bounds the bare-metal entry by
`2 ^ 25` bytes for every length up to `inMax`, the bytes of the message one to a word, the line,
and its packed words included.
-/

namespace Demos.BignumCalc

open Library.Numerics.Bignum

open Library.Numerics.Decimal.Shared.StrconvGrammar (ascii words)
open Library.Numerics.Decimal.Int64Text (denote)
open LeanExe.Dialect

/-! ## Sizes of the texts -/

theorem toNat_size_add2 (X : Array UInt64) (h : X.size < 2 ^ 32) :
    (X.size.toUInt64 + 2).toNat = X.size + 2 := by
  rw [UInt64.toNat_add, size_toNat64 (by omega)]
  simp only [UInt64.reduceToNat]
  omega

theorem textBinary_text_size (d : Bool) {f : ℤ → ℤ → ℤ}
    (hf : ∀ a b, (f a b).natAbs ≤ (a.natAbs + 1) * (b.natAbs + 1)) (s t : Array UInt64) :
    (textBinary d f s t).2.size ≤ s.size + t.size + 2 := by
  unfold textBinary
  cases hx : denote s.toList with
  | none => simp
  | some x =>
    cases hy : denote t.toList with
    | none => simp
    | some y =>
      dsimp only
      split
      · simp
      · exact result_text_size hf hx hy

theorem textNeg_text_size (s : Array UInt64) (hs : s.size < 2 ^ 30) :
    (textNeg s).2.size ≤ s.size + 1 := by
  rw [textNeg_eq s hs]
  unfold textNegSpec textUnary
  cases hx : denote s.toList with
  | none => simp
  | some x =>
    dsimp only
    exact printSpec_size_le (by rw [Int.natAbs_neg]; exact denote_natAbs_lt hx)

theorem cmpText_size (c : UInt64) : (cmpText c).size ≤ 2 := by
  unfold cmpText
  split
  · rfl
  · split <;> simp

/-- The bounds and the texts' sizes of the binary text exports on two operands. -/
theorem binary_facts (A B : Array UInt64) (hA : A.size < 2 ^ 30) (hB : B.size < 2 ^ 30) :
    messageCompiled.textCmp.bound (A, B) ≤ 2 * (A.size + B.size) + 256 ∧
    ((cmpText (textCmp A B).2).size.toUInt64 + 2).toNat ≤ 4 ∧
    messageCompiled.textAdd.bound (A, B) ≤ 344 * (A.size + B.size) + 2214 ∧
    ((textAdd A B).2.size.toUInt64 + 2).toNat ≤ A.size + B.size + 4 ∧
    messageCompiled.textSub.bound (A, B) ≤ 344 * (A.size + B.size) + 2214 ∧
    ((textSub A B).2.size.toUInt64 + 2).toNat ≤ A.size + B.size + 4 ∧
    messageCompiled.textMul.bound (A, B) ≤ 344 * (A.size + B.size) + 2214 ∧
    ((textMul A B).2.size.toUInt64 + 2).toNat ≤ A.size + B.size + 4 ∧
    messageCompiled.textTDiv.bound (A, B) ≤ 344 * (A.size + B.size) + 2214 ∧
    ((textTDiv A B).2.size.toUInt64 + 2).toNat ≤ A.size + B.size + 4 ∧
    messageCompiled.textTMod.bound (A, B) ≤ 344 * (A.size + B.size) + 2214 ∧
    ((textTMod A B).2.size.toUInt64 + 2).toNat ≤ A.size + B.size + 4 ∧
    messageCompiled.textEDiv.bound (A, B) ≤ 344 * (A.size + B.size) + 2214 ∧
    ((textEDiv A B).2.size.toUInt64 + 2).toNat ≤ A.size + B.size + 4 ∧
    messageCompiled.textEMod.bound (A, B) ≤ 344 * (A.size + B.size) + 2214 ∧
    ((textEMod A B).2.size.toUInt64 + 2).toNat ≤ A.size + B.size + 4 := by
  have sz : ∀ X : Array UInt64, X.size ≤ A.size + B.size + 2 →
      (X.size.toUInt64 + 2).toNat ≤ A.size + B.size + 4 := fun X h => by
    rw [toNat_size_add2 X (by omega)]; omega
  have ct := cmpText_size (textCmp A B).2
  refine ⟨by rw [m_textCmp_bound]; exact textCmp_bound_le A B hA hB,
    by rw [toNat_size_add2 _ (by omega)]; omega,
    by rw [m_textAdd_bound]; have := textAdd_bound_le A B hA hB; omega,
    sz _ (by rw [textAdd_eq A B hA hB]; exact textBinary_text_size _ computes_add.le A B),
    by rw [m_textSub_bound]; have := textSub_bound_le A B hA hB; omega,
    sz _ (by rw [textSub_eq A B hA hB]; exact textBinary_text_size _ computes_sub.le A B),
    by rw [m_textMul_bound]; have := textMul_bound_le A B hA hB; omega,
    sz _ (by rw [textMul_eq A B hA hB]; exact textBinary_text_size _ computes_mul.le A B),
    by rw [m_textTDiv_bound]; have := textTDiv_bound_le A B hA hB; omega,
    sz _ (by rw [textTDiv_eq A B hA hB]; exact textBinary_text_size _ computes_tdiv.le A B),
    by rw [m_textTMod_bound]; have := textTMod_bound_le A B hA hB; omega,
    sz _ (by rw [textTMod_eq A B hA hB]; exact textBinary_text_size _ computes_tmod.le A B),
    by rw [m_textEDiv_bound]; exact textEDiv_bound_le A B hA hB,
    sz _ (by rw [textEDiv_eq A B hA hB]; exact textBinary_text_size _ computes_ediv.le A B),
    by rw [m_textEMod_bound]; exact textEMod_bound_le A B hA hB,
    sz _ (by rw [textEMod_eq A B hA hB]; exact textBinary_text_size _ computes_emod.le A B)⟩

/-! ## The line -/

set_option maxHeartbeats 2000000 in
/-- The calculator's line allocates at most `400 n + 4096` bytes for a message of `n ≤ 65,536`
words. -/
theorem calcLine_bound_le (m : Array UInt64) (hm : m.size ≤ 65536) :
    messageCompiled.calcLine.bound m ≤ 400 * m.size + 4096 := by
  have hN : m.size.toUInt64.toNat = m.size := size_toNat64 (by omega)
  rw [messageCompiled.calcLine.bound_eq]
  rw [ite_eq_right_iff.mpr (fun h => absurd (by
    rw [UInt64.lt_iff_toNat_lt, hN] at h; simpa using h) (by omega : ¬ 65536 < m.size))]
  generalize hn64 : m.size.toUInt64 = n64 at hN ⊢
  have s1 := nextSpace_spec m 0 (by omega)
  generalize hq1 : nextSpace m 0 = p1 at s1 ⊢
  have s2 := nextSpace_spec m (p1 + 1) (by omega)
  generalize hq2 : nextSpace m (p1 + 1) = p2 at s2 ⊢
  have s3 := nextSpace_spec m (p2 + 1) (by omega)
  generalize hq3 : nextSpace m (p2 + 1) = p3 at s3 ⊢
  generalize opCode m p1 = op
  have hp1 : p1.toNat ≤ m.size := by rcases s1 with ⟨h, -⟩ | ⟨-, h, -⟩ <;> omega
  have hp1' : (p1 + 1).toNat = p1.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  rw [hp1'] at s2
  have hp2 : p2.toNat = m.size ∨ (p1.toNat + 1 ≤ p2.toNat ∧ p2.toNat < m.size) := by
    rcases s2 with ⟨h, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  have hlt : ∀ u : UInt64, (decide (u < n64)) = decide (u.toNat < m.size) := by
    intro u; exact decide_eq_decide.mpr (by rw [UInt64.lt_iff_toNat_lt, hN])
  have heq : ∀ u : UInt64, (u == n64) = decide (u.toNat = m.size) := by
    intro u
    rw [← hN]
    by_cases h : u = n64
    · subst h; simp
    · simp [h, UInt64.toNat_inj]
  have hne : ∀ u : UInt64, (u != n64) = !decide (u.toNat = m.size) := by
    intro u; rw [bne, heq]
  -- the operand of `neg`
  have hneg : p1.toNat < m.size →
      (n64 - p1 - 1).toNat ≤ m.size ∧
      messageCompiled.textNeg.bound (slice m (p1 + 1) (n64 - p1 - 1)) ≤
        104 * (n64 - p1 - 1).toNat + 608 ∧
      ((textNeg (slice m (p1 + 1) (n64 - p1 - 1))).2.size.toUInt64 + 2).toNat ≤
        (n64 - p1 - 1).toNat + 3 := by
    intro h
    have hl : (n64 - p1 - 1).toNat = m.size - p1.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_sub_of_le _ _ ?_, hN]
      · simp
      · rw [UInt64.le_iff_toNat_le, hN]; omega
      · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, hN]; omega), hN]
        simp; omega
    have hs : (slice m (p1 + 1) (n64 - p1 - 1)).size < 2 ^ 30 := by
      rw [slice_size]; omega
    have ht := textNeg_text_size _ hs
    rw [slice_size] at ht
    refine ⟨by omega, ?_, ?_⟩
    · rw [m_textNeg_bound]
      have := textNeg_bound_le _ hs
      rw [slice_size] at this
      exact this
    · rw [toNat_size_add2 _ (by omega)]; omega
  -- the operands of the binary operations
  have hbin : p2.toNat ≠ m.size →
      (p2 - p1 - 1).toNat + (n64 - p2 - 1).toNat ≤ m.size ∧
      (slice m (p1 + 1) (p2 - p1 - 1)).size = (p2 - p1 - 1).toNat ∧
      (slice m (p2 + 1) (n64 - p2 - 1)).size = (n64 - p2 - 1).toNat := by
    intro h
    have ⟨h1, h2⟩ : p1.toNat + 1 ≤ p2.toNat ∧ p2.toNat < m.size := by omega
    have la : (p2 - p1 - 1).toNat = p2.toNat - p1.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_sub_of_le _ _ ?_]
      · simp
      · rw [UInt64.le_iff_toNat_le]; omega
      · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le]; omega)]
        simp; omega
    have lb : (n64 - p2 - 1).toNat = m.size - p2.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_sub_of_le _ _ ?_, hN]
      · simp
      · rw [UInt64.le_iff_toNat_le, hN]; omega
      · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, hN]; omega), hN]
        simp; omega
    exact ⟨by omega, slice_size _ _ _, slice_size _ _ _⟩
  simp (config := { maxSteps := 4000000 }) only [hlt, heq, hne, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq,
    Verified.blockCost_eq, Verified.growCost_eq, Verified.paidGrowCost_eq, List.size_toArray,
    List.length_nil, UInt64.reduceToNat]
  repeat' split
  all_goals first
    | omega
    | (obtain ⟨n1, n2, n3⟩ := hneg (by omega); omega)
    | (obtain ⟨b1, b2, b3⟩ := hbin (by omega)
       obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
         binary_facts (slice m (p1 + 1) (p2 - p1 - 1)) (slice m (p2 + 1) (n64 - p2 - 1))
           (by omega) (by omega)
       omega)

/-! ## The length of the line -/

theorem okLine_length (z : ℤ) : (okLine z).length = (printSpec z).size + 2 := by
  rw [okLine, ascii_append, List.length_append, printSpec, words_size]
  have : (ascii "0 ").length = 2 := by decide
  omega

theorem errLine_length {k : ℕ} (hk : k < 10) : (errLine k).length = 1 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 by
    omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem operand_natAbs_lt {a : List UInt8} {x : ℤ} (h : operand a = some x) :
    x.natAbs < 10 ^ a.length := by
  have := denote_natAbs_lt (s := words a) (by rw [words_toList]; exact h)
  rwa [words_size] at this

theorem binaryLine_length (d : Bool) {f : ℤ → ℤ → ℤ}
    (hf : ∀ a b, (f a b).natAbs ≤ (a.natAbs + 1) * (b.natAbs + 1)) (a b : List UInt8) :
    (binaryLine d f a b).length ≤ a.length + b.length + 4 := by
  unfold binaryLine
  cases hx : operand a with
  | none => rw [errLine_length (by norm_num)]; omega
  | some x =>
    cases hy : operand b with
    | none => dsimp only; rw [errLine_length (by norm_num)]; omega
    | some y =>
      dsimp only
      split
      · rw [errLine_length (by norm_num)]; omega
      · rw [okLine_length]
        have := result_text_size hf (s := words a) (t := words b) (by rw [words_toList]; exact hx)
          (by rw [words_toList]; exact hy)
        rw [words_size, words_size] at this
        omega

theorem sign_le (a b : ℤ) : (a - b).sign.natAbs ≤ (a.natAbs + 1) * (b.natAbs + 1) := by
  have : (a - b).sign.natAbs ≤ 1 := by
    rcases Int.sign_trichotomy (a - b) with h | h | h <;> rw [h] <;> decide
  have : 1 ≤ (a.natAbs + 1) * (b.natAbs + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-- A line has at most four bytes more than its message. -/
theorem calcSpec_length_le (m : List UInt8) : (calcSpec m).length ≤ m.length + 4 := by
  have hint : [(32 : UInt8)].intercalate (m.splitOn 32) = m := List.intercalate_splitOn 32
  unfold calcSpec
  split
  · rw [errLine_length (by norm_num)]; omega
  split
  · rw [errLine_length (by norm_num)]; omega
  split
  · rename_i name a heq
    rw [heq] at hint
    have ha : a.length + 1 ≤ m.length := by
      rw [← hint]; simp [List.intercalate]
    split
    · unfold unaryLine
      cases hx : operand a with
      | none => rw [errLine_length (by norm_num)]; omega
      | some x =>
        dsimp only
        rw [okLine_length]
        have := printSpec_size_le (z := -x) (D := a.length)
          (by rw [Int.natAbs_neg]; exact operand_natAbs_lt hx)
        omega
    · rw [errLine_length (by norm_num)]; omega
  · rename_i name a b heq
    rw [heq] at hint
    have hab : a.length + b.length + 2 ≤ m.length := by
      rw [← hint]; simp [List.intercalate]; omega
    split_ifs
    · exact le_trans (binaryLine_length false sign_le a b) (by omega)
    · exact le_trans (binaryLine_length false computes_add.le a b) (by omega)
    · exact le_trans (binaryLine_length false computes_sub.le a b) (by omega)
    · exact le_trans (binaryLine_length false computes_mul.le a b) (by omega)
    · exact le_trans (binaryLine_length true computes_tdiv.le a b) (by omega)
    · exact le_trans (binaryLine_length true computes_tmod.le a b) (by omega)
    · exact le_trans (binaryLine_length true computes_ediv.le a b) (by omega)
    · exact le_trans (binaryLine_length true computes_emod.le a b) (by omega)
    · rw [errLine_length (by norm_num)]; omega
  · rw [errLine_length (by norm_num)]; omega

/-! ## The bare-metal entry -/

/-- The bare-metal entry allocates at most `2 ^ 25` bytes, whatever its arguments. -/
theorem calcWords_bound_le (ws : Array UInt64) (len : UInt64) :
    messageCompiled.calcWords.bound (ws, len) ≤ 2 ^ 25 := by
  rw [messageCompiled.calcWords.bound_eq, messageCompiled.pack.bound_eq]
  by_cases h : 65536 < len
  · simp only [h, ite_true, Verified.blockCost_eq, Verified.growCost_eq, List.size_toArray,
      List.length_cons, List.length_nil, UInt64.reduceToNat]
    decide
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), ite_eq_right_iff.mpr (fun h' => absurd h' h),
      messageCompiled.unpack.bound_eq]
    have hl : len.toNat ≤ 65536 := by
      rw [UInt64.lt_iff_toNat_lt] at h; simp at h; omega
    have hus : (unpack ws len).size = len.toNat := by rw [unpack, build_size]
    have hc := calcLine_bound_le (unpack ws len) (by omega)
    have hsz : (calcLine (unpack ws len)).size ≤ len.toNat + 4 := by
      rw [unpack_eq, calcLine_eq _ (by simp; omega), words_size]
      have := calcSpec_length_le ((List.range len.toNat).map (Library.Bytes.byteAt ws))
      simpa using this
    have hp : (((calcLine (unpack ws len)).size.toUInt64 + 7) / 8).toNat ≤ len.toNat / 8 + 2 := by
      rw [UInt64.toNat_div, UInt64.toNat_add, size_toNat64 (by omega)]
      simp only [UInt64.reduceToNat]
      omega
    rw [hus] at hc
    simp only [Verified.blockCost_eq]
    omega

end Demos.BignumCalc
