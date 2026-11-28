module

public import Demos.BignumCalc.MessageProgram
public import Demos.BignumCalc.Message
public import Library.Numerics.Bignum.Export
public import Library.Bytes.Packed
import all Init.Data.Repr
import all Init.Data.Int.Repr

@[expose] public section

/-!
# The calculator computes the line of its message

`calcLine_eq` states that `calcLine`, on the bytes of a message one to a word, returns the bytes of
`calcSpec`'s line.  `nextSpace_spec` gives the position of the first space at or after a start,
`splitOn_at` splits a message at such a position as `List.splitOn` does, `opCode_eq` reads the
operation's name, and `line_binary`, `line_unary`, and `line_cmp` join the text exports'
specifications with the lines of `Message.lean`.
-/

namespace Demos.BignumCalc

open Library.Numerics.Bignum

open Library.Numerics.Decimal.Shared.StrconvGrammar (ascii words)
open Library.Numerics.Decimal.Int64Text (denote)
open LeanExe.Dialect

/-! ## Bytes one to a word -/

theorem words_size (m : List UInt8) : (words m).size = m.length := by simp [words]

theorem words_toList (m : List UInt8) : (words m).toList = m.map UInt8.toUInt64 := by simp [words]

theorem words_get (m : List UInt8) {i : ℕ} (hi : i < m.length) :
    (words m)[i]! = (m[i]).toUInt64 := by
  simp [words, hi]

theorem toUInt64_eq_32 (b : UInt8) : b.toUInt64 = 32 ↔ b = 32 := by
  constructor
  · intro h
    have : b.toUInt64 = (32 : UInt8).toUInt64 := h
    exact UInt8.toUInt64_inj.mp this
  · rintro rfl; rfl

theorem toNat64_of_lt {k : ℕ} (h : k < 2 ^ 64) : (UInt64.ofNat k).toNat = k :=
  UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)

/-! ## The next space -/

/-- `nextSpace m s` is the size of `m` when no word from `s` on is a space, and otherwise the first
position from `s` on that holds a space. -/
theorem nextSpace_spec (M : Array UInt64) (s : UInt64) (hn : M.size < 2 ^ 64) :
    ((nextSpace M s).toNat = M.size ∧ ∀ j, s.toNat ≤ j → j < M.size → M[j]! ≠ 32) ∨
    (s.toNat ≤ (nextSpace M s).toNat ∧ (nextSpace M s).toNat < M.size ∧
      M[(nextSpace M s).toNat]! = 32 ∧
      ∀ j, s.toNat ≤ j → j < (nextSpace M s).toNat → M[j]! ≠ 32) := by
  have hN : M.size.toUInt64.toNat = M.size := size_toNat64 hn
  unfold nextSpace
  have h := loop_induction (n := M.size.toUInt64) (init := M.size.toUInt64)
    (f := fun i p => if p == M.size.toUInt64 && s ≤ i && M[i.toNat]! == 32 then i else p)
    (fun k p => (p = M.size.toUInt64 ∧ ∀ j, s.toNat ≤ j → j < k → M[j]! ≠ 32) ∨
      (s.toNat ≤ p.toNat ∧ p.toNat < k ∧ M[p.toNat]! = 32 ∧
        ∀ j, s.toNat ≤ j → j < p.toNat → M[j]! ≠ 32))
    (Or.inl ⟨rfl, fun j _ h => absurd h (Nat.not_lt_zero _)⟩)
    (fun k p hk ih => by
      rw [hN] at hk
      have hk64 : (UInt64.ofNat k).toNat = k := toNat64_of_lt (by omega)
      rcases ih with ⟨rfl, hno⟩ | ⟨hs, hpk, h32, hno⟩
      · split
        · rename_i hcond
          simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
            decide_eq_true_eq, UInt64.le_iff_toNat_le, hk64] at hcond
          right
          rw [hk64]
          exact ⟨hcond.1, by omega, hcond.2, fun j hj1 hj2 => hno j hj1 hj2⟩
        · rename_i hcond
          simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
            decide_eq_true_eq, UInt64.le_iff_toNat_le, hk64, not_and] at hcond
          left
          refine ⟨rfl, fun j hj1 hj2 => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj2 with hj | rfl
          · exact hno j hj1 hj
          · exact hcond hj1
      · have hne : p ≠ M.size.toUInt64 := by
          intro he
          rw [he, hN] at hpk
          omega
        split
        · rename_i hcond
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          exact absurd hcond.1.1 hne
        · right
          exact ⟨hs, by omega, h32, hno⟩)
  rw [hN] at h
  rcases h with ⟨he, hno⟩ | h
  · left
    exact ⟨by rw [he]; exact hN, hno⟩
  · exact Or.inr h

/-! ## Splitting a message at a space -/

/-- A message whose first space is at position `p` splits into the bytes before it and the parts of
the bytes after it. -/
theorem splitOn_at {m : List UInt8} {p : ℕ} (hp : p < m.length) (h32 : m[p] = 32)
    (hno : ∀ j, j < p → (hj : j < m.length) → m[j] ≠ 32) :
    m.splitOn 32 = m.take p :: (m.drop (p + 1)).splitOn 32 := by
  have hm : m = m.take p ++ 32 :: m.drop (p + 1) := by
    conv_lhs => rw [← List.take_append_drop p m]
    rw [List.drop_eq_getElem_cons hp, h32]
  have hnot : (32 : UInt8) ∉ m.take p := by
    intro hmem
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hmem
    rw [List.length_take] at hj
    rw [List.getElem_take] at hjv
    exact hno j (by omega) (by omega) hjv
  conv_lhs => rw [hm]
  exact List.splitOn_append_cons_self_of_not_mem hnot _

/-- A message with no space at or after position `p` has no space in its bytes from `p` on. -/
theorem not_mem_drop {m : List UInt8} {p : ℕ}
    (hno : ∀ j, p ≤ j → (hj : j < m.length) → m[j] ≠ 32) : (32 : UInt8) ∉ m.drop p := by
  intro hmem
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hmem
  rw [List.length_drop] at hj
  rw [List.getElem_drop] at hjv
  exact hno (p + j) (by omega) (by omega) hjv

/-! ## The operation's name -/

/-- The code of the operation that a name names, as `opCode` returns it. -/
def specCode (name : List UInt8) : UInt64 :=
  if name = ascii "neg" then 1
  else if name = ascii "cmp" then 2
  else if name = ascii "add" then 3
  else if name = ascii "sub" then 4
  else if name = ascii "mul" then 5
  else if name = ascii "tdiv" then 6
  else if name = ascii "tmod" then 7
  else if name = ascii "ediv" then 8
  else if name = ascii "emod" then 9
  else 0

theorem take_three {m : List UInt8} (h : 3 ≤ m.length) :
    m.take 3 = [m[0], m[1], m[2]] := by
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [List.length_take, List.length_cons, List.length_nil] at h1 h2
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> simp

theorem take_four {m : List UInt8} (h : 4 ≤ m.length) :
    m.take 4 = [m[0], m[1], m[2], m[3]] := by
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [List.length_take, List.length_cons, List.length_nil] at h1 h2
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> simp

theorem name3_eq (m : List UInt8) (p : UInt64) (hp : p.toNat ≤ m.length) (c0 c1 c2 : UInt8) :
    name3 (words m) p c0.toUInt64 c1.toUInt64 c2.toUInt64 = decide (m.take p.toNat = [c0, c1, c2]) := by
  unfold name3
  by_cases h3 : p = 3
  · subst h3
    have hl : 3 ≤ m.length := by simpa using hp
    simp only [UInt64.reduceToNat, beq_self_eq_true, Bool.true_and]
    simp only [take_three hl, words_get m (show 0 < m.length by omega),
      words_get m (show 1 < m.length by omega), words_get m (show 2 < m.length by omega),
      List.cons.injEq, and_true]
    by_cases a : m[0] = c0 <;> by_cases b : m[1] = c1 <;> by_cases c : m[2] = c2 <;> simp [a, b, c, UInt8.toUInt64_inj]
  · have hne : (p == 3) = false := by simpa using h3
    have hlen : (m.take p.toNat).length ≠ 3 := by
      rw [List.length_take, Nat.min_eq_left hp]
      intro h
      exact h3 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    rw [hne]
    symm
    simp only [Bool.false_and, decide_eq_false_iff_not]
    intro h
    exact hlen (by rw [h]; rfl)

theorem name4_eq (m : List UInt8) (p : UInt64) (hp : p.toNat ≤ m.length) (c0 c1 c2 c3 : UInt8) :
    name4 (words m) p c0.toUInt64 c1.toUInt64 c2.toUInt64 c3.toUInt64 =
      decide (m.take p.toNat = [c0, c1, c2, c3]) := by
  unfold name4
  by_cases h4 : p = 4
  · subst h4
    have hl : 4 ≤ m.length := by simpa using hp
    simp only [UInt64.reduceToNat, beq_self_eq_true, Bool.true_and]
    simp only [take_four hl, words_get m (show 0 < m.length by omega),
      words_get m (show 1 < m.length by omega), words_get m (show 2 < m.length by omega),
      words_get m (show 3 < m.length by omega), List.cons.injEq, and_true]
    by_cases a : m[0] = c0 <;> by_cases b : m[1] = c1 <;> by_cases c : m[2] = c2 <;>
      by_cases d : m[3] = c3 <;> simp [a, b, c, d, UInt8.toUInt64_inj]
  · have hne : (p == 4) = false := by simpa using h4
    have hlen : (m.take p.toNat).length ≠ 4 := by
      rw [List.length_take, Nat.min_eq_left hp]
      intro h
      exact h4 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    rw [hne]
    symm
    simp only [Bool.false_and, decide_eq_false_iff_not]
    intro h
    exact hlen (by rw [h]; rfl)

theorem opCode_eq (m : List UInt8) (p : UInt64) (hp : p.toNat ≤ m.length) :
    opCode (words m) p = specCode (m.take p.toNat) := by
  unfold opCode specCode
  rw [show (110 : UInt64) = (110 : UInt8).toUInt64 from rfl,
    show (101 : UInt64) = (101 : UInt8).toUInt64 from rfl,
    show (103 : UInt64) = (103 : UInt8).toUInt64 from rfl,
    show (99 : UInt64) = (99 : UInt8).toUInt64 from rfl,
    show (109 : UInt64) = (109 : UInt8).toUInt64 from rfl,
    show (112 : UInt64) = (112 : UInt8).toUInt64 from rfl,
    show (97 : UInt64) = (97 : UInt8).toUInt64 from rfl,
    show (100 : UInt64) = (100 : UInt8).toUInt64 from rfl,
    show (115 : UInt64) = (115 : UInt8).toUInt64 from rfl,
    show (117 : UInt64) = (117 : UInt8).toUInt64 from rfl,
    show (98 : UInt64) = (98 : UInt8).toUInt64 from rfl,
    show (108 : UInt64) = (108 : UInt8).toUInt64 from rfl,
    show (116 : UInt64) = (116 : UInt8).toUInt64 from rfl,
    show (105 : UInt64) = (105 : UInt8).toUInt64 from rfl,
    show (118 : UInt64) = (118 : UInt8).toUInt64 from rfl,
    show (111 : UInt64) = (111 : UInt8).toUInt64 from rfl]
  rw [name3_eq m p hp, name3_eq m p hp, name3_eq m p hp, name3_eq m p hp, name3_eq m p hp,
    name4_eq m p hp, name4_eq m p hp, name4_eq m p hp, name4_eq m p hp]
  rw [show ascii "neg" = [110, 101, 103] by decide, show ascii "cmp" = [99, 109, 112] by decide,
    show ascii "add" = [97, 100, 100] by decide, show ascii "sub" = [115, 117, 98] by decide,
    show ascii "mul" = [109, 117, 108] by decide, show ascii "tdiv" = [116, 100, 105, 118] by decide,
    show ascii "tmod" = [116, 109, 111, 100] by decide,
    show ascii "ediv" = [101, 100, 105, 118] by decide,
    show ascii "emod" = [101, 109, 111, 100] by decide]
  simp only [decide_eq_true_eq]

/-! ## Operands and lines -/

theorem slice_words (m : List UInt8) (s len : UInt64) (h : s.toNat + len.toNat ≤ m.length)
    (h64 : m.length < 2 ^ 64) :
    slice (words m) s len = words ((m.drop s.toNat).take len.toNat) := by
  apply Array.ext
  · rw [slice, build_size, words_size, List.length_take, List.length_drop]
    omega
  · intro i h1 h2
    rw [slice, build_size] at h1
    have hi : (s + UInt64.ofNat i).toNat = s.toNat + i := by
      rw [UInt64.toNat_add, toNat64_of_lt (by have := len.toNat_lt; omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have e1 := build_get (f := fun i => (words m)[(s + i).toNat]!) h1
    rw [← getElem!_pos (slice (words m) s len) i (by rw [slice, build_size]; exact h1)]
    rw [slice, e1]
    simp only [hi]
    rw [words_get m (by omega)]
    simp [words]

theorem words_errLine1 : words (errLine 1) = #[49] := by decide
theorem words_errLine2 : words (errLine 2) = #[50] := by decide
theorem words_errLine3 : words (errLine 3) = #[51] := by decide
theorem words_errLine4 : words (errLine 4) = #[52] := by decide

theorem words_okLine (z : ℤ) : words (okLine z) = #[48, 32] ++ printSpec z := by
  rw [okLine, ascii_append, printSpec]
  apply Array.ext'
  have h0 : List.map UInt8.toUInt64 (ascii "0 ") = [48, 32] := by decide
  simp [words, h0]

theorem line_zero (t : Array UInt64) (ht : t.size < 2 ^ 32) : line 0 t = #[48, 32] ++ t := by
  have hs : (t.size.toUInt64 + 2).toNat = t.size + 2 := by
    rw [UInt64.toNat_add, size_toNat64 (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  unfold line
  simp only [beq_self_eq_true, ite_true]
  apply Array.ext
  · rw [build_size, hs, Array.size_append]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega
  · intro i h1 h2
    rw [build_size, hs] at h1
    rw [← getElem!_pos _ i (by rw [build_size, hs]; exact h1), build_get (by rw [hs]; exact h1)]
    have hi : (UInt64.ofNat i).toNat = i := toNat64_of_lt (by omega)
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | h2i
    · simp
    · simp
    · have hne0 : (UInt64.ofNat i == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, hi, UInt64.reduceToNat]
        omega
      have hne1 : (UInt64.ofNat i == 1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, hi, UInt64.reduceToNat]
        omega
      have hsub : (UInt64.ofNat i - 2).toNat = i - 2 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hi]; simp; omega), hi]
        rfl
      simp only [hne0, hne1, Bool.false_eq_true, ite_false, hsub]
      rw [Array.getElem_append_right (by simp; omega), getElem!_pos t (i - 2) (by omega)]
      simp

theorem line_err (k : UInt64) (hk : (k == 0) = false) (t : Array UInt64 := #[]) :
    line k t = #[48 + k] := by
  unfold line
  simp [hk]

theorem printSpec_size_le {z : ℤ} {D : ℕ} (h : z.natAbs < 10 ^ D) : (printSpec z).size ≤ D + 1 := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hz : z = 0 := by simp at h; omega
    subst hz
    decide
  rw [printSpec_size]
  have hlen : (Library.Numerics.Decimal.Int64Text.digitWords z.natAbs).length ≤ D :=
    (Library.Numerics.Decimal.Int64Text.digitWords_length_le_iff _ _ hD).mpr h
  split <;> omega

theorem result_text_size {f : ℤ → ℤ → ℤ} (hf : ∀ a b, (f a b).natAbs ≤ (a.natAbs + 1) * (b.natAbs + 1))
    {s t : Array UInt64} {x y : ℤ} (hx : denote s.toList = some x) (hy : denote t.toList = some y) :
    (printSpec (f x y)).size ≤ s.size + t.size + 2 := by
  apply printSpec_size_le (D := s.size + t.size + 1)
  have h1 := denote_natAbs_lt hx
  have h2 := denote_natAbs_lt hy
  calc (f x y).natAbs ≤ (x.natAbs + 1) * (y.natAbs + 1) := hf x y
    _ ≤ 10 ^ s.size * 10 ^ t.size := Nat.mul_le_mul h1 h2
    _ = 10 ^ (s.size + t.size) := (pow_add _ _ _).symm
    _ < 10 ^ (s.size + t.size + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- The line of a binary text export's status and text is the line of `binaryLine`. -/
theorem line_binary (d : Bool) (f : ℤ → ℤ → ℤ)
    (hf : ∀ a b, (f a b).natAbs ≤ (a.natAbs + 1) * (b.natAbs + 1))
    (a b : List UInt8) (ha : a.length < 2 ^ 30) (hb : b.length < 2 ^ 30) :
    line (textBinary d f (words a) (words b)).1 (textBinary d f (words a) (words b)).2 =
      words (binaryLine d f a b) := by
  unfold textBinary binaryLine operand
  rw [words_toList, words_toList]
  cases hx : denote (a.map UInt8.toUInt64) with
  | none => rw [line_err 1 rfl, words_errLine1]; rfl
  | some x =>
    cases hy : denote (b.map UInt8.toUInt64) with
    | none => rw [line_err 2 rfl, words_errLine2]; rfl
    | some y =>
      dsimp only
      split
      · rw [line_err 3 rfl, words_errLine3]; rfl
      · have hs := result_text_size hf (s := words a) (t := words b) (by rwa [words_toList])
          (by rwa [words_toList])
        rw [words_size, words_size] at hs
        rw [line_zero _ (by dsimp only; omega), words_okLine]

/-- The line of `neg`'s status and text is the line of `unaryLine`. -/
theorem line_unary (a : List UInt8) (ha : a.length < 2 ^ 30) :
    line (textUnary (fun x => -x) (words a)).1 (textUnary (fun x => -x) (words a)).2 =
      words (unaryLine (fun x => -x) a) := by
  unfold textUnary unaryLine operand
  rw [words_toList]
  cases hx : denote (a.map UInt8.toUInt64) with
  | none => rw [line_err 1 rfl, words_errLine1]; rfl
  | some x =>
    dsimp only
    have h1 := denote_natAbs_lt (s := words a) (by rwa [words_toList])
    rw [words_size] at h1
    have hs : (printSpec (-x)).size ≤ a.length + 1 :=
      printSpec_size_le (by rw [Int.natAbs_neg]; exact h1)
    rw [line_zero _ (by omega), words_okLine]

theorem cmpText_eq (x y : ℤ) : cmpText (cmpSpec x y) = printSpec (x - y).sign := by
  unfold cmpSpec
  by_cases h1 : x < y
  · rw [ite_eq_left_iff.mpr (fun h => absurd h1 h), Int.sign_eq_neg_one_of_neg (by omega)]
    decide
  · by_cases h2 : x = y
    · rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_left_iff.mpr (fun h => absurd h2 h), h2,
        Int.sub_self, Int.sign_zero]
      decide
    · rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_right_iff.mpr (fun h => absurd h h2),
        Int.sign_eq_one_of_pos (by omega)]
      decide

/-- The line of `cmp`'s status and code is the line of `binaryLine` with the sign of the
difference. -/
theorem line_cmp (a b : List UInt8) :
    line (textCmpSpec (words a) (words b)).1 (cmpText (textCmpSpec (words a) (words b)).2) =
      words (binaryLine false (fun x y => (x - y).sign) a b) := by
  unfold textCmpSpec binaryLine operand
  rw [words_toList, words_toList]
  cases hx : denote (a.map UInt8.toUInt64) with
  | none =>
    dsimp only
    rw [line_err 1 rfl (cmpText 0), words_errLine1]; rfl
  | some x =>
    cases hy : denote (b.map UInt8.toUInt64) with
    | none =>
      dsimp only
      rw [line_err 2 rfl (cmpText 0), words_errLine2]; rfl
    | some y =>
      dsimp only
      simp only [Bool.false_eq_true, false_and, ite_false]
      rw [cmpText_eq, line_zero _ ?_, words_okLine]
      · have : (printSpec (x - y).sign).size ≤ 2 := printSpec_size_le (D := 1) (by
          rcases Int.sign_trichotomy (x - y) with h | h | h <;> rw [h] <;> decide)
        omega

/-! ## The calculator's line -/

/-- `nextSpace` on the words of a message, in terms of the message's bytes. -/
theorem nextSpace_list (m : List UInt8) (s : UInt64) (h64 : m.length < 2 ^ 64) :
    ((nextSpace (words m) s).toNat = m.length ∧
        ∀ j, s.toNat ≤ j → (hj : j < m.length) → m[j] ≠ 32) ∨
      (s.toNat ≤ (nextSpace (words m) s).toNat ∧
        ∃ hp : (nextSpace (words m) s).toNat < m.length, m[(nextSpace (words m) s).toNat] = 32 ∧
          ∀ j, s.toNat ≤ j → j < (nextSpace (words m) s).toNat → (hj : j < m.length) → m[j] ≠ 32) := by
  rcases nextSpace_spec (words m) s (by rw [words_size]; exact h64) with ⟨he, hno⟩ | ⟨hs, hp, h32, hno⟩
  · left
    rw [words_size] at he hno
    refine ⟨he, fun j hj1 hj2 => ?_⟩
    have := hno j hj1 hj2
    rw [words_get m hj2] at this
    exact fun h => this (by rw [h]; rfl)
  · right
    rw [words_size] at hp
    refine ⟨hs, hp, ?_, fun j hj1 hj2 hj => ?_⟩
    · rw [words_get m hp] at h32
      exact (toUInt64_eq_32 _).mp h32
    · have := hno j hj1 hj2
      rw [words_get m hj] at this
      exact fun h => this (by rw [h]; rfl)

/-- The branch of `calcLine` for the binary operations, on the words of two operands. -/
theorem binary_dispatch (name a b : List UInt8) (ha : a.length < 2 ^ 30) (hb : b.length < 2 ^ 30)
    (h0 : specCode name ≠ 0) (h1 : specCode name ≠ 1) :
    (if (specCode name == 2) = true then
        line (textCmp (words a) (words b)).1 (cmpText (textCmp (words a) (words b)).2)
      else
        line
          (if (specCode name == 3) = true then textAdd (words a) (words b)
            else if (specCode name == 4) = true then textSub (words a) (words b)
            else if (specCode name == 5) = true then textMul (words a) (words b)
            else if (specCode name == 6) = true then textTDiv (words a) (words b)
            else if (specCode name == 7) = true then textTMod (words a) (words b)
            else if (specCode name == 8) = true then textEDiv (words a) (words b)
            else textEMod (words a) (words b)).1
          (if (specCode name == 3) = true then textAdd (words a) (words b)
            else if (specCode name == 4) = true then textSub (words a) (words b)
            else if (specCode name == 5) = true then textMul (words a) (words b)
            else if (specCode name == 6) = true then textTDiv (words a) (words b)
            else if (specCode name == 7) = true then textTMod (words a) (words b)
            else if (specCode name == 8) = true then textEDiv (words a) (words b)
            else textEMod (words a) (words b)).2) =
      words (if name = ascii "cmp" then binaryLine false (fun x y => (x - y).sign) a b
        else if name = ascii "add" then binaryLine false (· + ·) a b
        else if name = ascii "sub" then binaryLine false (· - ·) a b
        else if name = ascii "mul" then binaryLine false (· * ·) a b
        else if name = ascii "tdiv" then binaryLine true Int.tdiv a b
        else if name = ascii "tmod" then binaryLine true Int.tmod a b
        else if name = ascii "ediv" then binaryLine true (· / ·) a b
        else if name = ascii "emod" then binaryLine true (· % ·) a b
        else errLine 4) := by
  have hA : (words a).size < 2 ^ 30 := by rw [words_size]; exact ha
  have hB : (words b).size < 2 ^ 30 := by rw [words_size]; exact hb
  by_cases hn : name = ascii "neg"
  · exact absurd (by rw [hn]; decide) h1
  by_cases hc : name = ascii "cmp"
  · subst hc
    rw [show specCode (ascii "cmp") = 2 by decide]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [textCmp_eq _ _ hA hB]
    exact line_cmp a b
  by_cases hadd : name = ascii "add"
  · subst hadd
    rw [show specCode (ascii "add") = 3 by decide]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [textAdd_eq _ _ hA hB]
    exact line_binary false (· + ·) computes_add.le a b ha hb
  by_cases hsub : name = ascii "sub"
  · subst hsub
    rw [show specCode (ascii "sub") = 4 by decide]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [textSub_eq _ _ hA hB]
    exact line_binary false (· - ·) computes_sub.le a b ha hb
  by_cases hmul : name = ascii "mul"
  · subst hmul
    rw [show specCode (ascii "mul") = 5 by decide]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [textMul_eq _ _ hA hB]
    exact line_binary false (· * ·) computes_mul.le a b ha hb
  by_cases htdiv : name = ascii "tdiv"
  · subst htdiv
    rw [show specCode (ascii "tdiv") = 6 by decide]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [textTDiv_eq _ _ hA hB]
    exact line_binary true Int.tdiv computes_tdiv.le a b ha hb
  by_cases htmod : name = ascii "tmod"
  · subst htmod
    rw [show specCode (ascii "tmod") = 7 by decide]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [textTMod_eq _ _ hA hB]
    exact line_binary true Int.tmod computes_tmod.le a b ha hb
  by_cases hediv : name = ascii "ediv"
  · subst hediv
    rw [show specCode (ascii "ediv") = 8 by decide]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [textEDiv_eq _ _ hA hB]
    exact line_binary true (· / ·) computes_ediv.le a b ha hb
  by_cases hemod : name = ascii "emod"
  · subst hemod
    rw [show specCode (ascii "emod") = 9 by decide]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [textEMod_eq _ _ hA hB]
    exact line_binary true (· % ·) computes_emod.le a b ha hb
  exact absurd (by simp only [specCode, hn, hc, hadd, hsub, hmul, htdiv, htmod, hediv, hemod, ite_false]) h0

theorem specCode_one {name : List UInt8} (h : specCode name = 1) : name = ascii "neg" := by
  unfold specCode at h
  split_ifs at h <;> first | assumption | exact absurd h (by decide)

theorem specCode_zero {name : List UInt8} (h : specCode name = 0) :
    name ≠ ascii "cmp" ∧ name ≠ ascii "add" ∧ name ≠ ascii "sub" ∧ name ≠ ascii "mul" ∧
      name ≠ ascii "tdiv" ∧ name ≠ ascii "tmod" ∧ name ≠ ascii "ediv" ∧ name ≠ ascii "emod" := by
  unfold specCode at h
  split_ifs at h <;> first | exact absurd h (by decide) | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> assumption)

theorem drop_take_full (l : List UInt8) (k : ℕ) (h : l.length ≤ k) : l.take k = l :=
  List.take_of_length_le h

set_option maxHeartbeats 1000000 in
/-- `calcLine` on the bytes of a message, one to a word, returns the bytes of its line. -/
theorem calcLine_eq (m : List UInt8) (h64 : m.length < 2 ^ 64) :
    calcLine (words m) = words (calcSpec m) := by
  have hsz := words_size m
  have hN : (words m).size.toUInt64.toNat = m.length := by
    rw [size_toNat64 (by rw [hsz]; exact h64), hsz]
  unfold calcLine calcSpec
  by_cases hbig : msgMax < m.length
  · rw [ite_eq_left_iff.mpr (fun h => absurd (by rw [UInt64.lt_iff_toNat_lt, hN]; exact hbig) h),
      ite_eq_left_iff.mpr (fun h => absurd hbig h), words_errLine4]
  rw [ite_eq_right_iff.mpr (fun h => absurd (by rw [UInt64.lt_iff_toNat_lt, hN] at h; exact h) hbig),
    ite_eq_right_iff.mpr (fun h => absurd h hbig)]
  dsimp only
  have hn : m.length ≤ 65536 := by unfold msgMax at hbig; omega
  generalize hn64 : (words m).size.toUInt64 = n64 at hN ⊢
  have hlt : ∀ u : UInt64, (decide (u < n64)) = decide (u.toNat < m.length) := by
    intro u; exact decide_eq_decide.mpr (by rw [UInt64.lt_iff_toNat_lt, hN])
  have heq : ∀ u : UInt64, (u == n64) = decide (u.toNat = m.length) := by
    intro u
    rw [← hN]
    by_cases h : u = n64
    · subst h; simp
    · simp [h, UInt64.toNat_inj]
  have hplus : ∀ u : UInt64, u.toNat ≤ 65536 → (u + 1).toNat = u.toNat + 1 := by
    intro u hu
    rw [UInt64.toNat_add]
    simp only [UInt64.reduceToNat]
    omega
  rcases nextSpace_list m 0 h64 with ⟨hp1, hno1⟩ | ⟨-, hp1, h32a, hno1⟩
  · -- no space: the line is `4`
    have hnot : (32 : UInt8) ∉ m := by
      have := not_mem_drop (m := m) (p := 0) (fun j _ hj => hno1 j (by simp) hj)
      simpa using this
    rw [List.splitOn_eq_singleton hnot]
    generalize hq1 : nextSpace (words m) 0 = p1 at hp1 ⊢
    have hp2 : (nextSpace (words m) (p1 + 1)).toNat = m.length := by
      rcases nextSpace_list m (p1 + 1) h64 with ⟨h, -⟩ | ⟨h, hlt2, -⟩
      · exact h
      · rw [hplus p1 (by omega)] at h; omega
    have hd1 : decide ((p1 + 1).toNat < m.length) = false :=
      decide_eq_false (by rw [hplus p1 (by omega)]; omega)
    simp only [hlt, heq, hd1, hp2, decide_true, Bool.false_and, Bool.or_true, Bool.true_or,
      Bool.false_eq_true, ite_false, ite_true, ite_self, words_errLine4]
  · -- a first space at `p1`
    generalize hq1 : nextSpace (words m) 0 = p1 at hp1 h32a hno1 ⊢
    have hP1 : p1.toNat < m.length := hp1
    rw [splitOn_at hP1 h32a (fun j hj hjl => hno1 j (by simp) hj hjl), opCode_eq m p1 (by omega)]
    have hp1' : (p1 + 1).toNat = p1.toNat + 1 := hplus p1 (by omega)
    rcases nextSpace_list m (p1 + 1) h64 with ⟨hp2, hno2⟩ | ⟨hs2, hp2, h32b, hno2⟩
    · -- one space
      have hnot : (32 : UInt8) ∉ m.drop (p1.toNat + 1) :=
        not_mem_drop (fun j hj hjl => hno2 j (by rw [hp1']; exact hj) hjl)
      rw [List.splitOn_eq_singleton hnot]
      generalize hq2 : nextSpace (words m) (p1 + 1) = p2 at hp2 ⊢
      simp only [hlt, heq, hp1', hp2, decide_true, Bool.and_true, Bool.or_true, Bool.true_or,
        ite_true]
      by_cases hneg : m.take p1.toNat = ascii "neg"
      · rw [hneg, show specCode (ascii "neg") = 1 by decide]
        simp only [beq_self_eq_true, ite_true]
        by_cases hroom : p1.toNat + 1 < m.length
        swap
        · have hdrop : m.drop (p1.toNat + 1) = [] := List.drop_eq_nil_of_le (by omega)
          rw [hdrop]
          simp [hroom, words_errLine4]
        have hni : [] ∉ [ascii "neg", m.drop (p1.toNat + 1)] :=
          nil_not_mem2 (by decide) (fun h => by
            have := congrArg List.length h
            simp at this
            omega)
        rw [ite_eq_right_iff.mpr (fun h => absurd h hni)]
        simp only [hroom, decide_true, ite_true]
        have hsl : slice (words m) (p1 + 1) (n64 - p1 - 1) = words (m.drop (p1.toNat + 1)) := by
          have hl : (n64 - p1 - 1).toNat = m.length - p1.toNat - 1 := by
            rw [UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_sub_of_le _ _ ?_, hN]
            · simp
            · rw [UInt64.le_iff_toNat_le, hN]; omega
            · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by
                rw [UInt64.le_iff_toNat_le, hN]; omega), hN]
              simp; omega
          rw [slice_words m _ _ (by rw [hp1', hl]; omega) h64, hp1', hl,
            drop_take_full _ _ (by simp; omega)]
        rw [hsl, textNeg_eq _ (by rw [words_size]; simp; omega)]
        exact line_unary _ (by simp; omega)
      · have h1 : (specCode (m.take p1.toNat) == 1) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun h => hneg (specCode_one h)
        simp only [h1, Bool.false_eq_true, ite_false, hneg, ite_self, words_errLine4]
    · -- a second space at `p2`
      generalize hq2 : nextSpace (words m) (p1 + 1) = p2 at hs2 hp2 h32b hno2 ⊢
      rw [hp1'] at hs2 hno2
      have hP2 : p2.toNat < m.length := hp2
      have hr : (m.drop (p1.toNat + 1)).splitOn 32 =
          (m.drop (p1.toNat + 1)).take (p2.toNat - p1.toNat - 1) ::
            (m.drop (p2.toNat + 1)).splitOn 32 := by
        have hlen : p2.toNat - p1.toNat - 1 < (m.drop (p1.toNat + 1)).length := by simp; omega
        rw [splitOn_at hlen (by simp only [List.getElem_drop]; rw [← h32b]; congr 1; omega)
          (fun j hj hjl => by
            simp only [List.getElem_drop]
            exact hno2 _ (by omega) (by omega) _),
          List.drop_drop]
        congr 3
        omega
      rw [hr]
      have hp2' : (p2 + 1).toNat = p2.toNat + 1 := hplus p2 (by omega)
      have hp2ne : (p2 == n64) = false := by rw [heq]; simp; omega
      rcases nextSpace_list m (p2 + 1) h64 with ⟨hp3, hno3⟩ | ⟨hs3, hp3, h32c, hno3⟩
      · -- two spaces
        have hnot : (32 : UInt8) ∉ m.drop (p2.toNat + 1) :=
          not_mem_drop (fun j hj hjl => hno3 j (by rw [hp2']; exact hj) hjl)
        rw [List.splitOn_eq_singleton hnot]
        generalize hq3 : nextSpace (words m) (p2 + 1) = p3 at hp3 ⊢
        have hp3ne : (p3 != n64) = false := by
          simp only [bne_eq_false_iff_eq]
          rw [← UInt64.toNat_inj, hN]; exact hp3
        have hle1 : decide (p2 ≤ p1 + 1) = decide (p2.toNat ≤ p1.toNat + 1) :=
          decide_eq_decide.mpr (by rw [UInt64.le_iff_toNat_le, hp1'])
        have hle2 : decide (n64 ≤ p2 + 1) = decide (m.length ≤ p2.toNat + 1) :=
          decide_eq_decide.mpr (by rw [UInt64.le_iff_toNat_le, hN, hp2'])
        simp only [hlt, hle1, hle2, hp2ne, hp3ne, Bool.and_false, Bool.or_false,
          Bool.false_eq_true, ite_false]
        by_cases hmem : [] ∈ [m.take p1.toNat,
            (m.drop (p1.toNat + 1)).take (p2.toNat - p1.toNat - 1), m.drop (p2.toNat + 1)]
        · rw [ite_eq_left_iff.mpr (fun h => absurd hmem h), words_errLine4]
          have hcases : m.take p1.toNat = [] ∨ p2.toNat ≤ p1.toNat + 1 ∨
              m.length ≤ p2.toNat + 1 := by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
            rcases hmem with h | h | h
            · exact Or.inl h.symm
            · right; left
              have := congrArg List.length h
              simp at this
              omega
            · right; right
              have := congrArg List.length h
              simp at this
              omega
          rcases hcases with h | h | h
          · rw [h, show specCode [] = 0 by decide]
            simp
          · simp [h]
          · simp [h]
        rw [ite_eq_right_iff.mpr (fun h => absurd h hmem)]
        have hgap1 : ¬ p2.toNat ≤ p1.toNat + 1 := by
          intro h
          apply hmem
          have : (m.drop (p1.toNat + 1)).take (p2.toNat - p1.toNat - 1) = [] := by
            rw [show p2.toNat - p1.toNat - 1 = 0 by omega, List.take_zero]
          simp [this]
        have hgap2 : ¬ m.length ≤ p2.toNat + 1 := by
          intro h
          apply hmem
          simp [List.drop_eq_nil_of_le h]
        simp only [hgap1, hgap2, decide_false, Bool.or_false]
        by_cases hneg : m.take p1.toNat = ascii "neg"
        · rw [hneg, show specCode (ascii "neg") = 1 by decide]
          simp (config := { decide := true }) only [ite_true, ite_false]
        · have h1 : specCode (m.take p1.toNat) ≠ 1 := fun h => hneg (specCode_one h)
          have h1' : (specCode (m.take p1.toNat) == 1) = false := by simpa using h1
          simp only [h1', Bool.false_eq_true, ite_false]
          by_cases h0 : specCode (m.take p1.toNat) = 0
          · obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := specCode_zero h0
            simp only [h0, beq_self_eq_true, ite_true, n1, n2, n3, n4, n5, n6, n7, n8,
              ite_false, words_errLine4]
          · have h0' : (specCode (m.take p1.toNat) == 0) = false := by simpa using h0
            simp only [h0', Bool.false_eq_true, ite_false]
            have hsa : slice (words m) (p1 + 1) (p2 - p1 - 1) =
                words ((m.drop (p1.toNat + 1)).take (p2.toNat - p1.toNat - 1)) := by
              have hl : (p2 - p1 - 1).toNat = p2.toNat - p1.toNat - 1 := by
                rw [UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_sub_of_le _ _ ?_]
                · simp
                · rw [UInt64.le_iff_toNat_le]; omega
                · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by
                    rw [UInt64.le_iff_toNat_le]; omega)]
                  simp; omega
              rw [slice_words m _ _ (by rw [hp1', hl]; omega) h64, hp1', hl]
            have hsb : slice (words m) (p2 + 1) (n64 - p2 - 1) = words (m.drop (p2.toNat + 1)) := by
              have hl : (n64 - p2 - 1).toNat = m.length - p2.toNat - 1 := by
                rw [UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_sub_of_le _ _ ?_, hN]
                · simp
                · rw [UInt64.le_iff_toNat_le, hN]; omega
                · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by
                    rw [UInt64.le_iff_toNat_le, hN]; omega), hN]
                  simp; omega
              rw [slice_words m _ _ (by rw [hp2', hl]; omega) h64, hp2', hl,
                drop_take_full _ _ (by simp; omega)]
            rw [hsa, hsb]
            exact binary_dispatch _ _ _ (by simp; omega) (by simp; omega) h0 h1
      · -- three or more spaces: the line is `4`
        have hP3 : (nextSpace (words m) (p2 + 1)).toNat < m.length := hp3
        rw [hp2'] at hs3 hno3
        have hr3 : (m.drop (p2.toNat + 1)).splitOn 32 =
            (m.drop (p2.toNat + 1)).take ((nextSpace (words m) (p2 + 1)).toNat - p2.toNat - 1) ::
              (m.drop ((nextSpace (words m) (p2 + 1)).toNat + 1)).splitOn 32 := by
          have hlen : (nextSpace (words m) (p2 + 1)).toNat - p2.toNat - 1 <
              (m.drop (p2.toNat + 1)).length := by simp; omega
          rw [splitOn_at hlen (by simp only [List.getElem_drop]; rw [← h32c]; congr 1; omega)
            (fun j hj hjl => by
              simp only [List.getElem_drop]
              exact hno3 _ (by omega) (by omega) _), List.drop_drop]
          congr 3
          omega
        obtain ⟨y, rest, hy⟩ := List.exists_cons_of_ne_nil
          (List.splitOn_ne_nil 32 (m.drop ((nextSpace (words m) (p2 + 1)).toNat + 1)))
        rw [hr3, hy]
        generalize hq3 : nextSpace (words m) (p2 + 1) = p3 at hP3 ⊢
        have hp3ne : (p3 != n64) = true := by
          simp only [bne_iff_ne, ne_eq]
          rw [← UInt64.toNat_inj, hN]; omega
        simp only [hlt, hp2ne, hp3ne, Bool.and_false, Bool.or_true, Bool.true_or,
          Bool.false_eq_true, ite_false, ite_true, ite_self, words_errLine4]

/-! ## Bytes packed eight to a word -/

theorem byte_and (x : UInt64) : (x &&& 255).toNat = x.toNat % 256 := by
  rw [UInt64.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 8

/-- `unpack` reads the message's bytes, one to a word. -/
theorem unpack_eq (ws : Array UInt64) (n : UInt64) :
    unpack ws n = words ((List.range n.toNat).map (Library.Bytes.byteAt ws)) := by
  apply Array.ext
  · simp [unpack, build_size, words_size]
  · intro i h1 h2
    rw [unpack, build_size] at h1
    rw [← getElem!_pos (unpack ws n) i (by rw [unpack, build_size]; exact h1), unpack,
      build_get h1, ← getElem!_pos _ i h2, words_get _ (by simp; exact h1)]
    have hi : (UInt64.ofNat i).toNat = i := toNat64_of_lt (by have := n.toNat_lt; omega)
    simp only [List.getElem_map, List.getElem_range, Library.Bytes.byteAt]
    apply UInt64.toNat_inj.mp
    rw [byte_and, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
      UInt64.toNat_shiftRight]
    have h8 : (UInt64.ofNat i / 8).toNat = i / 8 := by rw [UInt64.toNat_div, hi]; rfl
    have hs : (8 * (UInt64.ofNat i % 8)).toNat = 8 * (i % 8) := by
      rw [UInt64.toNat_mul, UInt64.toNat_mod, hi]
      simp only [UInt64.reduceToNat]
      omega
    have hs' : (8 * (i % 8)).toUInt64.toNat = 8 * (i % 8) :=
      UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    rw [h8, hs, hs']

theorem natToUInt64_toNat {k : ℕ} (h : k < 2 ^ 64) : k.toUInt64.toNat = k := toNat64_of_lt h

/-- The value of the eight bytes that `pack` adds into a word. -/
theorem word_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (b0.toUInt64 + (b1.toUInt64 <<< 8) + (b2.toUInt64 <<< 16) + (b3.toUInt64 <<< 24) +
      (b4.toUInt64 <<< 32) + (b5.toUInt64 <<< 40) + (b6.toUInt64 <<< 48) +
      (b7.toUInt64 <<< 56)).toNat =
      b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat + 256 ^ 4 * b4.toNat +
        256 ^ 5 * b5.toNat + 256 ^ 6 * b6.toNat + 256 ^ 7 * b7.toNat := by
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, Nat.shiftLeft_eq,
    UInt64.reduceToNat]
  simp only [Nat.reduceMod, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (a := b1.toNat * 256) (by omega),
    Nat.mod_eq_of_lt (a := b2.toNat * 65536) (by omega),
    Nat.mod_eq_of_lt (a := b3.toNat * 16777216) (by omega),
    Nat.mod_eq_of_lt (a := b4.toNat * 4294967296) (by omega),
    Nat.mod_eq_of_lt (a := b5.toNat * 1099511627776) (by omega),
    Nat.mod_eq_of_lt (a := b6.toNat * 281474976710656) (by omega),
    Nat.mod_eq_of_lt (a := b7.toNat * 72057594037927936) (by omega)]
  repeat rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- Byte `i` of the word that `pack` adds from eight bytes is the `i`-th of them. -/
theorem word_byte (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) {i : ℕ} (hi : i < 8) :
    ((b0.toUInt64 + (b1.toUInt64 <<< 8) + (b2.toUInt64 <<< 16) + (b3.toUInt64 <<< 24) +
      (b4.toUInt64 <<< 32) + (b5.toUInt64 <<< 40) + (b6.toUInt64 <<< 48) +
      (b7.toUInt64 <<< 56)) >>> UInt64.ofNat (8 * i)).toUInt8 =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD i 0 := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, word_toNat, toNat64_of_lt (by omega),
    Nat.shiftRight_eq_div_pow]
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega

/-- Word `j` of `pack (words l)` holds the bytes `8 j` to `8 j + 7` of `l`, zeros past its end. -/
theorem pack_byte (l : List UInt8) (hl : l.length < 2 ^ 32) {j : ℕ}
    (hj : j < (pack (words l)).size) {i : ℕ} (hi : i < 8) :
    ((pack (words l))[j] >>> UInt64.ofNat (8 * i)).toUInt8 = l.getD (8 * j + i) 0 := by
  have hsz : (pack (words l)).size = (l.length + 7) / 8 := by
    rw [pack, build_size, words_size, UInt64.toNat_div, UInt64.toNat_add,
      natToUInt64_toNat (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  rw [hsz] at hj
  have hjn : (UInt64.ofNat j).toNat = j := toNat64_of_lt (by omega)
  have hb : ∀ t, t < 8 → (words l)[(8 * UInt64.ofNat j + UInt64.ofNat t).toNat]! =
      (l.getD (8 * j + t) 0).toUInt64 := by
    intro t ht
    have e : (8 * UInt64.ofNat j + UInt64.ofNat t).toNat = 8 * j + t := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, hjn, toNat64_of_lt (by omega)]
      simp only [UInt64.reduceToNat]
      omega
    rw [e]
    by_cases hq : 8 * j + t < l.length
    · rw [words_get l hq]
      simp [List.getD_eq_getElem?_getD, hq]
    · rw [getElem!_neg _ _ (by rw [words_size]; exact hq)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show l.length ≤ 8 * j + t by omega)]
      rfl
  have hb0 : (words l)[(8 * UInt64.ofNat j).toNat]! = (l.getD (8 * j) 0).toUInt64 := by
    have := hb 0 (by norm_num)
    simpa using this
  rw [← getElem!_pos (pack (words l)) j (by rw [hsz]; exact hj), pack,
    build_get (by rw [UInt64.toNat_div, UInt64.toNat_add, natToUInt64_toNat (by rw [words_size]; omega),
      words_size]; simp only [UInt64.reduceToNat]; omega)]
  rw [hb0, show (8 * UInt64.ofNat j + 1) = 8 * UInt64.ofNat j + UInt64.ofNat 1 from rfl,
    show (8 * UInt64.ofNat j + 2) = 8 * UInt64.ofNat j + UInt64.ofNat 2 from rfl,
    show (8 * UInt64.ofNat j + 3) = 8 * UInt64.ofNat j + UInt64.ofNat 3 from rfl,
    show (8 * UInt64.ofNat j + 4) = 8 * UInt64.ofNat j + UInt64.ofNat 4 from rfl,
    show (8 * UInt64.ofNat j + 5) = 8 * UInt64.ofNat j + UInt64.ofNat 5 from rfl,
    show (8 * UInt64.ofNat j + 6) = 8 * UInt64.ofNat j + UInt64.ofNat 6 from rfl,
    show (8 * UInt64.ofNat j + 7) = 8 * UInt64.ofNat j + UInt64.ofNat 7 from rfl,
    hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num), hb 4 (by norm_num),
    hb 5 (by norm_num), hb 6 (by norm_num), hb 7 (by norm_num)]
  rw [word_byte _ _ _ _ _ _ _ _ hi]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The bare-metal entry, on the words that hold a message of `n` bytes, returns the packed words of
the message's line. -/
theorem calcWords_eq (ws : Array UInt64) (n : ℕ) (hn : n < 2 ^ 64) :
    calcWords ws (UInt64.ofNat n) =
      pack (words (calcSpec ((List.range n).map (Library.Bytes.byteAt ws)))) := by
  unfold calcWords
  have hn' : (UInt64.ofNat n).toNat = n := toNat64_of_lt hn
  by_cases h : 65536 < n
  · rw [ite_eq_left_iff.mpr (fun h' => absurd (by rw [UInt64.lt_iff_toNat_lt, hn']; exact h) h')]
    have : calcSpec ((List.range n).map (Library.Bytes.byteAt ws)) = errLine 4 := by
      unfold calcSpec
      rw [ite_eq_left_iff.mpr (fun h' => absurd (by simp [msgMax]; omega) h')]
    rw [this, words_errLine4]
  · rw [ite_eq_right_iff.mpr (fun h' => absurd (by rw [UInt64.lt_iff_toNat_lt, hn'] at h'; exact h') h),
      unpack_eq, hn', calcLine_eq _ (by simp; exact hn)]

end Demos.BignumCalc
