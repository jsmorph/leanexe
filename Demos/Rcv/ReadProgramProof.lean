import Demos.Rcv.ReadProgram
import Demos.Rcv.ReadWords
import Demos.Rcv.ReadProof
import Library.Numerics.Decimal.Int64Text.Proof
import LeanExe.Dialect.Lemmas

/-!
The reader program equals the specification: `readContest b` holds the words of `readResult` of the
bytes of `b`.  The proof reads every position of the program as a natural number below the buffer's
size, and the bytes from `s` to `e` as `slice b s e`.  `findByte_splitOn` states that the position
that `findByte` finds splits the bytes from `s` to `e` as `List.splitOn` does, which ties every loop
of the program over lines, numbers, indices, and fields to the specification's split at the same
separator.
-/

namespace Demos.Rcv.ReadProgram

open LeanExe Demos.Rcv Demos.Rcv.Spec

/-! ## Bytes, positions, and slices -/

/-- The bytes of a buffer. -/
abbrev bytesOf (b : Bytes) : List UInt8 := b.data.data.toList

@[simp] theorem bytesOf_length (b : Bytes) : (bytesOf b).length = b.data.size := by
  simp only [bytesOf, Array.length_toList]
  rfl

/-- `b.get x` is the byte at `x`, or 0 past the end. -/
theorem get_eq (b : Bytes) (x : UInt64) : b.get x = ((bytesOf b).getD x.toNat 0).toUInt64 := by
  have hlen := bytesOf_length b
  unfold Bytes.get
  by_cases h : x.toNat < b.data.size
  · rw [dite_eq_left_of_eq_true (eq_true h), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hlen]; exact h), Option.getD_some]
    rfl
  · rw [dite_eq_right_of_eq_false (eq_false h), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [hlen]; omega)]
    rfl

/-- The bytes of `b` from position `s` to position `e`. -/
def slice (b : Bytes) (s e : Nat) : List UInt8 := ((bytesOf b).drop s).take (e - s)

theorem slice_length {b : Bytes} {s e : Nat} (he : e ≤ b.data.size) :
    (slice b s e).length = e - s := by
  simp [slice]
  omega

theorem slice_getElem {b : Bytes} {s e i : Nat} (he : e ≤ b.data.size)
    (hi : i < (slice b s e).length) : (slice b s e)[i] = (bytesOf b).getD (s + i) 0 := by
  rw [slice_length he] at hi
  simp only [slice, List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
  rfl

theorem slice_eq_map {b : Bytes} {s e : Nat} (he : e ≤ b.data.size) :
    slice b s e = (List.range (e - s)).map fun i => (bytesOf b).getD (s + i) 0 := by
  apply List.ext_getElem (by simp [slice_length he])
  intro i h1 h2
  rw [slice_getElem he h1]
  simp

/-- The bytes from `s` to `e` are those from `s` to `q` and those from `q` to `e`. -/
theorem slice_append {b : Bytes} {s q e : Nat} (hsq : s ≤ q) (hqe : q ≤ e) (he : e ≤ b.data.size) :
    slice b s e = slice b s q ++ slice b q e := by
  apply List.ext_getElem (by simp [slice_length he, slice_length (Nat.le_trans hqe he)]; omega)
  intro i h1 h2
  rw [slice_getElem he h1]
  by_cases hi : i < q - s
  · rw [List.getElem_append_left (by rw [slice_length (Nat.le_trans hqe he)]; exact hi),
      slice_getElem (Nat.le_trans hqe he)]
  · rw [List.getElem_append_right (by rw [slice_length (Nat.le_trans hqe he)]; omega),
      slice_getElem he]
    simp only [slice_length (Nat.le_trans hqe he)]
    congr 1
    omega

/-- The bytes from `q` to `e` start with the byte at `q` when `q < e`. -/
theorem slice_cons {b : Bytes} {q e : Nat} (hqe : q < e) (he : e ≤ b.data.size) :
    slice b q e = (bytesOf b).getD q 0 :: slice b (q + 1) e := by
  apply List.ext_getElem (by simp [slice_length he]; omega)
  intro i h1 h2
  rw [slice_getElem he h1]
  cases i with
  | zero => simp
  | succ i =>
    simp only [List.getElem_cons_succ]
    rw [slice_getElem he]
    congr 1
    omega

theorem slice_self (b : Bytes) (s : Nat) : slice b s s = [] := by simp [slice]

/-- The bytes from `s` to the end. -/
theorem slice_end {b : Bytes} (s : Nat) : slice b s b.data.size = (bytesOf b).drop s := by
  simp only [slice]
  rw [List.take_of_length_le (by simp)]

/-! ## Words and natural numbers -/

theorem ofNat_toNat_small {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

theorem toNat_add_ofNat {s : UInt64} {i : Nat} (h : s.toNat + i < 2 ^ 64) :
    (s + UInt64.ofNat i).toNat = s.toNat + i := by
  rw [UInt64.toNat_add, ofNat_toNat_small (n := i) (by omega), Nat.mod_eq_of_lt h]

theorem toNat_add_one {p e : UInt64} (h : p < e) : (p + 1).toNat = p.toNat + 1 := by
  have := UInt64.lt_iff_toNat_lt.mp h
  have := UInt64.toNat_lt e
  rw [UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  omega

theorem toNat_sub_of_le' {s e : UInt64} (h : s ≤ e) : (e - s).toNat = e.toNat - s.toNat :=
  UInt64.toNat_sub_of_le e s h

/-- The byte of `b` at a position, as a word, is below 256. -/
theorem getD_toUInt64_lt (b : Bytes) (i : Nat) : ((bytesOf b).getD i 0).toUInt64.toNat < 256 := by
  simpa using ((bytesOf b).getD i 0).toNat_lt

/-! ## Loops that test every index -/

/-- A loop that ands a test of each index is the test of every index. -/
theorem loop_and (n : UInt64) (f : UInt64 → Bool) :
    LeanExe.loop n true (fun i ok => ok && f i) =
      (List.range n.toNat).all fun i => f (UInt64.ofNat i) := by
  unfold LeanExe.loop
  generalize n.toNat = m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.fold_succ, ih, List.range_succ, List.all_append]
    simp

theorem all_range_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    (List.range n).all f = (List.range n).all g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.all_append, List.all_append, ih (fun i hi => h i (by omega))]
    simp [h n (by omega)]

/-- A loop that tests each byte from `s` to `e` is the test of every byte of the slice. -/
theorem loop_bytes (b : Bytes) (s e : UInt64) (P : UInt64 → Bool) (hse : s ≤ e)
    (he : e.toNat ≤ b.data.size) :
    LeanExe.loop (e - s) true (fun i ok => ok && P (b.get (s + i))) =
      (slice b s.toNat e.toNat).all fun x => P x.toUInt64 := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  rw [loop_and, toNat_sub_of_le' hse, slice_eq_map he, List.all_map]
  apply all_range_congr
  intro i hi
  have := UInt64.toNat_lt e
  simp only [Function.comp_apply, get_eq, toNat_add_ofNat (show s.toNat + i < 2 ^ 64 by omega)]

/-! ## Finding a byte -/

/-- `findByte` returns the first position from `p` below `e` whose byte is `c`, or `e`. -/
theorem findByte_spec (b : Bytes) (c p e : UInt64) (hpe : p ≤ e) :
    p ≤ findByte b c p e ∧ findByte b c p e ≤ e ∧
      (∀ i, p.toNat ≤ i → i < (findByte b c p e).toNat → b.get (UInt64.ofNat i) ≠ c) ∧
      (findByte b c p e < e → b.get (findByte b c p e) = c) := by
  induction h : (e - p).toNat using Nat.strong_induction_on generalizing p with
  | _ m ih =>
    rw [findByte]
    by_cases hlt : p < e
    · rw [ite_eq_left hlt]
      by_cases hc : b.get p == c
      · rw [ite_eq_left hc]
        refine ⟨UInt64.le_refl _, hpe, fun i h1 h2 => absurd h2 (by omega), fun _ => by
          simpa using hc⟩
      · rw [ite_eq_right hc]
        have h1 := toNat_add_one hlt
        have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
        have hle : p + 1 ≤ e := UInt64.le_iff_toNat_le.mpr (by omega)
        have hm : (e - (p + 1)).toNat < m := by
          rw [← h, toNat_sub_of_le' hle, toNat_sub_of_le' hpe, h1]
          omega
        obtain ⟨r1, r2, r3, r4⟩ := ih _ hm (p + 1) hle rfl
        refine ⟨UInt64.le_iff_toNat_le.mpr (by have := UInt64.le_iff_toNat_le.mp r1; omega), r2,
          ?_, r4⟩
        intro i hi1 hi2
        by_cases hip : i = p.toNat
        · subst hip
          simpa using hc
        · exact r3 i (by omega) hi2
    · rw [ite_eq_right hlt]
      have : p = e := by
        have := UInt64.le_iff_toNat_le.mp hpe
        have := UInt64.lt_iff_toNat_lt.not.mp hlt
        exact UInt64.toNat_inj.mp (by omega)
      subst this
      exact ⟨UInt64.le_refl _, UInt64.le_refl _, fun i h1 h2 => absurd h2 (by omega),
        fun h => absurd h (UInt64.lt_irrefl _)⟩

/-- The position that `findByte` finds splits the bytes from `p` to `e` at the byte `c`, as
`List.splitOn` does. -/
theorem findByte_splitOn (b : Bytes) (c : UInt8) (p e : UInt64) (hpe : p ≤ e)
    (he : e.toNat ≤ b.data.size) :
    let q := findByte b c.toUInt64 p e
    c ∉ slice b p.toNat q.toNat ∧
      (slice b p.toNat e.toNat).splitOn c =
        if q < e then slice b p.toNat q.toNat :: (slice b (q.toNat + 1) e.toNat).splitOn c
        else [slice b p.toNat e.toNat] := by
  obtain ⟨r1, r2, r3, r4⟩ := findByte_spec b c.toUInt64 p e hpe
  have r1' := UInt64.le_iff_toNat_le.mp r1
  have r2' := UInt64.le_iff_toNat_le.mp r2
  have hsz := UInt64.toNat_lt e
  have hnot : c ∉ slice b p.toNat (findByte b c.toUInt64 p e).toNat := by
    intro hm
    obtain ⟨i, hi, hx⟩ := List.getElem_of_mem hm
    have hl := slice_length (b := b) (s := p.toNat) (Nat.le_trans r2' he)
    rw [slice_getElem (Nat.le_trans r2' he)] at hx
    rw [hl] at hi
    apply r3 (p.toNat + i) (by omega) (by omega)
    rw [get_eq, ofNat_toNat_small (by omega), hx]
  refine ⟨hnot, ?_⟩
  by_cases hq : findByte b c.toUInt64 p e < e
  · rw [ite_eq_left hq]
    have hq' := UInt64.lt_iff_toNat_lt.mp hq
    have hbyte : (bytesOf b).getD (findByte b c.toUInt64 p e).toNat 0 = c := by
      have := r4 hq
      rw [get_eq] at this
      exact UInt8.toUInt64_inj.mp this
    rw [slice_append r1' r2' he, slice_cons hq' he, hbyte]
    exact List.splitOn_append_cons_self_of_not_mem hnot _
  · rw [ite_eq_right hq]
    have : findByte b c.toUInt64 p e = e := UInt64.le_antisymm r2 (UInt64.not_lt.mp hq)
    rw [this] at hnot
    exact List.splitOn_eq_singleton hnot

/-! ## Texts of the format -/

/-- Bytes 0 to `n - 1` of `w`, least significant first, as words. -/
def wordBytes (w : UInt64) (n : Nat) : List UInt64 :=
  (List.range n).map fun i => wordByte w (UInt64.ofNat i)

theorem wordBytes_length (w : UInt64) (n : Nat) : (wordBytes w n).length = n := by
  simp [wordBytes]

theorem all_beq_range {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (n : Nat) (f g : Nat → α) :
    (List.range n).all (fun i => f i == g i) =
      decide ((List.range n).map f = (List.range n).map g) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.map_inj_left, List.all_eq_true]
  simp

/-- `matchWord` compares the bytes from `p` with bytes 0 to `len - 1` of `w`. -/
theorem matchWord_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (p w len : UInt64)
    (hp : p.toNat + len.toNat ≤ b.data.size) :
    matchWord b p w len =
      decide ((slice b p.toNat (p.toNat + len.toNat)).map UInt8.toUInt64 =
        wordBytes w len.toNat) := by
  rw [matchWord, loop_and, slice_eq_map hp, List.map_map, wordBytes, Nat.add_sub_cancel_left]
  have h2 : (List.range len.toNat).all
      (fun i => b.get (p + UInt64.ofNat i) == wordByte w (UInt64.ofNat i)) =
      (List.range len.toNat).all (fun i =>
        (UInt8.toUInt64 ∘ fun i => (bytesOf b).getD (p.toNat + i) 0) i ==
          wordByte w (UInt64.ofNat i)) := by
    apply all_range_congr
    intro i hi
    rw [get_eq, toNat_add_ofNat (by omega)]
    rfl
  rw [h2, all_beq_range]

theorem map_toUInt64_inj {a c : List UInt8} : a.map UInt8.toUInt64 = c.map UInt8.toUInt64 ↔ a = c :=
  ⟨map_toUInt64_injective, fun h => h ▸ rfl⟩

/-- `hasPrefix` tests that the bytes from `s` to `e` start with the text `T` of the two words. -/
theorem hasPrefix_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (s e w1 l1 w2 l2 : UInt64)
    (hl1 : l1.toNat ≤ 8) (hl2 : l2.toNat ≤ 8) (T : List UInt8)
    (hT : T.map UInt8.toUInt64 = wordBytes w1 l1.toNat ++ wordBytes w2 l2.toNat)
    (hse : s ≤ e) (he : e.toNat ≤ b.data.size) :
    hasPrefix b s e w1 l1 w2 l2 = T.isPrefixOf (slice b s.toNat e.toNat) := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  have hTlen : T.length = l1.toNat + l2.toNat := by
    have := congrArg List.length hT
    simpa [wordBytes_length] using this
  have hsum : (l1 + l2).toNat = l1.toNat + l2.toNat := by
    rw [UInt64.toNat_add]; omega
  rw [hasPrefix, Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take]
  by_cases hlen : l1 + l2 ≤ e - s
  · have hlen' : l1.toNat + l2.toNat ≤ e.toNat - s.toNat := by
      rw [← hsum, ← toNat_sub_of_le' hse]; exact UInt64.le_iff_toNat_le.mp hlen
    rw [ite_eq_left hlen]
    have hs1 : (s + l1).toNat = s.toNat + l1.toNat := by
      rw [UInt64.toNat_add]; omega
    rw [matchWord_eq b hb s w1 l1 (by omega), matchWord_eq b hb (s + l1) w2 l2 (by omega), hs1]
    have htake : (slice b s.toNat e.toNat).take T.length =
        slice b s.toNat (s.toNat + l1.toNat) ++
          slice b (s.toNat + l1.toNat) (s.toNat + l1.toNat + l2.toNat) := by
      rw [← slice_append (by omega) (by omega) (by omega), hTlen]
      simp only [slice, List.take_take]
      congr 1
      omega
    rw [htake]
    have hsplit : T = T.take l1.toNat ++ T.drop l1.toNat := (List.take_append_drop _ _).symm
    have hT1 : (T.take l1.toNat).map UInt8.toUInt64 = wordBytes w1 l1.toNat := by
      rw [List.map_take, hT, List.take_append_of_le_length (by simp [wordBytes_length]),
        List.take_of_length_le (by simp [wordBytes_length])]
    have hT2 : (T.drop l1.toNat).map UInt8.toUInt64 = wordBytes w2 l2.toNat := by
      rw [List.map_drop, hT, List.drop_append_of_le_length (by simp [wordBytes_length]),
        List.drop_of_length_le (by simp [wordBytes_length]), List.nil_append]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [← hT1, ← hT2, map_toUInt64_inj, map_toUInt64_inj]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1, h2, List.take_append_drop]
    · intro h
      have hl : (slice b s.toNat (s.toNat + l1.toNat)).length = (T.take l1.toNat).length := by
        rw [slice_length (by omega)]; simp [hTlen]
      rw [hsplit] at h
      exact List.append_inj h.symm hl
  · rw [ite_eq_right hlen]
    simp only [Bool.false_eq_true, false_iff]
    intro h
    have hlen' : e.toNat - s.toNat < l1.toNat + l2.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlen)
      rw [hsum, toNat_sub_of_le' hse] at this; exact this
    have := congrArg List.length h
    simp [slice_length he, hTlen] at this
    omega

/-! ## Loops over the bytes of a slice -/

/-- A loop over the positions from `s` to `e` whose step reads the byte at its position is a fold
over the slice. -/
theorem loop_foldl_bytes {α : Type} (b : Bytes) (hb : b.data.size < 2 ^ 64) (s e : UInt64)
    (hse : s ≤ e) (he : e.toNat ≤ b.data.size) (init : α) (g : UInt64 → α → α) :
    LeanExe.loop (e - s) init (fun i st => g (b.get (s + i)) st) =
      (slice b s.toNat e.toNat).foldl (fun st x => g x.toUInt64 st) init := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  rw [slice_eq_map he, LeanExe.loop, toNat_sub_of_le' hse]
  have key : ∀ m, m ≤ e.toNat - s.toNat →
      Nat.fold m (fun i _ st => g (b.get (s + UInt64.ofNat i)) st) init =
        ((List.range m).map fun i => (bytesOf b).getD (s.toNat + i) 0).foldl
          (fun st x => g x.toUInt64 st) init := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [Nat.fold_succ, ih (by omega), List.range_succ, List.map_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [get_eq, toNat_add_ofNat (by omega)]
  exact key _ le_rfl

/-! ## Numbers -/

/-- The quotient of `2 ^ 64 - 1` by 10: ten times a word plus a digit stays below `2 ^ 64` exactly
when the word is below it, or equal to it with the digit at most 5. -/
theorem no_overflow (v d : UInt64) (hd : d.toNat < 10) :
    (decide (v < 1844674407370955161) || (v == 1844674407370955161 && decide (d ≤ 5))) = true ↔
      10 * v.toNat + d.toNat < 2 ^ 64 := by
  have hM : (1844674407370955161 : UInt64).toNat = 1844674407370955161 := rfl
  have h5 : (5 : UInt64).toNat = 5 := rfl
  rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, hM, h5]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · omega
    · rw [h, hM]; omega
  · intro h
    by_cases hv : v.toNat < 1844674407370955161
    · exact Or.inl hv
    · exact Or.inr ⟨UInt64.toNat_inj.mp (by rw [hM]; omega), by omega⟩

/-- The step of `readNumber`'s loop on the byte `x`. -/
def numberStep (x : UInt64) (st : Bool × UInt64) : Bool × UInt64 :=
  (st.1 && x - 48 < 10 &&
      (st.2 < 1844674407370955161 || (st.2 == 1844674407370955161 && x - 48 ≤ 5)),
    10 * st.2 + (x - 48))

theorem digit_sub (x : UInt8) : decide (x.toUInt64 - 48 < 10) = isDigit x := by
  have hx := x.toNat_lt
  have hxu : x.toUInt64.toNat = x.toNat := UInt8.toNat_toUInt64 x
  have h48 : (0x30 : UInt8).toNat = 48 := rfl
  have h57 : (0x39 : UInt8).toNat = 57 := rfl
  have h10 : (10 : UInt64).toNat = 10 := rfl
  have h48' : (48 : UInt64).toNat = 48 := rfl
  unfold isDigit
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff,
    decide_eq_true_iff, UInt8.le_iff_toNat_le, UInt8.le_iff_toNat_le, UInt64.lt_iff_toNat_lt,
    h48, h57, h10, UInt64.toNat_sub, hxu, h48']
  omega

theorem digit_value (x : UInt8) (h : isDigit x = true) :
    (x.toUInt64 - 48).toNat = x.toNat - 48 := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
    UInt8.reduceToNat] at h
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using h.1))]
  simp

theorem digitsValue_snoc' (L : List UInt8) (x : UInt8) :
    digitsValue (L ++ [x]) = 10 * digitsValue L + (x.toNat - 0x30) := by
  simp [digitsValue, List.foldl_append]

/-- The fold of `numberStep` holds `true` exactly when every byte is a digit and the value is
below `2 ^ 64`, and then the value. -/
theorem numberStep_fold (L : List UInt8) :
    let r := L.foldl (fun st x => numberStep x.toUInt64 st) (true, 0)
    (r.1 = true ↔ L.all isDigit = true ∧ digitsValue L < 2 ^ 64) ∧
      (r.1 = true → r.2.toNat = digitsValue L) := by
  induction L using List.reverseRecOn with
  | nil => simp [digitsValue]
  | append_singleton L x ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.all_append,
      List.all_cons, List.all_nil, Bool.and_true, digitsValue_snoc'] at ih ⊢
    obtain ⟨ih1, ih2⟩ := ih
    generalize L.foldl (fun st x => numberStep x.toUInt64 st) (true, 0) = r at ih1 ih2
    obtain ⟨ok, v⟩ := r
    simp only at ih1 ih2
    simp only [numberStep, digit_sub]
    cases ok with
    | false =>
      simp only [Bool.false_and, Bool.false_eq_true, false_iff, false_implies, and_true]
      intro ⟨hall, hlt⟩
      simp only [Bool.and_eq_true] at hall
      exact absurd (ih1.mpr ⟨hall.1, by omega⟩) (by simp)
    | true =>
      have ⟨hall, hlt⟩ := ih1.mp rfl
      have hv := ih2 rfl
      by_cases hx : isDigit x = true
      · have hd := digit_value x hx
        have hd10 : (x.toUInt64 - 48).toNat < 10 := by
          have := x.toNat_lt
          simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
            UInt8.reduceToNat] at hx
          omega
        rw [hx]
        simp only [Bool.true_and]
        rw [no_overflow v _ hd10, hv, hd]
        refine ⟨by simp [hall], fun h => ?_⟩
        rw [UInt64.toNat_add, UInt64.toNat_mul, hv, hd]
        simp only [UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt (by omega : 10 * digitsValue L < 2 ^ 64)]
        omega
      · simp only [Bool.not_eq_true] at hx
        simp [hx]

/-- What `readNumber` returns on the bytes `L`: their value with `true` when they are a number
below `2 ^ 64`, and `(false, 0)` otherwise. -/
def numberResult (L : List UInt8) : Bool × UInt64 :=
  match number L with
  | some v => if v < 2 ^ 64 then (true, UInt64.ofNat v) else (false, 0)
  | none => (false, 0)

/-- A number of more than 20 digits is at least `10 ^ 20`, above every word. -/
theorem number_long {L : List UInt8} {v : Nat} (h : number L = some v) (hl : 20 < L.length) :
    2 ^ 64 ≤ v := by
  have hd := decimal_of_number h
  have hlen : (Library.Numerics.Decimal.Int64Text.digitWords v).length = L.length := by
    rw [digitWords_eq, List.length_map, hd]
  have := (Library.Numerics.Decimal.Int64Text.digitWords_length_le_iff v 20 (by decide)).not.mp
    (by omega)
  omega

theorem readNumber_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (s e : UInt64) (hse : s ≤ e)
    (he : e.toNat ≤ b.data.size) :
    readNumber b s e = numberResult (slice b s.toNat e.toNat) := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  have hlen := slice_length (b := b) (s := s.toNat) he
  have hesub := toNat_sub_of_le' hse
  rw [readNumber]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq] at hc
    obtain ⟨⟨hlt, h20⟩, hlead⟩ := hc
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have h20' : e.toNat - s.toNat ≤ 20 := by
      rw [← hesub]; exact UInt64.le_iff_toNat_le.mp h20
    have hloop := loop_foldl_bytes b hb s e hse he (true, (0 : UInt64)) numberStep
    simp only [numberStep] at hloop
    simp only []
    rw [hloop]
    obtain ⟨hr1, hr2⟩ := numberStep_fold (slice b s.toNat e.toNat)
    simp only [numberStep] at hr1 hr2
    obtain ⟨x, xs, hx⟩ : ∃ x xs, slice b s.toNat e.toNat = x :: xs := by
      cases h : slice b s.toNat e.toNat with
      | nil => rw [h] at hlen; simp at hlen; omega
      | cons x xs => exact ⟨x, xs, rfl⟩
    have hxs : x ≠ 0x30 ∨ xs = [] := by
      rcases hlead with h | h
      · left
        intro hx0
        apply h
        have := slice_cons (b := b) hlt' he
        rw [hx] at this
        have hx' : x = (bytesOf b).getD s.toNat 0 := (List.cons.inj this).1
        rw [get_eq, ← hx', hx0]
        rfl
      · right
        have : (e - s).toNat = 1 := by rw [h]; rfl
        rw [hesub] at this
        rw [hx] at hlen
        simp at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
    have hnum : number (slice b s.toNat e.toNat) =
        if (slice b s.toNat e.toNat).all isDigit then some (digitsValue (slice b s.toNat e.toNat))
        else none := by
      rw [hx, number]
      have : (x != (0x30 : UInt8) || xs.isEmpty) = true := by
        rcases hxs with h | h
        · simp [h]
        · simp [h]
      simp [this]
    rw [numberResult, hnum]
    generalize hr : List.foldl _ (true, (0 : UInt64)) (slice b s.toNat e.toNat) = r at hr1 hr2
    obtain ⟨ok, v⟩ := r
    cases ok with
    | true =>
      obtain ⟨hall, hval⟩ := hr1.mp rfl
      rw [ite_eq_left (show (true, v).1 = true from rfl), ite_eq_left hall]
      simp only []
      rw [ite_eq_left hval]
      have hv := hr2 rfl
      simp only at hv
      rw [← hv, UInt64.ofNat_toNat]
    | false =>
      rw [ite_eq_right (show ¬ (false, v).1 = true by simp)]
      by_cases hall : (slice b s.toNat e.toNat).all isDigit = true
      · rw [ite_eq_left hall]
        simp only []
        rw [ite_eq_right]
        intro hval
        exact absurd (hr1.mpr ⟨hall, hval⟩) (by simp)
      · rw [ite_eq_right hall]
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq, not_and_or, not_or, not_not] at hc
    rw [numberResult]
    split
    · rename_i v hv
      rcases hc with (hc | hc) | ⟨h0, h1⟩
      · have : e.toNat = s.toNat := by
          have := UInt64.lt_iff_toNat_lt.not.mp hc; omega
        rw [this, slice_self] at hv
        simp [number] at hv
      · have h20 : 20 < e.toNat - s.toNat := by
          rw [← hesub]; exact UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hc)
        rw [ite_eq_right (by have := number_long hv (by omega); omega)]
      · exfalso
        have hlt : s.toNat < e.toNat := by
          by_contra hcon
          have : e.toNat = s.toNat := by omega
          rw [this, slice_self] at hv
          simp [number] at hv
        have hne1 : e.toNat - s.toNat ≠ 1 := by
          intro h
          apply h1
          apply UInt64.toNat_inj.mp
          rw [hesub, h]
          rfl
        have hcons := slice_cons (b := b) hlt he
        have hx0 : (bytesOf b).getD s.toNat 0 = 0x30 := by
          rw [get_eq] at h0
          exact UInt8.toUInt64_inj.mp h0
        rw [hcons, hx0] at hv
        have hrest : slice b (s.toNat + 1) e.toNat ≠ [] := by
          intro h
          have := slice_length (b := b) (s := s.toNat + 1) he
          rw [h] at this
          simp at this
          omega
        simp [number, List.isEmpty_iff, hrest] at hv
    · rfl

/-- T2(d): the number reader over the whole of a buffer returns `(true, v)` exactly on the decimal
form of `v`, so it returns `v` on the printer's text of `v`, and every text that it accepts is the
printer's text of the value that it returns. -/
theorem readNumber_whole (b : Bytes) (hb : b.data.size < 2 ^ 64) (v : UInt64) :
    readNumber b 0 b.size = (true, v) ↔ bytesOf b = decimal v.toNat := by
  have hsize : b.size.toNat = b.data.size := Bytes.size_toNat b hb
  rw [readNumber_eq b hb 0 b.size (UInt64.le_iff_toNat_le.mpr (by simp)) (by rw [hsize]),
    hsize, UInt64.toNat_zero, slice_end, List.drop_zero, numberResult]
  constructor
  · intro h
    split at h
    · rename_i w hw
      split at h
      · rename_i hlt
        simp only [Prod.mk.injEq, true_and] at h
        rw [← decimal_of_number hw, ← h, ofNat_toNat_small hlt]
      · simp at h
    · simp at h
  · intro h
    rw [h, number_decimal]
    simp [v.toNat_lt]

/-! ## Bytes of identifiers and names -/

theorem identByte_table : ∀ n < 256, identByteW (UInt64.ofNat n) = identByte (UInt8.ofNat n) := by
  decide +kernel

theorem nameByte_table : ∀ n < 256, nameByteW (UInt64.ofNat n) =
    (((0x20 : UInt8) ≤ UInt8.ofNat n && UInt8.ofNat n ≤ (0x7E : UInt8)) ||
      (0x80 : UInt8) ≤ UInt8.ofNat n) := by
  decide +kernel

theorem toUInt64_eq_ofNat (x : UInt8) : x.toUInt64 = UInt64.ofNat x.toNat := by
  apply UInt64.toNat_inj.mp
  rw [UInt8.toNat_toUInt64, ofNat_toNat_small (by have := x.toNat_lt; omega)]

theorem identByteW_eq (x : UInt8) : identByteW x.toUInt64 = identByte x := by
  have := identByte_table x.toNat x.toNat_lt
  rwa [← toUInt64_eq_ofNat, UInt8.ofNat_toNat] at this

theorem nameByteW_eq (x : UInt8) :
    nameByteW x.toUInt64 = (((0x20 : UInt8) ≤ x && x ≤ (0x7E : UInt8)) || (0x80 : UInt8) ≤ x) := by
  have := nameByte_table x.toNat x.toNat_lt
  rwa [← toUInt64_eq_ofNat, UInt8.ofNat_toNat] at this

/-- The program's guard of a length from 1 to `m` on the positions `s ≤ e`. -/
theorem guard_length {s e : UInt64} (hse : s ≤ e) (m : UInt64) :
    (decide (s < e) && decide (e - s ≤ m)) = (decide (1 ≤ e.toNat - s.toNat) &&
      decide (e.toNat - s.toNat ≤ m.toNat)) := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  have h1 : decide (s < e) = decide (1 ≤ e.toNat - s.toNat) := by
    rw [decide_eq_decide, UInt64.lt_iff_toNat_lt]
    omega
  have h2 : decide (e - s ≤ m) = decide (e.toNat - s.toNat ≤ m.toNat) := by
    rw [decide_eq_decide, UInt64.le_iff_toNat_le, toNat_sub_of_le' hse]
  rw [h1, h2]

theorem isIdent_eq (b : Bytes) (s e : UInt64) (hse : s ≤ e) (he : e.toNat ≤ b.data.size) :
    isIdent b s e = identOk (slice b s.toNat e.toNat) := by
  rw [isIdent, identOk, slice_length he, guard_length hse]
  have h64 : (64 : UInt64).toNat = 64 := rfl
  rw [h64]
  split
  · rename_i hc
    rw [loop_bytes b s e identByteW hse he, hc, Bool.true_and]
    simp only [identByteW_eq]
  · rename_i hc
    rw [Bool.eq_false_iff.mpr hc, Bool.false_and]

theorem isName_eq (b : Bytes) (s e : UInt64) (hse : s ≤ e) (he : e.toNat ≤ b.data.size) :
    isName b s e = nameOk (slice b s.toNat e.toNat) := by
  rw [isName, nameOk, slice_length he, guard_length hse]
  have h255 : (255 : UInt64).toNat = 255 := rfl
  rw [h255]
  split
  · rename_i hc
    rw [loop_bytes b s e nameByteW hse he, hc, Bool.true_and]
    simp only [nameByteW_eq]
  · rename_i hc
    rw [Bool.eq_false_iff.mpr hc, Bool.false_and]

/-! ## Texts of a given length -/

theorem beq_length {s e : UInt64} (hse : s ≤ e) (m : UInt64) :
    (e - s == m) = decide (e.toNat - s.toNat = m.toNat) := by
  rw [← toNat_sub_of_le' hse, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, UInt64.toNat_inj.mp⟩

/-- The bytes from `s` to `e` are the text `T` of one word, when they have its length. -/
theorem matchWord_text (b : Bytes) (hb : b.data.size < 2 ^ 64) (s e w len : UInt64)
    (T : List UInt8) (hT : T.map UInt8.toUInt64 = wordBytes w len.toNat)
    (hlen : e.toNat - s.toNat = len.toNat) (hse : s ≤ e) (he : e.toNat ≤ b.data.size) :
    matchWord b s w len = decide (slice b s.toNat e.toNat = T) := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  rw [matchWord_eq b hb s w len (by omega), show s.toNat + len.toNat = e.toNat by omega, ← hT]
  exact decide_eq_decide.mpr map_toUInt64_inj

/-- The bytes from `s` to `e` are the text `T` of two words, when they have its length. -/
theorem hasPrefix_text (b : Bytes) (hb : b.data.size < 2 ^ 64) (s e w1 l1 w2 l2 : UInt64)
    (hl1 : l1.toNat ≤ 8) (hl2 : l2.toNat ≤ 8) (T : List UInt8)
    (hT : T.map UInt8.toUInt64 = wordBytes w1 l1.toNat ++ wordBytes w2 l2.toNat)
    (hlen : e.toNat - s.toNat = T.length) (hse : s ≤ e) (he : e.toNat ≤ b.data.size) :
    hasPrefix b s e w1 l1 w2 l2 = decide (slice b s.toNat e.toNat = T) := by
  rw [hasPrefix_eq b hb s e w1 l1 w2 l2 hl1 hl2 T hT hse he, Bool.eq_iff_iff,
    List.isPrefixOf_iff_prefix, decide_eq_true_iff]
  constructor
  · intro h
    exact (h.eq_of_length (by rw [slice_length he]; omega)).symm
  · intro h
    rw [h]

/-! ## Kind words -/

theorem decide_length_slice {b : Bytes} {s e : UInt64} (he : e.toNat ≤ b.data.size) {T : List UInt8}
    (hl : ¬ e.toNat - s.toNat = T.length) : decide (slice b s.toNat e.toNat = T) = false := by
  rw [decide_eq_false_iff_not]
  intro h
  apply hl
  rw [← slice_length he, h]

theorem kindCode_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (s e : UInt64) (hse : s ≤ e)
    (he : e.toNat ≤ b.data.size) :
    kindCode b s e = match parseKind (slice b s.toNat e.toNat) with
      | some k => UInt64.ofNat (Spec.kindCode k)
      | none => 4 := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  have h1 : (e - s == 6 && matchWord b s 0x64657473696c 6) =
      decide (slice b s.toNat e.toNat = ascii "listed") := by
    rw [beq_length hse, show (6 : UInt64).toNat = 6 from rfl]
    by_cases hl : e.toNat - s.toNat = 6
    · rw [decide_eq_true hl, Bool.true_and,
        matchWord_text b hb s e _ 6 (ascii "listed") (by decide) (by rw [hl]; rfl) hse he]
    · rw [decide_eq_false hl, Bool.false_and,
        decide_length_slice he (by rw [show (ascii "listed").length = 6 from rfl]; exact hl)]
  have h2 : (e - s == 13 && hasPrefix b s e 0x72772d64656d616e 8 0x6e69657469 5) =
      decide (slice b s.toNat e.toNat = ascii "named-writein") := by
    rw [beq_length hse, show (13 : UInt64).toNat = 13 from rfl]
    by_cases hl : e.toNat - s.toNat = 13
    · rw [decide_eq_true hl, Bool.true_and,
        hasPrefix_text b hb s e _ 8 _ 5 (by decide) (by decide) (ascii "named-writein") (by decide)
          (by rw [hl]; rfl) hse he]
    · rw [decide_eq_false hl, Bool.false_and,
        decide_length_slice he
          (by rw [show (ascii "named-writein").length = 13 from rfl]; exact hl)]
  have h3 : (e - s == 17 && hasPrefix b s e 0x7461676572676761 8 0x6965746972772d65 8 &&
      matchWord b (s + 16) 0x6e 1) =
      decide (slice b s.toNat e.toNat = ascii "aggregate-writein") := by
    rw [beq_length hse, show (17 : UInt64).toNat = 17 from rfl]
    by_cases hl : e.toNat - s.toNat = 17
    · rw [decide_eq_true hl, Bool.true_and]
      have hs16 : (s + 16).toNat = s.toNat + 16 := by
        rw [UInt64.toNat_add, show (16 : UInt64).toNat = 16 from rfl]; omega
      rw [hasPrefix_eq b hb s e _ 8 _ 8 (by decide) (by decide) (ascii "aggregate-writei")
          (by decide) hse he,
        matchWord_eq b hb (s + 16) _ 1 (by rw [hs16, show (1 : UInt64).toNat = 1 from rfl]; omega),
        hs16, show (1 : UInt64).toNat = 1 from rfl]
      have hsplit := slice_append (b := b) (s := s.toNat) (q := s.toNat + 16) (e := e.toNat)
        (by omega) (by omega) he
      have hT : ascii "aggregate-writein" = ascii "aggregate-writei" ++ ascii "n" := rfl
      rw [show s.toNat + 16 + 1 = e.toNat by omega, hsplit, hT,
        Bool.eq_iff_iff, Bool.and_eq_true, List.isPrefixOf_iff_prefix, decide_eq_true_iff,
        decide_eq_true_iff, show wordBytes 0x6e 1 = (ascii "n").map UInt8.toUInt64 by decide,
        map_toUInt64_inj]
      have hl16 : (slice b s.toNat (s.toNat + 16)).length = (ascii "aggregate-writei").length := by
        rw [slice_length (by omega), Nat.add_sub_cancel_left]; rfl
      constructor
      · rintro ⟨hp, hn⟩
        have : ascii "aggregate-writei" = slice b s.toNat (s.toNat + 16) :=
          (List.prefix_iff_eq_take.mp hp).trans (by rw [← hl16, List.take_left])
        rw [← this, hn]
      · intro h
        obtain ⟨h1', h2'⟩ := List.append_inj h hl16
        rw [h1', h2']
        exact ⟨List.prefix_append _ _, rfl⟩
    · rw [decide_eq_false hl, Bool.false_and, Bool.false_and,
        decide_length_slice he
          (by rw [show (ascii "aggregate-writein").length = 17 from rfl]; exact hl)]
  have h4 : (e - s == 8 && matchWord b s 0x646564756c637865 8) =
      decide (slice b s.toNat e.toNat = ascii "excluded") := by
    rw [beq_length hse, show (8 : UInt64).toNat = 8 from rfl]
    by_cases hl : e.toNat - s.toNat = 8
    · rw [decide_eq_true hl, Bool.true_and,
        matchWord_text b hb s e _ 8 (ascii "excluded") (by decide) (by rw [hl]; rfl) hse he]
    · rw [decide_eq_false hl, Bool.false_and,
        decide_length_slice he (by rw [show (ascii "excluded").length = 8 from rfl]; exact hl)]
  rw [kindCode, h1, h2, h3, h4, parseKind]
  split_ifs <;> first | rfl | simp_all

/-! ## Separators -/

/-- The bytes from `p` to `e` are those before the position `q` that `findByte` finds, which hold
no byte `c`, then `c` and the bytes after it when `q < e`. -/
theorem findByte_slice (b : Bytes) (c : UInt64) (c8 : UInt8) (hc : c8.toUInt64 = c) (p e : UInt64)
    (hpe : p ≤ e) (he : e.toNat ≤ b.data.size) :
    p ≤ findByte b c p e ∧ findByte b c p e ≤ e ∧ c8 ∉ slice b p.toNat (findByte b c p e).toNat ∧
      slice b p.toNat e.toNat = slice b p.toNat (findByte b c p e).toNat ++
        (if findByte b c p e < e then c8 :: slice b ((findByte b c p e).toNat + 1) e.toNat
          else []) := by
  subst hc
  obtain ⟨r1, r2, r3, r4⟩ := findByte_spec b c8.toUInt64 p e hpe
  have r1' := UInt64.le_iff_toNat_le.mp r1
  have r2' := UInt64.le_iff_toNat_le.mp r2
  have hsz := UInt64.toNat_lt e
  have hnot : c8 ∉ slice b p.toNat (findByte b c8.toUInt64 p e).toNat := by
    intro hm
    obtain ⟨i, hi, hx⟩ := List.getElem_of_mem hm
    have hl := slice_length (b := b) (s := p.toNat) (Nat.le_trans r2' he)
    rw [slice_getElem (Nat.le_trans r2' he)] at hx
    rw [hl] at hi
    apply r3 (p.toNat + i) (by omega) (by omega)
    rw [get_eq, ofNat_toNat_small (by omega), hx]
  refine ⟨r1, r2, hnot, ?_⟩
  rw [slice_append r1' r2' he]
  congr 1
  by_cases hq : findByte b c8.toUInt64 p e < e
  · rw [ite_eq_left hq]
    have hq' := UInt64.lt_iff_toNat_lt.mp hq
    have hbyte : (bytesOf b).getD (findByte b c8.toUInt64 p e).toNat 0 = c8 := by
      have := r4 hq
      rw [get_eq] at this
      exact UInt8.toUInt64_inj.mp this
    rw [slice_cons hq' he, hbyte]
  · rw [ite_eq_right hq]
    have : findByte b c8.toUInt64 p e = e := UInt64.le_antisymm r2 (UInt64.not_lt.mp hq)
    rw [this, slice_self]

theorem span_no_sep {s : UInt8} {l : List UInt8} (h : s ∉ l) : l.span (· != s) = (l, []) := by
  rw [List.span_eq_takeWhile_dropWhile]
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : (x != s) = true := by
      have : x ≠ s := fun e => h (e ▸ List.mem_cons_self)
      simpa using this
    have := ih (fun hm => h (List.mem_cons_of_mem x hm))
    simp only [Prod.mk.injEq] at this
    simp [hx, this.1, this.2]

/-- `List.span` at the separator `c` takes the bytes before the position that `findByte` finds. -/
theorem findByte_span (b : Bytes) (c : UInt64) (c8 : UInt8) (hc : c8.toUInt64 = c) (p e : UInt64)
    (hpe : p ≤ e) (he : e.toNat ≤ b.data.size) :
    (slice b p.toNat e.toNat).span (· != c8) =
      (slice b p.toNat (findByte b c p e).toNat,
        if findByte b c p e < e then c8 :: slice b ((findByte b c p e).toNat + 1) e.toNat
        else []) := by
  obtain ⟨_, _, hnot, hsplit⟩ := findByte_slice b c c8 hc p e hpe he
  rw [hsplit]
  split
  · exact span_sep hnot
  · rw [List.append_nil]
    exact span_no_sep hnot

/-- `List.splitOn` at the separator `c` takes the bytes before the position that `findByte` finds
first. -/
theorem findByte_split (b : Bytes) (c : UInt64) (c8 : UInt8) (hc : c8.toUInt64 = c) (p e : UInt64)
    (hpe : p ≤ e) (he : e.toNat ≤ b.data.size) :
    (slice b p.toNat e.toNat).splitOn c8 =
      slice b p.toNat (findByte b c p e).toNat ::
        if findByte b c p e < e then (slice b ((findByte b c p e).toNat + 1) e.toNat).splitOn c8
        else [] := by
  obtain ⟨_, _, hnot, hsplit⟩ := findByte_slice b c c8 hc p e hpe he
  rw [hsplit]
  split
  · exact List.splitOn_append_cons_self_of_not_mem hnot _
  · rw [List.append_nil]
    exact List.splitOn_eq_singleton hnot

/-- The bytes after a prefix of `k` bytes. -/
theorem slice_drop {b : Bytes} {s e : Nat} (k : Nat) :
    (slice b s e).drop k = slice b (s + k) e := by
  simp only [slice, List.drop_take, List.drop_drop]
  congr 1
  omega

theorem after_slice {b : Bytes} {s e : Nat} (T : List UInt8) :
    after T (slice b s e) =
      if T.isPrefixOf (slice b s e) then some (slice b (s + T.length) e) else none := by
  simp only [after, slice_drop]

theorem prefix_length {b : Bytes} {s e : Nat} (he : e ≤ b.data.size) {T : List UInt8}
    (h : T.isPrefixOf (slice b s e) = true) : T.length ≤ e - s := by
  have := (List.isPrefixOf_iff_prefix.mp h).length_le
  rwa [slice_length he] at this

/-! ## Candidate lines -/

theorem toNat_add_small {s e : UInt64} {k : Nat} (_hk : k < 2 ^ 64) (h : s.toNat + k ≤ e.toNat) :
    (s + UInt64.ofNat k).toNat = s.toNat + k := by
  have := UInt64.toNat_lt e
  exact toNat_add_ofNat (by omega)

theorem numberResult_eq_true {L : List UInt8} {i : UInt64} :
    ((numberResult L).1 && (numberResult L).2 == i) = true ↔ number L = some i.toNat := by
  unfold numberResult
  split
  · rename_i v hv
    split
    · rename_i hlt
      simp only [Bool.true_and, beq_iff_eq, hv, Option.some.injEq]
      constructor
      · intro h; rw [← h, ofNat_toNat_small hlt]
      · intro h; rw [h, UInt64.ofNat_toNat]
    · rename_i hlt
      simp only [Bool.false_and, Bool.false_eq_true, hv, Option.some.injEq, false_iff]
      intro h
      have := i.toNat_lt
      omega
  · rename_i hv
    simp [hv]

theorem candidateCode_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (i s e : UInt64) (hse : s ≤ e)
    (he : e.toNat ≤ b.data.size) :
    candidateCode b i s e = match parseCandidate i.toNat (slice b s.toNat e.toNat) with
      | some x => UInt64.ofNat (Spec.kindCode x.kind)
      | none => 4 := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  unfold candidateCode parseCandidate
  rw [hasPrefix_eq b hb s e _ 8 _ 2 (by decide) (by decide) (ascii "candidate ") (by decide) hse he,
    after_slice]
  by_cases hp : (ascii "candidate ").isPrefixOf (slice b s.toNat e.toNat) = true
  swap
  · rw [ite_eq_right hp, ite_eq_right hp]
  rw [ite_eq_left hp, ite_eq_left hp]
  have hlen : 10 ≤ e.toNat - s.toNat := prefix_length he hp
  have hs10 : (s + 10).toNat = s.toNat + 10 :=
    toNat_add_small (e := e) (k := 10) (by decide) (by omega)
  have hle10 : s + 10 ≤ e := UInt64.le_iff_toNat_le.mpr (by omega)
  simp only []
  rw [show (ascii "candidate ").length = 10 from rfl, ← hs10,
    findByte_span b 32 sp rfl (s + 10) e hle10 he]
  obtain ⟨q1a, q1b, -, -⟩ := findByte_slice b 32 sp rfl (s + 10) e hle10 he
  by_cases hq1 : findByte b 32 (s + 10) e < e
  swap
  · rw [ite_eq_right hq1, ite_eq_right hq1]
  rw [ite_eq_left hq1, ite_eq_left hq1]
  simp only []
  have hq1' := UInt64.lt_iff_toNat_lt.mp hq1
  have hq1n : (findByte b 32 (s + 10) e + 1).toNat = (findByte b 32 (s + 10) e).toNat + 1 :=
    toNat_add_one hq1
  have hle1 : findByte b 32 (s + 10) e + 1 ≤ e := UInt64.le_iff_toNat_le.mpr (by omega)
  rw [← hq1n, findByte_span b 32 sp rfl _ e hle1 he]
  obtain ⟨q2a, q2b, -, -⟩ := findByte_slice b 32 sp rfl _ e hle1 he
  by_cases hq2 : findByte b 32 (findByte b 32 (s + 10) e + 1) e < e
  swap
  · rw [ite_eq_right hq2, ite_eq_right hq2]
  rw [ite_eq_left hq2, ite_eq_left hq2]
  simp only []
  have hq2' := UInt64.lt_iff_toNat_lt.mp hq2
  have hq2n := toNat_add_one hq2
  rw [← hq2n, readNumber_eq b hb _ _ q1a (UInt64.le_iff_toNat_le.mp q1b |>.trans he),
    isName_eq b _ e (UInt64.le_iff_toNat_le.mpr (by omega)) he,
    kindCode_eq b hb _ _ q2a (UInt64.le_iff_toNat_le.mp q2b |>.trans he)]
  by_cases hc : (number (slice b (s + 10).toNat (findByte b 32 (s + 10) e).toNat) = some i.toNat ∧
      nameOk (slice b (findByte b 32 (findByte b 32 (s + 10) e + 1) e + 1).toNat e.toNat) = true)
  · rw [ite_eq_left hc]
    have h1 : ((numberResult (slice b (s + 10).toNat (findByte b 32 (s + 10) e).toNat)).1 &&
        (numberResult (slice b (s + 10).toNat (findByte b 32 (s + 10) e).toNat)).2 == i) = true :=
      numberResult_eq_true.mpr hc.1
    rw [ite_eq_left (by rw [Bool.and_eq_true]; exact ⟨h1, hc.2⟩)]
    cases parseKind (slice b (findByte b 32 (s + 10) e + 1).toNat
      (findByte b 32 (findByte b 32 (s + 10) e + 1) e).toNat) <;> rfl
  · rw [ite_eq_right hc]
    rw [ite_eq_right]
    intro h
    apply hc
    rw [Bool.and_eq_true] at h
    exact ⟨numberResult_eq_true.mp h.1, h.2⟩

/-! ## Bits of a mask -/

theorem shift_bit (seen k : UInt64) (hk : k.toNat < 64) :
    ((seen >>> k) &&& 1 == 0) = !seen.toNat.testBit k.toNat := by
  have h : ((seen >>> k) &&& 1).toNat = seen.toNat / 2 ^ k.toNat % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]
    simp
  have h2 : seen.toNat / 2 ^ k.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, ← UInt64.toNat_inj, h]
  simp only [UInt64.reduceToNat]
  omega

theorem or_bit (acc k : UInt64) (hk : k.toNat < 64) :
    (acc ||| (1 <<< k)).toNat = acc.toNat ||| 2 ^ k.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hk]
  have : 2 ^ k.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  simp only [UInt64.reduceToNat, Nat.one_shiftLeft]
  rw [Nat.mod_eq_of_lt this]

theorem testBit_or_two_pow (m k j : Nat) :
    (m ||| 2 ^ k).testBit j = (m.testBit j || decide (j = k)) := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases h : j = k
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ## Order lines -/

/-- A list of numbers is a permutation of 1 to `n` exactly when its members are distinct, lie in 1
to `n`, and number `n`. -/
theorem perm_range_iff (o : List Nat) (n : Nat) :
    o.Perm (List.range' 1 n) ↔ o.Nodup ∧ (∀ x ∈ o, 1 ≤ x ∧ x ≤ n) ∧ o.length = n := by
  constructor
  · intro h
    refine ⟨h.nodup_iff.mpr List.nodup_range', fun x hx => ?_, by simpa using h.length_eq⟩
    have := (h.mem_iff).mp hx
    rw [List.mem_range'_1] at this
    omega
  · rintro ⟨hnd, hin, hlen⟩
    have hsub : o ⊆ List.range' 1 n := fun x hx => by
      have := hin x hx
      rw [List.mem_range'_1]
      omega
    exact (List.subperm_of_subset hnd hsub).perm_of_length_le (by simp [hlen])

theorem nodup_length_le {o : List Nat} {n : Nat} (hnd : o.Nodup) (hin : ∀ x ∈ o, 1 ≤ x ∧ x ≤ n) :
    o.length ≤ n := by
  have hsub : o ⊆ List.range' 1 n := fun x hx => by
    have := hin x hx
    rw [List.mem_range'_1]
    omega
  simpa using (List.subperm_of_subset hnd hsub).length_le

/-- The condition on the indices `is` of an order line after the indices `pr` already read. -/
def OrderOk (n fuel : Nat) (pr is : List Nat) : Prop :=
  pr.length + is.length = n ∧ (pr ++ is).Nodup ∧ (∀ x ∈ is, 1 ≤ x ∧ x ≤ n) ∧ is.length ≤ fuel

theorem numberResult_true {L : List UInt8} {v : UInt64} (h : numberResult L = (true, v)) :
    number L = some v.toNat := by
  unfold numberResult at h
  split at h
  · rename_i w hw
    split at h
    · rename_i hlt
      simp only [Prod.mk.injEq, true_and] at h
      rw [hw, ← h, ofNat_toNat_small hlt]
    · simp at h
  · simp at h

theorem numberResult_of {L : List UInt8} {v : Nat} (h : number L = some v) (hv : v < 2 ^ 64) :
    numberResult L = (true, UInt64.ofNat v) := by
  unfold numberResult
  simp only [h]
  exact ite_eq_left hv

/-- The test of `orderFrom` on the index `i` that a piece reads as. -/
theorem order_cond (L : List UInt8) (i : Nat) (hnum : number L = some i) (n seen : UInt64)
    (hn : n.toNat ≤ 63) (pr : List Nat) (hseen : ∀ j, seen.toNat.testBit j = decide (j + 1 ∈ pr)) :
    ((numberResult L).1 && decide (1 ≤ (numberResult L).2) && decide ((numberResult L).2 ≤ n) &&
        ((seen >>> ((numberResult L).2 - 1)) &&& 1 == 0)) =
      decide (1 ≤ i ∧ i ≤ n.toNat ∧ i ∉ pr) := by
  by_cases hi : 1 ≤ i ∧ i ≤ n.toNat
  · have hi64 : i < 2 ^ 64 := by omega
    have hiN : (UInt64.ofNat i).toNat = i := ofNat_toNat_small hi64
    have hk : (UInt64.ofNat i - 1).toNat = i - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp [hiN]; omega)), hiN]
      simp
    rw [numberResult_of hnum hi64, shift_bit _ _ (by rw [hk]; omega), hk, hseen,
      show i - 1 + 1 = i by omega]
    have h1 : decide (1 ≤ UInt64.ofNat i) = true := by
      simp [UInt64.le_iff_toNat_le, hiN]; omega
    have h2 : decide (UInt64.ofNat i ≤ n) = true := by
      simp [UInt64.le_iff_toNat_le, hiN]; omega
    rw [h1, h2]
    simp [hi.1, hi.2]
  · rw [decide_eq_false (show ¬(1 ≤ i ∧ i ≤ n.toNat ∧ i ∉ pr) by tauto)]
    by_cases hi64 : i < 2 ^ 64
    · have hiN : (UInt64.ofNat i).toNat = i := ofNat_toNat_small hi64
      rw [numberResult_of hnum hi64, Bool.eq_false_iff]
      intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le, hiN] at h
      simp only [UInt64.reduceToNat] at h
      omega
    · have : numberResult L = (false, 0) := by
        unfold numberResult
        simp only [hnum]
        exact ite_eq_right hi64
      rw [this]
      simp

theorem orderFrom_spec (b : Bytes) (hb : b.data.size < 2 ^ 64) (n : UInt64) (hn : n.toNat ≤ 63) :
    ∀ (fuel : Nat) (p e seen count fuelW : UInt64) (out : Array UInt64) (pr : List Nat),
      fuelW.toNat = fuel → p ≤ e → e.toNat ≤ b.data.size → pr.Nodup →
      (∀ x ∈ pr, 1 ≤ x ∧ x ≤ n.toNat) → (∀ j, seen.toNat.testBit j = decide (j + 1 ∈ pr)) →
      count.toNat = pr.length →
      ((orderFrom b n p e seen count fuelW out).1 = true ↔
        ∃ is, ((slice b p.toNat e.toNat).splitOn sp).mapM number = some is ∧
          OrderOk n.toNat fuel pr is) ∧
      (∀ is, ((slice b p.toNat e.toNat).splitOn sp).mapM number = some is →
        OrderOk n.toNat fuel pr is →
        (orderFrom b n p e seen count fuelW out).2.toList = out.toList ++ is.map UInt64.ofNat) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p e seen count fuelW out pr hf hpe he hnd hin hseen hcount
    have hf0 : fuelW = 0 := UInt64.toNat_inj.mp (by simpa using hf)
    subst hf0
    rw [orderFrom]
    simp only [UInt64.lt_irrefl, ite_false, Bool.false_eq_true, false_iff]
    refine ⟨?_, fun is his hok => ?_⟩
    · rintro ⟨is, his, hok⟩
      have hne := List.splitOn_ne_nil sp (slice b p.toNat e.toNat)
      have hlen := ((mapM_some_iff _ _ _).mp his).length_eq
      have := hok.2.2.2
      cases is with
      | nil => simp at hlen
      | cons _ _ => simp at this
    · have hne := List.splitOn_ne_nil sp (slice b p.toNat e.toNat)
      have hlen := ((mapM_some_iff _ _ _).mp his).length_eq
      have := hok.2.2.2
      cases is with
      | nil => simp at hlen
      | cons _ _ => simp at this
  | succ fuel ih =>
    intro p e seen count fuelW out pr hf hpe he hnd hin hseen hcount
    have hpos : 0 < fuelW := UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
    have hf1 : (fuelW - 1).toNat = fuel := by rw [UInt64.toNat_sub_of_le _ _ (by
      exact UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hsplit := findByte_split b 32 sp rfl p e hpe he
    obtain ⟨qa, qb, -, -⟩ := findByte_slice b 32 sp rfl p e hpe he
    have qb' := UInt64.le_iff_toNat_le.mp qb
    rw [orderFrom, ite_eq_left hpos]
    simp only []
    rw [hsplit, readNumber_eq b hb p _ qa (qb'.trans he)]
    generalize hq : findByte b 32 p e = q at *
    rw [List.mapM_cons]
    cases hnum : number (slice b p.toNat q.toNat) with
    | none =>
      have hr : numberResult (slice b p.toNat q.toNat) = (false, 0) := by simp [numberResult, hnum]
      rw [hr]
      simp
    | some i =>
      rw [order_cond _ i hnum n seen hn pr hseen]
      by_cases hgood : 1 ≤ i ∧ i ≤ n.toNat ∧ i ∉ pr
      · have hi64 : i < 2 ^ 64 := by omega
        rw [ite_eq_left (decide_eq_true hgood), numberResult_of hnum hi64]
        by_cases hlast : q < e
        · rw [ite_eq_left hlast, ite_eq_left hlast]
          have hk : (UInt64.ofNat i - 1).toNat = i - 1 := by
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
              simp [ofNat_toNat_small hi64]; omega)), ofNat_toNat_small hi64]
            simp
          have hq1 := toNat_add_one hlast
          have hle1 : q + 1 ≤ e := UInt64.le_iff_toNat_le.mpr (by
            have := UInt64.lt_iff_toNat_lt.mp hlast; omega)
          have hseen' : ∀ j, (seen ||| (1 <<< (UInt64.ofNat i - 1))).toNat.testBit j =
              decide (j + 1 ∈ pr ++ [i]) := by
            intro j
            rw [or_bit _ _ (by rw [hk]; omega), hk, testBit_or_two_pow, hseen]
            simp only [List.mem_append, List.mem_singleton]
            by_cases hj : j = i - 1
            · subst hj; simp [show i - 1 + 1 = i by omega]
            · simp [hj, show ¬ (j + 1 = i) by omega]
          have hprlen : pr.length ≤ n.toNat := nodup_length_le hnd hin
          have hcount' : (count + 1).toNat = (pr ++ [i]).length := by
            rw [UInt64.toNat_add, hcount]
            simp only [UInt64.reduceToNat, List.length_append, List.length_singleton]
            omega
          have hnd' : (pr ++ [i]).Nodup := List.nodup_append.mpr ⟨hnd, List.nodup_singleton i,
              fun a ha c hc => by simp at hc; subst hc; exact fun e => hgood.2.2 (e ▸ ha)⟩
          have hin' : ∀ x ∈ pr ++ [i], 1 ≤ x ∧ x ≤ n.toNat := fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hin x hx
            · simp at hx; subst hx; exact ⟨hgood.1, hgood.2.1⟩
          obtain ⟨ih1, ih2⟩ := ih (q + 1) e _ (count + 1) (fuelW - 1) (out.push (UInt64.ofNat i))
            (pr ++ [i]) hf1 hle1 he hnd' hin' hseen' hcount'
          rw [hq1] at ih1 ih2
          constructor
          · rw [ih1]
            constructor
            · rintro ⟨is, his, hok⟩
              refine ⟨i :: is, by simp [his], ?_⟩
              obtain ⟨h1, h2, h3, h4⟩ := hok
              refine ⟨by simp at h1 ⊢; omega, by simpa using h2, ?_, by simp; omega⟩
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨hgood.1, hgood.2.1⟩
              · exact h3 x hx
            · rintro ⟨is', his', hok⟩
              cases hm : List.mapM number ((slice b (q.toNat + 1) e.toNat).splitOn sp) with
              | none => rw [hm] at his'; simp at his'
              | some is =>
                rw [hm] at his'
                simp at his'
                subst his'
                obtain ⟨h1, h2, h3, h4⟩ := hok
                refine ⟨is, rfl, by simp at h1 ⊢; omega, by simpa using h2, fun x hx => h3 x
                  (List.mem_cons_of_mem _ hx), by simp at h4; omega⟩
          · intro is' his' hok
            cases hm : List.mapM number ((slice b (q.toNat + 1) e.toNat).splitOn sp) with
            | none => rw [hm] at his'; simp at his'
            | some is =>
              rw [hm] at his'
              simp at his'
              subst his'
              obtain ⟨h1, h2, h3, h4⟩ := hok
              rw [ih2 is hm ⟨by simp at h1 ⊢; omega, by simpa using h2, fun x hx => h3 x
                (List.mem_cons_of_mem _ hx), by simp at h4; omega⟩]
              simp
        · rw [ite_eq_right hlast, ite_eq_right hlast]
          simp only [List.mapM_nil, Option.pure_def]
          have hprlen : pr.length ≤ n.toNat := nodup_length_le hnd hin
          have hnd' : (pr ++ [i]).Nodup := List.nodup_append.mpr ⟨hnd, List.nodup_singleton i,
              fun a ha c hc => by simp at hc; subst hc; exact fun e => hgood.2.2 (e ▸ ha)⟩
          constructor
          · constructor
            · intro h
              refine ⟨[i], rfl, ?_, hnd', ?_, by simp⟩
              · simp only [beq_iff_eq] at h
                have := congrArg UInt64.toNat h
                rw [UInt64.toNat_add, hcount] at this
                simp only [UInt64.reduceToNat] at this
                simp only [List.length_singleton]
                omega
              · intro x hx; simp at hx; subst hx; exact ⟨hgood.1, hgood.2.1⟩
            · rintro ⟨is, his, hok⟩
              cases his
              simp only [beq_iff_eq]
              apply UInt64.toNat_inj.mp
              rw [UInt64.toNat_add, hcount]
              simp only [UInt64.reduceToNat]
              have := hok.1
              simp only [List.length_singleton] at this
              omega
          · intro is his _
            cases his
            simp
      · rw [ite_eq_right (by simpa using hgood)]
        simp only [Bool.false_eq_true, false_iff]
        refine ⟨?_, fun is his hok => ?_⟩
        · rintro ⟨is, his, hok⟩
          apply hgood
          cases hm : List.mapM number (if q < e then (slice b (q.toNat + 1) e.toNat).splitOn sp
            else []) with
          | none => rw [hm] at his; simp at his
          | some rest =>
            rw [hm] at his
            simp at his
            subst his
            obtain ⟨_, h2, h3, _⟩ := hok
            exact ⟨(h3 i List.mem_cons_self).1, (h3 i List.mem_cons_self).2,
              fun hm' => (List.nodup_append.mp h2).2.2 i hm' i List.mem_cons_self rfl⟩
        · exfalso
          apply hgood
          cases hm : List.mapM number (if q < e then (slice b (q.toNat + 1) e.toNat).splitOn sp
            else []) with
          | none => rw [hm] at his; simp at his
          | some rest =>
            rw [hm] at his
            simp at his
            subst his
            obtain ⟨_, h2, h3, _⟩ := hok
            exact ⟨(h3 i List.mem_cons_self).1, (h3 i List.mem_cons_self).2,
              fun hm' => (List.nodup_append.mp h2).2.2 i hm' i List.mem_cons_self rfl⟩

theorem readOrder_spec (b : Bytes) (hb : b.data.size < 2 ^ 64) (n : UInt64) (hn : n.toNat ≤ 63)
    (s e : UInt64) (hse : s ≤ e) (he : e.toNat ≤ b.data.size) (out : Array UInt64) :
    (readOrder b n s e out).1 = (parseOrder n.toNat (slice b s.toNat e.toNat)).isSome ∧
      ∀ o, parseOrder n.toNat (slice b s.toNat e.toNat) = some o →
        (readOrder b n s e out).2.toList = out.toList ++ o.map UInt64.ofNat := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  unfold readOrder parseOrder
  rw [hasPrefix_eq b hb s e _ 6 0 0 (by decide) (by decide) (ascii "order ") (by decide) hse he,
    after_slice]
  by_cases hp : (ascii "order ").isPrefixOf (slice b s.toNat e.toNat) = true
  swap
  · rw [ite_eq_right hp, ite_eq_right hp]
    simp
  rw [ite_eq_left hp, ite_eq_left hp]
  have hlen : 6 ≤ e.toNat - s.toNat := prefix_length he hp
  have hs6 : (s + 6).toNat = s.toNat + 6 := toNat_add_small (e := e) (k := 6) (by decide) (by omega)
  have hle6 : s + 6 ≤ e := UInt64.le_iff_toNat_le.mpr (by omega)
  simp only []
  rw [show (ascii "order ").length = 6 from rfl, ← hs6]
  obtain ⟨h1, h2⟩ := orderFrom_spec b hb n hn n.toNat (s + 6) e 0 0 n out [] rfl hle6 he
    List.nodup_nil (by simp) (by simp) (by simp)
  have hok : ∀ is, OrderOk n.toNat n.toNat [] is ↔ is.Perm (List.range' 1 n.toNat) := by
    intro is
    rw [perm_range_iff]
    simp only [OrderOk, List.length_nil, Nat.zero_add, List.nil_append]
    constructor
    · rintro ⟨h1, h2, h3, _⟩
      exact ⟨h2, h3, h1⟩
    · rintro ⟨h2, h3, h1⟩
      exact ⟨h1, h2, h3, by omega⟩
  constructor
  · rw [Bool.eq_iff_iff, h1]
    cases hm : ((slice b (s + 6).toNat e.toNat).splitOn sp).mapM number with
    | none => simp
    | some is =>
      simp only [Option.some.injEq, exists_eq_left', hok]
      split <;> simp_all
  · intro o ho
    cases hm : ((slice b (s + 6).toNat e.toNat).splitOn sp).mapM number with
    | none => rw [hm] at ho; simp at ho
    | some is =>
      rw [hm] at ho
      simp only [] at ho
      split at ho
      · rename_i hperm
        simp only [Option.some.injEq] at ho
        subst ho
        exact h2 _ hm ((hok _).mpr hperm)
      · simp at ho

/-! ## Position fields -/

theorem or_two_pow_eq_add {a k : Nat} (h : a < 2 ^ k) : a ||| 2 ^ k = a + 2 ^ k := by
  have := Nat.two_pow_add_eq_or_of_lt h 1
  rw [Nat.mul_one] at this
  rw [Nat.or_comm, ← this, Nat.add_comm]

theorem mapM_cons_some {α β : Type} (f : α → Option β) (a : α) (l : List α) (b : β)
    (hb : f a = some b) : (a :: l).mapM f = (l.mapM f).map (b :: ·) := by
  rw [List.mapM_cons, hb]
  cases l.mapM f <;> rfl

theorem mapM_cons_none {α β : Type} (f : α → Option β) (a : α) (l : List α)
    (hb : f a = none) : (a :: l).mapM f = none := by
  rw [List.mapM_cons, hb]
  rfl

/-- `markFrom` reads the indices of a field after the index `prev`, with the word `acc` of the
indices before. -/
theorem markFrom_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (n : UInt64) (hn : n.toNat ≤ 63) :
    ∀ (fuel : Nat) (p e prev acc fuelW : UInt64), fuelW.toNat = fuel → p ≤ e →
      e.toNat ≤ b.data.size → prev.toNat ≤ n.toNat → acc.toNat < 2 ^ prev.toNat →
      markFrom b n p e prev acc fuelW =
        match ((slice b p.toNat e.toNat).splitOn bar).mapM number with
        | some is =>
          if increasing (prev.toNat :: is) = true ∧ (∀ x ∈ is, x ≤ n.toNat) ∧ is.length ≤ fuel then
            (true, UInt64.ofNat (acc.toNat + (is.map fun i : Nat => (2 : Nat) ^ (i - 1)).sum))
          else (false, 0)
        | none => (false, 0) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p e prev acc fuelW hf hpe he hprev hacc
    have hf0 : fuelW = 0 := UInt64.toNat_inj.mp (by simpa using hf)
    subst hf0
    rw [markFrom]
    simp only [UInt64.lt_irrefl, ite_false]
    split
    · rename_i is his
      rw [ite_eq_right]
      rintro ⟨_, _, h⟩
      have hlen := ((mapM_some_iff _ _ _).mp his).length_eq
      cases is with
      | nil => simp at hlen
      | cons _ _ => simp at h
    · rfl
  | succ fuel ih =>
    intro p e prev acc fuelW hf hpe he hprev hacc
    have hpos : 0 < fuelW := UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
    have hf1 : (fuelW - 1).toNat = fuel := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hsplit := findByte_split b 124 bar rfl p e hpe he
    obtain ⟨qa, qb, -, -⟩ := findByte_slice b 124 bar rfl p e hpe he
    have qb' := UInt64.le_iff_toNat_le.mp qb
    rw [markFrom, ite_eq_left hpos]
    simp only []
    rw [hsplit, readNumber_eq b hb p _ qa (qb'.trans he)]
    generalize findByte b 124 p e = q at *
    cases hnum : number (slice b p.toNat q.toNat) with
    | none =>
      have hr : numberResult (slice b p.toNat q.toNat) = (false, 0) := by
        unfold numberResult; simp only [hnum]
      rw [hr, mapM_cons_none _ _ _ hnum]
      simp
    | some i =>
      rw [mapM_cons_some _ _ _ i hnum]
      by_cases hgood : prev.toNat < i ∧ i ≤ n.toNat
      · have hi64 : i < 2 ^ 64 := by omega
        have hiN := ofNat_toNat_small hi64
        rw [numberResult_of hnum hi64]
        have hc :
            (true && decide (prev < UInt64.ofNat i) && decide (UInt64.ofNat i ≤ n)) = true := by
          simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt,
            UInt64.le_iff_toNat_le, hiN]
          exact hgood
        rw [ite_eq_left hc]
        have hk : (UInt64.ofNat i - 1).toNat = i - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp [hiN]; omega)), hiN]
          simp
        have hacc' : (acc ||| (1 <<< (UInt64.ofNat i - 1))).toNat = acc.toNat + 2 ^ (i - 1) := by
          rw [or_bit _ _ (by rw [hk]; omega), hk]
          exact or_two_pow_eq_add (Nat.lt_of_lt_of_le hacc
            (Nat.pow_le_pow_right (by decide) (by omega)))
        by_cases hlast : q < e
        · rw [ite_eq_left hlast, ite_eq_left hlast]
          have hq1 := toNat_add_one hlast
          have hle1 : q + 1 ≤ e := UInt64.le_iff_toNat_le.mpr (by
            have := UInt64.lt_iff_toNat_lt.mp hlast; omega)
          have hacc2 :
              (acc ||| (1 <<< (UInt64.ofNat i - 1))).toNat < 2 ^ (UInt64.ofNat i).toNat := by
            rw [hacc', hiN]
            have h1 : acc.toNat < 2 ^ (i - 1) := Nat.lt_of_lt_of_le hacc
              (Nat.pow_le_pow_right (by decide) (by omega))
            have h2 : 2 ^ i = 2 ^ (i - 1) + 2 ^ (i - 1) := by
              rw [show i = i - 1 + 1 by omega, Nat.pow_succ]; simp; omega
            omega
          rw [ih (q + 1) e (UInt64.ofNat i) _ (fuelW - 1) hf1 hle1 he (by rw [hiN]; exact hgood.2)
            hacc2, hq1, hiN, hacc']
          cases hm : ((slice b (q.toNat + 1) e.toNat).splitOn bar).mapM number with
          | none => rfl
          | some is =>
            simp only [Option.map_some]
            by_cases hc2 : increasing (i :: is) = true ∧ (∀ x ∈ is, x ≤ n.toNat) ∧ is.length ≤ fuel
            · have hc3 : increasing (prev.toNat :: i :: is) = true ∧ (∀ x ∈ i :: is, x ≤ n.toNat) ∧
                  (i :: is).length ≤ fuel + 1 := by
                refine ⟨?_, ?_, by simp; omega⟩
                · simp only [increasing, Bool.and_eq_true, decide_eq_true_eq]
                  exact ⟨hgood.1, hc2.1⟩
                · intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact hgood.2
                  · exact hc2.2.1 x hx
              rw [ite_eq_left hc2, ite_eq_left hc3]
              simp only [List.map_cons, List.sum_cons]
              congr 2
              omega
            · rw [ite_eq_right hc2, ite_eq_right]
              rintro ⟨h1, h2, h3⟩
              simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h1
              exact hc2 ⟨h1.2, fun x hx => h2 x (List.mem_cons_of_mem _ hx), by simp at h3; omega⟩
        · rw [ite_eq_right hlast, ite_eq_right hlast]
          simp only [List.mapM_nil, Option.pure_def, Option.map_some]
          rw [ite_eq_left (by
            refine ⟨?_, ?_, by simp⟩
            · simp only [increasing, Bool.and_true, decide_eq_true_eq]
              exact hgood.1
            · intro x hx
              simp at hx
              rw [hx]
              exact hgood.2)]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
            Prod.mk.injEq, true_and]
          have h1 : acc.toNat < 2 ^ (i - 1) := Nat.lt_of_lt_of_le hacc
            (Nat.pow_le_pow_right (by decide) (by omega))
          have h2 : 2 ^ (i - 1) ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by omega)
          apply UInt64.toNat_inj.mp
          rw [hacc', ofNat_toNat_small (by omega)]
      · have hc : ((numberResult (slice b p.toNat q.toNat)).1 &&
            decide (prev < (numberResult (slice b p.toNat q.toNat)).2) &&
              decide ((numberResult (slice b p.toNat q.toNat)).2 ≤ n)) = false := by
          by_cases hi64 : i < 2 ^ 64
          · have hiN := ofNat_toNat_small hi64
            rw [numberResult_of hnum hi64, Bool.eq_false_iff]
            intro h
            simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt,
              UInt64.le_iff_toNat_le, hiN] at h
            exact hgood h
          · have : numberResult (slice b p.toNat q.toNat) = (false, 0) := by
              unfold numberResult; simp only [hnum]; exact ite_eq_right hi64
            rw [this]
            simp
        rw [hc]
        simp only [Bool.false_eq_true, ite_false]
        cases hm :
            (if q < e then (slice b (q.toNat + 1) e.toNat).splitOn bar else []).mapM number with
        | none => rfl
        | some is =>
          simp only [Option.map_some]
          rw [ite_eq_right]
          rintro ⟨h1, h2, _⟩
          simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h1
          exact hgood ⟨h1.1, h2 i List.mem_cons_self⟩

/-- `fieldWord` reads a position field as `parsePosition` does. -/
theorem fieldWord_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (n : UInt64) (hn : n.toNat ≤ 63)
    (s e : UInt64) (hse : s ≤ e) (he : e.toNat ≤ b.data.size) :
    fieldWord b n s e = match parsePosition n.toNat (slice b s.toNat e.toNat) with
      | some w => (true, w)
      | none => (false, 0) := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  unfold fieldWord parsePosition
  by_cases h0 : s = e
  · subst h0
    simp [slice_self]
  rw [ite_eq_right (by simpa using h0)]
  have hlt : s.toNat < e.toNat := by
    have : s.toNat ≠ e.toNat := fun h => h0 (UInt64.toNat_inj.mp h)
    omega
  have hne : slice b s.toNat e.toNat ≠ [] := by
    intro h
    have := slice_length (b := b) (s := s.toNat) he
    rw [h] at this
    simp at this
    omega
  rw [ite_eq_right hne]
  have hstar : (e - s == 1 && b.get s == 42) = decide (slice b s.toNat e.toNat = ascii "*") := by
    rw [beq_length hse, show (1 : UInt64).toNat = 1 from rfl]
    by_cases hl : e.toNat - s.toNat = 1
    · rw [decide_eq_true hl, Bool.true_and, slice_cons hlt he,
        show s.toNat + 1 = e.toNat by omega, slice_self, get_eq, ascii_star]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, List.cons.injEq]
      simp only [and_true]
      constructor
      · intro h; exact UInt8.toUInt64_inj.mp h
      · intro h; rw [h]; rfl
    · rw [decide_eq_false hl, Bool.false_and,
        decide_length_slice he (by rw [show (ascii "*").length = 1 from rfl]; exact hl)]
  rw [hstar]
  by_cases hs : slice b s.toNat e.toNat = ascii "*"
  · rw [ite_eq_left (decide_eq_true hs), ite_eq_left hs]
    rfl
  rw [ite_eq_right (by simpa using hs), ite_eq_right hs,
    markFrom_eq b hb n hn n.toNat s e 0 0 n rfl hse he (by simp) (by simp)]
  cases hm : ((slice b s.toNat e.toNat).splitOn bar).mapM number with
  | none => rfl
  | some is =>
    simp only []
    have hiff : (increasing ((0 : UInt64).toNat :: is) = true ∧ (∀ x ∈ is, x ≤ n.toNat) ∧
        is.length ≤ n.toNat) ↔
        ((is.all fun i : Nat => 1 ≤ i && i ≤ n.toNat) && increasing is) = true := by
      rw [UInt64.toNat_zero, Bool.and_eq_true, List.all_eq_true, increasing_iff, increasing_iff,
        List.pairwise_cons]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, _⟩
        exact ⟨fun x hx => ⟨by have := h1 x hx; omega, h3 x hx⟩, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨fun x hx => by have := (h1 x hx).1; omega, h2⟩, fun x hx => (h1 x hx).2, ?_⟩
        exact nodup_length_le (List.Pairwise.nodup h2) (fun x hx => h1 x hx)
    by_cases hc : ((is.all fun i : Nat => 1 ≤ i && i ≤ n.toNat) && increasing is) = true
    · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]
      simp
    · rw [ite_eq_right (fun h => hc (hiff.mp h)), ite_eq_right hc]

/-! ## Ballot lines -/

theorem fieldsFrom_spec (b : Bytes) (hb : b.data.size < 2 ^ 64) (n : UInt64) (hn : n.toNat ≤ 63) :
    ∀ (fuel : Nat) (p e fuelW : UInt64) (out : Array UInt64), fuelW.toNat = fuel → p ≤ e →
      e.toNat ≤ b.data.size →
      ((fieldsFrom b n p e fuelW out).1 = true ↔
        ∃ ws, ((slice b p.toNat e.toNat).splitOn comma).mapM (parsePosition n.toNat) = some ws ∧
          ws.length ≤ fuel) ∧
      (∀ ws, ((slice b p.toNat e.toNat).splitOn comma).mapM (parsePosition n.toNat) = some ws →
        ws.length ≤ fuel → (fieldsFrom b n p e fuelW out).2.toList = out.toList ++ ws) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p e fuelW out hf hpe he
    have hf0 : fuelW = 0 := UInt64.toNat_inj.mp (by simpa using hf)
    subst hf0
    rw [fieldsFrom]
    simp only [UInt64.lt_irrefl, ite_false, Bool.false_eq_true, false_iff]
    refine ⟨?_, fun ws hws hl => ?_⟩
    · rintro ⟨ws, hws, hl⟩
      have hlen := ((mapM_some_iff _ _ _).mp hws).length_eq
      cases ws with
      | nil => simp at hlen
      | cons _ _ => simp at hl
    · have hlen := ((mapM_some_iff _ _ _).mp hws).length_eq
      cases ws with
      | nil => simp at hlen
      | cons _ _ => simp at hl
  | succ fuel ih =>
    intro p e fuelW out hf hpe he
    have hpos : 0 < fuelW := UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
    have hf1 : (fuelW - 1).toNat = fuel := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hsplit := findByte_split b 44 comma rfl p e hpe he
    obtain ⟨qa, qb, -, -⟩ := findByte_slice b 44 comma rfl p e hpe he
    have qb' := UInt64.le_iff_toNat_le.mp qb
    rw [fieldsFrom, ite_eq_left hpos]
    simp only []
    rw [hsplit, fieldWord_eq b hb n hn p _ qa (qb'.trans he)]
    generalize findByte b 44 p e = q at *
    cases hw : parsePosition n.toNat (slice b p.toNat q.toNat) with
    | none =>
      rw [mapM_cons_none _ _ _ hw]
      simp
    | some w =>
      rw [mapM_cons_some _ _ _ w hw]
      simp only [ite_true]
      by_cases hlast : q < e
      · rw [ite_eq_left hlast, ite_eq_left hlast]
        have hq1 := toNat_add_one hlast
        have hle1 : q + 1 ≤ e := UInt64.le_iff_toNat_le.mpr (by
          have := UInt64.lt_iff_toNat_lt.mp hlast; omega)
        obtain ⟨ih1, ih2⟩ := ih (q + 1) e (fuelW - 1) (out.push w) hf1 hle1 he
        rw [hq1] at ih1 ih2
        cases hm : ((slice b (q.toNat + 1) e.toNat).splitOn comma).mapM (parsePosition n.toNat) with
        | none =>
          rw [hm] at ih1
          simp only [Option.map_none, reduceCtorEq, false_and, exists_false, iff_false] at ih1 ⊢
          simp [ih1]
        | some ws =>
          rw [hm] at ih1 ih2
          simp only [Option.map_some, Option.some.injEq, exists_eq_left'] at ih1 ⊢
          refine ⟨by rw [ih1]; simp, fun ws' hws' hl => ?_⟩
          subst hws'
          rw [ih2 ws rfl (by simp at hl; omega)]
          simp
      · rw [ite_eq_right hlast, ite_eq_right hlast]
        simp only [List.mapM_nil, Option.pure_def, Option.map_some, Option.some.injEq,
          exists_eq_left', List.length_singleton, true_iff]
        refine ⟨by omega, fun ws hws _ => ?_⟩
        subst hws
        simp

theorem dropWhile_nil_not_mem {c : UInt8} {L : List UInt8} (h : L.dropWhile (· != c) = []) :
    c ∉ L := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.dropWhile_cons] at h
    by_cases hx : (x != c) = true
    · rw [ite_eq_left hx] at h
      intro hm
      rcases List.mem_cons.mp hm with rfl | hm
      · simp at hx
      · exact ih h hm
    · rw [ite_eq_right hx] at h
      simp at h

/-- A list splits at `c` into one more piece than it holds `c`. -/
theorem splitOn_length (c : UInt8) (L : List UInt8) : (L.splitOn c).length = L.count c + 1 := by
  induction h : L.length using Nat.strong_induction_on generalizing L with
  | _ m ih =>
    cases hs : L.span (· != c) with
    | mk a r =>
      cases r with
      | nil =>
        have hnot : c ∉ L := by
          rw [List.span_eq_takeWhile_dropWhile] at hs
          exact dropWhile_nil_not_mem (Prod.mk.inj hs).2
        rw [List.splitOn_eq_singleton hnot, List.count_eq_zero.mpr hnot]
        rfl
      | cons x r =>
        obtain ⟨hL, hca⟩ := span_some hs
        have hlt : r.length < m := by rw [← h, hL]; simp; omega
        rw [hL, List.splitOn_append_cons_self_of_not_mem hca, List.length_cons,
          ih r.length hlt r rfl, List.count_append, List.count_cons_self,
          List.count_eq_zero.mpr hca]
        omega

theorem countByte_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (c : UInt64) (c8 : UInt8)
    (hc : c8.toUInt64 = c) (s e : UInt64) (hse : s ≤ e) (he : e.toNat ≤ b.data.size) :
    (countByte b c s e).toNat = (slice b s.toNat e.toNat).count c8 := by
  have hloop := loop_foldl_bytes b hb s e hse he (0 : UInt64)
    (fun x acc => if x == c then acc + 1 else acc)
  rw [countByte, hloop]
  have key : ∀ (L : List UInt8) (a : UInt64), a.toNat + L.length < 2 ^ 64 →
      (L.foldl (fun acc x => if x.toUInt64 == c then acc + 1 else acc) a).toNat =
        a.toNat + L.count c8 := by
    intro L
    induction L with
    | nil => intro a _; simp
    | cons x L ih =>
      intro a ha
      rw [List.foldl_cons, List.count_cons]
      by_cases hx : x = c8
      · subst hx
        rw [ite_eq_left (by simp [hc]), ih _ (by rw [UInt64.toNat_add]; simp at ha ⊢; omega),
          UInt64.toNat_add]
        simp only [UInt64.reduceToNat, beq_self_eq_true, ite_true]
        simp at ha
        omega
      · have hx' : (x.toUInt64 == c) = false := by
          rw [← hc]; simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun h => hx (UInt8.toUInt64_inj.mp h)
        rw [hx', ite_eq_right (by simp), ih a (by simp at ha; omega)]
        simp [hx]
  rw [key _ 0 (by rw [slice_length he]; simp; have := UInt64.toNat_lt e; omega)]
  simp

/-- `ballotWords` reads a ballot line as `parseBallot` does, with its position words pushed onto
`out`. -/
theorem ballotWords_spec (b : Bytes) (hb : b.data.size < 2 ^ 64) (k n : UInt64)
    (hk : 1 ≤ k.toNat ∧ k.toNat ≤ 63) (hn : n.toNat ≤ 63) (s e : UInt64) (hse : s ≤ e)
    (he : e.toNat ≤ b.data.size) (out : Array UInt64) :
    (ballotWords b k n s e out).1 = (parseBallot k.toNat n.toNat (slice b s.toNat e.toNat)).isSome ∧
      ∀ bal, parseBallot k.toNat n.toNat (slice b s.toNat e.toNat) = some bal →
        (ballotWords b k n s e out).2.toList = out.toList ++ bal.positions := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  have hcount := countByte_eq b hb 44 comma rfl s e hse he
  have hlen := splitOn_length comma (slice b s.toNat e.toNat)
  have hsl := slice_length (b := b) (s := s.toNat) he
  have hcle : (slice b s.toNat e.toNat).count comma ≤ e.toNat - s.toNat := by
    rw [← hsl]; exact List.count_le_length
  have he64 := UInt64.toNat_lt e
  have hsplit := findByte_split b 44 comma rfl s e hse he
  obtain ⟨qa, qb, -, -⟩ := findByte_slice b 44 comma rfl s e hse he
  have qb' := UInt64.le_iff_toNat_le.mp qb
  unfold ballotWords parseBallot
  simp only []
  rw [hsplit]
  generalize hq : findByte b 44 s e = q at *
  have hc1 : (countByte b 44 s e + 1 == k) =
      decide (((slice b s.toNat q.toNat) :: if q < e then
        (slice b (q.toNat + 1) e.toNat).splitOn comma else []).length = k.toNat) := by
    rw [← hsplit, hlen, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj,
      UInt64.toNat_add, hcount]
    simp only [UInt64.reduceToNat]
    constructor
    · intro h
      by_cases h' : (slice b s.toNat e.toNat).count comma + 1 < 2 ^ 64
      · rw [Nat.mod_eq_of_lt h'] at h; exact h
      · omega
    · intro h; rw [Nat.mod_eq_of_lt (by omega)]; exact h
  have hc2 : (countByte b 44 s e == k) =
      decide (((slice b s.toNat q.toNat) :: if q < e then
        (slice b (q.toNat + 1) e.toNat).splitOn comma else []).length = k.toNat + 1) := by
    rw [← hsplit, hlen, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, hcount]
    omega
  rw [hc1]
  simp only []
  by_cases h1 : ((slice b s.toNat q.toNat) :: if q < e then
      (slice b (q.toNat + 1) e.toNat).splitOn comma else []).length = k.toNat
  · rw [ite_eq_left (decide_eq_true h1), ite_eq_left h1]
    obtain ⟨f1, f2⟩ := fieldsFrom_spec b hb n hn k.toNat s e k out rfl hse he
    rw [hsplit] at f1 f2
    constructor
    · rw [Bool.eq_iff_iff, f1]
      cases hm : List.mapM (parsePosition n.toNat) ((slice b s.toNat q.toNat) :: if q < e then
          (slice b (q.toNat + 1) e.toNat).splitOn comma else []) with
      | none => simp
      | some ws =>
        simp only [Option.some.injEq, exists_eq_left', Option.map_some, Option.isSome_some,
          iff_true]
        have := ((mapM_some_iff _ _ _).mp hm).length_eq
        omega
    · intro bal hbal
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp hbal
      rw [f2 ws hws (by have := ((mapM_some_iff _ _ _).mp hws).length_eq; omega)]
  · rw [ite_eq_right (by simpa using h1), ite_eq_right h1, hc2]
    by_cases h2 : ((slice b s.toNat q.toNat) :: if q < e then
        (slice b (q.toNat + 1) e.toNat).splitOn comma else []).length = k.toNat + 1
    · rw [ite_eq_left (decide_eq_true h2)]
      have hqe : q < e := by
        by_contra hqe
        rw [ite_eq_right hqe] at h2
        simp at h2
        omega
      rw [ite_eq_left hqe] at h2 ⊢
      have hrest : ((slice b (q.toNat + 1) e.toNat).splitOn comma).length = k.toNat := by
        simp at h2; omega
      rw [isIdent_eq b s q qa (qb'.trans he)]
      have hq1 := toNat_add_one hqe
      have hle1 : q + 1 ≤ e := UInt64.le_iff_toNat_le.mpr (by
        have := UInt64.lt_iff_toNat_lt.mp hqe; omega)
      obtain ⟨f1, f2⟩ := fieldsFrom_spec b hb n hn k.toNat (q + 1) e k out rfl hle1 he
      rw [hq1] at f1 f2
      by_cases hid : identOk (slice b s.toNat q.toNat) = true
      · rw [ite_eq_left hid, ite_eq_left ⟨hrest, hid⟩]
        constructor
        · rw [Bool.eq_iff_iff, f1]
          cases hm : List.mapM (parsePosition n.toNat)
              ((slice b (q.toNat + 1) e.toNat).splitOn comma) with
          | none => simp
          | some ws =>
            simp only [Option.some.injEq, exists_eq_left', Option.map_some, Option.isSome_some,
              iff_true]
            have := ((mapM_some_iff _ _ _).mp hm).length_eq
            omega
        · intro bal hbal
          obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp hbal
          rw [f2 ws hws (by have := ((mapM_some_iff _ _ _).mp hws).length_eq; omega)]
      · rw [ite_eq_right (by simpa using hid), ite_eq_right (fun h => hid h.2)]
        simp
    · rw [ite_eq_right (by simpa using h2), ite_eq_right (fun h => h2 (by
        rw [List.length_cons, h.1]))]
      simp

/-! ## Header lines -/

theorem isFormat_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (s e : UInt64) (hse : s ≤ e)
    (he : e.toNat ≤ b.data.size) :
    isFormat b s e = (parseFormat (slice b s.toNat e.toNat)).isSome := by
  unfold isFormat parseFormat
  rw [beq_length hse, show (13 : UInt64).toNat = 13 from rfl]
  by_cases hl : e.toNat - s.toNat = 13
  · rw [decide_eq_true hl, Bool.true_and,
      hasPrefix_text b hb s e _ 8 _ 5 (by decide) (by decide) (ascii "rcv-ballots 1") (by decide)
        (by rw [hl]; rfl) hse he]
    by_cases h : slice b s.toNat e.toNat = ascii "rcv-ballots 1" <;> simp [h]
  · rw [decide_eq_false hl, Bool.false_and]
    have : slice b s.toNat e.toNat ≠ ascii "rcv-ballots 1" := by
      intro h
      apply hl
      rw [← slice_length he, h]
      rfl
    simp [this]

theorem isContest_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (s e : UInt64) (hse : s ≤ e)
    (he : e.toNat ≤ b.data.size) :
    isContest b s e = (parseContest (slice b s.toNat e.toNat)).isSome := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  unfold isContest parseContest
  rw [hasPrefix_eq b hb s e _ 8 0 0 (by decide) (by decide) (ascii "contest ") (by decide) hse he,
    after_slice]
  by_cases hp : (ascii "contest ").isPrefixOf (slice b s.toNat e.toNat) = true
  · rw [ite_eq_left hp, hp, Bool.true_and]
    have hlen : 8 ≤ e.toNat - s.toNat := prefix_length he hp
    have hs8 : (s + 8).toNat = s.toNat + 8 :=
      toNat_add_small (e := e) (k := 8) (by decide) (by omega)
    rw [isIdent_eq b _ e (UInt64.le_iff_toNat_le.mpr (by omega)) he, hs8]
    simp only [show (ascii "contest ").length = 8 from rfl]
    split <;> simp_all
  · rw [ite_eq_right hp, Bool.eq_false_iff.mpr hp, Bool.false_and]
    rfl

theorem readAfter_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (s e w1 l1 w2 l2 lo hi : UInt64)
    (hl1 : l1.toNat ≤ 8) (hl2 : l2.toNat ≤ 8) (P : String)
    (hP : (ascii P).map UInt8.toUInt64 = wordBytes w1 l1.toNat ++ wordBytes w2 l2.toNat)
    (hse : s ≤ e) (he : e.toNat ≤ b.data.size) :
    readAfter b s e w1 l1 w2 l2 lo hi =
      match parseBounded P lo.toNat hi.toNat (slice b s.toNat e.toNat) with
      | some v => (true, UInt64.ofNat v)
      | none => (false, 0) := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  have hPlen : (ascii P).length = l1.toNat + l2.toNat := by
    have := congrArg List.length hP
    simpa [wordBytes_length] using this
  unfold readAfter parseBounded
  rw [hasPrefix_eq b hb s e _ _ _ _ hl1 hl2 (ascii P) hP hse he, after_slice]
  by_cases hp : (ascii P).isPrefixOf (slice b s.toNat e.toNat) = true
  · rw [ite_eq_left hp, ite_eq_left hp]
    have hlen : (ascii P).length ≤ e.toNat - s.toNat := prefix_length he hp
    have hs : (s + l1 + l2).toNat = s.toNat + (ascii P).length := by
      rw [hPlen, UInt64.toNat_add, UInt64.toNat_add]
      have := UInt64.toNat_lt e
      omega
    rw [readNumber_eq b hb _ e (UInt64.le_iff_toNat_le.mpr (by omega)) he, hs]
    simp only []
    cases hnum : number (slice b (s.toNat + (ascii P).length) e.toNat) with
    | none =>
      have : numberResult (slice b (s.toNat + (ascii P).length) e.toNat) = (false, 0) := by
        unfold numberResult; simp only [hnum]
      rw [this]
      rfl
    | some v =>
      simp only []
      by_cases hv : v < 2 ^ 64
      · have hvN := ofNat_toNat_small hv
        rw [numberResult_of hnum hv]
        by_cases hr : lo.toNat ≤ v ∧ v ≤ hi.toNat
        · rw [ite_eq_left hr, ite_eq_left (by simp [UInt64.le_iff_toNat_le, hvN]; omega)]
        · rw [ite_eq_right hr, ite_eq_right (by simp [UInt64.le_iff_toNat_le, hvN]; omega)]
      · have : numberResult (slice b (s.toNat + (ascii P).length) e.toNat) = (false, 0) := by
          unfold numberResult; simp only [hnum]; exact ite_eq_right hv
        rw [this]
        have hr : ¬ (lo.toNat ≤ v ∧ v ≤ hi.toNat) := by have := UInt64.toNat_lt hi; omega
        rw [ite_eq_right hr]
        rfl
  · rw [ite_eq_right hp, ite_eq_right hp]

/-! ## Lines of the file -/

/-- The pieces of the file from position `p` on. -/
def piecesFrom (b : Bytes) (p : UInt64) : List (List UInt8) :=
  (slice b p.toNat b.data.size).splitOn lf

theorem size_toNat (b : Bytes) (hb : b.data.size < 2 ^ 64) : b.size.toNat = b.data.size :=
  Bytes.size_toNat b hb

theorem readLine_pieces {α : Type} (b : Bytes) (hb : b.data.size < 2 ^ 64) (j : Nat) (r : Role)
    (parse : List UInt8 → Option α) (p : UInt64) (hp : p ≤ b.size) :
    readLine j r parse (piecesFrom b p) =
      if findByte b 10 p b.size < b.size then
        match parse (slice b p.toNat (findByte b 10 p b.size).toNat) with
        | some a => .ok (a, piecesFrom b (findByte b 10 p b.size + 1))
        | none => .error (j, r)
      else .error (j, r) := by
  have hsz := size_toNat b hb
  have hsplit := findByte_split b 10 lf rfl p b.size hp (by rw [hsz])
  rw [hsz] at hsplit
  unfold piecesFrom readLine takeLine
  rw [hsplit]
  by_cases he : findByte b 10 p b.size < b.size
  · rw [ite_eq_left he, ite_eq_left he, toNat_add_one he]
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil
      (List.splitOn_ne_nil lf (slice b ((findByte b 10 p b.size).toNat + 1) b.data.size))
    rw [hx]
    simp only []
    cases parse (slice b p.toNat (findByte b 10 p b.size).toNat) <;> rfl
  · rw [ite_eq_right he, ite_eq_right he]

theorem findByte_le_size (b : Bytes) (p : UInt64) (hp : p ≤ b.size) :
    p ≤ findByte b 10 p b.size ∧ findByte b 10 p b.size ≤ b.size :=
  ⟨(findByte_spec b 10 p b.size hp).1, (findByte_spec b 10 p b.size hp).2.1⟩

theorem next_le_size {b : Bytes} {e : UInt64} (he : e < b.size) : e + 1 ≤ b.size :=
  UInt64.le_iff_toNat_le.mpr (by have := UInt64.lt_iff_toNat_lt.mp he; rw [toNat_add_one he]; omega)

/-- The candidate lines read by `candidatesFrom` and by `readCandidates`. -/
theorem candidatesFrom_spec (b : Bytes) (hb : b.data.size < 2 ^ 64) :
    ∀ (count : Nat) (p i countW : UInt64) (out : Array UInt64), countW.toNat = count →
      p ≤ b.size → 1 ≤ i.toNat → i.toNat + count ≤ 64 →
      match readCandidates i.toNat count (piecesFrom b p) with
      | .ok (cs, rest) => ∃ p', p' ≤ b.size ∧ rest = piecesFrom b p' ∧
          (candidatesFrom b p i countW out).1 = 0 ∧ (candidatesFrom b p i countW out).2.1 = p' ∧
          (candidatesFrom b p i countW out).2.2.toList =
            out.toList ++ cs.map fun x => UInt64.ofNat (Spec.kindCode x.kind)
      | .error (j, _) => (candidatesFrom b p i countW out).1 = UInt64.ofNat j ∧ 5 ≤ j ∧
          j < 2 ^ 64 := by
  intro count
  induction count with
  | zero =>
    intro p i countW out hc hp hi1 hi
    have hc0 : countW = 0 := UInt64.toNat_inj.mp (by simpa using hc)
    subst hc0
    simp only [readCandidates]
    refine ⟨p, hp, rfl, ?_⟩
    rw [candidatesFrom]
    simp
  | succ count ih =>
    intro p i countW out hc hp hi1 hi
    have hpos : 0 < countW := UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
    have hc1 : (countW - 1).toNat = count := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have h4 : (4 + i : UInt64) = UInt64.ofNat (4 + i.toNat) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, ofNat_toNat_small (n := 4 + i.toNat) (by omega)]
      simp only [UInt64.reduceToNat]
      omega
    have hsz := size_toNat b hb
    obtain ⟨ea, eb⟩ := findByte_le_size b p hp
    have eb' := UInt64.le_iff_toNat_le.mp eb
    simp only [readCandidates]
    rw [readLine_pieces b hb _ _ _ p hp]
    rw [candidatesFrom, ite_eq_left hpos]
    simp only []
    by_cases he : findByte b 10 p b.size < b.size
    · rw [ite_eq_left he, ite_eq_left he,
        candidateCode_eq b hb i p _ ea (by rw [← hsz]; exact eb')]
      cases hx : parseCandidate i.toNat (slice b p.toNat (findByte b 10 p b.size).toNat) with
      | none => simp only []; exact ⟨h4, by omega, by omega⟩
      | some x =>
        simp only []
        have hk : UInt64.ofNat (Spec.kindCode x.kind) < 4 := by
          cases x.kind <;> decide
        rw [ite_eq_left hk]
        have hi1 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        have := ih _ (i + 1) (countW - 1) (out.push (UInt64.ofNat (Spec.kindCode x.kind))) hc1
          (next_le_size he) (by rw [hi1]; omega) (by rw [hi1]; omega)
        rw [hi1] at this
        revert this
        cases readCandidates (i.toNat + 1) count (piecesFrom b (findByte b 10 p b.size + 1)) with
        | ok v =>
          obtain ⟨cs, rest⟩ := v
          simp only []
          rintro ⟨p', hp', hrest, h1, h2, h3⟩
          exact ⟨p', hp', hrest, h1, h2, by rw [h3]; simp⟩
        | error e =>
          obtain ⟨j, r⟩ := e
          simp only []
          rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, h3⟩
    · rw [ite_eq_right he, ite_eq_right he]
      simp only []
      exact ⟨h4, by omega, by omega⟩

/-- The ballot lines read by `ballotsFrom` and by `readBallots`. -/
theorem ballotsFrom_spec (b : Bytes) (hb : b.data.size < 2 ^ 64) (k n : UInt64)
    (hk : 1 ≤ k.toNat ∧ k.toNat ≤ 63) (hn : n.toNat ≤ 63) :
    ∀ (count : Nat) (p j countW : UInt64) (out : Array UInt64) (acc : List Ballot),
      countW.toNat = count → p ≤ b.size → 1 ≤ j.toNat → j.toNat + count < 2 ^ 64 →
      match readBallots k.toNat n.toNat j.toNat count acc (piecesFrom b p) with
      | .ok (bs, rest) => ∃ p' new, p' ≤ b.size ∧ rest = piecesFrom b p' ∧
          bs = acc.reverse ++ new ∧
          (ballotsFrom b k n p j countW out).1 = 0 ∧ (ballotsFrom b k n p j countW out).2.1 = p' ∧
          (ballotsFrom b k n p j countW out).2.2.toList =
            out.toList ++ new.flatMap fun x : Ballot => x.positions
      | .error (j', _) => (ballotsFrom b k n p j countW out).1 = UInt64.ofNat j' ∧ 1 ≤ j' ∧
          j' < 2 ^ 64 := by
  intro count
  induction count with
  | zero =>
    intro p j countW out acc hc hp hj1 hj
    have hc0 : countW = 0 := UInt64.toNat_inj.mp (by simpa using hc)
    subst hc0
    simp only [readBallots]
    refine ⟨p, [], hp, rfl, by simp, ?_⟩
    rw [ballotsFrom]
    simp
  | succ count ih =>
    intro p j countW out acc hc hp hj1 hj
    have hpos : 0 < countW := UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
    have hc1 : (countW - 1).toNat = count := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hjN : j = UInt64.ofNat j.toNat := UInt64.ofNat_toNat.symm
    have hsz := size_toNat b hb
    obtain ⟨ea, eb⟩ := findByte_le_size b p hp
    have eb' := UInt64.le_iff_toNat_le.mp eb
    simp only [readBallots]
    rw [readLine_pieces b hb _ _ _ p hp]
    rw [ballotsFrom, ite_eq_left hpos]
    simp only []
    by_cases he : findByte b 10 p b.size < b.size
    · rw [ite_eq_left he, ite_eq_left he]
      obtain ⟨w1, w2⟩ := ballotWords_spec b hb k n hk hn p _ ea (by rw [← hsz]; exact eb') out
      cases hx : parseBallot k.toNat n.toNat (slice b p.toNat (findByte b 10 p b.size).toNat) with
      | none =>
        rw [hx] at w1
        simp only [Option.isSome_none] at w1
        rw [ite_eq_right (by rw [w1]; simp)]
        exact ⟨hjN, hj1, by omega⟩
      | some x =>
        rw [hx] at w1
        simp only [Option.isSome_some] at w1
        rw [ite_eq_left w1]
        have hj1' : (j + 1).toNat = j.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        have := ih _ (j + 1) (countW - 1) (ballotWords b k n p (findByte b 10 p b.size) out).2
          (x :: acc) hc1 (next_le_size he) (by rw [hj1']; omega) (by rw [hj1']; omega)
        rw [hj1'] at this
        simp only []
        revert this
        cases readBallots k.toNat n.toNat (j.toNat + 1) count (x :: acc)
            (piecesFrom b (findByte b 10 p b.size + 1)) with
        | ok v =>
          obtain ⟨bs, rest⟩ := v
          simp only []
          rintro ⟨p', new, hp', hrest, hbs, h1, h2, h3⟩
          refine ⟨p', x :: new, hp', hrest, by rw [hbs]; simp, h1, h2, ?_⟩
          rw [h3, w2 x hx]
          simp
        | error e =>
          obtain ⟨j', r⟩ := e
          simp only []
          rintro ⟨h1, h2, h3⟩
          exact ⟨h1, by omega, h3⟩
    · rw [ite_eq_right he, ite_eq_right he]
      exact ⟨hjN, hj1, by omega⟩

/-- The pieces from a position are the empty piece alone exactly at the end of the file. -/
theorem piecesFrom_end (b : Bytes) (hb : b.data.size < 2 ^ 64) (p : UInt64) (hp : p ≤ b.size) :
    piecesFrom b p = [[]] ↔ p = b.size := by
  have hsz := size_toNat b hb
  have hp' := UInt64.le_iff_toNat_le.mp hp
  unfold piecesFrom
  constructor
  · intro h
    have := List.intercalate_splitOn (xs := slice b p.toNat b.data.size) lf
    rw [h] at this
    simp only [List.intercalate_singleton] at this
    have hl := congrArg List.length this
    rw [slice_length (le_refl _)] at hl
    simp at hl
    exact UInt64.toNat_inj.mp (by omega)
  · intro h
    rw [h, hsz, slice_self]
    rfl

end Demos.Rcv.ReadProgram
