module

public import Demos.ManifestCheck.Program
public import Demos.ManifestCheck.Spec
public import LeanExe.Dialect.BytesLemmas
public import LeanExe.Dialect.Lemmas

@[expose] public section

/-! The pure core equals its specification: `parse_eq`, `hexMatches_eq`, and `render_eq`, each for a
byte string whose size leaves room for the program's positions below `2^64`.

`hexValue_eq` reads `hexValue` through `isHex` and `hexDigit`, and `loop_and` writes a loop that
ands a test over the indices as `List.all`.  `parse_eq` follows the lines with `tupleStep`, the step
of `parseStep` on a state of three parts, which `parseStep` computes on the state's encoding in one
array (`parseStep_enc`).  `tupleStep` keeps its state at a byte other than a newline (`plain_step`),
and at the newline or the end that closes a line it adds the line's positions and the test of its
format (`close_step`, `lineOk_eq`).  `parse_from` proves by strong induction on the positions that
remain that the loop from a position inside a line adds the positions of the lines that `linesFrom`
gives for the pieces from the line's start, split at newlines. -/

namespace Demos.ManifestCheck

open LeanExe Library.Hashing.Words

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

/-! ## Hex digits and loops -/

theorem hexValue_aux : ∀ n, n < 256 → hexValue (UInt8.ofNat n) =
    if isHex (UInt8.ofNat n).toUInt64 then some (hexDigit (UInt8.ofNat n).toUInt64).toNat
    else none := by
  decide +kernel

/-- `isHex` tests for a hex digit, and `hexDigit` gives its value. -/
theorem hexValue_eq (b : UInt8) :
    hexValue b = if isHex b.toUInt64 then some (hexDigit b.toUInt64).toNat else none := by
  have := hexValue_aux b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

theorem isHex_eq (b : UInt8) : isHex b.toUInt64 = (hexValue b).isSome := by
  rw [hexValue_eq]
  split <;> simp_all

/-- A comparison of `hexValue` with a value is the program's test of a digit and its value. -/
theorem hexValue_beq (b : UInt8) (v : Nat) :
    (hexValue b == some v) = (isHex b.toUInt64 && (hexDigit b.toUInt64).toNat == v) := by
  rw [hexValue_eq]
  split <;> simp_all

/-- A loop that ands a test over the indices below `n` is the test of every index. -/
theorem loop_and (n : UInt64) (g : UInt64 → Bool) :
    LeanExe.loop n true (fun k ok => ok && g k) =
      (List.range n.toNat).all fun k => g (UInt64.ofNat k) := by
  unfold LeanExe.loop
  generalize n.toNat = m
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.fold_succ, ih, List.range_succ, List.all_append]; simp

theorem all_range_congr {n : Nat} {f g : Nat → Bool} (h : ∀ k, k < n → f k = g k) :
    (List.range n).all f = (List.range n).all g := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro hf k hk
    rw [← h k (List.mem_range.mp hk)]
    exact hf k hk
  · intro hg k hk
    rw [h k (List.mem_range.mp hk)]
    exact hg k hk

theorem beq_toNat (x y : UInt64) : (x == y) = (x.toNat == y.toNat) := by
  by_cases h : x = y
  · subst h
    simp
  · have : x.toNat ≠ y.toNat := fun e => h (UInt64.toNat_inj.mp e)
    simp [h, this]

theorem toUInt64_beq (b c : UInt8) : (b.toUInt64 == c.toUInt64) = (b == c) := by
  by_cases h : b = c
  · subst h
    simp
  · have : b.toUInt64 ≠ c.toUInt64 := fun e => h (UInt8.toUInt64_inj.mp e)
    simp [h, this]

/-! ## `render` -/

/-- The bytes that follow the name in an output line. -/
def suffixList (ok : Bool) : List UInt8 :=
  if ok then [58, 32, 79, 75, 10] else [58, 32, 70, 65, 73, 76, 69, 68, 10]

theorem okBytes : (": OK" : String).toUTF8.data.toList = [58, 32, 79, 75] := by
  decide +kernel

theorem failedBytes :
    (": FAILED" : String).toUTF8.data.toList = [58, 32, 70, 65, 73, 76, 69, 68] := by
  decide +kernel

theorem renderSpec_eq (name : Bytes) (ok : Bool) :
    renderSpec (name, ok) = ⟨⟨(name.data.data.toList ++ suffixList ok).toArray⟩⟩ := by
  cases ok
  · show (⟨⟨(name.data.data.toList ++ (": FAILED" : String).toUTF8.data.toList ++
        [10]).toArray⟩⟩ : Bytes) = _
    rw [failedBytes, List.append_assoc]
    rfl
  · show (⟨⟨(name.data.data.toList ++ (": OK" : String).toUTF8.data.toList ++
        [10]).toArray⟩⟩ : Bytes) = _
    rw [okBytes, List.append_assoc]
    rfl

theorem suffixByte_eq (ok : Bool) (j : Nat) (hj : j < (suffixList ok).length) :
    (suffixByte ok (UInt64.ofNat j)).toUInt8 = (suffixList ok)[j] := by
  cases ok
  · simp only [suffixList, Bool.false_eq_true, ↓reduceIte, List.length_cons,
      List.length_nil] at hj ⊢
    interval_cases j <;> rfl
  · simp only [suffixList, ↓reduceIte, List.length_cons, List.length_nil] at hj ⊢
    interval_cases j <;> rfl

/-- `render` writes the name's bytes and the bytes of `: OK` or `: FAILED` and a newline. -/
theorem render_eq (name : Bytes) (ok : Bool) (hn : name.data.size + 9 < 2 ^ 64) :
    render name ok = renderSpec (name, ok) := by
  rw [renderSpec_eq]
  have hs : name.size.toNat = name.data.size := Bytes.size_toNat name (by omega)
  have hlen : (suffixList ok).length = (if ok then (5 : UInt64) else 9).toNat := by
    cases ok <;> rfl
  have hcount : (name.size + (if ok then (5 : UInt64) else 9)).toNat =
      name.data.size + (suffixList ok).length := by
    rw [UInt64.toNat_add, hs, hlen]
    have : (if ok then (5 : UInt64) else 9).toNat ≤ 9 := by cases ok <;> decide
    omega
  unfold render Bytes.build
  dsimp only
  congr 2
  apply Array.ext
  · rw [Array.size_ofFn, List.size_toArray, List.length_append, Array.length_toList,
      ByteArray.size_data, hcount]
  · intro i h1 h2
    rw [Array.getElem_ofFn, List.getElem_toArray]
    have hi : i < name.data.size + (suffixList ok).length := by
      rw [Array.size_ofFn, hcount] at h1
      exact h1
    have hsl : (suffixList ok).length ≤ 9 := by cases ok <;> decide
    have hi64 : i < 2 ^ 64 := by omega
    by_cases hlt : i < name.data.size
    · have hc : (UInt64.ofNat i < name.size) = True := by
        simp only [eq_iff_iff, iff_true]
        rw [UInt64.lt_iff_toNat_lt, toNat_ofNat hi64, hs]
        exact hlt
      simp only [hc, ↓reduceIte]
      rw [List.getElem_append_left (by rw [Array.length_toList]; exact hlt), Bytes.get_eq_get!,
        toNat_ofNat hi64, Bytes.get!_of_lt _ hlt, Array.getElem_toList]
      simp only [UInt8.toUInt8_toUInt64]
      rfl
    · have hc : (UInt64.ofNat i < name.size) = False := by
        simp only [eq_iff_iff, iff_false]
        rw [UInt64.lt_iff_toNat_lt, toNat_ofNat hi64, hs]
        exact hlt
      simp only [hc, ↓reduceIte]
      have hsub : UInt64.ofNat i - name.size = UInt64.ofNat (i - name.data.size) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, toNat_ofNat hi64, hs]; omega),
          toNat_ofNat hi64, hs, toNat_ofNat (by omega)]
      rw [hsub, List.getElem_append_right (by rw [Array.length_toList, ByteArray.size_data]; omega)]
      simp only [Array.length_toList, ByteArray.size_data]
      exact suffixByte_eq ok _ (by omega)

/-! ## `hexMatches` -/

theorem and255 (x : UInt64) : x &&& 255 = x.toUInt8.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8,
    show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- `digestByte` reads byte `k` of the digest. -/
theorem digestByte_eq (d : Words4) (k : Nat) (hk : k < 32) :
    digestByte d (UInt64.ofNat k) = ((d.bytes 32)[k]!).toUInt64 := by
  have hkn : (UInt64.ofNat k).toNat = k := toNat_ofNat (by omega)
  have hsh : (UInt64.ofNat k &&& 7) <<< 3 = (8 * (k % 8)).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, hkn,
      show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      show (3 : UInt64).toNat % 64 = 3 from rfl, Nat.shiftLeft_eq, Nat.toUInt64_eq,
      toNat_ofNat (by omega)]
    have : k % 2 ^ 3 * 2 ^ 3 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this]
    omega
  have hbyte : (d.bytes 32)[k]! = Library.Bytes.byteAt #[d.w0, d.w1, d.w2, d.w3] k := by
    rw [getElem!_pos (d.bytes 32) k hk, Words4.bytes, Vector.getElem_ofFn]
  have hword : (if UInt64.ofNat k < 8 then d.w0 else if UInt64.ofNat k < 16 then d.w1
      else if UInt64.ofNat k < 24 then d.w2 else d.w3) = #[d.w0, d.w1, d.w2, d.w3][k / 8]! := by
    have h8 : (UInt64.ofNat k < 8) = (k < 8) := by
      rw [UInt64.lt_iff_toNat_lt, hkn]; rfl
    have h16 : (UInt64.ofNat k < 16) = (k < 16) := by
      rw [UInt64.lt_iff_toNat_lt, hkn]; rfl
    have h24 : (UInt64.ofNat k < 24) = (k < 24) := by
      rw [UInt64.lt_iff_toNat_lt, hkn]; rfl
    simp only [h8, h16, h24]
    rcases (show k < 8 ∨ (8 ≤ k ∧ k < 16) ∨ (16 ≤ k ∧ k < 24) ∨ 24 ≤ k by omega)
      with h | h | h | h
    · rw [if_pos h, show k / 8 = 0 by omega]; rfl
    · rw [if_neg (by omega), if_pos h.2, show k / 8 = 1 by omega]; rfl
    · rw [if_neg (by omega), if_neg (by omega), if_pos h.2, show k / 8 = 2 by omega]; rfl
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show k / 8 = 3 by omega]; rfl
  unfold digestByte
  dsimp only
  rw [and255, hsh, hbyte, hword]
  rfl

theorem shr4_toNat (b : UInt8) : (b.toUInt64 >>> 4).toNat = b.toNat / 16 := by
  rw [UInt64.toNat_shiftRight, UInt8.toNat_toUInt64]
  simp [Nat.shiftRight_eq_div_pow]

theorem and15_toNat (b : UInt8) : (b.toUInt64 &&& 15).toNat = b.toNat % 16 := by
  rw [UInt64.toNat_and, UInt8.toNat_toUInt64,
    show (15 : UInt64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- `hexMatches` compares the 64 bytes from `start` with the digest's hex digits, for a manifest
of fewer than `2^64` bytes. -/
theorem hexMatches_eq (m : Bytes) (start : UInt64) (d : Words4) (hm : m.data.size < 2 ^ 64) :
    hexMatches m start d = hexMatchesSpec (m, start, d) := by
  have hs : m.size.toNat = m.data.size := Bytes.size_toNat m hm
  have hlen : m.data.data.toList.length = m.data.size := by simp
  unfold hexMatches hexMatchesSpec
  dsimp only
  split
  · rename_i hout
    have past : m.data.size ≤ start.toNat + 2 * 31 + 1 := by
      by_cases hsmall : m.data.size < 64
      · omega
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at hout
        have h64 : ¬ m.size < 64 := by
          rw [UInt64.lt_iff_toNat_lt, hs]
          simpa using hsmall
        rcases hout with h | h
        · exact absurd h h64
        · rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le, hs]; simp only [UInt64.reduceToNat]; omega), hs] at h
          simp only [UInt64.reduceToNat] at h
          omega
    have hnone : m.data.data.toList.getD (start.toNat + 2 * 31 + 1) 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; exact past)]
      rfl
    have hzero : hexValue 0 = none := by decide
    symm
    rw [List.all_eq_false]
    refine ⟨31, List.mem_range.mpr (by decide), ?_⟩
    rw [hnone, hzero]
    simp
  · rename_i hin
    have inside : start.toNat + 64 ≤ m.data.size := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hin
      obtain ⟨h1, h2⟩ := hin
      rw [UInt64.lt_iff_toNat_lt, hs] at h1
      simp only [UInt64.reduceToNat] at h1
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, hs]; simp only [UInt64.reduceToNat]; omega), hs] at h2
      simp only [UInt64.reduceToNat] at h2
      omega
    rw [loop_and]
    simp only [UInt64.reduceToNat]
    apply all_range_congr
    intro k hk32
    have p0 : (start + 2 * UInt64.ofNat k).toNat = start.toNat + 2 * k := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, toNat_ofNat (show k < 2 ^ 64 by omega)]
      simp only [UInt64.reduceToNat]
      omega
    have p1 : (start + 2 * UInt64.ofNat k + 1).toNat = start.toNat + 2 * k + 1 := by
      rw [UInt64.toNat_add, p0]
      simp only [UInt64.reduceToNat]
      omega
    rw [Bytes.get_eq_getD, Bytes.get_eq_getD, p0, p1, digestByte_eq d k hk32, beq_toNat,
      beq_toNat, shr4_toNat, and15_toNat, hexValue_beq, hexValue_beq]
    cases isHex (m.data.data.toList.getD (start.toNat + 2 * k) 0).toUInt64 <;>
      cases isHex (m.data.data.toList.getD (start.toNat + 2 * k + 1) 0).toUInt64 <;>
      simp [Bool.and_comm, Bool.and_left_comm]

/-! ## `parse` -/

/-- The positions of `ls` as `parseSpec` writes them. -/
def spanWords (ls : List (Nat × List UInt8)) : List UInt64 :=
  ls.flatMap fun l => [UInt64.ofNat l.1, UInt64.ofNat (l.1 + l.2.length)]

theorem spanWords_cons (s : Nat) (p : List UInt8) (ls : List (Nat × List UInt8)) :
    spanWords ((s, p) :: ls) = UInt64.ofNat s :: UInt64.ofNat (s + p.length) :: spanWords ls :=
  rfl

theorem spanWords_nil : spanWords [] = [] := rfl

theorem spanWords_length (ls : List (Nat × List UInt8)) :
    (spanWords ls).length = 2 * ls.length := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [spanWords, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem fold_range {α : Type} (k : Nat) (g : Nat → α → α) (init : α) :
    Nat.fold k (fun i _ s => g i s) init = (List.range k).foldl (fun s i => g i s) init := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.fold_succ, ih, List.range_succ, List.foldl_append]; rfl

section Parse

variable (m : Bytes)

/-- The step of `parseStep` on a state of three parts: the positions of the lines found so far,
the position where the current line starts, and whether every line so far is in the format. -/
def tupleStep (st : Array UInt64 × UInt64 × Bool) (i : UInt64) : Array UInt64 × UInt64 × Bool :=
  if i == m.size || m.get i == 10 then
    if st.2.1 < i then ((st.1.push st.2.1).push i, i + 1, st.2.2 && lineOk m st.2.1 i)
    else (st.1, i + 1, st.2.2)
  else st

/-- The state of three parts in one array, as `parseStep` holds it. -/
def enc (st : Array UInt64 × UInt64 × Bool) : Array UInt64 :=
  #[st.2.1, if st.2.2 then 1 else 0] ++ st.1

theorem parseStep_enc (st : Array UInt64 × UInt64 × Bool) (i : UInt64) :
    parseStep m (enc st) i = enc (tupleStep m st i) := by
  obtain ⟨acc, s, ok⟩ := st
  unfold parseStep tupleStep
  simp only [UInt64.reduceToNat]
  split
  · have h0 : (enc (acc, s, ok))[0]! = s := by
      simp [enc]
    have h1 : (enc (acc, s, ok))[1]! = if ok then 1 else 0 := by
      have hlt : 1 < (enc (acc, s, ok)).size := by simp [enc]; omega
      rw [getElem!_pos _ 1 hlt]
      simp [enc, Array.getElem_append_left]
    simp only [h0, h1]
    split
    · have hok : ((if ok then (1 : UInt64) else 0) == 1 && lineOk m s i) =
          (ok && lineOk m s i) := by
        cases ok <;> simp
      rw [hok]
      apply Array.toList_inj.mp
      simp [enc, Array.toList_setIfInBounds]
    · apply Array.toList_inj.mp
      simp [enc, Array.toList_setIfInBounds]
  · rfl

theorem loop_enc (n : Nat) (init : Array UInt64 × UInt64 × Bool) :
    Nat.fold n (fun i _ st => parseStep m st (UInt64.ofNat i)) (enc init) =
      enc (Nat.fold n (fun i _ st => tupleStep m st (UInt64.ofNat i)) init) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.fold_succ, Nat.fold_succ, ih, parseStep_enc]

/-- At a position that holds a byte other than a newline, `tupleStep` keeps its state. -/
theorem plain_step (st : Array UInt64 × UInt64 × Bool) (i : Nat) (hi : i < m.data.size)
    (hn : m.data.size < 2 ^ 64) (hb : m.data.data.toList.getD i 0 ≠ 10) :
    tupleStep m st (UInt64.ofNat i) = st := by
  have hs : m.size.toNat = m.data.size := Bytes.size_toNat m hn
  have hne : (UInt64.ofNat i == m.size) = false := by
    rw [beq_toNat, toNat_ofNat (by omega), hs]
    simp
    omega
  have hget : (m.get (UInt64.ofNat i) == 10) = false := by
    rw [Bytes.get_eq_getD, toNat_ofNat (by omega),
      show (10 : UInt64) = (10 : UInt8).toUInt64 from rfl, toUInt64_beq]
    simpa using hb
  unfold tupleStep
  rw [hne, hget]
  rfl

/-- At the newline or the end that closes the line from `s`, `tupleStep` adds the line's positions
and the test of its format when the line has a byte. -/
theorem close_step (acc : Array UInt64) (ok : Bool) (s i : Nat) (hsi : s ≤ i)
    (hi : i ≤ m.data.size) (hn : m.data.size + 1 < 2 ^ 64)
    (hb : i = m.data.size ∨ m.data.data.toList.getD i 0 = 10) :
    tupleStep m (acc, UInt64.ofNat s, ok) (UInt64.ofNat i) =
      if s < i then ((acc.push (UInt64.ofNat s)).push (UInt64.ofNat i), UInt64.ofNat (i + 1),
        ok && lineOk m (UInt64.ofNat s) (UInt64.ofNat i))
      else (acc, UInt64.ofNat (i + 1), ok) := by
  have hs : m.size.toNat = m.data.size := Bytes.size_toNat m (by omega)
  have hcond : (UInt64.ofNat i == m.size || m.get (UInt64.ofNat i) == 10) = true := by
    rcases hb with h | h
    · rw [beq_toNat, toNat_ofNat (by omega), hs, h]
      simp
    · rw [Bytes.get_eq_getD, toNat_ofNat (by omega), h]
      simp
  have hlt : (UInt64.ofNat s < UInt64.ofNat i) = (s < i) := by
    rw [UInt64.lt_iff_toNat_lt, toNat_ofNat (by omega),
      toNat_ofNat (by omega)]
  have hsucc : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, toNat_ofNat (by omega),
      toNat_ofNat (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  unfold tupleStep
  rw [hcond]
  simp only [↓reduceIte, hlt, hsucc]

/-- `lineOk` tests whether the bytes from `s` to `i` are a line in the format. -/
theorem lineOk_iff (s i : Nat) (hsi : s ≤ i) (hi : i ≤ m.data.size)
    (hn : m.data.size + 68 < 2 ^ 64) :
    lineOk m (UInt64.ofNat s) (UInt64.ofNat i) = true ↔
      WellFormed ((m.data.data.toList.drop s).take (i - s)) := by
  have hlen : m.data.data.toList.length = m.data.size := by simp
  generalize hline : (m.data.data.toList.drop s).take (i - s) = line
  have hlinelen : line.length = i - s := by
    rw [← hline]
    simp only [List.length_take, List.length_drop, hlen]
    omega
  have hat : ∀ k, k < i - s → line.getD k 0 = m.data.data.toList.getD (s + k) 0 := by
    intro k hk
    rw [← hline, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hk, List.getElem?_drop]
  have pos : ∀ k, k ≤ 67 → s + k ≤ i →
      (UInt64.ofNat s + UInt64.ofNat k).toNat = s + k := by
    intro k hk hki
    rw [UInt64.toNat_add, toNat_ofNat (by omega), toNat_ofNat (by omega)]
    omega
  unfold lineOk
  by_cases hshort : s + 67 ≤ i
  · have h67 : decide (UInt64.ofNat s + 67 ≤ UInt64.ofNat i) = true := by
      rw [decide_eq_true_iff, UInt64.le_iff_toNat_le,
        show (67 : UInt64) = UInt64.ofNat 67 from rfl, pos 67 le_rfl hshort,
        toNat_ofNat (by omega)]
      exact hshort
    have g64 : m.get (UInt64.ofNat s + 64) = (line.getD 64 0).toUInt64 := by
      rw [Bytes.get_eq_getD, show (64 : UInt64) = UInt64.ofNat 64 from rfl,
        pos 64 (by omega) (by omega), hat 64 (by omega)]
    have g65 : m.get (UInt64.ofNat s + 65) = (line.getD 65 0).toUInt64 := by
      rw [Bytes.get_eq_getD, show (65 : UInt64) = UInt64.ofNat 65 from rfl,
        pos 65 (by omega) (by omega), hat 65 (by omega)]
    have hhex : (∀ k, k < 64 → isHex (m.get (UInt64.ofNat s + UInt64.ofNat k)) = true) ↔
        ∀ k, k < 64 → (hexValue (line.getD k 0)).isSome = true := by
      constructor
      · intro h k hk
        have := h k hk
        rwa [Bytes.get_eq_getD, pos k (by omega) (by omega), ← hat k (by omega),
          isHex_eq] at this
      · intro h k hk
        rw [Bytes.get_eq_getD, pos k (by omega) (by omega), ← hat k (by omega), isHex_eq]
        exact h k hk
    rw [h67, loop_and, g64, g65, show (32 : UInt64) = (32 : UInt8).toUInt64 from rfl,
      show (42 : UInt64) = (42 : UInt8).toUInt64 from rfl, toUInt64_beq, toUInt64_beq,
      toUInt64_beq]
    simp only [Bool.true_and, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
      List.mem_range, UInt64.reduceToNat, beq_iff_eq]
    rw [hhex]
    constructor
    · rintro ⟨⟨hh, h64⟩, h65⟩
      exact ⟨by omega, hh, h64, h65⟩
    · rintro ⟨_, hh, h64, h65⟩
      exact ⟨⟨hh, h64⟩, h65⟩
  · have h67 : decide (UInt64.ofNat s + 67 ≤ UInt64.ofNat i) = false := by
      rw [decide_eq_false_iff_not, UInt64.le_iff_toNat_le,
        show (67 : UInt64) = UInt64.ofNat 67 from rfl, UInt64.toNat_add, toNat_ofNat (by omega),
        toNat_ofNat (by omega), toNat_ofNat (by omega)]
      omega
    rw [h67]
    simp only [Bool.false_and, Bool.false_eq_true, false_iff]
    intro wf
    exact hshort (by have := wf.1; omega)

theorem lineOk_eq (s i : Nat) (hsi : s ≤ i) (hi : i ≤ m.data.size)
    (hn : m.data.size + 68 < 2 ^ 64) :
    lineOk m (UInt64.ofNat s) (UInt64.ofNat i) =
      decide (WellFormed ((m.data.data.toList.drop s).take (i - s))) := by
  rw [Bool.eq_iff_iff, lineOk_iff m s i hsi hi hn, decide_eq_true_iff]

/-- From a position `i` inside the line that starts at `s`, every byte before `i` of which is not
a newline, the loop adds the positions of the lines of the pieces from `s` and the tests of their
format, and ends with the line start after the last position. -/
theorem parse_from (hn : m.data.size + 68 < 2 ^ 64) :
    ∀ k i s (acc : Array UInt64) (ok : Bool), m.data.size + 1 - i = k → s ≤ i →
      i ≤ m.data.size → (∀ j, s ≤ j → j < i → m.data.data.toList.getD j 0 ≠ 10) →
      ((List.range' i (m.data.size + 1 - i)).foldl
        (fun st j => tupleStep m st (UInt64.ofNat j)) (acc, UInt64.ofNat s, ok)).1.toList =
          acc.toList ++ spanWords (linesFrom s ((m.data.data.toList.drop s).splitOn 10)) ∧
      ((List.range' i (m.data.size + 1 - i)).foldl
        (fun st j => tupleStep m st (UInt64.ofNat j)) (acc, UInt64.ofNat s, ok)).2.2 =
          (ok && (linesFrom s ((m.data.data.toList.drop s).splitOn 10)).all
            fun l => decide (WellFormed l.2)) ∧
      (linesFrom s ((m.data.data.toList.drop s).splitOn 10)).length ≤ m.data.size + 1 - s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro i s acc ok hk hsi hi plain
  have hlen : m.data.data.toList.length = m.data.size := by simp
  have hpre : m.data.data.toList.drop s =
      (m.data.data.toList.drop s).take (i - s) ++ m.data.data.toList.drop i := by
    conv_lhs => rw [← List.take_append_drop (i - s) (m.data.data.toList.drop s)]
    rw [List.drop_drop, show s + (i - s) = i by omega]
  have hnot : (10 : UInt8) ∉ (m.data.data.toList.drop s).take (i - s) := by
    intro hmem
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hmem
    have hjl : j < i - s := by
      simp only [List.length_take, List.length_drop, hlen] at hj
      omega
    apply plain (s + j) (by omega) (by omega)
    rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop, ← List.getElem?_take_of_lt hjl,
      List.getElem?_eq_getElem hj, hjv]
    rfl
  have hok := lineOk_eq m s i hsi hi hn
  generalize hp : (m.data.data.toList.drop s).take (i - s) = p at hpre hnot hok
  have hplen : p.length = i - s := by
    rw [← hp]
    simp only [List.length_take, List.length_drop, hlen]
    omega
  by_cases hend : i = m.data.size
  · -- the end closes the last line
    subst hend
    have hrest : m.data.data.toList.drop m.data.size = [] := List.drop_eq_nil_of_le (by omega)
    rw [hrest, List.append_nil] at hpre
    rw [hpre, List.splitOn_eq_singleton hnot]
    rw [show m.data.size + 1 - m.data.size = 1 by omega, List.range'_one, List.foldl_cons,
      List.foldl_nil, close_step m acc ok s _ hsi le_rfl (by omega) (.inl rfl)]
    by_cases hsl : s < m.data.size
    · have hpne : p ≠ [] := by
        intro e
        rw [e] at hplen
        simp at hplen
        omega
      have hlines : linesFrom s [p] = [(s, p)] := by simp [linesFrom, hpne]
      rw [hlines]
      simp only [hsl, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · rw [Array.toList_push, Array.toList_push, spanWords_cons, spanWords_nil, hplen,
          show s + (m.data.size - s) = m.data.size by omega]
        simp
      · rw [hok]
        simp
      · simp only [List.length_cons, List.length_nil]
        omega
    · have hpe : p = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hlines : linesFrom s [p] = [] := by simp [linesFrom, hpe]
      rw [hlines]
      simp only [hsl, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · simp [spanWords_nil]
      · simp
      · simp
  · have hil : i < m.data.size := by omega
    have hrange : List.range' i (m.data.size + 1 - i) =
        i :: List.range' (i + 1) (m.data.size + 1 - (i + 1)) := by
      rw [show m.data.size + 1 - i = (m.data.size + 1 - (i + 1)) + 1 by omega, List.range'_succ]
    have hdrop : m.data.data.toList.drop i =
        m.data.data.toList.getD i 0 :: m.data.data.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    rw [hrange, List.foldl_cons]
    by_cases hnl : m.data.data.toList.getD i 0 = 10
    · -- a newline closes the line
      rw [close_step m acc ok s i hsi hil.le (by omega) (.inr hnl)]
      rw [hdrop, hnl] at hpre
      rw [hpre, List.splitOn_append_cons_self_of_not_mem hnot]
      have hnext := ih (m.data.size + 1 - (i + 1)) (by omega) (i + 1) (i + 1)
      by_cases hsl : s < i
      · have hpne : p ≠ [] := by
          intro e
          rw [e] at hplen
          simp at hplen
          omega
        have hlines : linesFrom s (p :: (m.data.data.toList.drop (i + 1)).splitOn 10) =
            (s, p) :: linesFrom (i + 1) ((m.data.data.toList.drop (i + 1)).splitOn 10) := by
          simp only [linesFrom, hpne, ↓reduceIte, List.singleton_append, hplen,
            show s + (i - s) + 1 = i + 1 by omega]
        rw [hlines]
        simp only [hsl, ↓reduceIte]
        obtain ⟨h1, h3, h4⟩ := hnext ((acc.push (UInt64.ofNat s)).push (UInt64.ofNat i))
          (ok && lineOk m (UInt64.ofNat s) (UInt64.ofNat i)) rfl le_rfl (by omega)
          (fun j h1 h2 => absurd h2 (by omega))
        refine ⟨?_, ?_, ?_⟩
        · rw [h1, Array.toList_push, Array.toList_push, spanWords_cons, hplen,
            show s + (i - s) = i by omega]
          simp
        · rw [h3, hok]
          simp [Bool.and_assoc]
        · simp only [List.length_cons]
          omega
      · have hpe : p = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hsi' : s = i := by omega
        subst hsi'
        have hlines : linesFrom s (p :: (m.data.data.toList.drop (s + 1)).splitOn 10) =
            linesFrom (s + 1) ((m.data.data.toList.drop (s + 1)).splitOn 10) := by
          simp only [linesFrom, hpe, ↓reduceIte, List.nil_append, List.length_nil,
            Nat.add_zero]
        rw [hlines]
        simp only [hsl, ↓reduceIte]
        obtain ⟨h1, h3, h4⟩ := hnext acc ok rfl le_rfl (by omega)
          (fun j h1 h2 => absurd h2 (by omega))
        exact ⟨h1, h3, by omega⟩
    · -- a byte of the line
      rw [plain_step m _ i hil (by omega) hnl]
      exact ih (m.data.size + 1 - (i + 1)) (by omega) (i + 1) s acc ok rfl (by omega)
        (by omega) (fun j h1 h2 => by
          by_cases hj : j < i
          · exact plain j h1 hj
          · rw [show j = i by omega]; exact hnl)

end Parse

/-- `parse` gives the positions of the manifest's lines, or the empty array for a refused
manifest, for a manifest of fewer than `2^62` bytes. -/
theorem parse_eq (m : Bytes) (hn : m.data.size < 2 ^ 62) : parse m = parseSpec m := by
  have hs : m.size.toNat = m.data.size := Bytes.size_toNat m (by omega)
  have hcount : (m.size + 1).toNat = m.data.size + 1 := by
    rw [UInt64.toNat_add, hs]
    simp only [UInt64.reduceToNat]
    omega
  obtain ⟨h1, h3, h4⟩ := parse_from m (by omega) (m.data.size + 1) 0 0 #[] true
    (by omega) (Nat.zero_le _) (Nat.zero_le _) (fun j h1 h2 => absurd h2 (by omega))
  simp only [Nat.sub_zero, List.drop_zero, show UInt64.ofNat 0 = 0 from rfl] at h1 h3 h4
  have hinit : (#[0, 1] : Array UInt64) = enc (#[], 0, true) := rfl
  unfold parse parseSpec
  dsimp only
  simp only [UInt64.reduceToNat]
  rw [LeanExe.loop, hcount, hinit, loop_enc, fold_range (m.data.size + 1)
    (fun i st => tupleStep m st (UInt64.ofNat i)), List.range_eq_range']
  generalize (List.range' 0 (m.data.size + 1)).foldl
    (fun st j => tupleStep m st (UInt64.ofNat j)) (#[], 0, true) = st at h1 h3 h4
  rw [show linesFrom 0 (m.data.data.toList.splitOn 10) = lines m.data.data.toList from rfl]
    at h1 h3 h4
  generalize lines m.data.data.toList = ls at h1 h3 h4 ⊢
  simp only [List.nil_append] at h1
  obtain ⟨acc, s, ok⟩ := st
  dsimp only at h1 h3
  simp only [Bool.true_and] at h3
  subst h3
  have hst : acc = (spanWords ls).toArray := by
    apply Array.toList_inj.mp
    rw [h1, List.toList_toArray]
  subst hst
  have hlen : (spanWords ls).length = 2 * ls.length := spanWords_length ls
  have hsmall : 2 * ls.length + 2 < 2 ^ 64 := by omega
  have hsize : (enc ((spanWords ls).toArray, s, ls.all fun l => decide (WellFormed l.2))).size =
      2 * ls.length + 2 := by
    simp only [enc, Array.size_append, List.size_toArray, hlen]
    simp
    omega
  have hsizeW : (enc ((spanWords ls).toArray, s,
      ls.all fun l => decide (WellFormed l.2))).size.toUInt64 =
        UInt64.ofNat (2 * ls.length + 2) := by
    rw [hsize]
  have hne : (UInt64.ofNat (2 * ls.length + 2) != 2) = decide (ls ≠ []) := by
    by_cases he : ls = []
    · subst he
      rfl
    · have hpos : 0 < ls.length := List.length_pos_iff.mpr he
      have hne : UInt64.ofNat (2 * ls.length + 2) ≠ 2 := by
        intro e
        have := congrArg UInt64.toNat e
        rw [toNat_ofNat hsmall] at this
        simp only [UInt64.reduceToNat] at this
        omega
      rw [show (UInt64.ofNat (2 * ls.length + 2) != 2) = true from bne_iff_ne.mpr hne,
        decide_eq_true he]
  have hflag : ((enc ((spanWords ls).toArray, s,
      ls.all fun l => decide (WellFormed l.2)))[1]! == 1) =
      (ls.all fun l => decide (WellFormed l.2)) := by
    cases (ls.all fun l => decide (WellFormed l.2)) <;> simp [enc]
  simp only [hsizeW, hne, hflag]
  by_cases hgood : ls ≠ [] ∧ ∀ l ∈ ls, WellFormed l.2
  · rw [if_pos hgood]
    have hall : (ls.all fun l => decide (WellFormed l.2)) = true := by
      rw [List.all_eq_true]
      intro l hl
      exact decide_eq_true (hgood.2 l hl)
    rw [hall, decide_eq_true hgood.1]
    rw [hall] at hsize
    simp only [Bool.and_self, ↓reduceIte]
    have hcount2 : (UInt64.ofNat (2 * ls.length + 2) - 2).toNat = (spanWords ls).length := by
      rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, toNat_ofNat hsmall]; simp), toNat_ofNat hsmall, hlen]
      simp
    apply Array.ext
    · rw [LeanExe.Dialect.build_size, hcount2, List.size_toArray]
      rfl
    · intro k hk1 hk2
      show _ = ((spanWords ls).toArray)[k]
      rw [LeanExe.Dialect.build_size, hcount2] at hk1
      rw [show (LeanExe.build (UInt64.ofNat (2 * ls.length + 2) - 2) fun k =>
          (enc ((spanWords ls).toArray, s, true))[(k + 2).toNat]!)[k] =
          (LeanExe.build (UInt64.ofNat (2 * ls.length + 2) - 2) fun k =>
          (enc ((spanWords ls).toArray, s, true))[(k + 2).toNat]!)[k]! from
          (getElem!_pos _ k _).symm,
        LeanExe.Dialect.build_get (by rw [hcount2]; exact hk1)]
      have hk2' : (UInt64.ofNat k + 2).toNat = k + 2 := by
        rw [UInt64.toNat_add, toNat_ofNat (by omega)]
        simp only [UInt64.reduceToNat]
        omega
      rw [hk2', getElem!_pos _ (k + 2) (by rw [hsize]; omega)]
      simp [enc, Array.getElem_append_right]
      rfl
  · rw [if_neg hgood]
    have hfalse : ((ls.all fun l => decide (WellFormed l.2)) && decide (ls ≠ [])) = false := by
      by_contra hc
      simp only [Bool.not_eq_false, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq] at hc
      exact hgood ⟨hc.2, hc.1⟩
    rw [hfalse]
    rfl

/-- The array that `parse`'s loop builds holds two words and two words for each line, and a
manifest of `n` bytes has at most `n + 1` lines. -/
theorem parse_loop_size (m : Bytes) (hn : m.data.size < 2 ^ 62) :
    2 ≤ (LeanExe.loop (m.size + 1) #[0, 1] fun i st => parseStep m st i).size ∧
      (LeanExe.loop (m.size + 1) #[0, 1] fun i st => parseStep m st i).size ≤
        2 * m.data.size + 4 := by
  have hs : m.size.toNat = m.data.size := Bytes.size_toNat m (by omega)
  have hcount : (m.size + 1).toNat = m.data.size + 1 := by
    rw [UInt64.toNat_add, hs]
    simp only [UInt64.reduceToNat]
    omega
  obtain ⟨h1, -, h4⟩ := parse_from m (by omega) (m.data.size + 1) 0 0 #[] true
    (by omega) (Nat.zero_le _) (Nat.zero_le _) (fun j h1 h2 => absurd h2 (by omega))
  simp only [Nat.sub_zero, List.drop_zero, show UInt64.ofNat 0 = 0 from rfl] at h1 h4
  have hinit : (#[0, 1] : Array UInt64) = enc (#[], 0, true) := rfl
  rw [LeanExe.loop, hcount, hinit, loop_enc, fold_range (m.data.size + 1)
    (fun i st => tupleStep m st (UInt64.ofNat i)), List.range_eq_range']
  generalize (List.range' 0 (m.data.size + 1)).foldl
    (fun st j => tupleStep m st (UInt64.ofNat j)) (#[], 0, true) = st at h1 h4
  simp only [List.nil_append] at h1
  have hsize : st.1.size = 2 * (linesFrom 0 (m.data.data.toList.splitOn 10)).length := by
    rw [← Array.length_toList, h1, spanWords_length]
  have hst : (enc st).size = 2 + 2 * (linesFrom 0 (m.data.data.toList.splitOn 10)).length := by
    rw [show enc st = #[st.2.1, if st.2.2 then 1 else 0] ++ st.1 from rfl, Array.size_append,
      hsize]
    rfl
  rw [hst]
  constructor <;> omega

end Demos.ManifestCheck
