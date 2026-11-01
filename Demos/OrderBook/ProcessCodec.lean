import Demos.OrderBook.Process
import Demos.OrderBook.Spec
import Demos.StreamFold.Bytes

/-! The little-endian codec of [the process](Process.lean) and the meaning of its byte streams.
`leWords` and `leBytes` state the conversion between bytes and words over byte lists, as sums and
quotients of powers of 256, and `expectedOutput` and `expectedStatus` give the stdout bytes and the
exit status for an input.  The equations show that `wordsOf`, `eventBytes`, and `tailBytes`, which
use shifts and ors, compute these conversions over the bytes of the carry followed by a read. -/

namespace Demos.OrderBook.Process

open LeanExe
open Demos.StreamFold (byteWords byteWords_length byteWords_get_nat byteWords_build_get
  bytes_get_narrow)

/-- The word whose bytes, least significant first, are the first eight elements of `group`, each
taken modulo 256: element `k` contributes its value times `256 ^ k`, and a missing element
contributes 0. -/
def leWord (group : List UInt64) : UInt64 :=
  UInt64.ofNat ((List.range 8).map fun k => (group.getD k 0).toNat % 256 * 256 ^ k).sum

/-- The words of the whole groups of eight bytes of `bytes`, least significant byte first.  A final
group of fewer than eight bytes gives no word. -/
def leWords (bytes : List UInt64) : List UInt64 :=
  (List.range (bytes.length / 8)).map fun j => leWord (bytes.drop (8 * j))

/-- The eight bytes of each word of `words`, least significant byte first. -/
def leBytes (words : List UInt64) : List UInt64 :=
  words.flatMap fun w => (List.range 8).map fun k => UInt64.ofNat (w.toNat / 256 ^ k % 256)

/-- The stdout bytes for the input bytes `input`: the little-endian bytes of the event words of
`Spec.run` from the empty book on the whole words of `input`. -/
def expectedOutput (input : List UInt64) : List UInt64 :=
  leBytes (Spec.encodeAll (Spec.run Spec.empty (leWords input)).2).toList

/-- The exit status for the input bytes `input`: 0 when they fill whole words and 28 otherwise. -/
def expectedStatus (input : List UInt64) : UInt64 :=
  if input.length % 8 = 0 then 0 else 28

theorem ofNat_toNat_small {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

/-! ## Byte lists -/

@[simp] theorem leWords_length (bytes : List UInt64) :
    (leWords bytes).length = bytes.length / 8 := by
  simp [leWords]

theorem leWord_congr {a b : List UInt64} (h : ∀ k < 8, a.getD k 0 = b.getD k 0) :
    leWord a = leWord b := by
  unfold leWord
  congr 2
  apply List.map_congr_left
  intro k hk
  rw [h k (List.mem_range.mp hk)]

/-- The words of two byte lists, the first of whole words, are the words of each in turn. -/
theorem leWords_append {p q : List UInt64} (h : p.length % 8 = 0) :
    leWords (p ++ q) = leWords p ++ leWords q := by
  unfold leWords
  rw [List.length_append, show (p.length + q.length) / 8 = p.length / 8 + q.length / 8 by omega,
    List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    apply leWord_congr
    intro k hk
    rw [List.drop_append_of_le_length (l₁ := p) (l₂ := q) (i := 8 * j) (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left]
    simp only [List.length_drop]
    omega
  · apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    rw [show 8 * (p.length / 8 + j) = p.length + 8 * j by omega, ← List.drop_drop,
      List.drop_append_length]

theorem leWords_short {bytes : List UInt64} (h : bytes.length < 8) : leWords bytes = [] := by
  simp [leWords, Nat.div_eq_of_lt h]

theorem leBytes_append (a b : List UInt64) : leBytes (a ++ b) = leBytes a ++ leBytes b := by
  simp [leBytes, List.flatMap_append]

@[simp] theorem leBytes_length (words : List UInt64) :
    (leBytes words).length = 8 * words.length := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    simp only [leBytes] at ih ⊢
    rw [List.flatMap_cons, List.length_append, ih]
    simp only [List.length_map, List.length_range, List.length_cons]
    omega

theorem leBytes_getElem (words : List UInt64) (i : Nat) (h : i < (leBytes words).length) :
    (leBytes words)[i] =
      UInt64.ofNat ((words[i / 8]'(by simp at h; omega)).toNat / 256 ^ (i % 8) % 256) := by
  induction words generalizing i with
  | nil => simp at h
  | cons w ws ih =>
    have split : leBytes (w :: ws) =
        ((List.range 8).map fun k => UInt64.ofNat (w.toNat / 256 ^ k % 256)) ++ leBytes ws := by
      simp [leBytes]
    have length : ((List.range 8).map fun k => UInt64.ofNat (w.toNat / 256 ^ k % 256)).length = 8 :=
      by simp
    simp only [split]
    by_cases small : i < 8
    · rw [List.getElem_append_left]
      rotate_left
      · rw [length]
        exact small
      · have zero : i / 8 = 0 := Nat.div_eq_of_lt small
        have same : i % 8 = i := Nat.mod_eq_of_lt small
        rw [List.getElem_map, List.getElem_range]
        simp only [zero, same, List.getElem_cons_zero]
    · rw [List.getElem_append_right]
      rotate_left
      · rw [length]
        omega
      · simp only [length]
        rw [ih (i - 8) (by simp at h ⊢; omega)]
        have quotient : i / 8 = (i - 8) / 8 + 1 := by omega
        have remainder : (i - 8) % 8 = i % 8 := by omega
        simp only [quotient, remainder, List.getElem_cons_succ]

/-! ## Bytes of a word and words of bytes -/

theorem byteAt_lt (carry input : Bytes) (i : UInt64) : (byteAt carry input i).toNat < 256 := by
  unfold byteAt
  split
  · exact Bytes.get_toNat_lt _ _
  · exact Bytes.get_toNat_lt _ _

theorem byteAt_narrow (carry input : Bytes) (i : UInt64) :
    (byteAt carry input i).toUInt8.toUInt64 = byteAt carry input i := by
  unfold byteAt
  split
  · exact bytes_get_narrow _ _
  · exact bytes_get_narrow _ _

/-- Byte `r` of a word, by the shift of the code, is the quotient of the word by `256 ^ r` modulo
256. -/
theorem shift_byte (w : UInt64) (r : Nat) (hr : r < 8) :
    (w >>> (8 * UInt64.ofNat r)).toUInt8.toUInt64 = UInt64.ofNat (w.toNat / 256 ^ r % 256) := by
  apply UInt64.toNat_inj.mp
  have shift : (8 * UInt64.ofNat r).toNat % 64 = 8 * r := by
    rw [UInt64.toNat_mul, ofNat_toNat_small (n := r) (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have power : (256 : Nat) ^ r = 2 ^ (8 * r) := by
    rw [Nat.pow_mul]
  rw [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, show (2 : Nat) ^ 8 = 256 from rfl,
    UInt64.toNat_shiftRight, shift, Nat.shiftRight_eq_div_pow,
    ofNat_toNat_small (n := w.toNat / 256 ^ r % 256) (by omega), power]

/-- The or of the bytes `g k`, shifted to byte `k`, over the first `m` bytes, is the sum of
`g k * 256 ^ k`. -/
theorem fold_word (g : UInt64 → UInt64) (hg : ∀ k, (g k).toNat < 256) (m : Nat) (hm : m ≤ 8) :
    (Nat.fold m (fun i _ w => w ||| (g (UInt64.ofNat i) <<< (8 * UInt64.ofNat i))) 0).toNat =
        ((List.range m).map fun k => (g (UInt64.ofNat k)).toNat * 256 ^ k).sum ∧
      ((List.range m).map fun k => (g (UInt64.ofNat k)).toNat * 256 ^ k).sum < 256 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨value, bound⟩ := ih (by omega)
    have shift : (8 * UInt64.ofNat m).toNat % 64 = 8 * m := by
      rw [UInt64.toNat_mul, ofNat_toNat_small (n := m) (by omega)]
      simp only [UInt64.reduceToNat]
      omega
    rw [Nat.fold_succ, List.range_succ, List.map_append, List.sum_append, UInt64.toNat_or,
      UInt64.toNat_shiftLeft, shift, value, Nat.shiftLeft_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    generalize ((List.range m).map fun k => (g (UInt64.ofNat k)).toNat * 256 ^ k).sum = S
      at bound ⊢
    have byte := hg (UInt64.ofNat m)
    generalize (g (UInt64.ofNat m)).toNat = x at byte ⊢
    have power : (256 : Nat) ^ m = 2 ^ (8 * m) := by rw [Nat.pow_mul]
    rw [power] at bound ⊢
    have room : 2 ^ (8 * m) * 256 ≤ 2 ^ 64 := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have positive : 0 < 2 ^ (8 * m) := Nat.two_pow_pos _
    have product : x * 2 ^ (8 * m) ≤ 255 * 2 ^ (8 * m) := Nat.mul_le_mul_right _ (by omega)
    have fits : x * 2 ^ (8 * m) < 2 ^ 64 := by omega
    have orEq : S ||| x * 2 ^ (8 * m) = S + x * 2 ^ (8 * m) := by
      rw [Nat.or_comm, Nat.mul_comm x, ← Nat.two_pow_add_eq_or_of_lt bound x]
      exact Nat.add_comm _ _
    rw [Nat.mod_eq_of_lt fits, orEq, Nat.pow_succ, power]
    exact ⟨rfl, by omega⟩

/-- The loop of `wordsOf` over the bytes of a word is the word of those bytes. -/
theorem loop_byteAt (carry input : Bytes) (j : UInt64) :
    LeanExe.loop 8 0 (fun k w => w ||| (byteAt carry input (8 * j + k) <<< (8 * k))) =
      UInt64.ofNat ((List.range 8).map fun k =>
        (byteAt carry input (8 * j + UInt64.ofNat k)).toNat * 256 ^ k).sum := by
  have facts := fold_word (fun k => byteAt carry input (8 * j + k))
    (fun k => byteAt_lt carry input _) 8 (Nat.le_refl _)
  apply UInt64.toNat_inj.mp
  rw [ofNat_toNat_small (Nat.lt_of_lt_of_le facts.2 (by decide))]
  exact facts.1

/-! ## The code's conversions -/

/-- Byte `i` of the carry followed by the input is element `i` of their byte lists. -/
theorem byteAt_eq (carry input : Bytes) (i : Nat)
    (total : carry.data.size + input.data.size < 2 ^ 64)
    (hi : i < carry.data.size + input.data.size) :
    byteAt carry input (UInt64.ofNat i) =
      (byteWords carry ++ byteWords input)[i]'(by simp; omega) := by
  have carryNat : carry.size.toNat = carry.data.size := Bytes.size_toNat carry (by omega)
  have iNat : (UInt64.ofNat i).toNat = i := ofNat_toNat_small (by omega)
  unfold byteAt
  by_cases inside : i < carry.data.size
  · have test : UInt64.ofNat i < carry.size := by
      rw [UInt64.lt_iff_toNat_lt, iNat, carryNat]
      exact inside
    rw [ite_eq_left test, List.getElem_append_left]
    rotate_left
    · simpa using inside
    · exact (byteWords_get_nat carry (show carry.data.size < 2 ^ 64 by omega) i inside).symm
  · have test : ¬ UInt64.ofNat i < carry.size := by
      rw [UInt64.lt_iff_toNat_lt, iNat, carryNat]
      exact inside
    have difference : UInt64.ofNat i - carry.size = UInt64.ofNat (i - carry.data.size) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le (UInt64.ofNat i) carry.size
          (UInt64.le_iff_toNat_le.mpr (by rw [iNat, carryNat]; omega)),
        iNat, carryNat, ofNat_toNat_small (n := i - carry.data.size) (by omega)]
    rw [ite_eq_right test, difference, List.getElem_append_right]
    rotate_left
    · simp only [byteWords_length]
      omega
    · simp only [byteWords_length]
      exact (byteWords_get_nat input (show input.data.size < 2 ^ 64 by omega)
        (i - carry.data.size) (by omega)).symm

/-- The bytes that `tailBytes` keeps are the byte lists of the carry and the input from `start`
on. -/
theorem tailBytes_words (carry input : Bytes) (start : UInt64)
    (total : carry.data.size + input.data.size < 2 ^ 64)
    (le : start.toNat ≤ carry.data.size + input.data.size) :
    byteWords (tailBytes carry input start) =
      (byteWords carry ++ byteWords input).drop start.toNat := by
  have carryNat : carry.size.toNat = carry.data.size := Bytes.size_toNat carry (by omega)
  have inputNat : input.size.toNat = input.data.size := Bytes.size_toNat input (by omega)
  have sum : (carry.size + input.size).toNat = carry.data.size + input.data.size := by
    rw [UInt64.toNat_add, carryNat, inputNat, Nat.mod_eq_of_lt total]
  have countNat : (carry.size + input.size - start).toNat =
      carry.data.size + input.data.size - start.toNat := by
    rw [UInt64.toNat_sub_of_le (carry.size + input.size) start
      (UInt64.le_iff_toNat_le.mpr (by rw [sum]; exact le)), sum]
  unfold tailBytes
  apply List.ext_getElem
  · rw [byteWords_length, Bytes.data_size_build, countNat, List.length_drop, List.length_append,
      byteWords_length, byteWords_length]
  · intro index left right
    have bound : index < carry.data.size + input.data.size - start.toNat := by
      rw [byteWords_length, Bytes.data_size_build, countNat] at left
      exact left
    rw [byteWords_build_get (carry.size + input.size - start)
      (fun i => byteAt carry input (start + i)) index (by rw [countNat]; exact bound),
      byteAt_narrow, List.getElem_drop]
    have sumEq : start + UInt64.ofNat index = UInt64.ofNat (start.toNat + index) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, ofNat_toNat_small (n := index) (by omega),
        ofNat_toNat_small (n := start.toNat + index) (by omega),
        Nat.mod_eq_of_lt (by omega : start.toNat + index < 2 ^ 64)]
    rw [sumEq, byteAt_eq carry input (start.toNat + index) total (by omega)]

/-- The words that `wordsOf` reads are the words of the first `8 * count` bytes of the carry and
the input. -/
theorem wordsOf_words (carry input : Bytes) (count : UInt64)
    (total : carry.data.size + input.data.size < 2 ^ 64)
    (le : 8 * count.toNat ≤ carry.data.size + input.data.size) :
    (wordsOf carry input count).toList =
      leWords ((byteWords carry ++ byteWords input).take (8 * count.toNat)) := by
  apply List.ext_getElem
  · simp only [wordsOf, LeanExe.build, Array.length_toList, Array.size_ofFn, leWords_length,
      List.length_take, List.length_append, byteWords_length]
    omega
  · intro j left right
    have jBound : j < count.toNat := by
      simpa [wordsOf, LeanExe.build] using left
    simp only [wordsOf, LeanExe.build, Array.getElem_toList, Array.getElem_ofFn]
    rw [loop_byteAt]
    simp only [leWords, List.getElem_map, List.getElem_range]
    unfold leWord
    congr 2
    apply List.map_congr_left
    intro k hk
    have kBound := List.mem_range.mp hk
    have index : 8 * UInt64.ofNat j + UInt64.ofNat k = UInt64.ofNat (8 * j + k) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_mul, ofNat_toNat_small (n := j) (by omega),
        ofNat_toNat_small (n := k) (by omega), ofNat_toNat_small (n := 8 * j + k) (by omega)]
      simp only [UInt64.reduceToNat]
      rw [Nat.mod_eq_of_lt (by omega : 8 * j < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 8 * j + k < 2 ^ 64)]
    have element := byteAt_eq carry input (8 * j + k) total (by omega)
    have small := byteAt_lt carry input (UInt64.ofNat (8 * j + k))
    rw [element] at small
    rw [index, element]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_take]
    rw [ite_eq_left (by omega : 8 * j + k < 8 * count.toNat),
      List.getElem?_eq_getElem (l := byteWords carry ++ byteWords input) (i := 8 * j + k)
        (by simp; omega),
      Option.getD_some, Nat.mod_eq_of_lt small]

/-- The bytes that `eventBytes` writes are the little-endian bytes of the words. -/
theorem eventBytes_words (words : Array UInt64) (small : 8 * words.size < 2 ^ 64) :
    byteWords (eventBytes words) = leBytes words.toList := by
  have sizeNat : words.size.toUInt64.toNat = words.size := by
    simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show words.size < 2 ^ 64 by omega)]
  have countNat : (8 * words.size.toUInt64).toNat = 8 * words.size := by
    rw [UInt64.toNat_mul, sizeNat]
    simp only [UInt64.reduceToNat]
    exact Nat.mod_eq_of_lt small
  unfold eventBytes
  apply List.ext_getElem
  · rw [byteWords_length, Bytes.data_size_build, countNat, leBytes_length, Array.length_toList]
  · intro i left right
    have bound : i < 8 * words.size := by
      rw [byteWords_length, Bytes.data_size_build, countNat] at left
      exact left
    have iNat : (UInt64.ofNat i).toNat = i := ofNat_toNat_small (by omega)
    have quotient : (UInt64.ofNat i / 8).toNat = i / 8 := by
      rw [UInt64.toNat_div, iNat]
      rfl
    have remainder : UInt64.ofNat i % 8 = UInt64.ofNat (i % 8) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mod, iNat, ofNat_toNat_small (n := i % 8) (by omega)]
      rfl
    rw [byteWords_build_get (8 * words.size.toUInt64)
      (fun i => words[(i / 8).toNat]! >>> (8 * (i % 8))) i (by rw [countNat]; exact bound),
      leBytes_getElem]
    simp only [Array.getElem_toList]
    rw [quotient, remainder, getElem!_pos words (i / 8) (by omega),
      shift_byte _ (i % 8) (Nat.mod_lt i (by decide))]

/-! ## Sizes -/

theorem tailBytes_size (carry input : Bytes) (start : UInt64) :
    (tailBytes carry input start).data.size = (carry.size + input.size - start).toNat := by
  simp [tailBytes]

theorem eventBytes_size (words : Array UInt64) :
    (eventBytes words).data.size = (8 * words.size.toUInt64).toNat := by
  simp [eventBytes]

theorem wordsOf_size (carry input : Bytes) (count : UInt64) :
    (wordsOf carry input count).size = count.toNat := by
  simp [wordsOf, LeanExe.build]

end Demos.OrderBook.Process
