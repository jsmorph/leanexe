import LeanExe.Dialect.Bytes

/-!
Windows of a byte buffer.  A start and a count name a window of a buffer: its first position is
the start, or the buffer's size when that is smaller, and its length is the count, or the bytes
from the first position to the end when they are fewer.  The arithmetic uses `Nat`, so no sum
wraps.  `Bytes.range` holds the bytes of a window, `Bytes.splice` replaces the bytes of a buffer
from a position, and `Bytes.clear` sets the bytes of a window to 0.
-/

namespace LeanExe

namespace Bytes

/-- The window of `buffer` that `start` and `count` name: its first position, `start` or the
buffer's size when that is smaller, and its length, `count` or the bytes from that position on
when they are fewer. -/
def window (buffer : Bytes) (start count : UInt64) : Nat × Nat :=
  let first := min start.toNat buffer.data.size
  (first, min count.toNat (buffer.data.size - first))

/-- The length of the window that `start` and `count` name, as a word. -/
def windowLength (buffer : Bytes) (start count : UInt64) : UInt64 :=
  UInt64.ofNat (buffer.window start count).2

/-- The bytes of `buffer` in the window that `start` and `count` name. -/
def range (buffer : Bytes) (start count : UInt64) : Bytes :=
  ⟨buffer.data.extract (buffer.window start count).1
    ((buffer.window start count).1 + (buffer.window start count).2)⟩

/-- `buffer` with the bytes from position `first` replaced by `bytes`, which end within it. -/
def splice (buffer : Bytes) (first : Nat) (bytes : Bytes) : Bytes :=
  ⟨buffer.data.extract 0 first ++ bytes.data ++
    buffer.data.extract (first + bytes.data.size) buffer.data.size⟩

/-- `count` bytes of 0. -/
def zeros (count : Nat) : Bytes := ⟨⟨Array.replicate count 0⟩⟩

/-- `buffer` with the bytes of the window that `start` and `count` name set to 0. -/
def clear (buffer : Bytes) (start count : UInt64) : Bytes :=
  buffer.splice (buffer.window start count).1 (zeros (buffer.window start count).2)

theorem window_fst_le (buffer : Bytes) (start count : UInt64) :
    (buffer.window start count).1 ≤ buffer.data.size := by
  simp only [window]
  omega

theorem window_le (buffer : Bytes) (start count : UInt64) :
    (buffer.window start count).1 + (buffer.window start count).2 ≤ buffer.data.size := by
  simp only [window]
  omega

theorem window_fst (buffer : Bytes) (start count : UInt64) :
    (buffer.window start count).1 = min start.toNat buffer.data.size := rfl

theorem window_snd (buffer : Bytes) (start count : UInt64) :
    (buffer.window start count).2 =
      min count.toNat (buffer.data.size - min start.toNat buffer.data.size) := rfl

theorem windowLength_toNat (buffer : Bytes) (start count : UInt64) :
    (buffer.windowLength start count).toNat = (buffer.window start count).2 := by
  have hLe : (buffer.window start count).2 ≤ count.toNat := by
    simp only [window]
    omega
  have := count.toNat_lt
  simp only [windowLength, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

@[simp] theorem range_size (buffer : Bytes) (start count : UInt64) :
    (buffer.range start count).data.size = (buffer.window start count).2 := by
  have := buffer.window_le start count
  simp only [range, ByteArray.size_extract]
  omega

theorem range_get (buffer : Bytes) (start count : UInt64) (i : Nat)
    (hi : i < (buffer.range start count).data.size) :
    (buffer.range start count).data[i] =
      buffer.data[(buffer.window start count).1 + i]'(by
        have := buffer.window_le start count
        rw [range_size] at hi
        omega) := by
  simp only [range]
  rw [ByteArray.getElem_extract]

@[simp] theorem zeros_size (count : Nat) : (zeros count).data.size = count := by
  simp [zeros, ByteArray.size]

theorem zeros_get (count i : Nat) (hi : i < (zeros count).data.size) : (zeros count).data[i] = 0 := by
  simp [zeros, ByteArray.getElem_eq_getElem_data]

theorem splice_size {buffer bytes : Bytes} {first : Nat}
    (h : first + bytes.data.size ≤ buffer.data.size) :
    (buffer.splice first bytes).data.size = buffer.data.size := by
  simp only [splice, ByteArray.size_append, ByteArray.size_extract]
  omega

theorem splice_get_before {buffer bytes : Bytes} {first i : Nat}
    (h : first + bytes.data.size ≤ buffer.data.size) (hi : i < first) :
    (buffer.splice first bytes).data[i]'(by rw [splice_size h]; omega) =
      buffer.data[i]'(by omega) := by
  have hLeft : i < (buffer.data.extract 0 first ++ bytes.data).size := by
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  have hFirst : i < (buffer.data.extract 0 first).size := by
    simp only [ByteArray.size_extract]
    omega
  simp only [splice]
  rw [ByteArray.getElem_append_left hLeft, ByteArray.getElem_append_left hFirst,
    ByteArray.getElem_extract]
  simp

theorem splice_get_inside {buffer bytes : Bytes} {first i : Nat}
    (h : first + bytes.data.size ≤ buffer.data.size) (hLow : first ≤ i)
    (hHigh : i < first + bytes.data.size) :
    (buffer.splice first bytes).data[i]'(by rw [splice_size h]; omega) =
      bytes.data[i - first]'(by omega) := by
  have hLeft : i < (buffer.data.extract 0 first ++ bytes.data).size := by
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  have hFirst : (buffer.data.extract 0 first).size ≤ i := by
    simp only [ByteArray.size_extract]
    omega
  have hSize : (buffer.data.extract 0 first).size = first := by
    simp only [ByteArray.size_extract]
    omega
  simp only [splice]
  rw [ByteArray.getElem_append_left hLeft, ByteArray.getElem_append_right hFirst]
  simp only [hSize]

theorem splice_get_after {buffer bytes : Bytes} {first i : Nat}
    (h : first + bytes.data.size ≤ buffer.data.size) (hLow : first + bytes.data.size ≤ i)
    (hi : i < buffer.data.size) :
    (buffer.splice first bytes).data[i]'(by rw [splice_size h]; omega) = buffer.data[i] := by
  have hRight : (buffer.data.extract 0 first ++ bytes.data).size ≤ i := by
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  have hSize : (buffer.data.extract 0 first ++ bytes.data).size = first + bytes.data.size := by
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  simp only [splice]
  rw [ByteArray.getElem_append_right hRight, ByteArray.getElem_extract]
  simp only [hSize]
  congr 1
  omega

private theorem min_toNat (a b : UInt64) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  split
  · rename_i h
    rw [UInt64.le_iff_toNat_le] at h
    omega
  · rename_i h
    rw [UInt64.le_iff_toNat_le] at h
    omega

/-- The window that a start of 0 and a count of the buffer's size name holds the whole buffer. -/
theorem range_zero_size (buffer : Bytes) (small : buffer.data.size < 2 ^ 64) :
    buffer.range 0 buffer.size = buffer := by
  have hSize := buffer.size_toNat small
  have hFirst : (buffer.window 0 buffer.size).1 = 0 := by
    rw [window_fst]
    simp
  have hLength : (buffer.window 0 buffer.size).2 = buffer.data.size := by
    rw [window_snd, hSize]
    simp
  simp only [range, hFirst, hLength, Nat.zero_add, ByteArray.extract_zero_size]

/-- The window's first position and length as words: the start, or the size when that is smaller,
and the count, or the bytes from that position on when they are fewer. -/
theorem window_of_words (buffer : Bytes) (small : buffer.data.size < 2 ^ 64)
    (start count : UInt64) :
    (min start buffer.size).toNat = (buffer.window start count).1 ∧
      (min count (buffer.size - min start buffer.size)).toNat = (buffer.window start count).2 := by
  have hSize := buffer.size_toNat small
  have hFirst : (min start buffer.size).toNat = (buffer.window start count).1 := by
    rw [min_toNat, hSize, window_fst]
  refine ⟨hFirst, ?_⟩
  have hLe : min start buffer.size ≤ buffer.size := by
    rw [UInt64.le_iff_toNat_le, hFirst, hSize]
    exact buffer.window_fst_le start count
  rw [min_toNat, UInt64.toNat_sub_of_le _ _ hLe, hSize, hFirst, window_snd, window_fst]

/-- The window from `written` bytes past the first position of the window that `start` and `count`
name, with the bytes of that window that remain, holds those bytes: the window's bytes after the
first `written`. -/
theorem range_after (buffer : Bytes) (small : buffer.data.size < 2 ^ 64)
    {start count written : UInt64} (le : written.toNat ≤ (buffer.window start count).2) :
    (buffer.range (min start buffer.size + written)
        (min count (buffer.size - min start buffer.size) - written)).data.data.toList =
      (buffer.range start count).data.data.toList.drop written.toNat := by
  obtain ⟨hFirst, hLength⟩ := buffer.window_of_words small start count
  have hWindow := buffer.window_le start count
  have hAt : (min start buffer.size + written).toNat =
      (buffer.window start count).1 + written.toNat := by
    rw [UInt64.toNat_add, hFirst]
    exact Nat.mod_eq_of_lt (by omega)
  have hRest : (min count (buffer.size - min start buffer.size) - written).toNat =
      (buffer.window start count).2 - written.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hLength]; exact le), hLength]
  have hNewFirst : (buffer.window (min start buffer.size + written)
      (min count (buffer.size - min start buffer.size) - written)).1 =
        (buffer.window start count).1 + written.toNat := by
    rw [window_fst, hAt]
    omega
  have hNewLength : (buffer.window (min start buffer.size + written)
      (min count (buffer.size - min start buffer.size) - written)).2 =
        (buffer.window start count).2 - written.toNat := by
    rw [window_snd, hAt, hRest]
    omega
  apply List.ext_getElem
  · simp only [Array.length_toList, List.length_drop, ByteArray.size_data, range_size, hNewLength]
  · intro i hNew hOld
    simp only [Array.getElem_toList, List.getElem_drop]
    have hNewSize : i < (buffer.range (min start buffer.size + written)
        (min count (buffer.size - min start buffer.size) - written)).data.size := by
      simpa only [Array.length_toList, ByteArray.size_data] using hNew
    have hOldSize : written.toNat + i < (buffer.range start count).data.size := by
      simp only [Array.length_toList, List.length_drop, ByteArray.size_data, range_size] at hOld
      rw [range_size]
      omega
    have hA := buffer.range_get _ _ i hNewSize
    have hB := buffer.range_get start count (written.toNat + i) hOldSize
    refine hA.trans (Eq.trans ?_ hB.symm)
    congr 1
    rw [hNewFirst]
    omega

/-- The bytes of a window as a list: the buffer's bytes from the window's first position, as many as
its length. -/
theorem range_toList (buffer : Bytes) (start count : UInt64) :
    (buffer.range start count).data.data.toList =
      (buffer.data.data.toList.drop (buffer.window start count).1).take
        (buffer.window start count).2 := by
  have hLe := buffer.window_le start count
  apply List.ext_getElem
  · simp only [Array.length_toList, ByteArray.size_data, range_size, List.length_take,
      List.length_drop]
    omega
  · intro i hRange _
    simp only [Array.getElem_toList, List.getElem_take, List.getElem_drop]
    have hi : i < (buffer.range start count).data.size := by
      simpa only [Array.length_toList, ByteArray.size_data] using hRange
    exact buffer.range_get start count i hi

/-- The window from `start`, at most the buffer's size, whose count is the bytes from `start` to
the end. -/
theorem window_from (buffer : Bytes) (small : buffer.data.size < 2 ^ 64) {start : UInt64}
    (le : start.toNat ≤ buffer.data.size) :
    (buffer.window start (buffer.size - start)).1 = start.toNat ∧
      (buffer.window start (buffer.size - start)).2 = buffer.data.size - start.toNat := by
  have hSize := buffer.size_toNat small
  have hCount : (buffer.size - start).toNat = buffer.data.size - start.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hSize]; exact le), hSize]
  refine ⟨?_, ?_⟩
  · rw [window_fst]
    omega
  · rw [window_snd, hCount]
    omega

/-- The window from `start` to the end holds the bytes from `start` on. -/
theorem range_from_toList (buffer : Bytes) (small : buffer.data.size < 2 ^ 64) {start : UInt64}
    (le : start.toNat ≤ buffer.data.size) :
    (buffer.range start (buffer.size - start)).data.data.toList =
      buffer.data.data.toList.drop start.toNat := by
  obtain ⟨hFirst, hLength⟩ := buffer.window_from small le
  rw [range_toList, hFirst, hLength]
  apply List.take_of_length_le
  simp

/-- The window from `start` to the end holds as many bytes as follow `start`. -/
theorem range_from_size (buffer : Bytes) (small : buffer.data.size < 2 ^ 64) {start : UInt64}
    (le : start.toNat ≤ buffer.data.size) :
    (buffer.range start (buffer.size - start)).data.size = buffer.data.size - start.toNat := by
  rw [range_size, (buffer.window_from small le).2]

/-- The bytes of a splice at the positions of the replacing bytes are the replacing bytes. -/
theorem splice_extract {buffer bytes : Bytes} {first n : Nat}
    (h : first + bytes.data.size ≤ buffer.data.size) (hn : n ≤ bytes.data.size) :
    (buffer.splice first bytes).data.extract first (first + n) = bytes.data.extract 0 n := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size_data, ByteArray.size_extract, splice_size h]
    omega
  · intro i hLeft hRight
    have hi : i < n := by
      simp only [ByteArray.size_data, ByteArray.size_extract] at hRight
      omega
    have hSplice := splice_get_inside (i := first + i) h (by omega) (by omega)
    simp only [Nat.add_sub_cancel_left] at hSplice
    simp only [ByteArray.data_extract, Array.getElem_extract, Nat.zero_add]
    simpa only [ByteArray.getElem_eq_getElem_data] using hSplice

theorem clear_size (buffer : Bytes) (start count : UInt64) :
    (buffer.clear start count).data.size = buffer.data.size :=
  splice_size (by rw [zeros_size]; exact buffer.window_le start count)

end Bytes

end LeanExe
