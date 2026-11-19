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

theorem clear_size (buffer : Bytes) (start count : UInt64) :
    (buffer.clear start count).data.size = buffer.data.size :=
  splice_size (by rw [zeros_size]; exact buffer.window_le start count)

end Bytes

end LeanExe
