import Lean

namespace LeanExe

structure Bytes where
  data : ByteArray
  deriving Inhabited

namespace Bytes

def empty : Bytes := ⟨ByteArray.empty⟩

def size (bytes : Bytes) : UInt64 := UInt64.ofNat bytes.data.size

def get (bytes : Bytes) (index : UInt64) : UInt64 :=
  if h : index.toNat < bytes.data.size then bytes.data[index.toNat].toUInt64 else 0

def build (count : UInt64) (element : UInt64 → UInt64) : Bytes :=
  ⟨⟨Array.ofFn (n := count.toNat) fun i => (element (UInt64.ofNat i)).toUInt8⟩⟩

@[simp] theorem data_size_build (count : UInt64) (element : UInt64 → UInt64) :
    (build count element).data.size = count.toNat := by
  simp [build, ByteArray.size]

@[simp] theorem size_empty : size empty = 0 := rfl

theorem size_toNat (bytes : Bytes) (h : bytes.data.size < 2 ^ 64) :
    (size bytes).toNat = bytes.data.size := by
  simp only [size, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

@[simp] theorem size_build (count : UInt64) (element : UInt64 → UInt64) :
    size (build count element) = count := by
  simp [size]

theorem get_eq_zero (bytes : Bytes) (index : UInt64)
    (h : bytes.data.size ≤ index.toNat) : get bytes index = 0 := by
  simp [get, Nat.not_lt.mpr h]

@[simp] theorem get_empty (index : UInt64) : get empty index = 0 := by
  simp [get, empty, ByteArray.size]

theorem get_build (count : UInt64) (element : UInt64 → UInt64) (index : UInt64) :
    get (build count element) index =
      if index.toNat < count.toNat then (element index).toUInt8.toUInt64 else 0 := by
  simp only [get, data_size_build]
  split <;> simp_all only [build, ByteArray.getElem_eq_getElem_data,
    Array.getElem_ofFn, UInt64.ofNat_toNat]

theorem get_toNat_lt (bytes : Bytes) (index : UInt64) :
    (get bytes index).toNat < 256 := by
  unfold get
  split
  · simpa using (bytes.data[index.toNat]).toNat_lt
  · decide

end Bytes

macro "bytes![" elements:num,* "]" : term => do
  for element in elements.getElems do
    if element.getNat > 255 then
      Lean.Macro.throwErrorAt element "byte literal exceeds 255"
  `(LeanExe.Bytes.mk (ByteArray.mk #[$[$elements],*]))

end LeanExe
