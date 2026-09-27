import Project.ProofKit.Array

namespace Project.ProofKit.UInt64Array
open Wasm Project.ProofKit.Memory

theorem initialStore_data_memory (m : Wasm.Module) (pages offset : UInt32)
    (bytes : List UInt8)
    (hm : m.memory = some
      { pagesMin := pages
        data := [{ offset := some offset, bytes := bytes, offsetType := some .i32 }] })
    (hbound : offset.toNat + bytes.length ≤ pages.toNat * 65536) :
    (m.initialStore (α := Unit)).mem =
      (Mem.empty pages.toNat).writeBytes offset.toNat bytes := by
  simp [Module.initialStore, hm, hbound, Mem.empty]

def wordBytes (word : UInt64) : List UInt8 :=
  [(word &&& 255).toUInt8, ((word >>> 8) &&& 255).toUInt8,
   ((word >>> 16) &&& 255).toUInt8, ((word >>> 24) &&& 255).toUInt8,
   ((word >>> 32) &&& 255).toUInt8, ((word >>> 40) &&& 255).toUInt8,
   ((word >>> 48) &&& 255).toUInt8, ((word >>> 56) &&& 255).toUInt8]

def dataBytes (words : List UInt64) : List UInt8 := words.flatMap wordBytes

theorem dataBytes_length (words : List UInt64) :
    (dataBytes words).length = 8 * words.length := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [dataBytes, List.flatMap_cons, List.length_append] at *
    rw [ih]
    simp [wordBytes, Nat.mul_add, Nat.add_comm]

theorem read64_writeBytes_before (mem : Mem) (offset : Nat) (bytes : List UInt8)
    (address : UInt32) (h : address.toNat + 8 ≤ offset) :
    (mem.writeBytes offset bytes).read64 address = mem.read64 address := by
  apply read64_congr
  intro i hi
  simp only [Mem.writeBytes]
  rw [dite_eq_right (by omega)]

theorem writeBytes_word (mem : Mem) (address : UInt32) (word : UInt64) :
    mem.writeBytes address.toNat (wordBytes word) = mem.write64 address word := by
  cases mem
  unfold Mem.writeBytes Mem.write64
  dsimp only
  congr 1
  funext i
  have hlen : (wordBytes word).length = 8 := rfl
  simp only [hlen]
  by_cases h : address.toNat ≤ i ∧ i < address.toNat + 8
  · rw [dite_eq_left h]
    obtain ⟨j, hj, rfl⟩ : ∃ j, j < 8 ∧ i = address.toNat + j :=
      ⟨i - address.toNat, by omega, by omega⟩
    interval_cases j <;> simp [wordBytes]
  · rw [dite_eq_right h]
    split_ifs <;> first | rfl | omega

set_option maxHeartbeats 1000000 in
theorem read64_write_word (mem : Mem) (address : UInt32) (word : UInt64) :
    (mem.write64 address word).read64 address = word := by
  simp only [Mem.read64, Mem.write64]
  simp only [Nat.add_eq_left, OfNat.ofNat_ne_zero, Nat.succ_ne_self, reduceIte,
    Nat.reduceEqDiff]
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8]
  ext i
  interval_cases i <;> simp

theorem dataBytes_read (mem : Mem) (offset : Nat) (words : List UInt64)
    (hfit : offset + 8 * words.length ≤ UInt32.size)
    (index : Nat) (hi : index < words.length) :
    (mem.writeBytes offset (dataBytes words)).read64
      (UInt32.ofNat (offset + 8 * index)) = words[index] := by
  induction words generalizing mem offset index with
  | nil => simp at hi
  | cons word words ih =>
    simp only [dataBytes, List.flatMap_cons, Mem.writeBytes_append]
    change ((mem.writeBytes offset (wordBytes word)).writeBytes
      (offset + 8) (dataBytes words)).read64 _ = _
    cases index with
    | zero =>
      have ho : offset < UInt32.size := by simp only [List.length_cons] at hfit; omega
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
      rw [read64_writeBytes_before _ _ _ _ (by
        rw [UInt32.toNat_ofNat_of_lt' ho])]
      rw [← UInt32.toNat_ofNat_of_lt' ho, writeBytes_word]
      simp only [UInt32.ofNat_toNat, read64_write_word]
    | succ index =>
      have hi' : index < words.length := by simpa using hi
      have hf : offset + 8 + 8 * words.length ≤ UInt32.size := by
        simp only [List.length_cons] at hfit
        omega
      have hr := ih (mem.writeBytes offset (wordBytes word)) (offset + 8) hf index hi'
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm, List.getElem_cons_succ] using hr

#print axioms dataBytes_read
end Project.ProofKit.UInt64Array
