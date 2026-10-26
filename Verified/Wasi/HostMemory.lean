import Verified.Wasi.HostBytes
import Verified.Wasi.Scratch
import Verified.Wasi.GuestFrame

/-! Guest memory facts that the host imports use: reading the bytes of a write request,
placing the bytes of a read reply, and the guest frames of those writes. -/

namespace Verified.Wasi

open Wasm

theorem readBytes_eq {memory : Mem} {pointer : UInt64} {bytes : LeanExe.Bytes}
    (data : Bytes.At memory pointer bytes) :
    memory.readBytes pointer.toNat bytes.data.size = bytes.data.data.toList := by
  apply List.ext_getElem
  · simp only [Mem.readBytes, List.length_map, List.length_range, Array.length_toList,
      ByteArray.size]
  · intro index inRead inBytes
    have bound : index < bytes.data.size := by
      simpa only [Mem.readBytes, List.length_map, List.length_range] using inRead
    simpa only [Mem.readBytes, List.getElem_map, List.getElem_range, Array.getElem_toList,
      ByteArray.getElem_eq_getElem_data] using data.contents index bound

theorem readBytes_value {memory : Mem} {pointer : UInt64} {bytes : LeanExe.Bytes}
    (data : Bytes.At memory pointer bytes) :
    bytesOfList (memory.readBytes pointer.toNat bytes.data.size) = bytes := by
  rw [readBytes_eq data, bytesOfList_data]

theorem written_at (memory : Mem) (pointer : UInt32) (bytes : List UInt8)
    (address : pointer.toNat + bytes.length ≤ 2 ^ 32)
    (capacity : pointer.toNat + bytes.length ≤ memory.pages * 65536) :
    Bytes.At (memory.writeBytes pointer.toNat bytes) pointer.toUInt64 (bytesOfList bytes) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [UInt32.toNat_toUInt64, bytesOfList_size, Nat.reducePow] using address
  · simpa only [Mem.writeBytes, UInt32.toNat_toUInt64, bytesOfList_size] using capacity
  · intro index bound
    have inBytes : index < bytes.length := by simpa only [bytesOfList_size] using bound
    simp only [Mem.writeBytes, UInt32.toNat_toUInt64]
    rw [dite_eq_left (by omega)]
    simp only [Nat.add_sub_cancel_left, bytesOfList, ByteArray.getElem_eq_getElem_data,
      List.getElem_toArray]

theorem at_count {memory : Mem} {pointer : UInt32} {bytes : LeanExe.Bytes}
    (data : Bytes.At memory pointer.toUInt64 bytes) (count : UInt32)
    (separate : bytes.data.size = 0 ∨ 16 ≤ pointer.toNat) :
    Bytes.At (memory.write32 8 count) pointer.toUInt64 bytes := by
  apply data.frame (memory' := memory.write32 8 count) (Nat.le_refl _)
  intro index bound
  apply write32_bytes_outside
  simp only [UInt32.toNat_toUInt64, UInt32.reduceToNat]
  rcases separate with empty | above
  · omega
  · omega

theorem frame_host (before : Store α) (host : α) (writable : List (Nat × Nat)) :
    GuestFrame before { before with host } writable :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem frame_payload (before : Store α) (host : α) (pointer capacity : Nat)
    (bytes : List UInt8) (bound : bytes.length ≤ capacity) :
    GuestFrame before { before with mem := before.mem.writeBytes pointer bytes, host }
      [ABI.scratch, (pointer, capacity)] := by
  refine ⟨rfl, rfl, ?_⟩
  intro address outside
  have apart := outside (pointer, capacity)
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [InRange] at apart
  simp only [Mem.writeBytes]
  rw [dite_eq_right (by omega)]

theorem frame_count (before : Store α) (host : α) (count : UInt32) :
    GuestFrame before { before with mem := before.mem.write32 8 count, host } [ABI.scratch] := by
  refine ⟨rfl, rfl, ?_⟩
  intro address outside
  have apart := outside ABI.scratch (List.mem_singleton_self _)
  apply write32_bytes_outside
  simp only [InRange, ABI.scratch, UInt32.reduceToNat] at apart ⊢
  omega

end Verified.Wasi
