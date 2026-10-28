import Verified.Bytes.Basic
import Verified.Bytes.Code
import Verified.LocalFrame
import LeanExe.TalosCompat

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.Pipeline.Bytes LeanExe.ProofKit

theorem wp_get {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {root length index : UInt64} {bytes : LeanExe.Bytes}
    {rootSlot lengthSlot indexSlot : Nat} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (h : Rep heap store root length bytes)
    (hRoot : s.get rootSlot = some (.i64 root))
    (hLength : s.get lengthSlot = some (.i64 length))
    (hIndex : s.get indexSlot = some (.i64 index))
    (hNext : wp m rest Q store { s with values := .i64 (bytes.get index) :: s.values } host) :
    wp m (getCode rootSlot lengthSlot indexSlot ++ rest) Q store s host := by
  simp only [getCode, List.cons_append, List.nil_append, wp_localGet_cons,
    LeanExe.Pipeline.Locals.get_with_values, hIndex, hLength, wp_ltUI64_cons,
    wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hi : index < length
  · have hiNat : index.toNat < bytes.data.size := by
      rw [← h.length_eq]
      exact UInt64.lt_iff_toNat_lt.mp hi
    rcases h.buffer with hNull | hBuffer
    · have := hNull.2
      omega
    · have hCapacity := hBuffer.capacity
      have hBelow := hBuffer.object.below
      have hTop := hHeap.top
      have h32 := hBuffer.index_address index hiNat
      have hMemory : ¬ store.mem.pages * 65536 < (root + index).toUInt32.toNat + 1 := by
        rw [h32]
        omega
      have hRead := hBuffer.get index hiNat
      have hExtend (value : UInt8) : UInt64.ofNat value.toUInt32.toNat = value.toUInt64 := by
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_ofNat', UInt8.toNat_toUInt32, UInt8.toNat_toUInt64]
        exact Nat.mod_eq_of_lt (by have := value.toNat_lt; omega)
      have hValue : UInt64.ofNat
          ((store.mem.read8 (root + index).toUInt32).toUInt32.toNat) = bytes.get index := by
        rw [hExtend]
        exact hRead
      have hOne : (1 : UInt32) ≠ 0 := by decide
      simp only [hi, ite_true]
      rw [ite_eq_left hOne]
      simp only [wp_localGet_cons, Locals.get_values, hRoot, hIndex, wp_addI64_cons,
        wp_wrapI64_cons, wrap_toUInt32, wp_load8U_cons, UInt32.toNat_zero, Nat.add_zero,
        UInt32.add_zero]
      rw [ite_eq_right hMemory]
      simp only [wp_extendUI32_cons, hValue]
      simpa using hNext
  · have hNot : ¬ index.toNat < bytes.data.size := by
      simpa only [UInt64.lt_iff_toNat_lt, h.length_eq] using hi
    have hGet : bytes.get index = 0 :=
      LeanExe.Bytes.get_eq_zero bytes index (Nat.le_of_not_lt hNot)
    simpa [hi, wp_simp, hGet] using hNext

end Verified.Bytes
