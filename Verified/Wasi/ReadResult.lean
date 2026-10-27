import Verified.Wasi.ReadLocals
import Verified.Wasi.ReadDiscard
import Verified.Wasi.Write

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.ProofKit

def readResultCode : Program :=
  [.extendUI32, .localSet 2, .localGet 2, .eqzI64,
   .iff 0 0
     [.const 8, .load32 0, .extendUI32, .localSet 3,
      .localGet 3, .eqzI64, .iff 0 0 (discardReadCode 1) [] [] []]
     (discardReadCode 1 ++ [.constI64 0, .localSet 3]) [] []]

theorem read_bytes_empty {bytes : LeanExe.Bytes} (h : bytes.data.size = 0) :
    bytes = LeanExe.Bytes.empty := by
  cases bytes with
  | mk data =>
    change data.size = 0 at h
    have hData := ByteArray.size_eq_zero_iff.mp h
    cases hData
    rfl

theorem wp_read_result {World : Type} {source target : Module}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv World}
    {heap : Heap} {store : Store World} {capacity root errno oldErrno oldLength : UInt64}
    {bytes : LeanExe.Bytes} {values : List Value} {rest : Program} {Q : Assertion World}
    (hHeap : heap.At (PureTransport.erase store))
    (hBytes : Bytes.Rep heap (PureTransport.erase store) root bytes.size bytes)
    (hErrno : errno.toNat < 4294967296)
    (hMemory : 16 ≤ store.mem.pages * 65536)
    (hCount : errno = 0 → store.mem.read32 8 = UInt32.ofNat bytes.data.size)
    (hError : errno ≠ 0 → bytes = LeanExe.Bytes.empty)
    (hKeep : errno = 0 → bytes.size ≠ 0 →
      wp target rest Q store (readLocals capacity root errno bytes.size values) targetHost)
    (hDiscard : bytes = LeanExe.Bytes.empty → ∀ final : Store World,
      PureTransport.erase final = Bytes.releasedStore heap (PureTransport.erase store) root →
      final.host = store.host →
      wp target rest Q final (readLocals capacity 0 errno 0 values) targetHost) :
    wp target (readResultCode ++ rest) Q store
      (readLocals capacity root oldErrno oldLength (.i32 errno.toUInt32 :: values)) targetHost := by
  have hSize := hBytes.size_lt
  have hSizeCast : UInt64.ofNat (UInt32.ofNat bytes.data.size).toNat = bytes.size := by
    rw [UInt32.toNat_ofNat_of_lt' (by change bytes.data.size < 4294967296; exact hSize)]
    rfl
  simp only [readResultCode, List.cons_append, List.nil_append,
    readLocals_stack, wp_extendUI32_cons, readLocals_values]
  refine wp_localSet_local (s := readLocals capacity root oldErrno oldLength values)
    (i := 2) (v := .i64 (UInt64.ofNat errno.toUInt32.toNat)) (vs := values)
    (by change 1 ≤ 2; omega) (by change 2 < 4; omega) ?_
  simp only [narrow_word errno hErrno, readLocals_values, readLocals_set_errno]
  change wp target _ Q store (readLocals capacity root errno oldLength values) targetHost
  simp only [wp_localGet_cons, readLocals_errno, readLocals_stack,
    wp_eqzI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hZero : errno = 0
  · simp only [ite_eq_left hZero]
    rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
    simp only [wp_const_cons, wp_load32_cons, readLocals_stack,
      UInt32.reduceToNat, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by omega), hCount hZero]
    simp only [wp_extendUI32_cons]
    refine wp_localSet_local (s := readLocals capacity root errno oldLength values)
      (i := 3) (v := .i64 (UInt64.ofNat (UInt32.ofNat bytes.data.size).toNat)) (vs := values)
      (by change 1 ≤ 3; omega) (by change 3 < 4; omega) ?_
    simp only [hSizeCast, readLocals_values, readLocals_set_length]
    change wp target _ _ store (readLocals capacity root errno bytes.size values) targetHost
    simp only [wp_localGet_cons, readLocals_length, readLocals_stack,
      wp_eqzI64_cons, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hEmpty : bytes.size = 0
    · simp only [ite_eq_left hEmpty]
      rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
      have hEmptyBytes : bytes = LeanExe.Bytes.empty := by
        apply read_bytes_empty
        have hLength := hBytes.length_eq
        rw [hEmpty] at hLength
        exact hLength.symm
      refine wp_discard_read (s := readLocals capacity root errno bytes.size values)
        (rootSlot := 1) runtime layout profile hImports sourceHost hHeap hBytes
        (readLocals_root ..) (by change 1 ≤ 1; omega) (by change 1 < 4; omega) ?_
      intro final hStore hWorld
      simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
      simpa only [readLocals_values, readLocals_set_root, readLocals_stack, hEmpty] using
        hDiscard hEmptyBytes final hStore hWorld
    · simp only [ite_eq_right hEmpty]
      rw [ite_eq_right (by decide : ¬((0 : UInt32) ≠ 0))]
      simpa only [wp_nil, List.take_zero, List.nil_append, List.drop_zero,
        readLocals_values, readLocals_stack] using hKeep hZero hEmpty
  · simp only [ite_eq_right hZero]
    rw [ite_eq_right (by decide : ¬((0 : UInt32) ≠ 0))]
    refine wp_discard_read (s := readLocals capacity root errno oldLength values)
      (rootSlot := 1) runtime layout profile hImports sourceHost hHeap hBytes
      (readLocals_root ..) (by change 1 ≤ 1; omega) (by change 1 < 4; omega) ?_
    intro final hStore hWorld
    simp only [readLocals_values, readLocals_set_root, readLocals_stack, wp_constI64_cons]
    refine wp_localSet_local (s := readLocals capacity 0 errno oldLength values)
      (i := 3) (v := .i64 0) (vs := values)
      (by change 1 ≤ 3; omega) (by change 3 < 4; omega) ?_
    simpa only [wp_nil, List.take_zero, List.nil_append, List.drop_zero,
      readLocals_values, readLocals_stack, readLocals_set_root, readLocals_set_length] using
      hDiscard (hError hZero) final hStore hWorld

end Verified.Wasi
