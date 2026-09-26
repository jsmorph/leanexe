import Project.ProofKit.PackedMemory
import Project.ProofKit.PackedFloatFrame
import Project.TalosCompat

namespace Project.ProofKit.PackedWordAccess
open Wasm PackedMemory PackedFloatFrame

def guardProgram (ptrLocal sizeLocal offsetLocal : Nat) : Wasm.Program :=
  [.iff 0 1
    [.localGet sizeLocal, .localGet offsetLocal, .subI64, .constI64 4, .geUI64,
      .iff 0 1
        [.localGet ptrLocal, .localGet offsetLocal, .addI64, .wrapI64, .load32 0, .extendUI32]
        [.unreachable] [] [.i64]]
    [.unreachable]]

theorem guard_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (ptr : UInt64) (bytes : ByteArray) (offset ptrLocal sizeLocal offsetLocal : Nat)
    (tail : List Value) (hBytes : ByteArrayAt initial.mem ptr.toNat bytes)
    (hOffset : offset + 4 ≤ bytes.size)
    (hPtr : frame.get ptrLocal = some (.i64 ptr))
    (hSize : frame.get sizeLocal = some (.i64 (UInt64.ofNat bytes.size)))
    (hIndex : frame.get offsetLocal = some (.i64 (UInt64.ofNat offset)))
    (hValues : frame.values = .i32 (if UInt64.ofNat offset ≤ UInt64.ofNat bytes.size then 1 else 0) :: tail)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q initial
      { frame with values := Value.i64 (LeanExe.Packed.getUInt32LE! bytes offset).toUInt64 :: tail } env) :
    wp module_ (guardProgram ptrLocal sizeLocal offsetLocal ++ rest) Q initial frame env := by
  have hFit := hBytes.1
  have hSize64 : bytes.size < UInt64.size := by change bytes.size < 18446744073709551616; omega
  have hOffset64 : offset < UInt64.size := by omega
  have hLE : UInt64.ofNat offset ≤ UInt64.ofNat bytes.size := by
    simpa [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hOffset64,
      UInt64.toNat_ofNat_of_lt' hSize64] using (show offset ≤ bytes.size by omega)
  have hRemaining : 4 ≤ UInt64.ofNat bytes.size - UInt64.ofNat offset := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hLE,
      UInt64.toNat_ofNat_of_lt' hOffset64, UInt64.toNat_ofNat_of_lt' hSize64]
    change 4 ≤ bytes.size - offset
    omega
  have hAddress : (UInt32.ofNat ((ptr + UInt64.ofNat offset).toNat % 2^32)).toNat = ptr.toNat + offset := by
    simp only [UInt32.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hOffset64]
    omega
  have hRead := read32_eq_getUInt32LE initial.mem ptr.toNat bytes offset
    (UInt32.ofNat ((ptr + UInt64.ofNat offset).toNat % 2^32)) hBytes hOffset hAddress
  have hBound : (UInt32.ofNat ((ptr + UInt64.ofNat offset).toNat % 2^32)).toNat + 4 ≤
      initial.mem.pages * 65536 := by
    rw [hAddress]
    have := hBytes.2.1
    omega
  simp only [Locals.get] at hPtr hSize hIndex
  simp only [guardProgram, List.cons_append, List.nil_append, wp_iff_control_types]
  refine wp_iff_cons hValues ?_
  rw [ite_eq_left (by simp only [hLE, ite_true]; decide)]
  wp_packed_frame [hPtr, hSize, hIndex]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simp only [ge_iff_le, hRemaining, ite_true]; decide)]
  wp_packed_frame [hPtr, hSize, hIndex, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
    not_lt_of_ge hBound, hRead]
  exact hNext

#print axioms guard_spec

end Project.ProofKit.PackedWordAccess
