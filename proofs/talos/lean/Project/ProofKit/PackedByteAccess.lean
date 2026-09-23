import Project.ProofKit.PackedByteMemory
import Project.ProofKit.PackedFloatFrame

namespace Project.ProofKit.PackedByteAccess
open Wasm PackedMemory PackedFloatFrame

def guardProgram (ptrLocal offsetLocal : Nat) : Wasm.Program :=
  [.iff 0 1
    [.localGet ptrLocal, .localGet offsetLocal, .addI64, .wrapI64, .load8U 0, .extendUI32]
    [.unreachable] [] [.i64]]

theorem guard_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (ptr : UInt64) (bytes : ByteArray) (offset ptrLocal offsetLocal : Nat)
    (tail : List Value) (hBytes : ByteArrayAt initial.mem ptr.toNat bytes)
    (hOffset : offset < bytes.size)
    (hPtr : frame.get ptrLocal = some (.i64 ptr))
    (hIndex : frame.get offsetLocal = some (.i64 (UInt64.ofNat offset)))
    (hValues : frame.values = .i32 (if UInt64.ofNat offset < UInt64.ofNat bytes.size then 1 else 0) :: tail)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q initial
      { frame with values := Value.i64 bytes[offset]!.toUInt64 :: tail } env) :
    wp module_ (guardProgram ptrLocal offsetLocal ++ rest) Q initial frame env := by
  obtain ⟨hLT, hBound, hRead⟩ := PackedByteMemory.access initial.mem ptr bytes offset hBytes hOffset
  have hFit := hBytes.1
  have hOffset64 : offset < UInt64.size := by change offset < 18446744073709551616; omega
  have hAddress : (ptr + UInt64.ofNat offset).toNat = ptr.toNat + offset := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hOffset64]
    apply Nat.mod_eq_of_lt
    change _ < 18446744073709551616
    omega
  simp only [Locals.get] at hPtr hIndex
  simp only [guardProgram, List.cons_append, List.nil_append, wp_iff_control_types]
  refine wp_iff_cons hValues ?_
  rw [ite_eq_left (by simp only [hLT, ite_true]; decide)]
  wp_packed_frame [hPtr, hIndex, hAddress, UInt32.toNat_zero, Nat.add_zero,
    UInt32.add_zero, not_lt_of_ge hBound, hRead]
  exact hNext

#print axioms guard_spec

end Project.ProofKit.PackedByteAccess
