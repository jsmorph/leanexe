import Project.ProofKit.FixedArrayFold

namespace Project.ProofKit.FixedArrayLengthRead
open Wasm FixedArrayFold

def program (pointerLocal lengthLocal : Nat) : Wasm.Program :=
  [.localGet pointerLocal, .wrapI64, .load64 0, .localSet lengthLocal]

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (pointer length : UInt64) (pointerLocal lengthLocal : Nat)
    (hValues : frame.values = [])
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hRead : store.mem.read64 pointer.toUInt32 = length)
    (hBound : pointer.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hLower : frame.params.length ≤ lengthLocal) (hValid : frame.validIndex lengthLocal)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store (resultFrame frame lengthLocal length) env) :
    wp module_ (program pointerLocal lengthLocal ++ rest) Q store frame env := by
  simp only [program, List.cons_append, List.nil_append, wp_localGet_cons, hPointer,
    wp_wrapI64_cons, wp_load64_cons, hValues]
  have hTwo32 : 2 ^ 32 = 4294967296 := by norm_num
  rw [hTwo32, ← Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, UInt32.add_zero, add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr hBound), hRead, wp_localSet_cons]
  have hNotParam : ¬lengthLocal < frame.params.length := Nat.not_lt.mpr hLower
  have hLocal : lengthLocal < frame.params.length + frame.locals.length := hValid
  simpa [Locals.set?, hNotParam, hLocal, resultFrame] using hNext

#print axioms program_spec

end Project.ProofKit.FixedArrayLengthRead
