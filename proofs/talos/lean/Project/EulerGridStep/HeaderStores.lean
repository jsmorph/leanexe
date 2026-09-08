import Project.EulerGridStep.CopyFrame

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

def headerConstStore (rootLocal : Nat) (offset value : UInt64) : Wasm.Program :=
  [.localGet rootLocal, .constI64 offset, .subI64, .wrapI64, .constI64 value, .store64 0]

def headerLocalStore (rootLocal valueLocal : Nat) (offset : UInt64) : Wasm.Program :=
  [.localGet rootLocal, .constI64 offset, .subI64, .wrapI64, .localGet valueLocal, .store64 0]

def writeHeaderWord (initial : Store Unit) (root offset value : UInt64) : Store Unit :=
  { initial with mem := initial.mem.write64 (root - offset).toUInt32 value }

theorem writeHeaderWord_pages (initial : Store Unit) (root offset value : UInt64) :
    (writeHeaderWord initial root offset value).mem.pages = initial.mem.pages := by
  simp [writeHeaderWord, Mem.write64_pages]

theorem header_const_store_spec (rootLocal : Nat) (root offset value : UInt64)
    (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (hRoot : frame.get rootLocal = some (.i64 root)) (hValues : frame.values = [])
    (hBound : (root - offset).toUInt32.toNat + 8 ≤ initial.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q (writeHeaderWord initial root offset value) frame env) :
    wp m (headerConstStore rootLocal offset value ++ rest) Q initial frame env := by
  have hWrap : UInt32.ofNat ((root - offset).toNat % (2 ^ 32)) = (root - offset).toUInt32 :=
    (Memory.toUInt32_eq_ofNat _).symm
  simp only [headerConstStore, List.cons_append, List.nil_append, wp_localGet_cons,
    hRoot, hValues, wp_constI64_cons, wp_subI64_cons,
    wp_wrapI64_cons, wp_store64_cons, hWrap, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr hBound), copyFrame_ofParts frame hValues]
  exact hNext

theorem header_local_store_spec (rootLocal valueLocal : Nat) (root offset value : UInt64)
    (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (hRoot : frame.get rootLocal = some (.i64 root))
    (hValue : frame.get valueLocal = some (.i64 value)) (hValues : frame.values = [])
    (hBound : (root - offset).toUInt32.toNat + 8 ≤ initial.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q (writeHeaderWord initial root offset value) frame env) :
    wp m (headerLocalStore rootLocal valueLocal offset ++ rest) Q initial frame env := by
  have hWrap : UInt32.ofNat ((root - offset).toNat % (2 ^ 32)) = (root - offset).toUInt32 :=
    (Memory.toUInt32_eq_ofNat _).symm
  simp only [headerLocalStore, List.cons_append, List.nil_append, wp_localGet_cons,
    copyFrame_get_withValues, hRoot, hValue, hValues, wp_constI64_cons, wp_subI64_cons,
    wp_wrapI64_cons, wp_store64_cons, hWrap, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr hBound), copyFrame_ofParts frame hValues]
  exact hNext

#print axioms header_const_store_spec
#print axioms header_local_store_spec
end Project.EulerGridStep.Execution
