import Project.EulerRiemann.OutputHeaderMemory
import Project.EulerRiemann.OutputShape
import Project.ProofKit.FixedArrayFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold

theorem output_header_field_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (root value : UInt64) (index inputLocal : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hInput : frame.get inputLocal = some (.i64 value))
    (hRoot : frame.get 47 = some (.i64 root))
    (hBound : (UInt64Array.wordAddress root (index + 1)).toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (UInt64Array.writeElement store root index value)
      (resultFrame frame 50 value) env) :
    wp module (resultProgram inputLocal 50 ++ ArrayField.constantStoreProgram 47 index 50 1 0 ++ rest)
      Q store frame env := by
  have hValid : frame.validIndex 50 := by simp [Locals.validIndex, hParams, hLocals]
  rw [List.append_assoc]
  apply resultProgram_spec inputLocal 50 module env store frame value hValues hInput (by omega) hValid
  apply ArrayField.constantStore_spec 47 index 50 1 0 module env store
    (resultFrame frame 50 value) root value [] rfl
    ((resultFrame_get_ne frame 50 47 value (by omega) (by decide)).trans hRoot)
    (resultFrame_get_result frame 50 value (by omega) hValid)
    (by simpa only [Nat.one_mul, Nat.add_zero] using hBound)
  simpa only [Nat.one_mul, Nat.add_zero, UInt64Array.writeElement, resultFrame] using hNext

theorem output_header_stores_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (root n time status : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = [])
    (hN : frame.get 0 = some (.i64 n)) (hTime : frame.get 1 = some (.i64 time))
    (hStatus : frame.get 2 = some (.i64 status)) (hRoot : frame.get 47 = some (.i64 root))
    (hFit : root.toNat + 40 ≤ 4294967296)
    (hMemory : root.toNat + 40 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (outputHeaderWrites store root n time status)
      (resultFrame frame 50 n) env) :
    wp module ((func99.drop 224).take 56 ++ rest) Q store frame env := by
  rw [output_header_stores_shape]
  simp only [List.append_assoc]
  iterate 4
    apply output_header_field_spec env _ _ root
    · simpa only [resultFrame_params] using hParams
    · simpa only [resultFrame_locals_length] using hLocals
    · first | exact hValues | rfl
    · repeat rw [resultFrame_get_ne _ 50 _ _ (by simpa only [resultFrame_params] using (show frame.params.length ≤ 50 by omega)) (by decide)]
      first | exact hStatus | exact hTime | exact hN
    · repeat rw [resultFrame_get_ne _ 50 47 _ (by simpa only [resultFrame_params] using (show frame.params.length ≤ 50 by omega)) (by decide)]
      exact hRoot
    · rw [UInt64Array.wordAddress_toNat (words := 5) hFit (by decide)]
      try simp only [UInt64Array.writeElement_pages]
      omega
  simpa only [outputHeaderWrites, resultFrame, List.set_set] using hNext

#print axioms output_header_field_spec
#print axioms output_header_stores_spec

end Project.EulerRiemann.Execution
