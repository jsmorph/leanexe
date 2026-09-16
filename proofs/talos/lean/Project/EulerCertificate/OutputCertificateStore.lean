import Project.EulerCertificate.OutputCertificateMemory
import Project.EulerCertificate.Program
import Project.ProofKit.FixedArrayFrame
import Project.ProofKit.ArrayFieldConstant

namespace Project.EulerCertificate.Execution
open Wasm Project.ProofKit FixedArrayFold
open Project.EulerCertificate.Flux (Vector)

set_option maxRecDepth 4096

def outputCertificateStoresProgram : Wasm.Program := (func15.drop 85).take 168

theorem output_certificate_stores_shape : outputCertificateStoresProgram =
    resultProgram 26 51 ++ ArrayField.constantStoreProgram 48 0 51 1 0 ++
    resultProgram 27 51 ++ ArrayField.constantStoreProgram 48 1 51 1 0 ++
    resultProgram 28 51 ++ ArrayField.constantStoreProgram 48 2 51 1 0 ++
    resultProgram 29 51 ++ ArrayField.constantStoreProgram 48 3 51 1 0 ++
    resultProgram 30 51 ++ ArrayField.constantStoreProgram 48 4 51 1 0 ++
    resultProgram 31 51 ++ ArrayField.constantStoreProgram 48 5 51 1 0 ++
    resultProgram 32 51 ++ ArrayField.constantStoreProgram 48 6 51 1 0 ++
    resultProgram 33 51 ++ ArrayField.constantStoreProgram 48 7 51 1 0 ++
    resultProgram 34 51 ++ ArrayField.constantStoreProgram 48 8 51 1 0 ++
    resultProgram 35 51 ++ ArrayField.constantStoreProgram 48 9 51 1 0 ++
    resultProgram 36 51 ++ ArrayField.constantStoreProgram 48 10 51 1 0 ++
    resultProgram 37 51 ++ ArrayField.constantStoreProgram 48 11 51 1 0 := rfl

theorem output_certificate_field_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (root value : UInt64) (index inputLocal : Nat)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48)
    (hValues : frame.values = []) (hInput : frame.get inputLocal = some (.i64 value))
    (hRoot : frame.get 48 = some (.i64 root))
    (hBound : (UInt64Array.wordAddress root (index + 1)).toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (UInt64Array.writeElement store root index value)
      (resultFrame frame 51 value) env) :
    wp module (resultProgram inputLocal 51 ++ ArrayField.constantStoreProgram 48 index 51 1 0 ++ rest)
      Q store frame env := by
  have hValid : frame.validIndex 51 := by simp [Locals.validIndex, hParams, hLocals]
  rw [List.append_assoc]
  apply resultProgram_spec inputLocal 51 module env store frame value hValues hInput (by omega) hValid
  apply ArrayField.constantStore_spec 48 index 51 1 0 module env store
    (resultFrame frame 51 value) root value [] rfl
    ((resultFrame_get_ne frame 51 48 value (by omega) (by decide)).trans hRoot)
    (resultFrame_get_result frame 51 value (by omega) hValid)
    (by simpa only [Nat.one_mul, Nat.add_zero] using hBound)
  simpa only [Nat.one_mul, Nat.add_zero, UInt64Array.writeElement, resultFrame] using hNext


theorem output_certificate_stores_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (root : UInt64) (r : Vector)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48)
    (hValues : frame.values = [])
    (hInputs : ∀ i : Fin 12, frame.get (26 + i.val) = some (.i64 ((Solve.certificateWords r)[i.val]'(by simpa only [Solve.certificateWords, List.length_cons, List.length_nil] using i.isLt))))
    (hRoot : frame.get 48 = some (.i64 root))
    (hFit : root.toNat + 104 ≤ 4294967296)
    (hMemory : root.toNat + 104 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (outputCertificateWrites store root r)
      (resultFrame frame 51 r.energy.upper) env) :
    wp module (outputCertificateStoresProgram ++ rest) Q store frame env := by
  have h0 := hInputs 0
  have h1 := hInputs 1
  have h2 := hInputs 2
  have h3 := hInputs 3
  have h4 := hInputs 4
  have h5 := hInputs 5
  have h6 := hInputs 6
  have h7 := hInputs 7
  have h8 := hInputs 8
  have h9 := hInputs 9
  have h10 := hInputs 10
  have h11 := hInputs 11
  simp [Solve.certificateWords] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [output_certificate_stores_shape]
  simp only [List.append_assoc]
  iterate 12
    apply output_certificate_field_spec env _ _ root
    · simpa only [resultFrame_params] using hParams
    · simpa only [resultFrame_locals_length] using hLocals
    · first | exact hValues | rfl
    · repeat rw [resultFrame_get_ne _ 51 _ _ (by simpa only [resultFrame_params] using (show frame.params.length ≤ 51 by omega)) (by decide)]
      assumption
    · repeat rw [resultFrame_get_ne _ 51 48 _ (by simpa only [resultFrame_params] using (show frame.params.length ≤ 51 by omega)) (by decide)]
      exact hRoot
    · rw [UInt64Array.wordAddress_toNat (words := 13) hFit (by decide)]
      try simp only [UInt64Array.writeElement_pages]
      omega
  simpa only [outputCertificateWrites, resultFrame, List.set_set] using hNext

#print axioms output_certificate_stores_shape
#print axioms output_certificate_field_spec
#print axioms output_certificate_stores_spec
end Project.EulerCertificate.Execution
