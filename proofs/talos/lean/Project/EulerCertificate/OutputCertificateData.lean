import Project.EulerCertificate.OutputCertificateStore
import Project.EulerRiemann.WordAllocationBounds
import Project.EulerRiemann.HeapWordsFinish

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayResult
open Project.EulerRiemann Project.EulerRiemann.Execution
open Project.EulerCertificate.Flux (Vector)

set_option maxRecDepth 4096

def outputCertificateDataProgram : Wasm.Program := (func15.drop 79).take 174

def outputCertificateResultFrame (frame : Locals) (root : UInt64) (r : Vector) : Locals :=
  resultFrame (resultFrame frame 48 root) 51 r.energy.upper

theorem output_certificate_data_shape : outputCertificateDataProgram =
    resultProgram 57 48 ++ lengthStoreProgram 48 12 ++ outputCertificateStoresProgram := rfl

theorem output_certificate_data_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (root : UInt64) (r : Vector)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48)
    (hValues : frame.values = [])
    (hInputs : ∀ i : Fin 12, frame.get (26 + i.val) =
      some (.i64 ((Solve.certificateWords r)[i.val]'(by simpa only [Solve.certificateWords, List.length_cons, List.length_nil] using i.isLt))))
    (hRoot : frame.get 57 = some (.i64 root))
    (hFit : root.toNat + 104 ≤ 4294967296)
    (hMemory : root.toNat + 104 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (outputCertificateStore store root r)
      (outputCertificateResultFrame frame root r) env) :
    wp module (outputCertificateDataProgram ++ rest) Q store frame env := by
  have hValid : frame.validIndex 48 := by simp [Locals.validIndex, hParams, hLocals]
  have hLengthBound : root.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [output_certificate_data_shape]
  simp only [List.append_assoc]
  apply resultProgram_spec 57 48 module env store frame root hValues hRoot (by omega) hValid
  apply lengthStore_spec module env store (resultFrame frame 48 root) root 12 48 rfl
    (resultFrame_get_result frame 48 root (by omega) hValid) hLengthBound
  apply output_certificate_stores_spec env (writeLength store root 12)
    (resultFrame frame 48 root) root r
    hParams (by simpa only [resultFrame_locals_length] using hLocals) rfl
    (fun i => (resultFrame_get_ne frame 48 (26 + i.val) root (by omega) (by omega)).trans (hInputs i))
    (resultFrame_get_result frame 48 root (by omega) hValid) hFit
    (by simpa only [writeLength_pages] using hMemory)
  exact hNext

theorem output_certificate_owned_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (need : UInt64) (r : Vector) (hHeap : heap.At initial)
    (hNeed : 104 ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48)
    (hValues : frame.values = [])
    (hInputs : ∀ i : Fin 12, frame.get (26 + i.val) =
      some (.i64 ((Solve.certificateWords r)[i.val]'(by simpa only [Solve.certificateWords, List.length_cons, List.length_nil] using i.isLt))))
    (hRoot : frame.get 57 = some (.i64 (allocatedRoot heap.top need heap.nodes)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final (allocatedNode heap.top need heap.nodes) (outputCertificateWords r) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need 1) final
        (allocatedRoot heap.top need heap.nodes).toNat
        ((allocatedRoot heap.top need heap.nodes).toNat + 104) →
      wp module rest Q final
        (outputCertificateResultFrame frame (allocatedRoot heap.top need heap.nodes) r) env) :
    wp module (outputCertificateDataProgram ++ rest) Q (heap.allocateArrayStore initial need 1) frame env := by
  have hBounds := heap.allocate_word_bounds initial need 1 12 hHeap hNeed
    (fun hNone => (hBump hNone).le)
  apply output_certificate_data_spec env _ frame (allocatedRoot heap.top need heap.nodes) r
    hParams hLocals hValues hInputs hRoot hBounds.1 hBounds.2
  have hWrites := output_certificate_store_frame (heap.allocateArrayStore initial need 1)
    (allocatedRoot heap.top need heap.nodes) r hBounds.1
  have hWords := output_certificate_store_words (heap.allocateArrayStore initial need 1)
    (allocatedRoot heap.top need heap.nodes) r hBounds.1 hBounds.2
  have hFinished := heap.finishWords initial _ need (outputCertificateWords r)
    hHeap hNeed hBump hWrites hWords
  exact hNext _ hFinished.1 hFinished.2 hWrites

#print axioms output_certificate_data_shape
#print axioms output_certificate_data_spec
#print axioms output_certificate_owned_spec
end Project.EulerCertificate.Execution
