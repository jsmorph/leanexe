import Project.EulerRiemann.FrozenOutputHeaderStore
import Project.EulerRiemann.FrozenWordAllocationBounds
import Project.EulerRiemann.FrozenHeapWordsFinish

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayResult

def outputHeaderDataProgram : Wasm.Program := (func99.drop 218).take 62

def outputHeaderResultFrame (frame : Locals) (root n : UInt64) : Locals :=
  resultFrame (resultFrame frame 47 root) 50 n

theorem output_header_data_shape : outputHeaderDataProgram =
    resultProgram 56 47 ++ lengthStoreProgram 47 4 ++ (func99.drop 224).take 56 := rfl

theorem output_header_data_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (root n time status : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = [])
    (hN : frame.get 0 = some (.i64 n)) (hTime : frame.get 1 = some (.i64 time))
    (hStatus : frame.get 2 = some (.i64 status)) (hRoot : frame.get 56 = some (.i64 root))
    (hFit : root.toNat + 40 ≤ 4294967296)
    (hMemory : root.toNat + 40 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (outputHeaderStore store root n time status)
      (outputHeaderResultFrame frame root n) env) :
    wp module (outputHeaderDataProgram ++ rest) Q store frame env := by
  have hValid : frame.validIndex 47 := by simp [Locals.validIndex, hParams, hLocals]
  have hLengthBound : root.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [output_header_data_shape]
  simp only [List.append_assoc]
  apply resultProgram_spec 56 47 module env store frame root hValues hRoot (by omega) hValid
  apply lengthStore_spec module env store (resultFrame frame 47 root) root 4 47 rfl
    (resultFrame_get_result frame 47 root (by omega) hValid) hLengthBound
  apply output_header_stores_spec env (writeLength store root 4)
    (resultFrame frame 47 root) root n time status
    hParams (by simpa only [resultFrame_locals_length] using hLocals) rfl
    ((resultFrame_get_ne frame 47 0 root (by omega) (by decide)).trans hN)
    ((resultFrame_get_ne frame 47 1 root (by omega) (by decide)).trans hTime)
    ((resultFrame_get_ne frame 47 2 root (by omega) (by decide)).trans hStatus)
    (resultFrame_get_result frame 47 root (by omega) hValid) hFit
    (by simpa only [writeLength_pages] using hMemory)
  exact hNext

theorem output_header_owned_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (need n time status : UInt64) (hHeap : heap.At initial)
    (hNeed : 40 ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = [])
    (hN : frame.get 0 = some (.i64 n)) (hTime : frame.get 1 = some (.i64 time))
    (hStatus : frame.get 2 = some (.i64 status))
    (hRoot : frame.get 56 = some (.i64 (allocatedRoot heap.top need heap.nodes)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final (allocatedNode heap.top need heap.nodes)
        (outputHeaderWords n time status) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need 1) final
        (allocatedRoot heap.top need heap.nodes).toNat
        ((allocatedRoot heap.top need heap.nodes).toNat + 40) →
      wp module rest Q final
        (outputHeaderResultFrame frame (allocatedRoot heap.top need heap.nodes) n) env) :
    wp module (outputHeaderDataProgram ++ rest) Q (heap.allocateArrayStore initial need 1) frame env := by
  have hBounds := heap.allocate_word_bounds initial need 1 4 hHeap hNeed
    (fun hNone => (hBump hNone).le)
  apply output_header_data_spec env _ frame (allocatedRoot heap.top need heap.nodes) n time status
    hParams hLocals hValues hN hTime hStatus hRoot hBounds.1 hBounds.2
  have hWrites := output_header_store_frame (heap.allocateArrayStore initial need 1)
    (allocatedRoot heap.top need heap.nodes) n time status hBounds.1
  have hWords := output_header_store_words (heap.allocateArrayStore initial need 1)
    (allocatedRoot heap.top need heap.nodes) n time status hBounds.1 hBounds.2
  have hFinished := heap.finishWords initial _ need (outputHeaderWords n time status)
    hHeap hNeed hBump hWrites hWords
  exact hNext _ hFinished.1 hFinished.2 hWrites

#print axioms output_header_data_shape
#print axioms output_header_data_spec
#print axioms output_header_owned_spec

end Project.EulerRiemann.Frozen.Execution
