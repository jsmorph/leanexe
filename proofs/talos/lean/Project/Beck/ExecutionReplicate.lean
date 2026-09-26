import Project.Beck.ExecutionBudget
import Project.ProofKit.ArrayReplicate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

theorem replicateFinish_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (frame : Locals)
    (targetLocal countLocal counterLocal valueLocal : Nat) (count : Nat) (value : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (bound : count ≤ 56)
    (budget : OutputBudget initial heap (48 + 8 * (count + 1) + remaining) pageLimit Project.Beck.«module»)
    (counterValid : frame.validIndex counterLocal) (values : frame.values = [])
    (targetDifferent : targetLocal ≠ counterLocal) (countDifferent : countLocal ≠ counterLocal)
    (valueDifferent : valueLocal ≠ counterLocal)
    (targetRead : frame.get targetLocal = some (.i64 (allocatedRoot heap.top (UInt64.ofNat (8 * (count + 1))) heap.nodes)))
    (countRead : frame.get countLocal = some (.i64 count.toUInt64)) (valueRead : frame.get valueLocal = some (.i64 value))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final,
      let need := UInt64.ofNat (8 * (count + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final node (Array.replicate count value) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      wp Project.Beck.«module» rest Q final (FixedArrayCopy.counterFrame frame counterLocal count counterValid) env) :
    wp Project.Beck.«module» (UInt64Array.replicateProgram targetLocal countLocal counterLocal valueLocal ++ rest) Q
      (heap.allocateArrayStore initial (UInt64.ofNat (8 * (count + 1))) 1) frame env := by
  let need := UInt64.ofNat (8 * (count + 1))
  let root := allocatedRoot heap.top need heap.nodes
  have needWord : need.toNat = 8 * (count + 1) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space := budget.bump need (by rw [needWord]; omega)
  have bump : takeFirstFitFrom 0 need heap.nodes = none → heap.top.toNat + 48 + need.toNat ≤ 4294967296 :=
    fun h => (space h).1.le
  have bounds := allocated_bounds initial heap.top need heap.nodes valid.freeList bump
  have capacity := allocated_capacity need heap.nodes
  rw [needWord] at capacity
  apply UInt64Array.replicate_spec targetLocal countLocal counterLocal valueLocal Project.Beck.«module» env
    (heap.allocateArrayStore initial need 1) frame root value count counterValid targetDifferent countDifferent valueDifferent
    values targetRead countRead valueRead (by dsimp [root]; omega)
    (by change root.toNat + 8 * (count + 1) ≤ (FixedArrayAllocate.allocated initial heap.top need 1 heap.nodes).mem.pages * 65536
        rw [arrayAllocated_pages]; dsimp [root]; omega)
  intro final writes represented
  have outputWrites : Memory.WritesRange (heap.allocateArrayStore initial need 1) final root.toNat
      (root.toNat + 8 * ((Array.replicate count value).size + 1)) := by simpa only [Array.size_replicate] using writes
  obtain ⟨finalValid, owned⟩ := heap.finishWords initial final need (Array.replicate count value) valid
    (by rw [Array.size_replicate, needWord]) (fun h => (space h).1) outputWrites represented
  exact next final finalValid owned (heap.frame_arrayWritten initial final need 1 count valid (by rw [needWord]) bump writes)
    (budget.allocated need 1 remaining (by rw [needWord]) writes)

#print axioms replicateFinish_owned

end Project.Beck.Execution
