import Project.Beck.ExecutionOmit
import Project.EulerRiemann.OutputBudget

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem omitIndex_budget (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (words : Array UInt64) (ptr owner : UInt64) (index remaining pageLimit : Nat)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (valid : heap.At initial) (bound : words.size ≤ 56) (inside : index < words.size)
    (budget : OutputBudget initial heap (48 + 8 * words.size + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 23 initial [.i64 index.toUInt64, .i64 ptr, .i64 owner]
      (fun final values =>
        let need := UInt64.ofNat (8 * words.size)
        let node := allocatedNode heap.top need heap.nodes
        values = [.i64 node.root, .i64 node.root] ∧
        (heap.allocate need).At final ∧
        (heap.allocate need).OwnsWords final node (omitIndex words index) ∧
        heap.Frame initial (heap.allocate need) final ∧
        OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module») := by
  have needWord : (UInt64.ofNat (8 * words.size)).toNat = 8 * words.size := by
    rw [UInt64.toNat_ofNat']; omega
  apply (omitIndex_inBounds env initial heap words ptr owner index represented protects valid bound inside
    (by
      have bump := budget.bump (UInt64.ofNat (8 * words.size)) (by rw [needWord]; omega)
      simpa only [FixedArrayBump.requiredPages, bumpPages, needWord] using bump)
    (budget.pages.trans budget.pageLimitBound)).mono
  rintro final values ⟨result, finalHeap, owned, frame, _, _, writes⟩
  exact ⟨result, finalHeap, owned, frame,
    budget.allocated (UInt64.ofNat (8 * words.size)) 1 remaining (by rw [needWord]) writes⟩

def determinantBytes : Nat → Nat
  | 0 => 0
  | order + 1 => (48 + 8 * (order + 1)) +
      (order + 1) * (48 + 8 * (order + 1) + determinantBytes order)

theorem determinantBytes_mono : Monotone determinantBytes := by
  apply monotone_nat_of_le_succ
  intro order
  cases order with
  | zero => simp [determinantBytes]
  | succ order =>
    change determinantBytes (order + 1) ≤ (48 + 8 * (order + 2)) +
      (order + 2) * (48 + 8 * (order + 2) + determinantBytes (order + 1))
    nlinarith

theorem determinantBytes_six : determinantBytes 6 = 200160 := by decide

theorem determinantBytes_bound (order : Nat) (bound : order ≤ 6) : determinantBytes order ≤ 200160 := by
  simpa only [determinantBytes_six] using determinantBytes_mono bound

#print axioms omitIndex_budget
#print axioms determinantBytes_bound

end Project.Beck.Execution
