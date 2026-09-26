import Project.Beck.ExecutionBudget
import Project.Beck.ExecutionRelease

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def FreshFor (heap : Heap) (node : FreeNode) : Prop :=
  ∀ lower upper, heap.Protects lower upper →
    upper ≤ node.root.toNat - 48 ∨ node.root.toNat + node.capacity.toNat ≤ lower

theorem allocated_fresh (original current : Heap) (initial middle : Store Unit)
    (preserved : original.Frame initial current middle) (need : UInt64)
    (space : takeFirstFitFrom 0 need current.nodes = none → current.top.toNat + 48 + need.toNat ≤ 4294967296) :
    FreshFor original (allocatedNode current.top need current.nodes) := by
  intro lower upper protectedRegion
  exact (preserved.protects lower upper protectedRegion).allocated_disjoint need space

theorem FreshFor.pointer_ne {heap : Heap} {node : FreeNode} (fresh : FreshFor heap node)
    (ptr : UInt64) (size : Nat) (protectedRegion : heap.Protects ptr.toNat (ptr.toNat + 8 * (size + 1)))
    (capacity : 8 ≤ node.capacity.toNat) (root : 48 ≤ node.root.toNat) : node.root ≠ ptr := by
  intro equal
  have separated := fresh _ _ protectedRegion
  rw [equal] at separated root
  omega

theorem FreshFor.release_frame {original current : Heap} {initial middle : Store Unit} {node : FreeNode}
    (fresh : FreshFor original node) (preserved : original.Frame initial current middle)
    (root : 48 ≤ node.root.toNat) (address : node.root.toNat ≤ 4294967296) :
    original.Frame initial (current.release node) (current.releaseStore middle node) :=
  preserved.released node root address fresh

theorem releaseWords_budget (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (node : FreeNode) (words : Array UInt64) (remaining pageLimit : Nat)
    (valid : current.At middle) (owned : current.OwnsWords middle node words)
    (preserved : original.Frame initial current middle) (fresh : FreshFor original node)
    (budget : OutputBudget middle current remaining pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 39 middle [.i64 node.root]
      (fun final values => values = [] ∧ final = current.releaseStore middle node ∧
        (current.release node).At final ∧ original.Frame initial (current.release node) final ∧
        OutputBudget final (current.release node) remaining pageLimit Project.Beck.«module») := by
  apply (releaseWords_exact env middle current node words valid owned).mono
  rintro final values ⟨result, rfl, finalValid⟩
  exact ⟨result, rfl, finalValid,
    fresh.release_frame preserved owned.buffer.rootBound (by have := owned.buffer.addressBound; omega),
    budget.released node⟩

#print axioms allocated_fresh
#print axioms releaseWords_budget

end Project.Beck.Execution
