import Project.Beck.ExecutionReleaseGuards

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

structure ReleaseEntry where
  owner : Nat
  others : List Nat
  node : FreeNode
  words : Array UInt64

def releasePlanProgram (entries : List ReleaseEntry) : Wasm.Program :=
  entries.flatMap fun entry => knownReleaseProgram entry.owner entry.others

theorem releasePlan_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (frame : Locals) (entries : List ReleaseEntry) (resultNode : FreeNode) (resultWords : Array UInt64)
    (remaining pageLimit : Nat) (valid : heap.At middle)
    (owned : ∀ entry ∈ entries, heap.OwnsWords middle entry.node entry.words)
    (resultOwned : heap.OwnsWords middle resultNode resultWords)
    (preserved : original.Frame initial heap middle) (fresh : ∀ entry ∈ entries, FreshFor original entry.node)
    (separated : entries.Pairwise (fun e f => regionsDisjoint e.node.region f.node.region))
    (resultSeparated : ∀ entry ∈ entries, regionsDisjoint entry.node.region resultNode.region)
    (budget : OutputBudget middle heap remaining pageLimit Project.Beck.«module»)
    (values : frame.values = [])
    (ownerReads : ∀ entry ∈ entries, frame.get entry.owner = some (.i64 entry.node.root))
    (otherReads : ∀ entry ∈ entries, ∀ other ∈ entry.others,
      ∃ pointer, frame.get other = some (.i64 pointer) ∧ entry.node.root ≠ pointer)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final resultNode resultWords →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final frame)) :
    wp Project.Beck.«module» (releasePlanProgram entries) Q middle frame env := by
  induction entries generalizing middle heap with
  | nil => simpa only [releasePlanProgram, List.flatMap_nil, wp_nil] using next middle heap valid resultOwned preserved budget
  | cons entry entries ih =>
    have firstOwned := owned entry (by simp)
    have firstFresh := fresh entry (by simp)
    have pairs := List.pairwise_cons.mp separated
    change wp Project.Beck.«module» (knownReleaseProgram entry.owner entry.others ++ releasePlanProgram entries) Q middle frame env
    refine Sequence.wp_append (P := fun store after => wp Project.Beck.«module» (releasePlanProgram entries) Q store after env) ?_ (fun _ _ h => h)
    apply knownRelease_exact env initial middle original heap frame entry.owner entry.others entry.node entry.words remaining pageLimit
      valid firstOwned preserved firstFresh budget values (ownerReads entry (by simp)) (otherReads entry (by simp))
    intro finalValid finalFrame finalBudget
    dsimp only [Sequence.Fallthrough]
    have address : entry.node.root.toNat ≤ 4294967296 := by have := firstOwned.buffer.addressBound; omega
    apply ih _ _ finalValid
    · intro other member
      exact (owned other (List.mem_cons_of_mem _ member)).released entry.node firstOwned.buffer.rootBound address
        (regionsDisjoint_symm (pairs.1 other member))
    · exact resultOwned.released entry.node firstOwned.buffer.rootBound address
        (regionsDisjoint_symm (resultSeparated entry (by simp)))
    · exact finalFrame
    · exact fun other member => fresh other (List.mem_cons_of_mem _ member)
    · exact pairs.2
    · exact fun other member => resultSeparated other (List.mem_cons_of_mem _ member)
    · exact finalBudget
    · exact fun other member => ownerReads other (List.mem_cons_of_mem _ member)
    · exact fun other member => otherReads other (List.mem_cons_of_mem _ member)

#print axioms releasePlan_exact

end Project.Beck.Execution
