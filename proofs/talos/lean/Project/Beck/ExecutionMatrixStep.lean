import Project.Beck.ExecutionMatrixRead
import Project.Beck.ExecutionMatrixRelease
import Project.Beck.ExecutionMatrixFinish
import Project.Beck.ExecutionDetState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixRowStep_exact (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (category index : Nat) (oldNode : FreeNode) (initialOwner : UInt64) (words : Array UInt64)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) (remaining pageLimit : Nat)
    (valid : current.At middle) (owned : current.OwnsWords middle oldNode words)
    (preserved : original.Frame initial current middle)
    (active : oldNode.root = initialOwner ∨ FreshFor original oldNode)
    (pointArray : UInt64Array.At middle pointPointer point.numerators)
    (inputArray : UInt64Array.At middle inputPointer input.incidence)
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8)
    (categoryBound : category < input.categories) (indexBound : index < input.jobs) (bound : words.size < 56)
    (budget : OutputBudget middle current (48 + 8 * (words.size + 2) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final →
      finalHeap.OwnsWords final node (words.push (matrixEntry input point category index)) →
      original.Frame initial finalHeap final → FreshFor original node →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ saved tail after, Q (.Break 0 final (matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer
        category (index + 1) node.root initialOwner saved tail after))) :
    wp Project.Beck.«module» (matrixRowBody.drop 4) Q middle
      (matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer category index oldNode.root initialOwner saved tail after) env := by
  let need := UInt64.ofNat (8 * (words.size + 2))
  have needWord : need.toNat = 8 * (words.size + 2) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space : takeFirstFitFrom 0 need current.nodes = none → current.top.toNat + 48 + need.toNat ≤ 4294967296 :=
    fun h => ((budget.bump need (by rw [needWord]; omega)) h).1.le
  have separated := owned.allocation_disjoint need space
  have fresh := allocated_fresh original current initial middle preserved need space
  change wp Project.Beck.«module» ((matrixRowBody.drop 4).take 46 ++ matrixRowBody.drop 50) Q middle _ env
  apply matrixRead_exact env middle input point inputOwner inputPointer pointOwner pointPointer category index oldNode.root initialOwner
    words saved tail after pointArray inputArray owned.buffer.values pointSize inputSize jobs categories categoryBound indexBound
  dsimp only
  change wp Project.Beck.«module» ((matrixRowBody.drop 50).take 54 ++ matrixRowBody.drop 104) Q middle _ env
  apply matrixPushCapacity_owned env middle current _ _ rfl oldNode.root words (matrixEntry input point category index)
    (tail 4) (tail 5) (tail 7) (tail 8) _ _ _ _ _ _ _ remaining pageLimit
    owned.buffer.values (ownedWords_protects owned) valid bound budget
  intro allocated
  dsimp only
  intro allocatedValid newOwned allocationFrame allocatedBudget previous cursor capacity afterAllocation
  change wp Project.Beck.«module» ((matrixRowBody.drop 104).take 14 ++ ((matrixRowBody.drop 118).take 12 ++ matrixRowBody.drop 130)) Q allocated _ env
  apply matrixInstall_exact env allocated _ rfl _ oldNode.root words.size (allocatedNode current.top need current.nodes).root
    (matrixEntry input point category index) (tail 7) (tail 8) need previous cursor capacity afterAllocation _
  apply matrixCleanup_exact env initial allocated original (current.allocate need) _ oldNode
    (allocatedNode current.top need current.nodes) words (words.push (matrixEntry input point category index)) initialOwner remaining pageLimit
    allocatedValid (allocationFrame.ownsWords allocatedValid owned) newOwned (preserved.trans allocationFrame) active separated allocatedBudget
  all_goals first
    | (solve | simp only [matrixInstalledFrame, matrixPushFrame, matrixParams, inputValues, pointValues,
        matrixPrefix, matrixSuffix, matrixInstalledSaved, matrixInstalledAfter, matrixReadSaved, matrixRowSaved,
        matrixEntryAfter, matrixRowAfter, Bool.and_false, Bool.false_eq_true,
        Locals.get, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, List.length,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, decide_false, reduceIte, need])
    | skip
  intro final finalHeap finalValid finalOwned finalFrame finalBudget
  apply matrixFinish_exact env final input point inputOwner inputPointer pointOwner pointPointer category index oldNode.root initialOwner words.size
    (matrixReadSaved input point pointOwner pointPointer category index oldNode.root saved)
    (allocatedNode current.top need current.nodes).root (matrixEntry input point category index)
    (tail 7) (tail 8) need previous cursor capacity afterAllocation _ rfl rfl rfl rfl
    (by simp [matrixEntryAfter, matrixRowAfter]) (by change index + 1 < 18446744073709551616; omega)
  exact next final finalHeap _ finalValid finalOwned finalFrame fresh finalBudget

#print axioms matrixRowStep_exact

end Project.Beck.Execution
