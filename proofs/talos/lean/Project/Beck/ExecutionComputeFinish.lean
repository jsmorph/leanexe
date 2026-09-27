import Project.Beck.ExecutionComputeOutputState
import Project.Beck.ExecutionKeptRelease

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def computeFinishedLocals (locals : List Value) (root : UInt64) : List Value :=
  (((((locals.set 50 (.i64 root)).set 51 (.i64 root)).set 52 (.i64 root)).set 53 (.i64 root)).set 54 (.i64 root)).set 55 (.i64 root)

theorem computeFinished_update (locals : List Value) (typed : WordLocals locals) (root : UInt64) :
    WordUpdate locals (computeFinishedLocals locals root) 50 6 := by
  unfold computeFinishedLocals
  exact ((((((WordUpdate.refl typed 50 6).set 50 root (by omega) (by omega)).set 51 root (by omega) (by omega)).set
    52 root (by omega) (by omega)).set 53 root (by omega) (by omega)).set 54 root (by omega) (by omega)).set 55 root (by omega) (by omega)

set_option maxRecDepth 4096 in
theorem computeFinishPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (root : UInt64) (paramsSize : params.length = 1) (localsSize : locals.length = 79)
    (ownerRead : locals[37]? = some (.i64 root)) (pointerRead : locals[38]? = some (.i64 root))
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := computeFinishedLocals locals root })) :
    wp Project.Beck.«module» ((computeOutput.drop 84).take 12) Q initial { params := params, locals := locals } env := by
  simp only [computeOutput, computeAccepted, func35, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ownerRead, pointerRead, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem compute_finish_shape : computeOutput.drop 84 =
    (computeOutput.drop 84).take 12 ++ keptReleaseProgram 36 55 := rfl

theorem computeFinish_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (params locals : List Value) (firstNode resultNode : FreeNode) (firstWords resultWords : Array UInt64)
    (paramsSize : params.length = 1) (localsSize : locals.length = 79)
    (firstRead : locals[35]? = some (.i64 firstNode.root)) (ownerRead : locals[37]? = some (.i64 resultNode.root))
    (pointerRead : locals[38]? = some (.i64 resultNode.root))
    (remaining pageLimit : Nat) (valid : heap.At middle)
    (firstOwned : heap.OwnsWords middle firstNode firstWords) (resultOwned : heap.OwnsWords middle resultNode resultWords)
    (preserved : original.Frame initial heap middle) (fresh : FreshFor original firstNode)
    (separated : firstNode.root ≠ resultNode.root → regionsDisjoint firstNode.region resultNode.region)
    (budget : OutputBudget middle heap remaining pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final resultNode resultWords →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final { params := params, locals := computeFinishedLocals locals resultNode.root })) :
    wp Project.Beck.«module» (computeOutput.drop 84) Q middle { params := params, locals := locals } env := by
  let prepared := computeFinishedLocals locals resultNode.root
  have preparedSize : prepared.length = 79 := by simp [prepared, computeFinishedLocals, localsSize]
  rw [compute_finish_shape]
  refine Sequence.wp_append (P := fun store frame => store = middle ∧ frame = { params := params, locals := prepared }) ?_ ?_
  · exact computeFinishPrepare_exact env middle params locals resultNode.root paramsSize localsSize ownerRead pointerRead _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  simpa only [List.append_nil] using keptRelease_exact env initial middle original heap
    { params := params, locals := prepared } 36 55 firstNode resultNode firstWords resultWords remaining pageLimit valid firstOwned resultOwned
    preserved fresh separated budget rfl
    (by simpa only [Locals.get, paramsSize, preparedSize, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      prepared, computeFinishedLocals, List.length_set, localsSize, List.getElem?_set, Nat.reduceEqDiff] using firstRead)
    (by simp [Locals.get, paramsSize, prepared, computeFinishedLocals, localsSize]) Q [] (by
      intro final finalHeap finalValid finalOwned finalFrame finalBudget
      rw [wp_nil]
      exact next final finalHeap finalValid finalOwned finalFrame finalBudget)

#print axioms computeFinish_exact

end Project.Beck.Execution
