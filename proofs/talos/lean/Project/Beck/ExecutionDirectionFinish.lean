import Project.Beck.ExecutionDirectionLoop
import Project.Beck.ExecutionKeptRelease

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionFinishedLocals (locals : List Value) (root : UInt64) : List Value :=
  (((((locals.set 83 (.i64 root)).set 84 (.i64 root)).set 85 (.i64 root)).set 86 (.i64 root)).set 87 (.i64 root)).set 88 (.i64 root)

theorem directionFinished_update (locals : List Value) (typed : WordLocals locals) (root : UInt64) :
    WordUpdate locals (directionFinishedLocals locals root) 83 6 := by
  unfold directionFinishedLocals
  exact ((((((WordUpdate.refl typed 83 6).set 83 root (by omega) (by omega)).set 84 root (by omega) (by omega)).set
    85 root (by omega) (by omega)).set 86 root (by omega) (by omega)).set 87 root (by omega) (by omega)).set 88 root (by omega) (by omega)

set_option maxRecDepth 4096 in
theorem directionFinishPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (root : UInt64) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (ownerRead : locals[54]? = some (.i64 root)) (pointerRead : locals[55]? = some (.i64 root))
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := directionFinishedLocals locals root })) :
    wp Project.Beck.«module» ((directionEligible.drop 86).take 12) Q initial { params := params, locals := locals } env := by
  simp only [directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ownerRead, pointerRead, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem direction_finish_shape : directionEligible.drop 86 =
    (directionEligible.drop 86).take 12 ++ keptReleaseProgram 61 96 := rfl

theorem directionFinish_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (params locals : List Value) (firstNode resultNode : FreeNode) (firstWords resultWords : Array UInt64)
    (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (firstRead : locals[52]? = some (.i64 firstNode.root)) (ownerRead : locals[54]? = some (.i64 resultNode.root))
    (pointerRead : locals[55]? = some (.i64 resultNode.root))
    (remaining pageLimit : Nat) (valid : heap.At middle)
    (firstOwned : heap.OwnsWords middle firstNode firstWords) (resultOwned : heap.OwnsWords middle resultNode resultWords)
    (preserved : original.Frame initial heap middle) (fresh : FreshFor original firstNode)
    (separated : firstNode.root ≠ resultNode.root → regionsDisjoint firstNode.region resultNode.region)
    (budget : OutputBudget middle heap remaining pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final resultNode resultWords →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final { params := params, locals := directionFinishedLocals locals resultNode.root })) :
    wp Project.Beck.«module» (directionEligible.drop 86) Q middle { params := params, locals := locals } env := by
  let prepared := directionFinishedLocals locals resultNode.root
  have preparedSize : prepared.length = 112 := by simp [prepared, directionFinishedLocals, localsSize]
  rw [direction_finish_shape]
  refine Sequence.wp_append (P := fun store frame => store = middle ∧ frame = { params := params, locals := prepared }) ?_ ?_
  · exact directionFinishPrepare_exact env middle params locals resultNode.root paramsSize localsSize ownerRead pointerRead _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  simpa only [List.append_nil] using keptRelease_exact env initial middle original heap
    { params := params, locals := prepared } 61 96 firstNode resultNode firstWords resultWords remaining pageLimit valid firstOwned resultOwned
    preserved fresh separated budget rfl
    (by simpa only [Locals.get, paramsSize, preparedSize, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      prepared, directionFinishedLocals, List.length_set, localsSize, List.getElem?_set, Nat.reduceEqDiff] using firstRead)
    (by simp [Locals.get, paramsSize, prepared, directionFinishedLocals, localsSize]) Q [] (by
      intro final finalHeap finalValid finalOwned finalFrame finalBudget
      rw [wp_nil]
      exact next final finalHeap finalValid finalOwned finalFrame finalBudget)

#print axioms directionFinish_exact

end Project.Beck.Execution
