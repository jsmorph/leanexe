import Project.Beck.ExecutionRoundLoop
import Project.Beck.ExecutionKeptRelease

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundFinishedLocals (locals : List Value) (root denominator : UInt64) : List Value :=
  ((((((locals.set 47 (.i64 root)).set 48 (.i64 root)).set 49 (.i64 root)).set 50 (.i64 root)).set
    51 (.i64 denominator)).set 52 (.i64 root)).set 53 (.i64 root)

theorem roundFinished_update (locals : List Value) (typed : WordLocals locals) (root denominator : UInt64) :
    WordUpdate locals (roundFinishedLocals locals root denominator) 47 7 := by
  unfold roundFinishedLocals
  exact (((((((WordUpdate.refl typed 47 7).set 47 root (by omega) (by omega)).set 48 root (by omega) (by omega)).set
    49 root (by omega) (by omega)).set 50 root (by omega) (by omega)).set 51 denominator (by omega) (by omega)).set
    52 root (by omega) (by omega)).set 53 root (by omega) (by omega)

set_option maxRecDepth 4096 in
theorem roundFinishPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (root denominator : UInt64) (paramsSize : params.length = 9) (localsSize : locals.length = 77)
    (ownerRead : locals[36]? = some (.i64 root)) (pointerRead : locals[37]? = some (.i64 root))
    (denRead : locals[32]? = some (.i64 denominator)) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := roundFinishedLocals locals root denominator })) :
    wp Project.Beck.«module» ((roundUpdating.drop 60).take 14) Q initial { params := params, locals := locals } env := by
  simp only [roundUpdating, roundUsable, func33, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ownerRead, pointerRead, denRead, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem round_finish_shape : roundUpdating.drop 60 =
    (roundUpdating.drop 60).take 14 ++ keptReleaseProgram 43 61 := rfl

theorem roundFinish_exact (env : HostEnv Unit) (initial middle : Store Unit) (original heap : Heap)
    (params locals : List Value) (denominator : UInt64) (firstNode resultNode : FreeNode) (firstWords resultWords : Array UInt64)
    (paramsSize : params.length = 9) (localsSize : locals.length = 77)
    (firstRead : locals[34]? = some (.i64 firstNode.root)) (ownerRead : locals[36]? = some (.i64 resultNode.root))
    (pointerRead : locals[37]? = some (.i64 resultNode.root))
    (denRead : locals[32]? = some (.i64 denominator)) (remaining pageLimit : Nat) (valid : heap.At middle)
    (firstOwned : heap.OwnsWords middle firstNode firstWords) (resultOwned : heap.OwnsWords middle resultNode resultWords)
    (preserved : original.Frame initial heap middle) (fresh : FreshFor original firstNode)
    (separated : firstNode.root ≠ resultNode.root → regionsDisjoint firstNode.region resultNode.region)
    (budget : OutputBudget middle heap remaining pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final resultNode resultWords →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final { params := params, locals := roundFinishedLocals locals resultNode.root denominator })) :
    wp Project.Beck.«module» (roundUpdating.drop 60) Q middle { params := params, locals := locals } env := by
  let prepared := roundFinishedLocals locals resultNode.root denominator
  have preparedSize : prepared.length = 77 := by simp [prepared, roundFinishedLocals, localsSize]
  rw [round_finish_shape]
  refine Sequence.wp_append (P := fun store frame => store = middle ∧ frame = { params := params, locals := prepared }) ?_ ?_
  · exact roundFinishPrepare_exact env middle params locals resultNode.root denominator paramsSize localsSize ownerRead pointerRead denRead _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  simpa only [List.append_nil] using keptRelease_exact env initial middle original heap
    { params := params, locals := prepared } 43 61 firstNode resultNode firstWords resultWords remaining pageLimit valid firstOwned resultOwned
    preserved fresh separated budget rfl
    (by simpa only [Locals.get, paramsSize, preparedSize, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      prepared, roundFinishedLocals, List.length_set, localsSize, List.getElem?_set, Nat.reduceEqDiff] using firstRead)
    (by simp [Locals.get, paramsSize, prepared, roundFinishedLocals, localsSize]) Q [] (by
      intro final finalHeap finalValid finalOwned finalFrame finalBudget
      rw [wp_nil]
      exact next final finalHeap finalValid finalOwned finalFrame finalBudget)

#print axioms roundFinish_exact

end Project.Beck.Execution
