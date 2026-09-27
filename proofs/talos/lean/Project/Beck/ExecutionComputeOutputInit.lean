import Project.Beck.ExecutionComputeHeaderLocal
import Project.Beck.ExecutionComputeOutputState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def computeOutputStartLocals (locals : List Value) (root : UInt64) (jobs : Nat) : List Value :=
  (((((locals.set 56 (.i64 0)).set 57 (.i64 jobs.toUInt64)).set 58 (.i64 1)).set 37 (.i64 root)).set 38 (.i64 root)).set 77 (.i64 root)

set_option maxRecDepth 4096 in
theorem computeOutputStart_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (pointer root : UInt64) (jobs : Nat) (size : locals.length = 79)
    (jobsRead : locals[9]? = some (.i64 jobs.toUInt64))
    (ownerRead : locals[35]? = some (.i64 root)) (pointerRead : locals[36]? = some (.i64 root))
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := [.i64 pointer], locals := computeOutputStartLocals locals root jobs })) :
    wp Project.Beck.«module» ((computeOutput.drop 71).take 12) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  simp only [computeOutput, computeAccepted, func35, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [size, jobsRead, ownerRead, pointerRead, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem compute_output_init_shape : computeOutput.take 83 = computeOutput.take 71 ++ (computeOutput.drop 71).take 12 := rfl

set_option maxRecDepth 4096 in
theorem computeOutputInit_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (pointer : UInt64) (input : Input) (initialOwner initialPointer pointRoot : UInt64)
    (size : locals.length = 79) (typed : WordLocals locals)
    (jobsRead : locals[9]? = some (.i64 input.jobs.toUInt64)) (overlapRead : locals[11]? = some (.i64 input.overlap.toUInt64))
    (initialOwnerRead : locals[25]? = some (.i64 initialOwner)) (initialPointerRead : locals[26]? = some (.i64 initialPointer))
    (pointRead : locals[32]? = some (.i64 pointRoot)) (remaining pageLimit : Nat)
    (valid : heap.At initial) (budget : OutputBudget initial heap (72 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : let final := pairWords heap initial 0 input.overlap.toUInt64
      let node := allocatedNode heap.top 24 heap.nodes
      (heap.allocate 24).At final → (heap.allocate 24).OwnsWords final node #[0, input.overlap.toUInt64] →
      heap.Frame initial (heap.allocate 24) final → FreshFor heap node →
      OutputBudget final (heap.allocate 24) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, ComputeOutputLocals nextLocals input.jobs input.overlap initialOwner initialPointer pointRoot node.root node.root 0 →
      Q (.Fallthrough final { params := [.i64 pointer], locals := nextLocals })) :
    wp Project.Beck.«module» (computeOutput.take 83) Q initial { params := [.i64 pointer], locals := locals } env := by
  rw [compute_output_init_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module» ((computeOutput.drop 71).take 12) Q store frame env)
    ?_ (fun _ _ h => h)
  apply computeHeaderLocal_exact env initial heap pointer input.overlap.toUInt64 locals size typed overlapRead remaining pageLimit valid budget
  dsimp only
  intro finalValid owned preserved fresh finalBudget filled update firstOwnerRead firstPointerRead
  dsimp only [Sequence.Fallthrough]
  have filledSize : filled.length = 79 := update.size.trans size
  have finalJobs := (update.keeps 9 (Or.inl (by decide))).trans jobsRead
  have finalOverlap := (update.keeps 11 (Or.inl (by decide))).trans overlapRead
  have finalInitialOwner := (update.keeps 25 (Or.inl (by decide))).trans initialOwnerRead
  have finalInitialPointer := (update.keeps 26 (Or.inl (by decide))).trans initialPointerRead
  have finalPoint := (update.keeps 32 (Or.inl (by decide))).trans pointRead
  apply computeOutputStart_exact env _ filled pointer (allocatedNode heap.top 24 heap.nodes).root input.jobs filledSize
    finalJobs firstOwnerRead firstPointerRead
  apply next finalValid owned preserved fresh finalBudget
  constructor
  · simp [computeOutputStartLocals, filledSize]
  · unfold computeOutputStartLocals
    repeat' apply WordLocals.set
    exact update.words
  all_goals simp only [computeOutputStartLocals, List.length_set, List.getElem?_set, filledSize,
    Nat.reduceLT, Nat.reduceEqDiff, reduceIte, finalJobs, finalOverlap, finalInitialOwner, finalInitialPointer,
    finalPoint, firstOwnerRead, firstPointerRead]
  all_goals rfl

#print axioms computeOutputInit_exact

end Project.Beck.Execution
