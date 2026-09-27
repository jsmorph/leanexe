import Project.Beck.ExecutionComputeInitial
import Project.Beck.ExecutionRoundsInitial

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def computeRoundedLocals (locals : List Value) (point : Point) (owner root : UInt64) : List Value :=
  ((((locals.set 29 (.i64 root)).set 28 (.i64 owner)).set 27 (.i64 point.denominator)).set 30 (.i64 point.denominator)).set 32 (.i64 root)

set_option maxRecDepth 4096 in
theorem computeRoundsPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (pointer : UInt64) (input : Input) (inputOwner inputRoot pointOwner pointRoot : UInt64)
    (state : ComputeInitialLocals locals input inputOwner inputRoot pointOwner pointRoot) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := [.i64 pointer], locals := locals, values := (roundsParams (inputOwner := inputOwner) input.jobs input ⟨1, Array.replicate input.jobs 0⟩
        inputRoot pointOwner pointRoot).reverse })) :
    wp Project.Beck.«module» ((computeAccepted.drop 120).take 10) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  simp only [computeAccepted, func35, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop]
  wp_run [state.size, state.fuel, state.inputStatus, state.inputJobs, state.inputCategories, state.inputOverlap,
    state.inputOwner, state.inputPointer, state.denominator, state.pointOwner, state.pointPointer,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem computeRoundsRead_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (pointer : UInt64) (point : Point) (owner root : UInt64) (size : locals.length = 79)
    (nonzero : point.denominator ≠ 0) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := [.i64 pointer], locals := computeRoundedLocals locals point owner root, values := [.i32 0] })) :
    wp Project.Beck.«module» ((computeAccepted.drop 131).take 17) Q initial
      { params := [.i64 pointer], locals := locals, values := pointValues point owner root } env := by
  simp only [computeAccepted, func35, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop, pointValues]
  repeat' first
    | wp_run [size, nonzero, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
        show (1 : UInt64) ≠ 0 by decide, show (0 : UInt64) ≠ 1 by decide, show (1 : UInt32) ≠ 0 by decide,
        ne_eq, not_true_eq_false, not_false_eq_true, List.take, List.drop, List.append_nil, reduceIte]
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  exact next

set_option maxRecDepth 4096 in
theorem compute_rounds_shape : (computeAccepted.drop 120).take 28 =
    (computeAccepted.drop 120).take 10 ++ (.call 34 :: (computeAccepted.drop 131).take 17) := rfl

set_option maxRecDepth 4096 in
theorem computeRounds_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (pointer : UInt64) (input : Input) (inputNode pointNode : FreeNode) (inputOwner pointOwner : UInt64)
    (remaining pageLimit : Nat)
    (state : ComputeInitialLocals locals input inputOwner inputNode.root pointOwner pointNode.root)
    (valid : heap.At initial) (supported : Project.Beck.State.Supported input)
    (pointOwned : heap.OwnsWords initial pointNode (Array.replicate input.jobs 0))
    (inputOwned : heap.OwnsWords initial inputNode input.incidence) (different : pointNode.root ≠ inputNode.root)
    (ownerMode : input.jobs = 0 ∨ inputOwner = inputNode.root)
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (roundMaxBytes * input.jobs + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap resultNode resultOwner, finalHeap.At final →
      finalHeap.OwnsWords final resultNode (Project.Beck.Result.finalPoint input).numerators →
      heap.Frame initial finalHeap final → (resultNode = pointNode ∨ FreshFor heap resultNode) → resultNode.root ≠ inputNode.root →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final { params := [.i64 pointer], locals := computeRoundedLocals locals (Project.Beck.Result.finalPoint input) resultOwner resultNode.root, values := [.i32 0] })) :
    wp Project.Beck.«module» ((computeAccepted.drop 120).take 28) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  rw [compute_rounds_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    (.call 34 :: (computeAccepted.drop 131).take 17) Q store frame env) ?_ (fun _ _ h => h)
  apply computeRoundsPrepare_exact env initial locals pointer input inputOwner inputNode.root pointOwner pointNode.root state
  dsimp only [Sequence.Fallthrough]
  refine wp_call_tw (rounds_initial_exact env initial heap input inputNode pointNode inputOwner pointOwner remaining pageLimit
    valid supported pointOwned inputOwned different ownerMode inputSize categories overlap budget) ?_
  rintro final values ⟨finalHeap, resultNode, resultOwner, finalValid, resultOwned, preserved, output, resultDifferent, finalBudget, rfl⟩
  apply computeRoundsRead_exact env final locals pointer (Project.Beck.Result.finalPoint input) resultOwner resultNode.root
    state.size (Project.Beck.Loop.initial_finishes input supported).1
  exact next final finalHeap resultNode resultOwner finalValid resultOwned preserved output resultDifferent finalBudget

#print axioms computeRounds_exact

end Project.Beck.Execution
