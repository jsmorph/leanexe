import Project.Beck.ExecutionComputeRounds
import Project.Beck.ExecutionComputeCleanup

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def computeAcceptedBytes (jobs : Nat) : Nat :=
  2 * (48 + 8 * (jobs + 1)) + roundMaxBytes * jobs + 72 + 120 * jobs

def computeFailed : Wasm.Program := match (computeAccepted[148]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 4096 in
theorem compute_accepted_shape : computeAccepted = computeAccepted.take 120 ++
    ((computeAccepted.drop 120).take 28 ++
      ([.iff 0 0 computeFailed computeOutput] ++ computeAccepted.drop 149)) := rfl

theorem computeRounded_update (locals : List Value) (typed : WordLocals locals) (point : Point) (owner root : UInt64) :
    WordUpdate locals (computeRoundedLocals locals point owner root) 27 6 := by
  unfold computeRoundedLocals
  exact (((((WordUpdate.refl typed 27 6).set 29 root (by omega) (by omega)).set 28 owner (by omega) (by omega)).set
    27 point.denominator (by omega) (by omega)).set 30 point.denominator (by omega) (by omega)).set 32 root (by omega) (by omega)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem computeAccepted_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (pointer : UInt64) (input : Input) (inputNode : FreeNode) (inputOwner : UInt64) (remaining pageLimit : Nat)
    (state : ComputeInputLocals locals input inputOwner inputNode.root)
    (valid : heap.At initial) (supported : Project.Beck.State.Supported input)
    (inputOwned : heap.OwnsWords initial inputNode input.incidence)
    (ownerMode : input.jobs = 0 ∨ inputOwner = inputNode.root)
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (computeAcceptedBytes input.jobs + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap resultNode, finalHeap.At final →
      finalHeap.OwnsWords final resultNode (Project.Beck.Result.output input (Project.Beck.Result.finalPoint input)) →
      heap.Frame initial finalHeap final → FreshFor heap resultNode →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ finalLocals, finalLocals.length = 79 → finalLocals[55]? = some (.i64 resultNode.root) →
      Q (.Fallthrough final { params := [.i64 pointer], locals := finalLocals })) :
    wp Project.Beck.«module» computeAccepted Q initial { params := [.i64 pointer], locals := locals } env := by
  rw [compute_accepted_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ((computeAccepted.drop 120).take 28 ++ ([.iff 0 0 computeFailed computeOutput] ++ computeAccepted.drop 149)) Q store frame env)
    ?_ (fun _ _ h => h)
  apply computeInitial_exact env initial heap locals pointer input inputOwner inputNode.root
    (roundMaxBytes * input.jobs + 72 + 120 * input.jobs + remaining) pageLimit state supported.capacity valid
    (budget.mono (by simp only [computeAcceptedBytes]; omega))
  intro seededStore seededHeap ownerNode pointNode seededValid ownerOwned pointOwned seededFrame ownerFresh pointFresh separated seededBudget seededLocals seededState
  dsimp only [Sequence.Fallthrough]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ([.iff 0 0 computeFailed computeOutput] ++ computeAccepted.drop 149) Q store frame env) ?_ (fun _ _ h => h)
  apply computeRounds_exact env seededStore seededHeap seededLocals pointer input inputNode pointNode inputOwner ownerNode.root
    (72 + 120 * input.jobs + remaining) pageLimit seededState seededValid supported pointOwned
    (seededFrame.ownsWords seededValid inputOwned)
    (pointFresh.pointer_ne inputNode.root input.incidence.size (ownedWords_protects inputOwned)
      (by have := pointOwned.buffer.capacity; omega) pointOwned.buffer.rootBound)
    ownerMode inputSize categories overlap (seededBudget.mono (by omega))
  intro roundedStore roundedHeap roundedNode roundedOwner roundedValid roundedOwned roundedFrame _ _ roundedBudget
  dsimp only [Sequence.Fallthrough]
  simp only [List.cons_append, List.nil_append]
  refine wp_iff_cons rfl ?_
  simp only [ne_eq, not_true_eq_false, reduceIte]
  let roundedLocals := computeRoundedLocals seededLocals (Project.Beck.Result.finalPoint input) roundedOwner roundedNode.root
  have update := computeRounded_update seededLocals seededState.words (Project.Beck.Result.finalPoint input) roundedOwner roundedNode.root
  apply computeOutput_exact env roundedStore roundedHeap roundedLocals pointer input (Project.Beck.Result.finalPoint input)
    ownerNode.root pointNode.root roundedNode.root (update.size.trans seededState.size) update.words
    ((update.keeps 9 (Or.inl (by decide))).trans seededState.jobs)
    ((update.keeps 11 (Or.inl (by decide))).trans seededState.overlap)
    ((update.keeps 25 (Or.inl (by decide))).trans seededState.pointOwner)
    ((update.keeps 26 (Or.inl (by decide))).trans seededState.pointPointer)
    (by simp [roundedLocals, computeRoundedLocals, seededState.size]) remaining pageLimit roundedValid supported.capacity
    roundedOwned.buffer.values (Nat.le_of_eq (Project.Beck.Loop.initial_finishes input supported).2.1.symm)
    (ownedWords_protects roundedOwned) roundedBudget
  intro outputStore outputHeap resultNode outputValid resultOwned outputFrame resultFresh outputBudget outputLocals outputState
  change wp Project.Beck.«module» (computeAccepted.drop 149) Q outputStore { params := [.i64 pointer], locals := outputLocals } env
  have ownerRounded := roundedFrame.ownsWords roundedValid ownerOwned
  have pointRounded := roundedFrame.ownsWords roundedValid pointOwned
  apply computeCleanup_exact env initial outputStore heap outputHeap pointer outputLocals ownerNode pointNode resultNode
    (Array.replicate input.jobs 0) (Project.Beck.Result.output input (Project.Beck.Result.finalPoint input)) outputState
    remaining pageLimit outputValid (outputFrame.ownsWords outputValid ownerRounded) (outputFrame.ownsWords outputValid pointRounded)
    resultOwned (seededFrame.trans (roundedFrame.trans outputFrame)) ownerFresh pointFresh separated
    (resultFresh.separated ownerRounded resultOwned.buffer.rootBound)
    (resultFresh.separated pointRounded resultOwned.buffer.rootBound) outputBudget
  intro final finalHeap finalValid finalOwned finalFrame finalBudget
  exact next final finalHeap resultNode finalValid finalOwned finalFrame
    (resultFresh.original (seededFrame.trans roundedFrame)) finalBudget outputLocals outputState.size outputState.pointer

#print axioms computeAccepted_exact

end Project.Beck.Execution
