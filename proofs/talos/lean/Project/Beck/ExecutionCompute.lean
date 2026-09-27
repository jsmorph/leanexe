import Project.Beck.ExecutionComputeAccepted
import Project.Beck.ExecutionComputeRead

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def computeBytes (jobs : Nat) : Nat := 112 + 1520 * jobs + computeAcceptedBytes jobs

def computeMaxBytes : Nat := 223756952

theorem computeBytes_bound (jobs : Nat) (capacity : jobs ≤ 6) : computeBytes jobs ≤ computeMaxBytes := by
  change 112 + 1520 * jobs + (2 * (48 + 8 * (jobs + 1)) + 37291120 * jobs + 72 + 120 * jobs) ≤ 223756952
  omega

theorem accepted_overlap_bound (words : Array UInt64) (accepted : (readInput words).status = 0) :
    (readInput words).overlap ≤ 8 := by
  have valid := Project.Beck.Parser.accepted_valid words accepted
  rcases valid.1.maximum with zero | ⟨job, _, attained⟩
  · change (readInput words).overlap = 0 at zero
    omega
  · have bound : Project.Beck.Parser.degree (readInput words).categories (readInput words).incidence job ≤
        (readInput words).categories := by
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    change Project.Beck.Parser.degree (readInput words).categories (readInput words).incidence job =
      (readInput words).overlap at attained
    rw [attained] at bound
    exact bound.trans valid.2.2

def computeRejected : Wasm.Program := match (func35[40]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 4096 in
theorem compute_function_shape : func35 = func35.take 25 ++
    ((func35.drop 25).take 15 ++ [.iff 0 0 computeRejected computeAccepted, .localGet 56]) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem compute_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (pointer : UInt64) (words : Array UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (represented : UInt64Array.At initial pointer words)
    (wordsProtected : heap.Protects pointer.toNat (pointer.toNat + 8 * (words.size + 1)))
    (accepted : (readInput words).status = 0)
    (budget : OutputBudget initial heap (computeBytes (readInput words).jobs + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 35 initial [.i64 pointer]
      (fun final values => ∃ finalHeap node, finalHeap.At final ∧ finalHeap.OwnsWords final node (compute words) ∧
        heap.Frame initial finalHeap final ∧ FreshFor heap node ∧
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧ values = [.i64 node.root]) := by
  have supported := Project.Beck.Parser.accepted_supported words accepted
  have inputValid := Project.Beck.Parser.accepted_valid words accepted
  have jobsEq : (readInput words).jobs = words[0]!.toNat := by
    obtain ⟨_, _, _, _, _, result⟩ := Project.Beck.Parser.accepted_data words accepted
    exact congrArg Input.jobs result
  refine TerminatesWith.of_wp_entry_for (f := func35Def) rfl ?_
  change wp Project.Beck.«module» func35 _ initial
    { params := [.i64 pointer], locals := List.replicate 79 (.i64 0) } env
  rw [compute_function_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ((func35.drop 25).take 15 ++ [.iff 0 0 computeRejected computeAccepted, .localGet 56]) _ store frame env)
    ?_ (fun _ _ h => h)
  apply computeRead_exact env initial heap pointer words (computeAcceptedBytes (readInput words).jobs + remaining)
    pageLimit valid represented wordsProtected accepted
    (budget.mono (by simp only [computeBytes, jobsEq]; omega))
  intro parsedStore parsedHeap inputNode inputOwner parsedValid inputOwned parsedFrame parsedBudget ownerMode locals state
  dsimp only [Sequence.Fallthrough]
  refine Sequence.wp_append (P := fun store frame => store = parsedStore ∧
    frame = { params := [.i64 pointer], locals := locals, values := [.i32 0] }) ?_ ?_
  · exact computeStatus_exact env parsedStore locals pointer (readInput words) inputOwner inputNode.root state accepted _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  refine wp_iff_cons rfl ?_
  simp only [ne_eq, not_true_eq_false, reduceIte]
  apply computeAccepted_exact env parsedStore parsedHeap locals pointer (readInput words) inputNode inputOwner remaining pageLimit
    state parsedValid supported inputOwned ownerMode inputValid.1.size inputValid.2.2 (accepted_overlap_bound words accepted) parsedBudget
  intro final finalHeap resultNode finalValid resultOwned finalFrame resultFresh finalBudget finalLocals finalSize resultRead
  change wp Project.Beck.«module» [.localGet 56] _ final { params := [.i64 pointer], locals := finalLocals } env
  wp_run [finalSize, resultRead, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
  refine ⟨finalHeap, resultNode, finalValid, ?_, parsedFrame.trans finalFrame, resultFresh.original parsedFrame, finalBudget, ?_⟩
  · simpa only [Project.Beck.Result.compute_eq words accepted supported] using resultOwned
  · simp only [func35Def]
    rfl

#print axioms computeBytes_bound
#print axioms compute_exact

end Project.Beck.Execution
