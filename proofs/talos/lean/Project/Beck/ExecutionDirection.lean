import Project.Beck.ExecutionDirectionCleanup

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionBytes (input : Input) (point : Point) : Nat :=
  directionSearchBytes input point + directionAssemblyBytes (Project.Beck.Direction.sourceBasis input point) input.jobs

def directionUnavailable : Wasm.Program := match (func30[288]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 4096 in
theorem direction_function_shape : func30 = func30.take 275 ++ ((func30.drop 275).take 13 ++
    ([.iff 0 0 directionUnavailable directionEligible] ++ func30.drop 289)) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem direction_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (inputProtected : heap.Protects inputPointer.toNat (inputPointer.toNat + 8 * (input.incidence.size + 1)))
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (matrixBound : (protectedMatrix input point).size ≤ 56) (rowsBound : (protectedMatrix input point).size / input.jobs < 6)
    (wellFormed : Project.Beck.Basis.WellFormed input.jobs (protectedMatrix input point) (Project.Beck.Direction.sourceBasis input point))
    (rankBound : (Project.Beck.Direction.sourceBasis input point).rows.size ≤ 6)
    (freeBound : freeColumn input point (Project.Beck.Direction.sourceBasis input point).columns < input.jobs)
    (budget : OutputBudget initial heap (directionBytes input point + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 30 initial
      (matrixParams input point inputOwner inputPointer pointOwner pointPointer).reverse
      (fun final values => ∃ finalHeap node, finalHeap.At final ∧ finalHeap.OwnsWords final node (direction input point) ∧
        heap.Frame initial finalHeap final ∧ FreshFor heap node ∧
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧ values = [.i64 node.root, .i64 node.root]) := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  let basis := Project.Beck.Direction.sourceBasis input point
  let free := freeColumn input point basis.columns
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  refine TerminatesWith.of_wp_entry_for (f := func30Def) rfl ?_
  change wp Project.Beck.«module» func30 _ initial { params := params, locals := List.replicate 112 (.i64 0) } env
  rw [direction_function_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ((func30.drop 275).take 13 ++ ([.iff 0 0 directionUnavailable directionEligible] ++ func30.drop 289)) _ store frame env) ?_ (fun _ _ h => h)
  apply directionSearch_exact env initial heap input point inputOwner inputPointer pointOwner pointPointer
    (directionAssemblyBytes basis input.jobs + remaining) pageLimit valid pointArray pointProtected inputArray inputProtected
    pointSize inputSize jobs categories overlap matrixBound rowsBound
  · simpa only [directionBytes, basis, Nat.add_assoc] using budget
  · intro searchStore searchHeap matrixNode sro srp sco scp ro rp co cp searchLocals searchValid matrixOwned matrixFresh searchFrame seed separated searchBudget refs state
    dsimp only [Sequence.Fallthrough]
    let guarded := (searchLocals.set 45 (.i64 free.toUInt64)).set 46 (.i64 free.toUInt64)
    have guardUpdate : WordUpdate searchLocals guarded 45 2 :=
      ((WordUpdate.refl state.words 45 2).set 45 free.toUInt64 (by omega) (by omega)).set 46 free.toUInt64 (by omega) (by omega)
    have guardState := state.updated guardUpdate (by omega)
    refine Sequence.wp_append (P := fun store frame => store = searchStore ∧
      frame = { params := params, locals := guarded, values := [.i32 0] }) ?_ ?_
    · exact directionGuard_exact env searchStore searchLocals input point inputOwner inputPointer pointOwner pointPointer free
        state.size jobs freeBound _ ⟨rfl, rfl⟩
    rintro store frame ⟨same, frameSame⟩
    subst store frame
    simp only [List.cons_append, List.nil_append]
    refine wp_iff_cons rfl ?_
    simp only [ne_eq, not_true_eq_false, reduceIte]
    apply directionAssembly_exact env searchStore searchHeap guarded input point basis (protectedMatrix input point)
      inputOwner inputPointer pointOwner pointPointer matrixNode.root sro.root srp.root sco.root scp.root ro rp co cp
      free remaining pageLimit guardState
    · simp [guarded, state.size]
    · exact searchValid
    · exact wellFormed
    · exact jobs
    · exact matrixBound
    · exact rankBound
    · exact freeBound
    · exact matrixOwned.buffer.values
    · exact refs
    · exact ownedWords_protects matrixOwned
    · exact searchBudget
    · intro assemblyStore assemblyHeap resultNode assemblyValid resultOwned assemblyFrame resultFresh assemblyBudget assemblyLocals assemblyState resultRead pointerRead
      change wp Project.Beck.«module» (func30.drop 289) _ assemblyStore { params := params, locals := assemblyLocals } env
      have resultSeparation : ∀ entry ∈ directionCleanupEntries matrixNode sro srp sco scp (protectedMatrix input point),
          regionsDisjoint entry.node.region resultNode.region := by
        intro entry member
        simp only [directionCleanupEntries, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl
        · exact resultFresh.separated seed.columnPointer resultOwned.buffer.rootBound
        · exact resultFresh.separated seed.columnOwner resultOwned.buffer.rootBound
        · exact resultFresh.separated seed.rowPointer resultOwned.buffer.rootBound
        · exact resultFresh.separated seed.rowOwner resultOwned.buffer.rootBound
        · exact resultFresh.separated matrixOwned resultOwned.buffer.rootBound
      apply directionCleanup_exact env initial assemblyStore heap assemblyHeap params assemblyLocals matrixNode sro srp sco scp resultNode
        (protectedMatrix input point) (Project.Beck.Direction.assemble input.jobs (protectedMatrix input point) basis free) basis ro rp co cp
        paramsSize assemblyState resultRead pointerRead remaining pageLimit assemblyValid
        (assemblyFrame.ownsWords assemblyValid matrixOwned) resultOwned (seed.preserved assemblyFrame assemblyValid)
        (searchFrame.trans assemblyFrame) matrixFresh separated.1 separated.2.1 separated.2.2.1 separated.2.2.2
        resultSeparation assemblyBudget
      intro final finalHeap finalValid finalOwned finalFrame finalBudget
      refine ⟨finalHeap, resultNode, finalValid, ?_, finalFrame, resultFresh.original searchFrame, finalBudget, ?_⟩
      · simpa only [Project.Beck.Direction.direction_eq input point freeBound] using finalOwned
      · simp only [func30Def]
        rfl

#print axioms direction_exact

end Project.Beck.Execution
