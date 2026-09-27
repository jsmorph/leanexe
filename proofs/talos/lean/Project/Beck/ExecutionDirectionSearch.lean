import Project.Beck.ExecutionDirectionSearchFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionSearchBytes (input : Input) (point : Point) : Nat :=
  280 + 448 * input.jobs * input.categories + findBasisRoundBytes input.jobs (protectedMatrix input point) * input.jobs

set_option maxRecDepth 4096 in
theorem direction_search_shape : func30.take 275 = func30.take 214 ++
    ((func30.drop 214).take 12 ++ (func30.drop 226).take 49) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionSearch_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (inputProtected : heap.Protects inputPointer.toNat (inputPointer.toNat + 8 * (input.incidence.size + 1)))
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (matrixBound : (protectedMatrix input point).size ≤ 56) (rowsBound : (protectedMatrix input point).size / input.jobs < 6)
    (budget : OutputBudget initial heap (directionSearchBytes input point + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap matrix srOwner srPointer scOwner scPointer ro rp co cp locals,
      finalHeap.At final → finalHeap.OwnsWords final matrix (protectedMatrix input point) → FreshFor heap matrix →
      heap.Frame initial finalHeap final → DirectionSeed heap finalHeap final srOwner srPointer scOwner scPointer →
      (regionsDisjoint matrix.region srOwner.region ∧ regionsDisjoint matrix.region srPointer.region ∧
        regionsDisjoint matrix.region scOwner.region ∧ regionsDisjoint matrix.region scPointer.region) →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      BasisReferences finalHeap final (findBasis input.jobs input.jobs (protectedMatrix input point) ⟨#[], #[], 1⟩) rp cp →
      DirectionSearchLocals locals matrix.root srOwner.root srPointer.root scOwner.root scPointer.root
        (findBasis input.jobs input.jobs (protectedMatrix input point) ⟨#[], #[], 1⟩) ro rp co cp →
      Q (.Fallthrough final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals,
          values := [.i64 (freeColumn input point (findBasis input.jobs input.jobs (protectedMatrix input point) ⟨#[], #[], 1⟩).columns).toUInt64] })) :
    wp Project.Beck.«module» (func30.take 275) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := List.replicate 112 (.i64 0) } env := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  let matrixData := protectedMatrix input point
  let basis := findBasis input.jobs input.jobs matrixData ⟨#[], #[], 1⟩
  let searchBytes := findBasisRoundBytes input.jobs matrixData * input.jobs
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  rw [direction_search_shape]
  apply Sequence.wp_append (P := fun store frame => ∃ current matrix sro srp sco scp locals,
    current.At store ∧ current.OwnsWords store matrix matrixData ∧ FreshFor heap matrix ∧ heap.Frame initial current store ∧
    DirectionSeed heap current store sro srp sco scp ∧
    (regionsDisjoint matrix.region sro.region ∧ regionsDisjoint matrix.region srp.region ∧
      regionsDisjoint matrix.region sco.region ∧ regionsDisjoint matrix.region scp.region) ∧
    OutputBudget store current (searchBytes + remaining) pageLimit Project.Beck.«module» ∧
    DirectionSeedLocals locals input.jobs matrix.root sro.root srp.root sco.root scp.root ∧
    frame = { params := params, locals := locals })
  · apply directionInit_exact env initial heap input point inputOwner inputPointer pointOwner pointPointer
      (searchBytes + remaining) pageLimit valid pointArray pointProtected inputArray inputProtected pointSize inputSize jobs categories overlap
      (by simpa only [directionSearchBytes, searchBytes, matrixData, Nat.add_assoc] using budget)
    intro final finalHeap matrix sro srp sco scp finalValid owned fresh preserved seed separated finalBudget previous current capacity afterNode
    exact ⟨finalHeap, matrix, sro, srp, sco, scp, _, finalValid, owned, fresh, preserved, seed, separated, finalBudget,
      directionSeed_state input point inputOwner inputPointer pointOwner pointPointer matrix.root sro.root srp.root sco.root scp.root previous current capacity afterNode, rfl⟩
  rintro middle frame ⟨middleHeap, matrix, sro, srp, sco, scp, locals, middleValid, owned, fresh, preserved, seed, separated, middleBudget, state, rfl⟩
  apply Sequence.wp_append (P := fun store frame => ∃ current ro rp co cp,
    current.At store ∧ middleHeap.Frame middle current store ∧
    OutputBudget store current remaining pageLimit Project.Beck.«module» ∧ BasisReferences current store basis rp cp ∧
    frame = { params := params, locals := locals.set 23 (.i64 1), values := basisValues basis ro rp co cp })
  · apply directionBasis_exact env middle middleHeap params locals input.jobs matrixData matrix.root sro.root srp.root sco.root scp.root
      paramsSize state.toDirectionBasisLocals remaining pageLimit middleValid jobs matrixBound rowsBound owned.buffer.values (ownedWords_protects owned)
      ⟨seed.rowPointer.buffer.values, seed.columnPointer.buffer.values, ownedWords_protects seed.rowPointer, ownedWords_protects seed.columnPointer⟩ middleBudget
    intro final finalHeap ro rp co cp finalValid finalFrame finalBudget refs _
    exact ⟨finalHeap, ro, rp, co, cp, finalValid, finalFrame, finalBudget, refs, rfl⟩
  rintro final frame ⟨finalHeap, ro, rp, co, cp, finalValid, finalFrame, finalBudget, refs, rfl⟩
  apply directionFree_exact env final (locals.set 23 (.i64 1)) input point basis inputOwner inputPointer pointOwner pointPointer ro rp co cp
    (by simpa using state.size) ((preserved.trans finalFrame).words pointProtected pointArray) refs.columnsAt pointSize
  exact next final finalHeap matrix sro srp sco scp ro rp co cp _ finalValid (finalFrame.ownsWords finalValid owned)
    fresh (preserved.trans finalFrame) (seed.preserved finalFrame finalValid) separated finalBudget refs
    (directionSearch_state input point basis inputOwner inputPointer pointOwner pointPointer matrix.root sro.root srp.root sco.root scp.root ro rp co cp locals state)

#print axioms directionSearch_exact

end Project.Beck.Execution
