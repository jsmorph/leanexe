import Project.Beck.ExecutionDirectionStep
import Project.Beck.Direction
import Project.ProofKit.BlockLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionPrefix (jobs : Nat) (matrix : Array UInt64) (basis : Basis) (free : Nat) (seed : Array UInt64) (index : Nat) : Array UInt64 :=
  Project.Beck.Scatter.write (List.range index) (fun j => basis.columns[j]!.toNat)
    (Project.Beck.Direction.coefficient jobs matrix basis free) seed

theorem directionPrefix_size (jobs : Nat) (matrix : Array UInt64) (basis : Basis) (free : Nat) (seed : Array UInt64) (index : Nat) :
    (directionPrefix jobs matrix basis free seed index).size = seed.size := Project.Beck.Scatter.size ..

theorem directionPrefix_succ (jobs : Nat) (matrix : Array UInt64) (basis : Basis) (free : Nat) (seed : Array UInt64) (index : Nat)
    (inside : index < basis.columns.size) :
    directionPrefix jobs matrix basis free seed (index + 1) =
      (directionPrefix jobs matrix basis free seed index).set! basis.columns[index].toNat
        (0 - determinant basis.rows.size jobs matrix basis.rows (basis.columns.set! index free.toUInt64)) := by
  simp [directionPrefix, Project.Beck.Scatter.write, List.range_succ, List.foldl_append,
    Project.Beck.Direction.coefficient, getElem!_pos basis.columns index inside]

def directionLoopMeasure (rank : Nat) (_store : Store Unit) (frame : Locals) : Nat :=
  match (frame.locals[89]? : Option Value) with
  | some (.i64 index) => rank - index.toNat
  | _ => 0

set_option maxRecDepth 4096 in
theorem direction_loop_guard_shape : directionBody =
    [.localGet 98, .localGet 99, .geUI64, .br_if 1] ++ directionBody.drop 4 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionLoop_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (basis : Basis) (matrix seed : Array UInt64) (initialNode : FreeNode)
    (inputOwner inputPointer pointOwner pointPointer matrixPointer sro srp sco scp ro rp co cp : UInt64)
    (free remaining pageLimit : Nat)
    (state : DirectionLoopLocals locals matrixPointer sro srp sco scp basis ro rp co cp initialNode.root initialNode.root free 0)
    (valid : heap.At initial) (owned : heap.OwnsWords initial initialNode seed)
    (wellFormed : Project.Beck.Basis.WellFormed input.jobs matrix basis)
    (widthBound : input.jobs ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size ≤ 6)
    (freeBound : free < input.jobs) (seedSize : seed.size = input.jobs)
    (matrixAt : UInt64Array.At initial matrixPointer matrix) (references : BasisReferences heap initial basis rp cp)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (budget : OutputBudget initial heap (directionCofactorBytes basis input.jobs * basis.columns.size + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap resultNode, finalHeap.At final →
      finalHeap.OwnsWords final resultNode (directionPrefix input.jobs matrix basis free seed basis.columns.size) →
      heap.Frame initial finalHeap final → (resultNode = initialNode ∨ FreshFor heap resultNode) →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, DirectionLoopLocals nextLocals matrixPointer sro srp sco scp basis ro rp co cp initialNode.root resultNode.root free basis.columns.size →
      wp Project.Beck.«module» rest Q final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := nextLocals } env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 directionBody]] ++ rest) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  let Inv : AssertionF Unit := fun store frame => ∃ current index node currentLocals,
    current.At store ∧ heap.Frame initial current store ∧ index ≤ basis.columns.size ∧
    current.OwnsWords store node (directionPrefix input.jobs matrix basis free seed index) ∧
    (node = initialNode ∨ FreshFor heap node) ∧
    OutputBudget store current (directionCofactorBytes basis input.jobs * (basis.columns.size - index) + remaining) pageLimit Project.Beck.«module» ∧
    DirectionLoopLocals currentLocals matrixPointer sro srp sco scp basis ro rp co cp initialNode.root node.root free index ∧
    frame = { params := params, locals := currentLocals }
  let Done : AssertionF Unit := fun store frame => ∃ current node currentLocals,
    current.At store ∧ heap.Frame initial current store ∧
    current.OwnsWords store node (directionPrefix input.jobs matrix basis free seed basis.columns.size) ∧
    (node = initialNode ∨ FreshFor heap node) ∧
    OutputBudget store current remaining pageLimit Project.Beck.«module» ∧
    DirectionLoopLocals currentLocals matrixPointer sro srp sco scp basis ro rp co cp initialNode.root node.root free basis.columns.size ∧
    frame = { params := params, locals := currentLocals }
  have rankFit : basis.columns.size < UInt64.size := by
    rw [← wellFormed.square]
    change basis.rows.size < 18446744073709551616
    omega
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ directionBody Inv Done (directionLoopMeasure basis.columns.size)
  · rintro store frame ⟨current, index, node, currentLocals, _, _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨current, node, currentLocals, _, _, _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, 0, initialNode, locals, valid, Heap.Frame.refl heap initial, Nat.zero_le _, owned, Or.inl rfl,
      by simpa only [Nat.sub_zero] using budget, state, rfl⟩
  · rintro store frame ⟨current, index, node, currentLocals, currentValid, preserved, indexBound, currentOwned, active, currentBudget, currentState, rfl⟩
    have indexFit : index < UInt64.size := indexBound.trans_lt rankFit
    rw [direction_loop_guard_shape]
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, paramsSize, currentState.size,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, currentState.position, currentState.limit,
      wp_geUI64_cons, wp_br_if_cons]
    by_cases inside : index < basis.columns.size
    · have guard : ¬basis.columns.size.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' rankFit, UInt64.toNat_ofNat_of_lt' indexFit]
        omega
      simp only [ge_iff_le, guard, reduceIte]
      have cost : directionCofactorBytes basis input.jobs +
          (directionCofactorBytes basis input.jobs * (basis.columns.size - (index + 1)) + remaining) =
          directionCofactorBytes basis input.jobs * (basis.columns.size - index) + remaining := by
        rw [show basis.columns.size - index = (basis.columns.size - (index + 1)) + 1 by omega, Nat.mul_add, Nat.mul_one]
        omega
      apply directionStep_exact env initial store heap current currentLocals input point basis matrix
        (directionPrefix input.jobs matrix basis free seed index) node
        inputOwner inputPointer pointOwner pointPointer matrixPointer sro srp sco scp ro rp co cp initialNode.root
        free index (directionCofactorBytes basis input.jobs * (basis.columns.size - (index + 1)) + remaining) pageLimit inside
        currentState currentValid currentOwned preserved
        (active.elim (fun same => Or.inl (congrArg FreeNode.root same)) Or.inr)
        wellFormed widthBound matrixBound rankBound freeBound
        ((directionPrefix_size _ _ _ _ _ _).trans seedSize)
        (preserved.words matrixProtected matrixAt) (references.preserved preserved)
        (preserved.protects _ _ matrixProtected) (by simpa only [cost] using currentBudget)
      intro final finalHeap resultNode finalValid finalOwned finalFrame fresh finalBudget nextLocals nextState
      change Inv final _ ∧ _
      refine ⟨⟨finalHeap, index + 1, resultNode, nextLocals, finalValid, finalFrame, by omega, ?_, Or.inr fresh, finalBudget, nextState, rfl⟩, ?_⟩
      · simpa only [directionPrefix_succ input.jobs matrix basis free seed index inside] using finalOwned
      · simp only [directionLoopMeasure, nextState.position, currentState.position,
          UInt64.toNat_ofNat_of_lt' indexFit, UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega)]
        omega
    · have equal : index = basis.columns.size := by omega
      subst index
      simp only [UInt64.le_refl, reduceIte]
      change Done store _
      exact ⟨current, node, currentLocals, currentValid, preserved, currentOwned, active,
        by simpa only [Nat.sub_self, Nat.mul_zero, Nat.zero_add] using currentBudget, currentState, rfl⟩
  · rintro final frame ⟨finalHeap, resultNode, nextLocals, finalValid, finalFrame, finalOwned, active, finalBudget, finalState, rfl⟩
    exact next final finalHeap resultNode finalValid finalOwned finalFrame active finalBudget nextLocals finalState

#print axioms directionLoop_exact

end Project.Beck.Execution
