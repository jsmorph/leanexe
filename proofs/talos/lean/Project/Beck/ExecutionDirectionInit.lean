import Project.Beck.ExecutionDirectionFree

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionInitialLocals (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer root : UInt64) : List Value :=
  directionMatrixLocals (directionPreparedLocals (List.replicate 112 (.i64 0)) input point inputOwner inputPointer pointOwner pointPointer) input.jobs root

theorem directionInitialLocals_size (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer root : UInt64) :
    (directionInitialLocals input point inputOwner inputPointer pointOwner pointPointer root).length = 112 := by
  simp [directionInitialLocals, directionMatrixLocals, directionPreparedLocals]

theorem directionInitialLocals_high (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer root : UInt64)
    (i : Nat) (lower : 17 ≤ i) (upper : i < 112) :
    (directionInitialLocals input point inputOwner inputPointer pointOwner pointPointer root)[i]? = some (.i64 0) := by
  simp (discharger := omega) only [directionInitialLocals, directionMatrixLocals, directionPreparedLocals,
    List.getElem?_set_ne, List.getElem?_replicate_of_lt]

theorem direction_window (params locals : List Value) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (reads : ∀ i < 6, locals[93 + i]? = some (.i64 0)) :
    ({ params := params, locals := locals } : Locals) =
      FixedArraySearch.frame params (locals.take 93) (locals.drop 99) 0 0 0 0 0 0 := by
  exact FixedArraySearch.frame_eq_of_gets { params := params, locals := locals } 93 0 0 0 0 0 0
    (by simp only [localsSize]; decide) rfl (by
      intro i hi
      simp only [Locals.get, paramsSize, localsSize,
        show ¬9 + 93 + i < 9 by omega, show 9 + 93 + i < 9 + 112 by omega, reduceIte,
        show 9 + 93 + i - 9 = 93 + i by omega, reads i hi]
      interval_cases i <;> rfl)

theorem direction_initial_window (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer root : UInt64) :
    let locals := directionInitialLocals input point inputOwner inputPointer pointOwner pointPointer root
    ({ params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } : Locals) =
      FixedArraySearch.frame (matrixParams input point inputOwner inputPointer pointOwner pointPointer)
        (locals.take 93) (locals.drop 99) 0 0 0 0 0 0 := by
  exact direction_window (matrixParams input point inputOwner inputPointer pointOwner pointPointer)
    (directionInitialLocals input point inputOwner inputPointer pointOwner pointPointer root)
    (by simp [matrixParams, inputValues, pointValues]) (directionInitialLocals_size ..)
    (fun i hi => directionInitialLocals_high input point inputOwner inputPointer pointOwner pointPointer root (93 + i) (by omega) (by omega))

theorem direction_seed_basis_state (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer matrix ro rp co cp : UInt64)
    (previous current capacity afterNode : UInt64) :
    let locals := directionInitialLocals input point inputOwner inputPointer pointOwner pointPointer matrix
    DirectionBasisLocals (FixedArraySearch.frame (matrixParams input point inputOwner inputPointer pointOwner pointPointer)
      (directionSeedSaved (locals.take 93) ro rp co cp) (locals.drop 99) 8 previous current capacity afterNode cp).locals
      input.jobs matrix ro rp co cp := by
  dsimp only
  constructor <;>
    simp [FixedArraySearch.frame, directionSeedSaved, directionEmptySaved,
      directionInitialLocals, directionMatrixLocals, directionPreparedLocals]

set_option maxRecDepth 4096 in
theorem direction_init_shape : func30.take 214 = func30.take 42 ++ (func30.drop 42).take 172 := rfl

set_option maxRecDepth 4096 in
theorem directionInit_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (inputProtected : heap.Protects inputPointer.toNat (inputPointer.toNat + 8 * (input.incidence.size + 1)))
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (280 + 448 * input.jobs * input.categories + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap matrix ro rp co cp, finalHeap.At final →
      finalHeap.OwnsWords final matrix (protectedMatrix input point) → FreshFor heap matrix →
      heap.Frame initial finalHeap final → DirectionSeed heap finalHeap final ro rp co cp →
      (regionsDisjoint matrix.region ro.region ∧ regionsDisjoint matrix.region rp.region ∧
        regionsDisjoint matrix.region co.region ∧ regionsDisjoint matrix.region cp.region) →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity afterNode,
      let locals := directionInitialLocals input point inputOwner inputPointer pointOwner pointPointer matrix.root
      Q (.Fallthrough final (FixedArraySearch.frame (matrixParams input point inputOwner inputPointer pointOwner pointPointer)
        (directionSeedSaved (locals.take 93) ro.root rp.root co.root cp.root) (locals.drop 99) 8 previous current capacity afterNode cp.root))) :
    wp Project.Beck.«module» (func30.take 214) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := List.replicate 112 (.i64 0) } env := by
  rw [direction_init_shape]
  apply Sequence.wp_append (P := fun store frame => ∃ middleHeap matrix, middleHeap.At store ∧
    middleHeap.OwnsWords store matrix (protectedMatrix input point) ∧ heap.Frame initial middleHeap store ∧ FreshFor heap matrix ∧
    OutputBudget store middleHeap (224 + remaining) pageLimit Project.Beck.«module» ∧
    frame = { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := directionInitialLocals input point inputOwner inputPointer pointOwner pointPointer matrix.root })
  · apply directionStart_exact env initial heap input point inputOwner inputPointer pointOwner pointPointer
      _ (by simp) (224 + remaining) pageLimit valid pointArray pointProtected inputArray inputProtected pointSize inputSize jobs categories overlap
      (by convert budget using 1; omega)
    intro final finalHeap matrix finalValid owned preserved fresh finalBudget
    exact ⟨finalHeap, matrix, finalValid, owned, preserved, fresh, finalBudget, rfl⟩
  rintro middle frame ⟨middleHeap, matrix, middleValid, matrixOwned, matrixFrame, matrixFresh, matrixBudget, rfl⟩
  rw [direction_initial_window]
  simpa only [List.append_nil] using directionSeed_exact env middle middleHeap _ _ _
    (by simp [matrixParams, inputValues, pointValues])
    (by simp [directionInitialLocals, directionMatrixLocals, directionPreparedLocals])
    (by simp [directionInitialLocals, directionMatrixLocals, directionPreparedLocals])
    0 0 0 0 0 0 remaining pageLimit middleValid matrixBudget Q [] (by
      intro final finalHeap ro rp co cp finalValid finalFrame seed finalBudget previous current capacity afterNode
      rw [wp_nil]
      refine next final finalHeap matrix ro rp co cp finalValid (finalFrame.ownsWords finalValid matrixOwned)
        matrixFresh (matrixFrame.trans finalFrame) ?_ ?_ finalBudget previous current capacity afterNode
      · exact { seed with
          rowOwnerFresh := seed.rowOwnerFresh.original matrixFrame
          rowPointerFresh := seed.rowPointerFresh.original matrixFrame
          columnOwnerFresh := seed.columnOwnerFresh.original matrixFrame
          columnPointerFresh := seed.columnPointerFresh.original matrixFrame }
      · exact ⟨seed.rowOwnerFresh.separated matrixOwned seed.rowOwner.buffer.rootBound,
          seed.rowPointerFresh.separated matrixOwned seed.rowPointer.buffer.rootBound,
          seed.columnOwnerFresh.separated matrixOwned seed.columnOwner.buffer.rootBound,
          seed.columnPointerFresh.separated matrixOwned seed.columnPointer.buffer.rootBound⟩)

#print axioms directionInit_exact

end Project.Beck.Execution
