import Project.Beck.ExecutionExtendOuterStep

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def extendOuterMeasure (rows : Nat) (_store : Store Unit) (frame : Locals) : Nat :=
  match (frame.locals[122]? : Option Value) with
  | some (.i64 row) => rows - row.toNat
  | _ => 0

def extendOuterInv (initial : Store Unit) (heap : Heap) (width : Nat) (matrix : Array UInt64) (basis : Basis)
    (params : List Value) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current row locals,
    current.At store ∧ heap.Frame initial current store ∧ row ≤ matrix.size / width ∧
    (∀ earlier < row, (List.range width).findSome? (borderCandidate width matrix basis earlier) = none) ∧
    OutputBudget store current ((208 + determinantBytes (basis.rows.size + 1)) * width * (matrix.size / width - row) + remaining) pageLimit Project.Beck.«module» ∧
    ExtendOuterLocals locals row (matrix.size / width) ∧ frame = { params := params, locals := locals }

def extendOuterDone (initial : Store Unit) (heap : Heap) (width : Nat) (matrix : Array UInt64) (basis : Basis)
    (params : List Value) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current locals, current.At store ∧ heap.Frame initial current store ∧
    OutputBudget store current remaining pageLimit Project.Beck.«module» ∧
    ExtendOuterOutput heap current store locals (Project.Beck.Basis.extension width matrix basis) ∧
    frame = { params := params, locals := locals }

set_option maxRecDepth 4096 in
theorem extend_outer_guard_shape : extendBody =
    [.localGet 130, .localGet 131, .geUI64, .br_if 1] ++ extendBody.drop 4 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extendOuterLoop_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (width : Nat) (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (locals : List Value)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (wellFormed : Project.Beck.Basis.WellFormed width matrix basis)
    (widthBound : width ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size < 6)
    (state : ExtendOuterLocals locals 0 (matrix.size / width))
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer basis.rows) (columnsAt : UInt64Array.At initial columnPointer basis.columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (basis.rows.size + 1)))
    (columnsProtected : heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (basis.columns.size + 1)))
    (budget : OutputBudget initial heap ((208 + determinantBytes (basis.rows.size + 1)) * width * (matrix.size / width) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, ExtendOuterOutput heap finalHeap final nextLocals (Project.Beck.Basis.extension width matrix basis) →
        wp Project.Beck.«module» rest Q final
          { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := nextLocals } env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 extendBody]] ++ rest) Q initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  let params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
  have paramsSize : params.length = 8 := by simp [params, extendParams, basisValues]
  have rowsBound : matrix.size / width ≤ 56 := (Nat.div_le_self matrix.size width).trans matrixBound
  have rowsFit : matrix.size / width < UInt64.size := by change matrix.size / width < 18446744073709551616; omega
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ extendBody
    (extendOuterInv initial heap width matrix basis params remaining pageLimit)
    (extendOuterDone initial heap width matrix basis params remaining pageLimit) (extendOuterMeasure (matrix.size / width))
  · rintro store frame ⟨current, row, currentLocals, _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨current, currentLocals, _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, 0, locals, valid, Heap.Frame.refl heap initial, Nat.zero_le _, by simp,
      by simpa only [Nat.sub_zero] using budget, state, rfl⟩
  · rintro store frame ⟨current, row, currentLocals, currentValid, preserved, rowBound, earlier, currentBudget, currentState, rfl⟩
    have rowFit : row < UInt64.size := rowBound.trans_lt rowsFit
    rw [extend_outer_guard_shape]
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, paramsSize, currentState.size,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, currentState.rowIndex, currentState.rowLimit,
      wp_geUI64_cons, wp_br_if_cons]
    by_cases inside : row < matrix.size / width
    · have guard : ¬(matrix.size / width).toUInt64 ≤ row.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' rowsFit, UInt64.toNat_ofNat_of_lt' rowFit]
        omega
      simp only [ge_iff_le, guard, reduceIte]
      have cost : (208 + determinantBytes (basis.rows.size + 1)) * width +
          ((208 + determinantBytes (basis.rows.size + 1)) * width * (matrix.size / width - (row + 1)) + remaining) =
          (208 + determinantBytes (basis.rows.size + 1)) * width * (matrix.size / width - row) + remaining := by
        rw [show matrix.size / width - row = (matrix.size / width - (row + 1)) + 1 by omega, Nat.mul_add, Nat.mul_one]
        omega
      apply extendOuterStep_exact env store current width matrix matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        row currentLocals ((208 + determinantBytes (basis.rows.size + 1)) * width * (matrix.size / width - (row + 1)) + remaining) pageLimit
        currentValid wellFormed widthBound matrixBound rankBound inside currentState
        (preserved.words matrixProtected matrixAt) (preserved.words rowsProtected rowsAt) (preserved.words columnsProtected columnsAt)
        (preserved.protects _ _ matrixProtected) (preserved.protects _ _ rowsProtected) (preserved.protects _ _ columnsProtected)
        (by simpa only [cost] using currentBudget)
      · intro absent final finalHeap finalValid finalFrame finalBudget nextLocals nextState
        change extendOuterInv initial heap width matrix basis params remaining pageLimit final _ ∧ _
        refine ⟨⟨finalHeap, row + 1, nextLocals, finalValid, preserved.trans finalFrame, by omega, ?_, finalBudget, nextState, rfl⟩, ?_⟩
        · intro k bound
          by_cases same : k = row
          · simpa only [same] using absent
          · exact earlier k (by omega)
        · simp only [extendOuterMeasure, nextState.rowIndex, currentState.rowIndex,
            UInt64.toNat_ofNat_of_lt' rowFit,
            UInt64.toNat_ofNat_of_lt' (show row + 1 < UInt64.size by omega)]
          omega
      · intro result candidate final finalHeap rowsNode columnsNode finalValid finalFrame finalBudget owned nextLocals choice
        change extendOuterDone initial heap width matrix basis params remaining pageLimit final _
        refine ⟨finalHeap, nextLocals, finalValid, preserved.trans finalFrame, finalBudget.mono (by omega), ?_, rfl⟩
        rw [Project.Beck.Basis.extension, rangeSearch_found _ (matrix.size / width) row result inside earlier candidate]
        exact ⟨rowsNode, columnsNode, owned.original preserved, choice⟩
    · have equal : row = matrix.size / width := by omega
      subst row
      simp only [UInt64.le_refl, reduceIte]
      change extendOuterDone initial heap width matrix basis params remaining pageLimit store _
      refine ⟨current, currentLocals, currentValid, preserved, ?_, ?_, rfl⟩
      · simpa only [Nat.sub_self, Nat.mul_zero, Nat.zero_add] using currentBudget
      · have absent : Project.Beck.Basis.extension width matrix basis = none := by
          simpa only [Project.Beck.Basis.extension, List.findSome?_eq_none_iff, List.mem_range] using earlier
        rw [absent]
        exact currentState.choice
  · rintro final frame ⟨finalHeap, nextLocals, finalValid, finalFrame, finalBudget, output, rfl⟩
    exact next final finalHeap finalValid finalFrame finalBudget nextLocals output

#print axioms extendOuterLoop_exact

end Project.Beck.Execution
