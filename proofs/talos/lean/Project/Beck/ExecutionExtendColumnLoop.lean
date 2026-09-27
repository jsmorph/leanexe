import Project.Beck.ExecutionExtendSearch

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extendColumnLoop_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (width : Nat) (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (row : Nat) (locals : List Value)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (wellFormed : Project.Beck.Basis.WellFormed width matrix basis)
    (widthBound : width ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size < 6)
    (rowBound : row < matrix.size / width)
    (state : ExtendSearchLocals locals row (matrix.size / width) 0 width)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer basis.rows) (columnsAt : UInt64Array.At initial columnPointer basis.columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (basis.rows.size + 1)))
    (columnsProtected : heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (basis.columns.size + 1)))
    (budget : OutputBudget initial heap ((208 + determinantBytes (basis.rows.size + 1)) * width + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, ExtendScanLocals nextLocals row (matrix.size / width) width →
        ExtendColumnOutput heap finalHeap final nextLocals ((List.range width).findSome? (borderCandidate width matrix basis row)) →
        wp Project.Beck.«module» rest Q final
          { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := nextLocals } env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 extendColumnBody]] ++ rest) Q initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  let params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
  have paramsSize : params.length = 8 := by simp [params, extendParams, basisValues]
  have widthFit : width < UInt64.size := by change width < 18446744073709551616; omega
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ extendColumnBody
    (extendColumnInv initial heap width matrix basis row params remaining pageLimit)
    (extendColumnDone initial heap width matrix basis row params remaining pageLimit) (extendColumnMeasure width)
  · rintro store frame ⟨current, column, currentLocals, _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨current, currentLocals, _, _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, 0, locals, valid, Heap.Frame.refl heap initial, Nat.zero_le _, by simp,
      by simpa only [Nat.sub_zero] using budget, state, rfl⟩
  · rintro store frame ⟨current, column, currentLocals, currentValid, preserved, columnBound, earlier, currentBudget, currentState, rfl⟩
    have columnFit : column < UInt64.size := columnBound.trans_lt widthFit
    rw [extend_column_guard_shape]
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, paramsSize, currentState.size,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, currentState.columnIndex, currentState.columnLimit,
      wp_geUI64_cons, wp_br_if_cons]
    by_cases inside : column < width
    · have guard : ¬width.toUInt64 ≤ column.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' widthFit, UInt64.toNat_ofNat_of_lt' columnFit]
        omega
      simp only [ge_iff_le, guard, reduceIte]
      have cost : 208 + determinantBytes (basis.rows.size + 1) +
          ((208 + determinantBytes (basis.rows.size + 1)) * (width - (column + 1)) + remaining) =
          (208 + determinantBytes (basis.rows.size + 1)) * (width - column) + remaining := by
        rw [show width - column = (width - (column + 1)) + 1 by omega, Nat.mul_add, Nat.mul_one]
        omega
      apply extendColumnStep_exact env store current width matrix matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        row column currentLocals ((208 + determinantBytes (basis.rows.size + 1)) * (width - (column + 1)) + remaining) pageLimit
        currentValid wellFormed widthBound matrixBound rankBound rowBound inside currentState
        (preserved.words matrixProtected matrixAt) (preserved.words rowsProtected rowsAt) (preserved.words columnsProtected columnsAt)
        (preserved.protects _ _ matrixProtected) (preserved.protects _ _ rowsProtected) (preserved.protects _ _ columnsProtected)
        (by simpa only [cost] using currentBudget)
      · intro absent final finalHeap finalValid finalFrame finalBudget nextLocals nextState
        change extendColumnInv initial heap width matrix basis row params remaining pageLimit final _ ∧ _
        refine ⟨⟨finalHeap, column + 1, nextLocals, finalValid, preserved.trans finalFrame, by omega, ?_, finalBudget, nextState, rfl⟩, ?_⟩
        · intro k bound
          by_cases same : k = column
          · simpa only [same] using absent
          · exact earlier k (by omega)
        · simp only [extendColumnMeasure, nextState.columnIndex, currentState.columnIndex,
            UInt64.toNat_ofNat_of_lt' columnFit,
            UInt64.toNat_ofNat_of_lt' (show column + 1 < UInt64.size by omega)]
          omega
      · intro result candidate final finalHeap rowsNode columnsNode finalValid finalFrame finalBudget owned nextLocals scan choice
        change extendColumnDone initial heap width matrix basis row params remaining pageLimit final _
        refine ⟨finalHeap, nextLocals, finalValid, preserved.trans finalFrame, finalBudget.mono (by omega), scan, ?_, rfl⟩
        rw [rangeSearch_found _ width column result inside earlier candidate]
        exact ⟨rowsNode, columnsNode, owned.original preserved, choice⟩
    · have equal : column = width := by omega
      subst column
      simp only [UInt64.le_refl, reduceIte]
      change extendColumnDone initial heap width matrix basis row params remaining pageLimit store _
      refine ⟨current, currentLocals, currentValid, preserved, ?_, currentState.toExtendScanLocals, ?_, rfl⟩
      · simpa only [Nat.sub_self, Nat.mul_zero, Nat.zero_add] using currentBudget
      · have absent : (List.range width).findSome? (borderCandidate width matrix basis row) = none := by
          simpa only [List.findSome?_eq_none_iff, List.mem_range] using earlier
        rw [absent]
        exact currentState.choice
  · rintro final frame ⟨finalHeap, nextLocals, finalValid, finalFrame, finalBudget, scan, output, rfl⟩
    exact next final finalHeap finalValid finalFrame finalBudget nextLocals scan output

#print axioms extendColumnLoop_exact

end Project.Beck.Execution
