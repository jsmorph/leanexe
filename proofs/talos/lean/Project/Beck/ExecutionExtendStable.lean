import Project.Beck.ExecutionExtendPrepare
import Project.Beck.ExecutionExtendAfterCandidate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def extendScanRegisters : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 122, 123, 124, 126, 127, 137, 139]

theorem ExtendScanLocals.preserved {locals next : List Value} {row rows width : Nat}
    (state : ExtendScanLocals locals row rows width) (size : next.length = locals.length)
    (reads : ∀ k ∈ extendScanRegisters, next[k]? = locals[k]?) : ExtendScanLocals next row rows width := by
  refine ⟨size.trans state.size, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k bound
    interval_cases k <;> rw [reads _ (by decide)] <;> exact state.outerEmpty _ (by decide)
  all_goals rw [reads _ (by decide)]
  · exact state.currentRow
  · exact state.rowIndex
  · exact state.rowLimit
  · exact state.rowStep
  · exact state.columnLimit
  · exact state.columnStep
  · exact state.oldRows
  · exact state.oldColumns

theorem extendPrepared_scan {locals : List Value} {row rows width : Nat}
    (state : ExtendScanLocals locals row rows width) (matrixOwner matrixPointer : UInt64)
    (basis : Basis) (rowOwner rowPointer columnOwner columnPointer : UInt64) (column : Nat) :
    ExtendScanLocals (extendPreparedLocals locals width matrixOwner matrixPointer basis
      rowOwner rowPointer columnOwner columnPointer row column) row rows width := by
  apply state.preserved
  · simp [extendPreparedLocals]
  · intro k member
    simp only [extendScanRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [extendPreparedLocals, List.getElem?_set]

theorem extendInstalled_scan {locals : List Value} {row rows width : Nat}
    (state : ExtendScanLocals locals row rows width) (found : Bool) (rowPointer columnPointer value : UInt64) :
    ExtendScanLocals (extendInstalledLocals locals found rowPointer columnPointer value) row rows width := by
  apply state.preserved
  · simp [extendInstalledLocals, extendSelectedLocals]
  · intro k member
    simp only [extendScanRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [extendInstalledLocals, extendSelectedLocals, List.getElem?_set]

theorem extendAdvanced_scan {locals : List Value} {row rows width : Nat}
    (state : ExtendScanLocals locals row rows width) (column : Nat) :
    ExtendScanLocals (extendAdvancedLocals locals column) row rows width := by
  apply state.preserved
  · simp [extendAdvancedLocals]
  · intro k member
    simp only [extendScanRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [extendAdvancedLocals, List.getElem?_set]

structure ExtendChoiceLocals (locals : List Value) (found : Bool) (rows columns value : UInt64) : Prop where
  tag : locals[8]? = some (.i64 (if found then 1 else 0))
  rowsOwner : locals[9]? = some (.i64 (if found then rows else 0))
  rowsPointer : locals[10]? = some (.i64 (if found then rows else 0))
  columnsOwner : locals[11]? = some (.i64 (if found then columns else 0))
  columnsPointer : locals[12]? = some (.i64 (if found then columns else 0))
  determinant : locals[13]? = some (.i64 (if found then value else 0))
  extraOwner : locals[14]? = some (.i64 0)

theorem extendInstalled_choice (locals : List Value) (size : locals.length = 158)
    (found : Bool) (rows columns value : UInt64) :
    ExtendChoiceLocals (extendInstalledLocals locals found rows columns value) found rows columns value := by
  constructor <;> simp [extendInstalledLocals, extendSelectedLocals, List.getElem?_set, size]

#print axioms extendPrepared_scan
#print axioms extendInstalled_scan
#print axioms extendAdvanced_scan
#print axioms extendInstalled_choice

end Project.Beck.Execution
