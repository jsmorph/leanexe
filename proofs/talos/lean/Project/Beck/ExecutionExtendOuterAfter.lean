import Project.Beck.ExecutionExtendOuterFinish

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem extend_outer_after_shape : extendBody.drop 31 =
    (extendBody.drop 31).take 78 ++ ((extendBody.drop 109).take 51 ++ extendBody.drop 160) := rfl

set_option maxRecDepth 4096 in
theorem extendOuterAfter_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (paramsSize : params.length = 8) (localsSize : locals.length = 158)
    (emptyRows : locals[1]? = some (.i64 0)) (emptyColumns : locals[3]? = some (.i64 0))
    (row : Nat) (rowBound : row < 56)
    (rowRead : locals[122]? = some (.i64 row.toUInt64)) (stepRead : locals[124]? = some (.i64 1))
    (found : Bool) (rows columns value : UInt64)
    (choice : ExtendChoiceLocals locals found rows columns value) (Q : Assertion Unit)
    (next : if found then Q (.Break 1 initial { params := params, locals := extendOuterInstalledLocals locals found rows columns value })
      else Q (.Break 0 initial { params := params, locals := extendOuterAdvancedLocals (extendOuterInstalledLocals locals found rows columns value) row })) :
    wp Project.Beck.«module» (extendBody.drop 31) Q initial { params := params, locals := locals } env := by
  rw [extend_outer_after_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧
    frame = { params := params, locals := extendOuterSelectedLocals locals found rows columns value })
  · exact extendOuterSelect_exact env initial params locals paramsSize localsSize found rows columns value choice _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  apply Sequence.wp_append (P := fun st frame => st = initial ∧
    frame = { params := params, locals := extendOuterHandledLocals locals found rows columns value })
  · exact extendOuterCleanup_exact env initial params locals paramsSize localsSize emptyRows emptyColumns found rows columns value _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  exact extendOuterFinish_exact env initial params locals paramsSize localsSize row rowBound rowRead stepRead found rows columns value Q next

structure ExtendOuterChoiceLocals (locals : List Value) (found : Bool) (rows columns value : UInt64) : Prop where
  size : locals.length = 158
  tag : locals[0]? = some (.i64 (if found then 1 else 0))
  rowsOwner : locals[1]? = some (.i64 (if found then rows else 0))
  rowsPointer : locals[2]? = some (.i64 (if found then rows else 0))
  columnsOwner : locals[3]? = some (.i64 (if found then columns else 0))
  columnsPointer : locals[4]? = some (.i64 (if found then columns else 0))
  determinant : locals[5]? = some (.i64 (if found then value else 0))
  extraOwner : locals[6]? = some (.i64 0)

theorem extendOuterInstalled_choice (locals : List Value) (size : locals.length = 158)
    (found : Bool) (rows columns value : UInt64) :
    ExtendOuterChoiceLocals (extendOuterInstalledLocals locals found rows columns value) found rows columns value := by
  constructor <;> simp [extendOuterInstalledLocals, extendOuterHandledLocals, extendOuterSelectedLocals, size]

theorem extendOuterContinue_state {locals : List Value} {row rows width : Nat}
    (state : ExtendScanLocals locals row rows width) :
    ExtendOuterLocals (extendOuterAdvancedLocals (extendOuterInstalledLocals locals false 0 0 0) row) (row + 1) rows := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [extendOuterAdvancedLocals, extendOuterInstalledLocals, extendOuterHandledLocals, extendOuterSelectedLocals, state.size]
  · intro k bound
    interval_cases k <;> simp [extendOuterAdvancedLocals, extendOuterInstalledLocals, extendOuterHandledLocals, extendOuterSelectedLocals, state.size]
  · simp [extendOuterAdvancedLocals, extendOuterInstalledLocals, extendOuterHandledLocals, extendOuterSelectedLocals, state.size]
  · simpa [extendOuterAdvancedLocals, extendOuterInstalledLocals, extendOuterHandledLocals, extendOuterSelectedLocals] using state.rowLimit
  · simpa [extendOuterAdvancedLocals, extendOuterInstalledLocals, extendOuterHandledLocals, extendOuterSelectedLocals] using state.rowStep

def ExtendOuterOutput (original current : Heap) (store : Store Unit) (locals : List Value) (result : Option Basis) : Prop :=
  match result with
  | none => ExtendOuterChoiceLocals locals false 0 0 0
  | some basis => ∃ rows columns, CandidateBasis original current store basis rows columns ∧
      ExtendOuterChoiceLocals locals true rows.root columns.root basis.determinant

theorem ExtendOuterLocals.choice {locals : List Value} {row rows : Nat}
    (state : ExtendOuterLocals locals row rows) : ExtendOuterChoiceLocals locals false 0 0 0 := by
  refine ⟨state.size, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact state.empty _ (by decide)

#print axioms extendOuterAfter_exact
#print axioms extendOuterContinue_state

end Project.Beck.Execution
