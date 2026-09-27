import Project.Beck.ExecutionExtendFinish

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem extend_after_candidate_shape : extendColumnBody.drop 37 =
    (extendColumnBody.drop 37).take 58 ++ ((extendColumnBody.drop 95).take 30 ++
      ((extendColumnBody.drop 125).take 74 ++ extendColumnBody.drop 199)) := rfl

set_option maxRecDepth 4096 in
theorem extendAfterCandidate_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (paramsSize : params.length = 8) (localsSize : locals.length = 158)
    (emptyRows : locals[9]? = some (.i64 0)) (emptyColumns : locals[11]? = some (.i64 0))
    (oldRows : locals[137]? = some (.i64 0)) (oldColumns : locals[139]? = some (.i64 0))
    (column : Nat) (columnBound : column < 6)
    (columnRead : locals[125]? = some (.i64 column.toUInt64)) (stepRead : locals[127]? = some (.i64 1))
    (found : Bool) (rows columns value : UInt64) (Q : Assertion Unit)
    (next : if found then Q (.Break 1 initial { params := params, locals := extendInstalledLocals locals found rows columns value })
      else Q (.Break 0 initial { params := params, locals := extendAdvancedLocals (extendInstalledLocals locals found rows columns value) column })) :
    wp Project.Beck.«module» (extendColumnBody.drop 37) Q initial
      { params := params, locals := locals, values :=
        if found then [.i64 value, .i64 columns, .i64 columns, .i64 rows, .i64 rows, .i64 1]
        else List.replicate 6 (.i64 0) } env := by
  rw [extend_after_candidate_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧
    frame = { params := params, locals := extendSelectedLocals locals found rows columns value })
  · exact extendSelect_exact env initial params locals paramsSize localsSize found rows columns value _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  apply Sequence.wp_append (P := fun st frame => st = initial ∧
    frame = { params := params, locals := extendSelectedLocals locals found rows columns value })
  · exact extendCleanup_exact env initial params locals paramsSize localsSize emptyRows emptyColumns found rows columns value _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  apply Sequence.wp_append (P := fun st frame => st = initial ∧
    frame = { params := params, locals := extendInstalledLocals locals found rows columns value })
  · exact extendInstall_exact env initial params locals paramsSize localsSize emptyRows emptyColumns oldRows oldColumns
      found rows columns value _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  exact extendFinish_exact env initial params locals paramsSize localsSize column columnBound columnRead stepRead
    found rows columns value Q next

#print axioms extendAfterCandidate_exact

end Project.Beck.Execution
