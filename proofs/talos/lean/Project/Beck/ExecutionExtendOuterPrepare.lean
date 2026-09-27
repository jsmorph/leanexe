import Project.Beck.ExecutionExtendColumnLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

structure ExtendOuterLocals (locals : List Value) (row rows : Nat) : Prop where
  size : locals.length = 158
  empty : ∀ k ≤ 6, locals[k]? = some (.i64 0)
  rowIndex : locals[122]? = some (.i64 row.toUInt64)
  rowLimit : locals[123]? = some (.i64 rows.toUInt64)
  rowStep : locals[124]? = some (.i64 1)

def extendOuterPreparedLocals (locals : List Value) (row width : Nat) : List Value :=
  let l := (((locals.set 7 (.i64 row.toUInt64)).set 125 (.i64 0)).set 126 (.i64 width.toUInt64)).set 127 (.i64 1)
  let l := (((l.set 8 (.i64 0)).set 9 (.i64 0)).set 10 (.i64 0)).set 11 (.i64 0)
  let l := ((l.set 12 (.i64 0)).set 13 (.i64 0)).set 14 (.i64 0)
  (l.set 137 (.i64 0)).set 139 (.i64 0)

theorem extendOuterPrepared_search {locals : List Value} {row rows : Nat}
    (state : ExtendOuterLocals locals row rows) (width : Nat) :
    ExtendSearchLocals (extendOuterPreparedLocals locals row width) row rows 0 width := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [extendOuterPreparedLocals, state.size]
  · intro k bound
    interval_cases k <;> simpa [extendOuterPreparedLocals] using state.empty _ (by decide)
  · simp [extendOuterPreparedLocals, state.size]
  · simpa [extendOuterPreparedLocals] using state.rowIndex
  · simpa [extendOuterPreparedLocals] using state.rowLimit
  · simpa [extendOuterPreparedLocals] using state.rowStep
  all_goals try simp [extendOuterPreparedLocals, state.size]
  intro k lower upper
  interval_cases k <;> simp [extendOuterPreparedLocals, state.size]

set_option maxRecDepth 4096 in
theorem extendOuterPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (width : Nat) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (row : Nat)
    (size : locals.length = 158) (rowRead : locals[122]? = some (.i64 row.toUInt64))
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := extendOuterPreparedLocals locals row width })) :
    wp Project.Beck.«module» ((extendBody.drop 4).take 26) Q initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  simp only [extendBody, func26, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, rowRead, reduceIte]
  exact next

#print axioms extendOuterPrepare_exact

end Project.Beck.Execution
