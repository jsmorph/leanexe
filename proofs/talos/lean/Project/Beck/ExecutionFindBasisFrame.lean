import Project.Beck.ExecutionFindBasisAfter

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

structure FindBasisLocals (locals : List Value) (stopped : Bool) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) : Prop where
  size : locals.length = 47
  owner9 : locals[0]? = some (.i64 0)
  owner10 : locals[1]? = some (.i64 0)
  owner11 : locals[2]? = some (.i64 0)
  flag : locals[8]? = some (.i64 (if stopped then 1 else 0))
  result : stopped = true →
    locals[3]? = some (.i64 rowOwner) ∧ locals[4]? = some (.i64 rowPointer) ∧
    locals[5]? = some (.i64 columnOwner) ∧ locals[6]? = some (.i64 columnPointer) ∧
    locals[7]? = some (.i64 basis.determinant)

theorem findBasisPrepared_state {locals : List Value} {basis : Basis}
    {rowOwner rowPointer columnOwner columnPointer : UInt64}
    (state : FindBasisLocals locals false basis rowOwner rowPointer columnOwner columnPointer)
    (width : Nat) (matrixOwner matrixPointer : UInt64) :
    FindBasisLocals (findBasisPreparedLocals locals width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer)
      false basis rowOwner rowPointer columnOwner columnPointer := by
  constructor
  · simp [findBasisPreparedLocals, state.size]
  · simpa [findBasisPreparedLocals] using state.owner9
  · simpa [findBasisPreparedLocals] using state.owner10
  · simpa [findBasisPreparedLocals] using state.owner11
  · simpa [findBasisPreparedLocals] using state.flag
  · simp

theorem findBasisRead_state {locals : List Value} {basis : Basis}
    {rowOwner rowPointer columnOwner columnPointer : UInt64}
    (state : FindBasisLocals locals false basis rowOwner rowPointer columnOwner columnPointer)
    (nextBasis : Basis) (nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer : UInt64) :
    FindBasisLocals (findBasisReadLocals locals nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer)
      false basis rowOwner rowPointer columnOwner columnPointer := by
  constructor
  · simp [findBasisReadLocals, state.size]
  · simpa [findBasisReadLocals] using state.owner9
  · simpa [findBasisReadLocals] using state.owner10
  · simpa [findBasisReadLocals] using state.owner11
  · simpa [findBasisReadLocals] using state.flag
  · simp

theorem findBasisContinued_state {locals : List Value} {basis : Basis}
    {rowOwner rowPointer columnOwner columnPointer : UInt64}
    (state : FindBasisLocals locals false basis rowOwner rowPointer columnOwner columnPointer)
    (width : Nat) (matrixOwner matrixPointer : UInt64)
    (nextBasis : Basis) (nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer : UInt64) :
    FindBasisLocals (findBasisContinuedLocals locals width matrixOwner matrixPointer nextBasis
      nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer)
      false nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer := by
  constructor
  · simp [findBasisContinuedLocals, findBasisReadLocals, state.size]
  · simp [findBasisContinuedLocals, findBasisReadLocals, state.size]
  · simp [findBasisContinuedLocals, findBasisReadLocals, state.size]
  · simp [findBasisContinuedLocals, findBasisReadLocals, state.size]
  · simpa [findBasisContinuedLocals, findBasisReadLocals] using state.flag
  · simp

theorem findBasisStopped_state {locals : List Value} {basis : Basis}
    {rowOwner rowPointer columnOwner columnPointer : UInt64}
    (state : FindBasisLocals locals false basis rowOwner rowPointer columnOwner columnPointer) :
    FindBasisLocals (findBasisStoppedLocals locals basis rowOwner rowPointer columnOwner columnPointer)
      true basis rowOwner rowPointer columnOwner columnPointer := by
  constructor
  · simp [findBasisStoppedLocals, state.size]
  · simpa [findBasisStoppedLocals] using state.owner9
  · simpa [findBasisStoppedLocals] using state.owner10
  · simpa [findBasisStoppedLocals] using state.owner11
  · simp [findBasisStoppedLocals, state.size]
  · simp [findBasisStoppedLocals, state.size]

#print axioms findBasisContinued_state
#print axioms findBasisStopped_state

end Project.Beck.Execution
