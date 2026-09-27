import Project.Beck.ExecutionDirectionCoefficient

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem directionColumn_state {locals : List Value} {matrix sro srp sco scp : UInt64}
    {basis : Basis} {ro rp co cp original current : UInt64} {free index : Nat}
    (state : DirectionLoopLocals locals matrix sro srp sco scp basis ro rp co cp original current free index) :
    DirectionLoopLocals (directionColumnLocals locals cp current free index)
      matrix sro srp sco scp basis ro rp co cp original current free index := by
  apply state.preserved
  · simp [directionColumnLocals]
  · exact (directionColumnLocals_update locals state.words cp current free index).words
  · intro k bound
    simp (discharger := omega) only [directionColumnLocals, List.getElem?_set_ne]

theorem directionDet_state {locals : List Value} {matrix sro srp sco scp : UInt64}
    {basis : Basis} {ro rp co cp original current : UInt64} {free index : Nat}
    (state : DirectionLoopLocals locals matrix sro srp sco scp basis ro rp co cp original current free index)
    (width : Nat) (columns : UInt64) :
    DirectionLoopLocals (directionDetLocals locals basis.rows.size width matrix ro rp columns)
      matrix sro srp sco scp basis ro rp co cp original current free index := by
  apply state.preserved
  · simp [directionDetLocals]
  · unfold directionDetLocals
    repeat' apply WordLocals.set
    exact state.words
  · intro k bound
    simp (discharger := omega) only [directionDetLocals, List.getElem?_set_ne]

theorem directionCoefficient_state {locals : List Value} {matrix sro srp sco scp : UInt64}
    {basis : Basis} {ro rp co cp original current : UInt64} {free index : Nat}
    (state : DirectionLoopLocals locals matrix sro srp sco scp basis ro rp co cp original current free index)
    (value column : UInt64) :
    DirectionLoopLocals (directionCoefficientLocals locals current cp value column index)
      matrix sro srp sco scp basis ro rp co cp original current free index := by
  apply state.preserved
  · simp [directionCoefficientLocals, directionCoefficientPrepared]
  · exact directionCoefficientLocals_words locals state.words current cp value column index
  · intro k bound
    simp (discharger := omega) only [directionCoefficientLocals, directionCoefficientPrepared, List.getElem?_set_ne]

#print axioms directionCoefficient_state

end Project.Beck.Execution
