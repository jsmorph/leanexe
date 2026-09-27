import Project.Beck.ExecutionBorderFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem borderPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (width : Nat)
    (matrixOwner matrixPointer : UInt64) (basis : Basis) (rowOwner rowPointer columnOwner columnPointer : UInt64)
    (row column : Nat) (columns : Bool) (saved : BorderSaved) (tail : BorderTail)
    (represented : UInt64Array.At initial (if columns then columnPointer else rowPointer)
      (if columns then basis.columns else basis.rows))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : let pointer := if columns then columnPointer else rowPointer
      let words := if columns then basis.columns else basis.rows
      wp Project.Beck.«module» rest Q initial
        (borderPushFrame (borderParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column)
          (borderPreparedSaved saved columns pointer) pointer words.size (tail 4) (tail 5)
          (if columns then column.toUInt64 else row.toUInt64) (tail 7) (tail 8) (tail 9) (tail 10) (tail 11) (tail 12) (tail 13) (tail 14)) env) :
    wp Project.Beck.«module» ((if columns then (borderEligible.drop 76).take 18 else borderEligible.take 18) ++ rest) Q initial
      (borderFrame (borderParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column) saved tail) env := by
  have read := represented.lengthRead
  have memory := represented.lengthBound
  have lengthWord (n : Nat) : UInt64.ofNat n + 1 = (n + 1).toUInt64 := (UInt64.ofNat_add _ _).symm
  cases columns
  all_goals
    simp only [Bool.false_eq_true, reduceIte] at represented read memory next ⊢
    simp only [borderEligible, func25, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take,
      List.cons_append, List.nil_append, borderFrame, borderParams, basisValues, borderPrefix, borderTail,
      List.reverse_cons, List.reverse_nil]
    wp_fixed_frame
    rw [show 2 ^ 32 = 4294967296 by decide, ← Memory.toUInt32_eq_ofNat]
    simp only [UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, Nat.not_lt.mpr memory, reduceIte, read]
    wp_fixed_frame [lengthWord]
    simpa only [borderPushFrame, borderParams, basisValues, borderPrefix, borderPreparedSaved, List.reverse_cons,
      List.reverse_nil, List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
      Bool.false_eq_true, reduceIte, Nat.toUInt64, UInt64.mul_one] using next

#print axioms borderPrepare_exact

end Project.Beck.Execution
