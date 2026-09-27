import Project.Beck.ExecutionExtendInstall

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def extendAdvancedLocals (locals : List Value) (column : Nat) : List Value :=
  (((locals.set 128 (.i64 column.toUInt64)).set 129 (.i64 1)).set 130 (.i64 (column + 1).toUInt64)).set 125 (.i64 (column + 1).toUInt64)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extendFinish_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (paramsSize : params.length = 8) (localsSize : locals.length = 158)
    (column : Nat) (columnBound : column < 6)
    (columnRead : locals[125]? = some (.i64 column.toUInt64)) (stepRead : locals[127]? = some (.i64 1))
    (found : Bool) (rows columns value : UInt64) (Q : Assertion Unit)
    (next : if found then Q (.Break 1 initial { params := params, locals := extendInstalledLocals locals found rows columns value })
      else Q (.Break 0 initial { params := params, locals := extendAdvancedLocals (extendInstalledLocals locals found rows columns value) column })) :
    wp Project.Beck.«module» (extendColumnBody.drop 199) Q initial
      { params := params, locals := extendInstalledLocals locals found rows columns value } env := by
  have guard : ¬ UInt64.ofNat column + 1 < UInt64.ofNat column := CheckedNatAdd.guard_of_fits column 1 (by change column + 1 < 18446744073709551616; omega)
  have add : UInt64.ofNat column + 1 = UInt64.ofNat (column + 1) := (UInt64.ofNat_add column 1).symm
  cases found
  all_goals
    simp only [extendColumnBody, extendBody, func26, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, List.take, extendInstalledLocals, extendSelectedLocals, Bool.false_eq_true, reduceIte]
    repeat' first
      | (wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil,
          columnRead, stepRead, Nat.toUInt64, guard,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  · simpa only [extendAdvancedLocals, extendInstalledLocals, extendSelectedLocals, Nat.toUInt64, add,
      Bool.false_eq_true, reduceIte] using next
  · change Q (.Break 1 initial { params := params, locals := extendInstalledLocals locals true rows columns value })
    exact next

#print axioms extendFinish_exact

end Project.Beck.Execution
