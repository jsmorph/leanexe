import Project.Beck.ExecutionExtendOuterCleanup

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def extendOuterInstalledLocals (locals : List Value) (found : Bool) (rows columns value : UInt64) : List Value :=
  let tag : UInt64 := if found then 1 else 0
  let r := if found then rows else 0
  let c := if found then columns else 0
  let d := if found then value else 0
  let l := extendOuterHandledLocals locals found rows columns value
  let l := ((((l.set 144 (.i64 tag)).set 145 (.i64 r)).set 146 (.i64 r)).set 147 (.i64 c))
  let l := ((((l.set 148 (.i64 c)).set 149 (.i64 d)).set 150 (.i64 0)).set 143 (.i64 tag))
  let l := ((((l.set 0 (.i64 tag)).set 1 (.i64 r)).set 2 (.i64 r)).set 3 (.i64 c))
  (((l.set 4 (.i64 c)).set 5 (.i64 d)).set 6 (.i64 0))

def extendOuterAdvancedLocals (locals : List Value) (row : Nat) : List Value :=
  (((locals.set 125 (.i64 row.toUInt64)).set 126 (.i64 1)).set 127 (.i64 (row + 1).toUInt64)).set 122 (.i64 (row + 1).toUInt64)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extendOuterFinish_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (paramsSize : params.length = 8) (localsSize : locals.length = 158)
    (row : Nat) (rowBound : row < 56)
    (rowRead : locals[122]? = some (.i64 row.toUInt64)) (stepRead : locals[124]? = some (.i64 1))
    (found : Bool) (rows columns value : UInt64) (Q : Assertion Unit)
    (next : if found then Q (.Break 1 initial { params := params, locals := extendOuterInstalledLocals locals found rows columns value })
      else Q (.Break 0 initial { params := params, locals := extendOuterAdvancedLocals (extendOuterInstalledLocals locals found rows columns value) row })) :
    wp Project.Beck.«module» (extendBody.drop 160) Q initial
      { params := params, locals := extendOuterHandledLocals locals found rows columns value } env := by
  have guard : ¬ UInt64.ofNat row + 1 < UInt64.ofNat row :=
    CheckedNatAdd.guard_of_fits row 1 (by change row + 1 < 18446744073709551616; omega)
  have add : UInt64.ofNat row + 1 = UInt64.ofNat (row + 1) := (UInt64.ofNat_add row 1).symm
  cases found
  all_goals
    simp only [extendBody, func26, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, extendOuterHandledLocals, extendOuterSelectedLocals, Bool.false_eq_true, reduceIte]
    repeat' first
      | (wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil,
          rowRead, stepRead, Nat.toUInt64, guard,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  · simpa only [extendOuterAdvancedLocals, extendOuterInstalledLocals, extendOuterHandledLocals, extendOuterSelectedLocals,
      Nat.toUInt64, add, Bool.false_eq_true, reduceIte] using next
  · change Q (.Break 1 initial { params := params, locals := extendOuterInstalledLocals locals true rows columns value })
    exact next

#print axioms extendOuterFinish_exact

end Project.Beck.Execution

