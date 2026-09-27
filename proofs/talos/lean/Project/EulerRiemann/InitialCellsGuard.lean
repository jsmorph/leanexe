import Project.EulerRiemann.InitialSingletonBuild
import Project.ProofKit.FixedArrayEqNode

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def initialCellsInvalid : Wasm.Program :=
  (Annotation.resolve func96 [{ instructionIndex := 4, field := .elseBranch }]).getD []

theorem initial_cells_function_shape : func96 =
    [.constI64 2, .localGet 0, .leUI64,
      .iff 0 1 [.localGet 0, .constI64 800, .leUI64] [.const 0] [] [.i32],
      .iff 0 0 initialCellsBody initialCellsInvalid, .localGet 19, .localGet 20] := rfl

theorem initial_cells_body_shape : initialCellsBody = initialCellsBody.take 164 ++
    [.localGet 21, .localSet 13, .localGet 13, .localSet 14, .localGet 13, .localSet 15,
      .localGet 1, .localGet 2, .localGet 3, .localGet 14, .localGet 15, .call 95,
      .localSet 17, .localSet 16, .localGet 16, .localSet 19, .localGet 17, .localSet 20,
      .localGet 13, .constI64 0, .eqI64, .eqz,
      .iff 0 1 [.localGet 13, .localGet 19, .eqI64, .eqz] [.const 0] [] [.i32],
      .iff 0 0 [.localGet 13, .call 107] []] := by
  have hTail : initialCellsBody.drop 164 =
      [.localGet 21, .localSet 13, .localGet 13, .localSet 14, .localGet 13, .localSet 15,
        .localGet 1, .localGet 2, .localGet 3, .localGet 14, .localGet 15, .call 95,
        .localSet 17, .localSet 16, .localGet 16, .localSet 19, .localGet 17, .localSet 20,
        .localGet 13, .constI64 0, .eqI64, .eqz,
        .iff 0 1 [.localGet 13, .localGet 19, .eqI64, .eqz] [.const 0] [] [.i32],
        .iff 0 0 [.localGet 13, .call 107] []] := rfl
  exact (List.take_append_drop 164 initialCellsBody).symm.trans
    (congrArg (fun tail => initialCellsBody.take 164 ++ tail) hTail)

theorem initial_cells_guard_spec (env : HostEnv Unit) (store : Store Unit)
    (n : Nat) (hn2 : 2 ≤ n) (hn : n ≤ 800) (Q : Assertion Unit)
    (hBody : wp module initialCellsBody
      (FixedArrayEqNode.branchPost module env [.localGet 19, .localGet 20] Q)
      store (initialCellsEntryFrame n) env) :
    wp module func96 Q store (initialCellsEntryFrame n) env := by
  have hN : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (by change n < 18446744073709551616; omega)
  have hLower : (2 : UInt64) ≤ UInt64.ofNat n := by
    simpa [UInt64.le_iff_toNat_le, hN] using hn2
  have hUpper : UInt64.ofNat n ≤ (800 : UInt64) := by
    simpa [UInt64.le_iff_toNat_le, hN] using hn
  rw [initial_cells_function_shape]
  wp_run [initialCellsEntryFrame, func96Def, hLower, hUpper]
  refine wp_iff_cons rfl ?_
  conv => arg 2; simp
  wp_run [hLower, hUpper, reduceIte, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  refine wp_iff_cons rfl ?_
  conv => arg 2; simp
  apply wp.conseq (Q := FixedArrayEqNode.branchPost module env [.localGet 19, .localGet 20] Q)
  · intro continuation hBranch
    cases continuation
    case Break depth final frame =>
      cases depth <;> simpa [FixedArrayEqNode.branchPost, wp_simp, Locals.get] using hBranch
    all_goals simpa [FixedArrayEqNode.branchPost, wp_simp, Locals.get] using hBranch
  · exact hBody

#print axioms initial_cells_function_shape
#print axioms initial_cells_body_shape
#print axioms initial_cells_guard_spec

end Project.EulerRiemann.Execution
