import Project.EulerRiemann.InitialCellsGuard

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def runBody : Wasm.Program :=
  (Annotation.resolve func97 [{ instructionIndex := 4, field := .thenBranch }]).getD []

def runInvalid : Wasm.Program :=
  (Annotation.resolve func97 [{ instructionIndex := 4, field := .elseBranch }]).getD []

def runEntryFrame (n : Nat) : Locals := func97Def.toLocals [.i64 (UInt64.ofNat n)]

theorem run_function_shape : func97 =
    [.constI64 2, .localGet 0, .leUI64,
      .iff 0 1 [.localGet 0, .constI64 800, .leUI64] [.const 0] [] [.i32],
      .iff 0 0 runBody runInvalid, .localGet 14, .localGet 15, .localGet 16, .localGet 17] := rfl

theorem run_body_shape : runBody =
    [.call 0, .localSet 18, .constI64 1, .localSet 19,
      .localGet 18, .localGet 19, .addI64, .localTee 20, .localGet 18, .ltUI64,
      .iff 0 1 [.unreachable] [.localGet 20] [] [.i64], .localSet 1,
      .localGet 0, .localSet 2, .constI64 0, .localSet 3, .localGet 0, .localSet 4,
      .localGet 4, .call 96, .localSet 6, .localSet 5,
      .localGet 5, .localSet 7, .localGet 6, .localSet 8,
      .localGet 1, .localGet 2, .localGet 3, .localGet 7, .localGet 8, .call 85,
      .localSet 12, .localSet 11, .localSet 10, .localSet 9,
      .localGet 9, .localSet 14, .localGet 10, .localSet 15,
      .localGet 11, .localSet 16, .localGet 12, .localSet 17] := rfl

theorem run_guard_spec (env : HostEnv Unit) (store : Store Unit)
    (n : Nat) (hn2 : 2 ≤ n) (hn : n ≤ 800) (Q : Assertion Unit)
    (hBody : wp module runBody
      (FixedArrayEqNode.branchPost module env
        [.localGet 14, .localGet 15, .localGet 16, .localGet 17] Q)
      store (runEntryFrame n) env) :
    wp module func97 Q store (runEntryFrame n) env := by
  have hN : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (by change n < 18446744073709551616; omega)
  have hLower : (2 : UInt64) ≤ UInt64.ofNat n := by
    simpa [UInt64.le_iff_toNat_le, hN] using hn2
  have hUpper : UInt64.ofNat n ≤ (800 : UInt64) := by
    simpa [UInt64.le_iff_toNat_le, hN] using hn
  rw [run_function_shape]
  wp_run [runEntryFrame, func97Def, hLower, hUpper]
  refine wp_iff_cons rfl ?_
  conv => arg 2; simp
  wp_run [hLower, hUpper, reduceIte, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  refine wp_iff_cons rfl ?_
  conv => arg 2; simp
  apply wp.conseq (Q := FixedArrayEqNode.branchPost module env
    [.localGet 14, .localGet 15, .localGet 16, .localGet 17] Q)
  · intro continuation hBranch
    cases continuation
    case Break depth final frame =>
      cases depth <;> simpa [FixedArrayEqNode.branchPost, wp_simp, Locals.get] using hBranch
    all_goals simpa [FixedArrayEqNode.branchPost, wp_simp, Locals.get] using hBranch
  · exact hBody

#print axioms run_function_shape
#print axioms run_body_shape
#print axioms run_guard_spec

end Project.EulerRiemann.Execution
