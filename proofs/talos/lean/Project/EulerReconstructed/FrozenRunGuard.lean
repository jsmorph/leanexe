import Project.EulerRiemann.FrozenInitialCellsGuard
import Project.EulerReconstructed.FrozenExecutionAdvanceTotal

namespace Project.EulerReconstructed.Frozen.Execution
open Project.EulerRiemann.Frozen
open Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit

def runBody : Wasm.Program :=
  (Annotation.resolve func142 [{ instructionIndex := 4, field := .thenBranch }]).getD []

def runInvalid : Wasm.Program :=
  (Annotation.resolve func142 [{ instructionIndex := 4, field := .elseBranch }]).getD []

def runEntryFrame (n : Nat) (trials : UInt64) : Locals := func142Def.toLocals [.i64 (UInt64.ofNat n), .i64 trials]

theorem run_function_shape : func142 =
    [.constI64 2, .localGet 0, .leUI64,
      .iff 0 1 [.localGet 0, .constI64 800, .leUI64] [.const 0] [] [.i32],
      .iff 0 0 runBody runInvalid, .localGet 16, .localGet 17, .localGet 18, .localGet 19] := rfl

theorem run_body_shape : runBody =
    [.call 0, .localSet 20, .constI64 1, .localSet 21,
      .localGet 20, .localGet 21, .addI64, .localTee 22, .localGet 20, .ltUI64,
      .iff 0 1 [.unreachable] [.localGet 22] [] [.i64], .localSet 2,
      .localGet 0, .localSet 3, .localGet 1, .localSet 4,
      .constI64 0, .localSet 5, .localGet 0, .localSet 6,
      .localGet 6, .call 141, .localSet 8, .localSet 7,
      .localGet 7, .localSet 9, .localGet 8, .localSet 10,
      .localGet 2, .localGet 3, .localGet 4, .localGet 5, .localGet 9, .localGet 10, .call 129,
      .localSet 14, .localSet 13, .localSet 12, .localSet 11,
      .localGet 11, .localSet 16, .localGet 12, .localSet 17,
      .localGet 13, .localSet 18, .localGet 14, .localSet 19] := rfl

theorem run_guard_spec (env : HostEnv Unit) (store : Store Unit)
    (n : Nat) (trials : UInt64) (hn2 : 2 ≤ n) (hn : n ≤ 800) (Q : Assertion Unit)
    (hBody : wp module runBody
      (FixedArrayEqNode.branchPost module env
        [.localGet 16, .localGet 17, .localGet 18, .localGet 19] Q)
      store (runEntryFrame n trials) env) :
    wp module func142 Q store (runEntryFrame n trials) env := by
  have hN : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (by change n < 18446744073709551616; omega)
  have hLower : (2 : UInt64) ≤ UInt64.ofNat n := by
    simpa [UInt64.le_iff_toNat_le, hN] using hn2
  have hUpper : UInt64.ofNat n ≤ (800 : UInt64) := by
    simpa [UInt64.le_iff_toNat_le, hN] using hn
  rw [run_function_shape]
  wp_run [runEntryFrame, func142Def, hLower, hUpper]
  refine wp_iff_cons rfl ?_
  conv => arg 2; simp
  wp_run [hLower, hUpper, reduceIte, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  refine wp_iff_cons rfl ?_
  conv => arg 2; simp
  apply wp.conseq (Q := FixedArrayEqNode.branchPost module env
    [.localGet 16, .localGet 17, .localGet 18, .localGet 19] Q)
  · intro continuation hBranch
    cases continuation
    case Break depth final frame =>
      cases depth <;> simpa [FixedArrayEqNode.branchPost, wp_simp, Locals.get] using hBranch
    all_goals simpa [FixedArrayEqNode.branchPost, wp_simp, Locals.get] using hBranch
  · exact hBody

#print axioms run_function_shape
#print axioms run_body_shape
#print axioms run_guard_spec

end Project.EulerReconstructed.Frozen.Execution
