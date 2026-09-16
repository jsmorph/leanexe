import Project.EulerRiemann.InitialCellsGuard
import Project.EulerCertificate.ExecutionAdvanceTotal

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Wasm Project.ProofKit

set_option maxRecDepth 32768

def runBody : Wasm.Program :=
  match (func189[4]? : Option Wasm.Instruction) with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

def runInvalid : Wasm.Program :=
  match (func189[4]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ body _ _) => body
  | _ => []

def runEntryFrame (n : Nat) (trials : UInt64) : Locals := func189Def.toLocals [.i64 (UInt64.ofNat n), .i64 trials]

theorem run_function_shape : func189 =
    [.constI64 2, .localGet 0, .leUI64,
      .iff 0 1 [.localGet 0, .constI64 800, .leUI64] [.const 0] [] [.i32],
      .iff 0 0 runBody runInvalid] ++ [.localGet 226, .localGet 227, .localGet 228, .localGet 229, .localGet 230, .localGet 231, .localGet 232, .localGet 233, .localGet 234, .localGet 235, .localGet 236, .localGet 237, .localGet 238, .localGet 239, .localGet 240, .localGet 241] := rfl

theorem run_guard_spec (env : HostEnv Unit) (store : Store Unit)
    (n : Nat) (trials : UInt64) (hn2 : 2 ≤ n) (hn : n ≤ 800) (Q : Assertion Unit)
    (hBody : wp module runBody
      (FixedArrayEqNode.branchPost module env
        [.localGet 226, .localGet 227, .localGet 228, .localGet 229, .localGet 230, .localGet 231, .localGet 232, .localGet 233, .localGet 234, .localGet 235, .localGet 236, .localGet 237, .localGet 238, .localGet 239, .localGet 240, .localGet 241] Q)
      store (runEntryFrame n trials) env) :
    wp module func189 Q store (runEntryFrame n trials) env := by
  have hN : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (by change n < 18446744073709551616; omega)
  have hLower : (2 : UInt64) ≤ UInt64.ofNat n := by
    simpa [UInt64.le_iff_toNat_le, hN] using hn2
  have hUpper : UInt64.ofNat n ≤ (800 : UInt64) := by
    simpa [UInt64.le_iff_toNat_le, hN] using hn
  rw [run_function_shape]
  simp only [List.cons_append, List.nil_append]
  wp_run [runEntryFrame, func189Def, hLower, hUpper]
  refine wp_iff_cons rfl ?_
  conv => arg 2; simp
  wp_run [hLower, hUpper, reduceIte, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  refine wp_iff_cons rfl ?_
  conv => arg 2; simp
  apply wp.conseq (Q := FixedArrayEqNode.branchPost module env
    [.localGet 226, .localGet 227, .localGet 228, .localGet 229, .localGet 230, .localGet 231, .localGet 232, .localGet 233, .localGet 234, .localGet 235, .localGet 236, .localGet 237, .localGet 238, .localGet 239, .localGet 240, .localGet 241] Q)
  · intro continuation hBranch
    cases continuation
    case Break depth final frame =>
      cases depth <;> simpa [FixedArrayEqNode.branchPost, wp_simp, Locals.get] using hBranch
    all_goals simpa [FixedArrayEqNode.branchPost, wp_simp, Locals.get] using hBranch
  · exact hBody

#print axioms run_function_shape
#print axioms run_guard_spec

end Project.EulerCertificate.Execution
