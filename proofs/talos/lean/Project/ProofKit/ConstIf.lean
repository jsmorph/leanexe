import Project.ProofKit.FixedFrame
import Project.TalosCompat

namespace Project.ProofKit
open Wasm

/-- Materialize a condition without expanding the caller's postcondition through
    both arms of the control-flow rule. -/
theorem wp_constIf {m : Wasm.Module} {env : HostEnv α} {store : Store α}
    {frame : Locals} {c : UInt32} {tail : List Value} {yes no : UInt64}
    {rest : Wasm.Program} {Q : Assertion α}
    {paramTypes resultTypes : List ValueType}
    (hStack : frame.values = .i32 c :: tail)
    (hNext : wp m rest Q store
      { frame with values := .i64 (if c ≠ 0 then yes else no) :: tail } env) :
    wp m (.iff 0 1 [.constI64 yes] [.constI64 no] paramTypes resultTypes :: rest)
      Q store frame env := by
  rw [wp_iff_control_types]
  refine wp_iff_cons hStack ?_
  by_cases hc : c = 0
  · simpa [hc, wp_simp] using hNext
  · simpa [hc, wp_simp] using hNext

#print axioms wp_constIf
end Project.ProofKit
