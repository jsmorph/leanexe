import LeanExe.Core.Program
import Lean

namespace LeanExe.Core

/-- Pure source functions have no observable effects. -/
def noEffects : Effects Unit := fun _ _ _ _ _ => False

theorem Eval.call_of_invokes
    {functions : Module} {effects : Effects σ}
    {expressions : List Wasm.ScalarDescriptor.Expr} {locals result : Locals}
    {initial final : σ} {callee destination : Nat} {args : List UInt64} {value : UInt64}
    (inputs : arguments expressions locals = some args)
    (called : Invokes functions effects callee initial args final value)
    (written : IR.ScalarStore.write locals destination value = some result) :
    Eval functions effects (.call destination callee expressions) initial locals final result := by
  obtain ⟨function, returned, found, arity, executed, output⟩ := called
  exact .call found inputs arity executed output written

/-- The value field is an ordinary Lean function. Its certificate states that
the generated core module returns that function's value for every argument. -/
def Native : Nat → Type
  | 0 => UInt64
  | n + 1 => UInt64 → Native n

def applyNative : {n : Nat} → Native n → List UInt64 → UInt64
  | 0, value, _ => value
  | n + 1, function, args => applyNative (n := n) (function (args.headD 0)) args.tail

structure NativeCertificate {arity : Nat} (function : Native arity) where
  source : Module
  entry : Nat
  correct : ∀ args, args.length = arity →
    Invokes source noEffects entry () args () (applyNative function args)

end LeanExe.Core

open Lean Elab Tactic

syntax "core_native_eval" : tactic
syntax "core_native_invokes" : tactic

/-- Internal proof construction for the ordinary-definition frontend. Each
step builds a kernel-checked evaluation constructor. -/
elab_rules : tactic
| `(tactic| core_native_eval) => do
  evalTactic (← `(tactic| (
    first
    | exact LeanExe.Core.Eval.skip
    | apply LeanExe.Core.Eval.assign <;> rfl
    | apply LeanExe.Core.Eval.seq
      · core_native_eval
      · core_native_eval
    | apply LeanExe.Core.Eval.yes
      · simp_all [LeanExe.Wasm.ScalarDescriptor.Cond.eval,
          LeanExe.Wasm.ScalarDescriptor.Expr.eval,
          LeanExe.Wasm.ScalarDescriptor.U64Op.apply]
      · core_native_eval
    | apply LeanExe.Core.Eval.no
      · simp_all [LeanExe.Wasm.ScalarDescriptor.Cond.eval,
          LeanExe.Wasm.ScalarDescriptor.Expr.eval,
          LeanExe.Wasm.ScalarDescriptor.U64Op.apply]
      · core_native_eval
    | apply LeanExe.Core.Eval.call_of_invokes
      · rfl
      · first | assumption | solve_by_elim
      · rfl)))

elab_rules : tactic
| `(tactic| core_native_invokes) => do
  evalTactic (← `(tactic| (
    unfold LeanExe.Core.Invokes
    refine ⟨_, _, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · core_native_eval
    · first
      | rfl
      | simp_all [LeanExe.Wasm.ScalarDescriptor.Expr.eval,
          LeanExe.Wasm.ScalarDescriptor.U64Op.apply])))
