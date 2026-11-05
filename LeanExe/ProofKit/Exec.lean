import Interpreter.Wasm.Semantics

/-!
Equations of Talos's `exec` for the empty and the nonempty list and of `execOne` at fuel 0 and
for `block` and `iff`, whose results `blockResult` computes from the results of their bodies.
The module declares no `simp` lemmas, so importing it leaves the simplifier's lemmas unchanged.
-/

namespace LeanExe.ProofKit

open Wasm

theorem exec_cons {α : Type} (F : Nat) (m : Module) (st : Store α) (sl : Locals)
    (env : HostEnv α) (i : Instruction) (rest : Program) :
    exec F m st sl (i :: rest) env =
      match execOne F m st sl i env with
      | .Fallthrough st s => exec F m st s rest env
      | other => other := by
  simp only [exec]
  rfl

theorem exec_nil {α : Type} (F : Nat) (m : Module) (st : Store α) (sl : Locals)
    (env : HostEnv α) : exec F m st sl [] env = .Fallthrough st sl := by
  simp only [exec]

theorem execOne_zero {α : Type} (m : Module) (st : Store α) (sl : Locals) (env : HostEnv α)
    (inst : Instruction) : execOne 0 m st sl inst env = .OutOfFuel := by
  simp only [execOne.eq_def]

/-- Talos's result for a `block` or `iff` from its body's `r`, with `ra` kept values over
`below`. -/
def blockResult {α : Type} (ra : Nat) (below : List Value) : Continuation α → Continuation α
  | .Fallthrough r' s' =>
      .Fallthrough r'
        { params := s'.params, locals := s'.locals, values := s'.values.take ra ++ below }
  | .Break 0 r' s' =>
      .Fallthrough r'
        { params := s'.params, locals := s'.locals, values := s'.values.take ra ++ below }
  | .Break (k + 1) r' s' => .Break k r' s'
  | other => other

theorem execOne_block {α : Type} (m : Module) (st : Store α) (sl : Locals) (env : HostEnv α)
    (f pa ra : Nat) (body : Program) (pts rts : List ValueType) :
    execOne (f + 1) m st sl (.block pa ra body pts rts) env =
      blockResult ra (sl.values.drop pa) (exec f m st sl body env) := by
  simp only [execOne.eq_def]
  cases exec f m st sl body env with
  | Break k r' s' => cases k <;> rfl
  | _ => rfl

theorem execOne_iff {α : Type} (m : Module) (st : Store α) (sl : Locals) (env : HostEnv α)
    (f pa ra : Nat) (thn els : Program) (pts rts : List ValueType) (x : UInt32) (vs : List Value)
    (hvs : sl.values = .i32 x :: vs) :
    execOne (f + 1) m st sl (.iff pa ra thn els pts rts) env =
      blockResult ra (vs.drop pa)
        (exec f m st { params := sl.params, locals := sl.locals, values := vs }
          (if x ≠ 0 then thn else els) env) := by
  simp only [execOne.eq_def, hvs]
  cases exec f m st { params := sl.params, locals := sl.locals, values := vs }
      (if x ≠ 0 then thn else els) env with
  | Break k r' s' => cases k <;> rfl
  | _ => rfl

end LeanExe.ProofKit
