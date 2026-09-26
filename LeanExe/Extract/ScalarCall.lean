import LeanExe.Source.ScalarCall
import LeanExe.Extract.ScalarHead

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (LocalCall ManyCall)

def scalarLocalCall? : Lean.Expr → Option LocalCall
  | .bvar index => some (.var index)
  | .app function operand => (scalarLocalCall? function).map fun call => .argument call operand
  | _ => none

@[simp] theorem scalarLocalCall_accepts (call : LocalCall) : scalarLocalCall? call.expr = some call := by
  induction call with
  | var => rfl
  | argument function operand ih => simp [LocalCall.expr, scalarLocalCall?, ih]

theorem scalarLocalCall_sound {expression : Lean.Expr} {call : LocalCall}
    (parsed : scalarLocalCall? expression = some call) : expression = call.expr := by
  induction expression using scalarLocalCall?.induct generalizing call with
  | case1 index => cases parsed; rfl
  | case2 function operand ih =>
    simp only [scalarLocalCall?, Option.map_eq_some_iff] at parsed
    obtain ⟨callee, found, rfl⟩ := parsed
    simp [LocalCall.expr, ih found]
  | case3 => simp [scalarLocalCall?] at parsed

def scalarManyCall? (head first second : Lean.Expr) : Option ManyCall := do
  let callee ← scalarLocalCall? head
  if positive : 0 < callee.arguments.length then some ⟨callee, positive, first, second⟩ else none

@[simp] theorem scalarManyCall_accepts (call : ManyCall) :
    scalarManyCall? call.callee.expr call.first call.second = some call := by
  cases call
  simp [scalarManyCall?, scalarLocalCall_accepts, *]

theorem scalarManyCall_sound {head first second : Lean.Expr} {call : ManyCall}
    (parsed : scalarManyCall? head first second = some call) :
    .app (.app head first) second = call.expr := by
  simp only [scalarManyCall?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨callee, found, accepted⟩ := parsed
  split at accepted
  · cases accepted
    simp [ManyCall.expr, scalarLocalCall_sound found]
  · contradiction

theorem scalarManyCall_size {head first second : Lean.Expr} {call : ManyCall}
    (parsed : scalarManyCall? head first second = some call) {operand : Lean.Expr}
    (member : operand ∈ call.arguments) :
    sizeOf operand < sizeOf (.app (.app head first) second : Lean.Expr) := by
  rw [scalarManyCall_sound parsed]
  exact call.argument_size member

theorem scalarLocalCall_not_primitive (call : LocalCall) : ScalarPrimitive.ofHead? call.expr = none := by
  unfold ScalarPrimitive.ofHead?
  split
  · rename_i name levels same
    have h := congrArg Lean.Expr.getAppFn same
    simp [LocalCall.head, Lean.Expr.getAppFn] at h
  · rename_i a b c same
    have h := congrArg Lean.Expr.getAppFn same
    simp [LocalCall.head, Lean.Expr.getAppFn] at h
  · rfl

end LeanExe.Extract.Core
