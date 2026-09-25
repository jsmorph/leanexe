import LeanExe.Source.ScalarManyFunction

namespace LeanExe.Source.Scalar

/-- Concrete applications whose head is a lexical var. -/
inductive LocalCall where
  | var (index : Nat)
  | argument (function : LocalCall) (operand : Lean.Expr)
  deriving Repr

namespace LocalCall

def expr : LocalCall → Lean.Expr
  | .var index => .bvar index
  | .argument function operand => .app function.expr operand

def index : LocalCall → Nat
  | .var index => index
  | .argument function _ => function.index

def arguments : LocalCall → List Lean.Expr
  | .var _ => []
  | .argument function operand => function.arguments ++ [operand]

@[simp] theorem head (call : LocalCall) : call.expr.getAppFn = .bvar call.index := by
  induction call with
  | var => rfl
  | argument function operand ih => exact ih

theorem argument_size (call : LocalCall) {operand : Lean.Expr} (member : operand ∈ call.arguments) :
    sizeOf operand < sizeOf call.expr := by
  induction call with
  | var => simp [arguments] at member
  | argument function last ih =>
    simp only [arguments, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · have bound := ih member
      simp only [expr]; simp_all; omega
    · simp [expr]; omega

theorem not_bvar (call : LocalCall) (positive : 0 < call.arguments.length) (index : Nat) :
    call.expr ≠ .bvar index := by
  cases call with
  | var => simp [arguments] at positive
  | argument => simp [expr]

end LocalCall

/-- A local application of at least three arguments, split at its final two
operands to agree with the scalar extractor's existing binary dispatch. -/
structure ManyCall where
  callee : LocalCall
  positive : 0 < callee.arguments.length
  first : Lean.Expr
  second : Lean.Expr

namespace ManyCall

abbrev expr (call : ManyCall) : Lean.Expr := .app (.app call.callee.expr call.first) call.second
abbrev index (call : ManyCall) : Nat := call.callee.index
abbrev arguments (call : ManyCall) : List Lean.Expr := call.callee.arguments ++ [call.first, call.second]
abbrev arity (call : ManyCall) : Nat := call.arguments.length

theorem arity_ge_three (call : ManyCall) : 3 ≤ call.arity := by
  have positive := call.positive
  simp [arity, arguments]; omega

theorem argument_size (call : ManyCall) {operand : Lean.Expr} (member : operand ∈ call.arguments) :
    sizeOf operand < sizeOf call.expr := by
  simp only [arguments, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with member | rfl | rfl
  · have bound := call.callee.argument_size member
    simp only [expr]; simp_all; omega
  · simp [expr]; omega
  · simp [expr]; omega

end ManyCall
end LeanExe.Source.Scalar
