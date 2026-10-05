import Project.IR.Correct
import Project.IR.Run

/-! Lemmas and tactics for the words the compiler computes from tests.  A `Bool` is a word that
is 0 or 1: the compiler computes `a && b`, `a || b`, and `!b` as the bitwise and, or, and
exclusive or with 1 of such words, and tests a result against 1.  The IR's division and remainder
test the divisor for 0, where Lean's give 0 and the dividend. -/

namespace Project.IR

open Wasm Project.Pipeline

theorem word_and (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) &&& if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem word_or (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) ||| if q then 1 else 0) = if p ∨ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem word_eq_one (p : Prop) [Decidable p] : ((if p then 1 else 0 : UInt64) = 1) ↔ p := by
  by_cases hp : p <;> simp [hp]

/-- The test of a word that the compiler computes from a proposition. -/
theorem word_beq_one (p : Prop) [Decidable p] : ((if p then 1 else 0 : UInt64) == 1) = decide p := by
  by_cases hp : p <;> simp [hp]

/-- The compiler computes `x != y` as the negation of the equality test. -/
theorem word_and_not (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) &&& if q then 0 else 1) = if p ∧ ¬q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem word_not (b : Bool) : ((if b = true then 1 else 0 : UInt64) ^^^ 1) =
    if b = false then 1 else 0 := by
  cases b <;> rfl

theorem divU_eq (a b : UInt64) : (if b = 0 then 0 else a / b) = a / b := by
  split <;> simp_all

theorem remU_eq (a b : UInt64) : (if b = 0 then a else a % b) = a % b := by
  split <;> simp_all

theorem min_word (a b : UInt64) : min a b = if a ≤ b then a else b := rfl

theorem max_word (a b : UInt64) : max a b = if a ≤ b then b else a := rfl

/-- Evaluates a compiled body of word code from its function's initial state. -/
macro "eval_body" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Stmt.run, Expr.eval, Func.state, Func.locals, Func.scratch, Func.width,
    Stmt.scratchWidth, Expr.scratchWidth, State.set?_eq_update, State.get, State.update,
    State.setAll, U64Op.apply, Scalar.values, ScalarType.valueType, Expr.evalResults,
    ScalarType.value, Flat.flat, divU_eq, remU_eq, word_and, word_or, word_eq_one, $args,*])

/-- Evaluates statements on a state known through its locals. -/
macro "eval_state" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Stmt.run, Expr.eval, State.set?_eq_update, State.setAll, U64Op.apply,
    Scalar.values, ScalarType.valueType, Expr.evalResults, ScalarType.value, Flat.flat, divU_eq,
    remU_eq, word_and, word_or, word_eq_one, $args,*])

end Project.IR
