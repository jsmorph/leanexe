import LeanExe.Util.ListRelation
import LeanExe.IR.ScalarSemantics

namespace LeanExe.Extract.Core

/-- Compile every supplied operand in source order. The membership argument
keeps recursive source extraction within the original application's size. -/
def extractScalarArguments : (arguments : List Lean.Expr) →
    ((operand : Lean.Expr) → operand ∈ arguments → Option LeanExe.IR.Expr) →
    Option (List LeanExe.IR.Expr)
  | [], _ => some []
  | first :: rest, compile => do
      let head ← compile first (by simp)
      let tail ← extractScalarArguments rest (fun operand member => compile operand (by simp [member]))
      pure (head :: tail)

theorem extractScalarArguments_accepts (arguments : List Lean.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ arguments → Option LeanExe.IR.Expr)
    (total : ∀ operand member, ∃ target, compile operand member = some target) :
    ∃ targets, extractScalarArguments arguments compile = some targets := by
  induction arguments with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
    obtain ⟨head, hh⟩ := total first (by simp)
    obtain ⟨tail, ht⟩ := ih (fun operand member => compile operand (by simp [member]))
      (fun operand member => total operand _)
    exact ⟨head :: tail, by simp [extractScalarArguments, hh, ht]⟩

theorem extractScalarArguments_operands (arguments : List Lean.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ arguments → Option LeanExe.IR.Expr)
    {targets : List LeanExe.IR.Expr} (compiled : extractScalarArguments arguments compile = some targets) :
    ∀ operand member, ∃ target, compile operand member = some target := by
  induction arguments generalizing targets with
  | nil => simp
  | cons first rest ih =>
    simp only [extractScalarArguments, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨head, hh, tail, ht, _⟩ := compiled
    intro operand member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨head, hh⟩
    · exact ih _ ht operand member

theorem extractScalarArguments_length (arguments : List Lean.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ arguments → Option LeanExe.IR.Expr)
    {targets : List LeanExe.IR.Expr} (compiled : extractScalarArguments arguments compile = some targets) :
    targets.length = arguments.length := by
  induction arguments generalizing targets with
  | nil => cases compiled; rfl
  | cons first rest ih =>
    simp only [extractScalarArguments, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨head, hh, tail, ht, rfl⟩ := compiled
    simp [ih _ ht]

theorem extractScalarArguments_relation (arguments : List Lean.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ arguments → Option LeanExe.IR.Expr)
    (native : Lean.Expr → α) (relation : LeanExe.IR.Expr → α → Prop)
    {targets : List LeanExe.IR.Expr} (compiled : extractScalarArguments arguments compile = some targets)
    (meanings : ∀ operand member target, compile operand member = some target → relation target (native operand)) :
    LeanExe.ListRelation relation targets (arguments.map native) := by
  induction arguments generalizing targets with
  | nil => cases compiled; exact .nil
  | cons first rest ih =>
    simp only [extractScalarArguments, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨head, hh, tail, ht, rfl⟩ := compiled
    exact .cons (meanings _ _ _ hh) (ih _ ht (fun operand member target found => meanings _ _ _ found))

theorem extractScalarArguments_holds (arguments : List Lean.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ arguments → Option LeanExe.IR.Expr)
    (P : LeanExe.IR.Expr → Prop) {targets : List LeanExe.IR.Expr}
    (compiled : extractScalarArguments arguments compile = some targets)
    (invariant : ∀ operand member target, compile operand member = some target → P target) :
    ∀ target ∈ targets, P target := by
  induction arguments generalizing targets with
  | nil => cases compiled; simp
  | cons first rest ih =>
    simp only [extractScalarArguments, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨head, hh, tail, ht, rfl⟩ := compiled
    intro target member
    rcases List.mem_cons.mp member with rfl | member
    · exact invariant _ _ _ hh
    · exact ih _ ht (fun operand member target found => invariant _ _ _ found) target member

end LeanExe.Extract.Core
