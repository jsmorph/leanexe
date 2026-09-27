import Project.Core.Validity

namespace Project.Core.Validity

open LeanExe.Core

instance (count : Nat) (indices : List Nat) : Decidable (Reads count indices) := by
  unfold Reads
  infer_instance

/-- Check source indices and call signatures before constructing a module. -/
def checkStatement (source : LeanExe.Core.Module) (effectArity : Nat → Option Nat)
    (count : Nat) : Stmt → Bool
  | .skip => true
  | .assign destination value => decide (destination < count ∧ Reads count value.reads)
  | .seq a b => checkStatement source effectArity count a && checkStatement source effectArity count b
  | .branch test yes no => decide (Reads count test.reads) &&
      checkStatement source effectArity count yes && checkStatement source effectArity count no
  | .loop test body => decide (Reads count test.reads) && checkStatement source effectArity count body
  | .call destination callee args =>
      match source[callee]? with
      | none => false
      | some function => decide (destination < count ∧ args.length = function.params ∧
          ∀ value ∈ args, Reads count value.reads)
  | .effect destination operation args =>
      decide (destination < count ∧ effectArity operation = some args.length ∧
        ∀ value ∈ args, Reads count value.reads)

theorem checkStatement_sound (source : LeanExe.Core.Module) (effectArity : Nat → Option Nat)
    (count : Nat) (statement : Stmt)
    (checked : checkStatement source effectArity count statement = true) :
    WellFormed source effectArity count statement := by
  induction statement with
  | skip => exact .skip
  | assign destination value =>
      simp only [checkStatement, decide_eq_true_eq] at checked
      exact .assign destination value checked.1 checked.2
  | seq a b first second =>
      simp only [checkStatement, Bool.and_eq_true] at checked
      exact .seq (first checked.1) (second checked.2)
  | branch test yes no first second =>
      simp only [checkStatement, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact .branch checked.1.1 (first checked.1.2) (second checked.2)
  | loop test body ih =>
      simp only [checkStatement, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact .loop checked.1 (ih checked.2)
  | call destination callee args =>
      simp only [checkStatement] at checked
      split at checked
      · contradiction
      · rename_i function found
        simp only [decide_eq_true_eq] at checked
        exact .call destination callee args function checked.1 found checked.2.1 checked.2.2
  | effect destination operation args =>
      simp only [checkStatement, decide_eq_true_eq] at checked
      exact .effect destination operation args checked.1 checked.2.1 checked.2.2

def checkSource (source : LeanExe.Core.Module) (effectArity : Nat → Option Nat) : Bool :=
  source.all fun function =>
    checkStatement source effectArity (function.params + function.locals) function.body &&
      decide (Reads (function.params + function.locals) function.result.reads)

theorem checkSource_sound (source : LeanExe.Core.Module) (effectArity : Nat → Option Nat)
    (checked : checkSource source effectArity = true) :
    ∀ function ∈ source,
      WellFormed source effectArity (function.params + function.locals) function.body ∧
      Reads (function.params + function.locals) function.result.reads := by
  intro function member
  have body := List.all_eq_true.mp checked function member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at body
  exact ⟨checkStatement_sound source effectArity _ _ body.1, body.2⟩

end Project.Core.Validity
