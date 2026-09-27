import LeanExe.Source.ScalarStepMatcher
import LeanExe.Source.ScalarFunction

namespace LeanExe.Source.Scalar.StepMatcher

/-- A checked forwarding declaration may be expanded at any expression position.
The matcher rule uses the exact declaration certificate and the native identity
proved by denote_cases. The other rules preserve the surrounding expression. -/
inductive Expansion (env : Lean.Environment) : Lean.Expr → Lean.Expr → Prop where
  | refl (source : Lean.Expr) : Expansion env source source
  | trans (first : Expansion env a b) (second : Expansion env b c) : Expansion env a c
  | matcher (defined : Defined env name) :
      Expansion env (call name motive value doneBody yieldBody)
        (cases (.succ .zero) motive value doneBody yieldBody)
  | app (function : Expansion env f g) (argument : Expansion env a b) :
      Expansion env (.app f a) (.app g b)
  | lam (domain : Expansion env a b) (body : Expansion env c d) :
      Expansion env (.lam name a c bi) (.lam name b d bi)
  | forallE (domain : Expansion env a b) (body : Expansion env c d) :
      Expansion env (.forallE name a c bi) (.forallE name b d bi)
  | letE (type : Expansion env a b) (value : Expansion env c d) (body : Expansion env e f) :
      Expansion env (.letE name a c e nondep) (.letE name b d f nondep)
  | mdata (body : Expansion env a b) : Expansion env (.mdata data a) (.mdata data b)
  | proj (body : Expansion env a b) : Expansion env (.proj type index a) (.proj type index b)

/-- Head expansion is required exactly when the original environment defines
that constant as the checked Boolean-step dispatcher. -/
inductive HeadExpansion (env : Lean.Environment) : Lean.Expr → Lean.Expr → Prop where
  | unchanged (source : Lean.Expr)
      (unrecognized : ∀ name motive value doneBody yieldBody,
        source = call name motive value doneBody yieldBody → ¬ Defined env name) :
      HeadExpansion env source source
  | matcher (defined : Defined env name) :
      HeadExpansion env (call name motive value doneBody yieldBody)
        (cases (.succ .zero) motive value doneBody yieldBody)

theorem HeadExpansion.expansion {env : Lean.Environment} {source target : Lean.Expr}
    (head : HeadExpansion env source target) : Expansion env source target := by
  cases head with
  | unchanged => exact .refl _
  | matcher defined => exact .matcher defined

/-- A source-only grammar for complete expansion, independent of the extractor. -/
inductive Normalizes (env : Lean.Environment) : Lean.Expr → Lean.Expr → Prop where
  | bvar (index : Nat) : Normalizes env (.bvar index) (.bvar index)
  | fvar (id : Lean.FVarId) : Normalizes env (.fvar id) (.fvar id)
  | mvar (id : Lean.MVarId) : Normalizes env (.mvar id) (.mvar id)
  | sort (level : Lean.Level) : Normalizes env (.sort level) (.sort level)
  | const (name : Lean.Name) (levels : List Lean.Level) : Normalizes env (.const name levels) (.const name levels)
  | lit (literal : Lean.Literal) : Normalizes env (.lit literal) (.lit literal)
  | app (function : Normalizes env f g) (argument : Normalizes env a b)
      (head : HeadExpansion env (.app g b) target) : Normalizes env (.app f a) target
  | lam (domain : Normalizes env a b) (body : Normalizes env c d) :
      Normalizes env (.lam name a c bi) (.lam name b d bi)
  | forallE (domain : Normalizes env a b) (body : Normalizes env c d) :
      Normalizes env (.forallE name a c bi) (.forallE name b d bi)
  | letE (type : Normalizes env a b) (value : Normalizes env c d) (body : Normalizes env e f) :
      Normalizes env (.letE name a c e nondep) (.letE name b d f nondep)
  | mdata (body : Normalizes env a b) : Normalizes env (.mdata data a) (.mdata data b)
  | proj (body : Normalizes env a b) : Normalizes env (.proj type index a) (.proj type index b)

theorem Normalizes.expansion {env : Lean.Environment} {source target : Lean.Expr}
    (normalized : Normalizes env source target) : Expansion env source target := by
  induction normalized with
  | bvar | fvar | mvar | sort | const | lit => exact .refl _
  | app _ _ head ihf iha => exact .trans (.app ihf iha) head.expansion
  | lam _ _ ihd ihb => exact .lam ihd ihb
  | forallE _ _ ihd ihb => exact .forallE ihd ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- Application of the original declaration in an environment with checked
forwarding definitions, followed by the existing native scalar source semantics. -/
inductive EnvironmentApply (env : Lean.Environment) (source : Lean.Expr)
    (locals : List Value) (args : List UInt64) (value : UInt64) : Prop where
  | expanded (reduction : Expansion env source target) (applied : Apply target locals args value) :
      EnvironmentApply env source locals args value

theorem EnvironmentApply.direct {env : Lean.Environment} {source : Lean.Expr}
    {locals : List Value} {args : List UInt64} {value : UInt64}
    (applied : Apply source locals args value) : EnvironmentApply env source locals args value :=
  .expanded (.refl _) applied

def EnvironmentSupported (env : Lean.Environment) (type source : Lean.Expr) : Prop :=
  DeclarationSupported type source ∨
    ∃ target, Normalizes env source target ∧ DeclarationSupported type target

end LeanExe.Source.Scalar.StepMatcher
