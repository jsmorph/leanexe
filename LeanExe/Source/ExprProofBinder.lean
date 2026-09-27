import Lean

namespace LeanExe.Source.ExprProofBinder

/-- Insert an unused binder at this depth, preserving the exact surrounding syntax. -/
def lift (depth : Nat) : Lean.Expr → Lean.Expr
  | .bvar index => .bvar (if index < depth then index else index + 1)
  | .app function argument => .app (lift depth function) (lift depth argument)
  | .lam name type body info => .lam name (lift depth type) (lift (depth + 1) body) info
  | .forallE name type body info => .forallE name (lift depth type) (lift (depth + 1) body) info
  | .letE name type value body nondep =>
      .letE name (lift depth type) (lift depth value) (lift (depth + 1) body) nondep
  | .mdata data body => .mdata data (lift depth body)
  | .proj name index body => .proj name index (lift depth body)
  | expression => expression

/-- Remove an unused proof binder. Any reference to that binder rejects, including
references beneath other binders; references to outer values retain their scope. -/
def drop? (depth : Nat) : Lean.Expr → Option Lean.Expr
  | .bvar index =>
      if index < depth then some (.bvar index)
      else if index = depth then none else some (.bvar (index - 1))
  | .app function argument => do
      let f ← drop? depth function
      let a ← drop? depth argument
      pure (.app f a)
  | .lam name type body info => do
      let type ← drop? depth type
      let body ← drop? (depth + 1) body
      pure (.lam name type body info)
  | .forallE name type body info => do
      let type ← drop? depth type
      let body ← drop? (depth + 1) body
      pure (.forallE name type body info)
  | .letE name type value body nondep => do
      let type ← drop? depth type
      let value ← drop? depth value
      let body ← drop? (depth + 1) body
      pure (.letE name type value body nondep)
  | .mdata data body => (drop? depth body).map (.mdata data)
  | .proj name index body => (drop? depth body).map (.proj name index)
  | expression => some expression

@[simp] theorem drop_lift (expression : Lean.Expr) (depth : Nat) :
    drop? depth (lift depth expression) = some expression := by
  induction expression generalizing depth with
  | bvar index =>
    by_cases before : index < depth
    · simp [lift, drop?, before]
    · have after : ¬ index + 1 < depth := by omega
      have different : index + 1 ≠ depth := by omega
      simp [lift, drop?, before, after, different]
  | app function argument ihf iha => simp [lift, drop?, ihf, iha]
  | lam name type body info iht ihb => simp [lift, drop?, iht, ihb]
  | forallE name type body info iht ihb => simp [lift, drop?, iht, ihb]
  | letE name type value body nondep iht ihv ihb => simp [lift, drop?, iht, ihv, ihb]
  | mdata data body ih => simp [lift, drop?, ih]
  | proj name index body ih => simp [lift, drop?, ih]
  | _ => rfl

theorem drop_sound (expression : Lean.Expr) (depth : Nat) {body : Lean.Expr}
    (dropped : drop? depth expression = some body) : expression = lift depth body := by
  induction expression generalizing depth body with
  | bvar index =>
    simp only [drop?] at dropped
    split at dropped
    · rename_i before
      cases dropped
      simp [lift, before]
    · rename_i after
      split at dropped
      · contradiction
      · rename_i different
        cases dropped
        have outside : ¬ index - 1 < depth := by omega
        simp only [lift, ite_eq_right outside]
        congr 1
        omega
  | app function argument ihf iha =>
    simp only [drop?, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at dropped
    obtain ⟨f, hf, a, ha, rfl⟩ := dropped
    simp [lift, ihf depth hf, iha depth ha]
  | lam name type original info iht ihb =>
    simp only [drop?, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at dropped
    obtain ⟨t, ht, b, hb, rfl⟩ := dropped
    simp [lift, iht depth ht, ihb (depth + 1) hb]
  | forallE name type original info iht ihb =>
    simp only [drop?, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at dropped
    obtain ⟨t, ht, b, hb, rfl⟩ := dropped
    simp [lift, iht depth ht, ihb (depth + 1) hb]
  | letE name type value original nondep iht ihv ihb =>
    simp only [drop?, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at dropped
    obtain ⟨t, ht, v, hv, b, hb, rfl⟩ := dropped
    simp [lift, iht depth ht, ihv depth hv, ihb (depth + 1) hb]
  | mdata data original ih =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp dropped
    simp [lift, ih depth hb]
  | proj name index original ih =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp dropped
    simp [lift, ih depth hb]
  | fvar | mvar | sort | const | lit => cases dropped; rfl

theorem lift_size (expression : Lean.Expr) (depth : Nat) :
    sizeOf expression ≤ sizeOf (lift depth expression) := by
  induction expression generalizing depth with
  | bvar index => simp only [lift]; split <;> simp_all <;> omega
  | app function argument ihf iha =>
    have first := ihf depth
    have second := iha depth
    change 1 + sizeOf function + sizeOf argument ≤
      1 + sizeOf (lift depth function) + sizeOf (lift depth argument)
    omega
  | lam name type body info iht ihb =>
    have typeBound := iht depth
    have bodyBound := ihb (depth + 1)
    change 1 + sizeOf name + sizeOf type + sizeOf body + sizeOf info ≤
      1 + sizeOf name + sizeOf (lift depth type) + sizeOf (lift (depth + 1) body) + sizeOf info
    omega
  | forallE name type body info iht ihb =>
    have typeBound := iht depth
    have bodyBound := ihb (depth + 1)
    change 1 + sizeOf name + sizeOf type + sizeOf body + sizeOf info ≤
      1 + sizeOf name + sizeOf (lift depth type) + sizeOf (lift (depth + 1) body) + sizeOf info
    omega
  | letE name type value body nondep iht ihv ihb =>
    have typeBound := iht depth
    have valueBound := ihv depth
    have bodyBound := ihb (depth + 1)
    change 1 + sizeOf name + sizeOf type + sizeOf value + sizeOf body + sizeOf nondep ≤
      1 + sizeOf name + sizeOf (lift depth type) + sizeOf (lift depth value) +
        sizeOf (lift (depth + 1) body) + sizeOf nondep
    omega
  | mdata data body ih =>
    have bound := ih depth
    change 1 + sizeOf data + sizeOf body ≤ 1 + sizeOf data + sizeOf (lift depth body)
    omega
  | proj name index body ih =>
    have bound := ih depth
    change 1 + sizeOf name + sizeOf index + sizeOf body ≤
      1 + sizeOf name + sizeOf index + sizeOf (lift depth body)
    omega
  | _ => exact Nat.le_refl _

theorem drop_size (expression : Lean.Expr) (depth : Nat) {body : Lean.Expr}
    (dropped : drop? depth expression = some body) : sizeOf body ≤ sizeOf expression := by
  rw [drop_sound expression depth dropped]
  exact lift_size body depth

end LeanExe.Source.ExprProofBinder
