import LeanExe.Source.Scalar

namespace LeanExe.Source.Scalar.Range.Exit

/-- Source range bounds retain their Nat meaning. Only representable Nat
literals may be lowered to the existing UInt64 loop counter. -/
inductive Count where
  | word (source : Lean.Expr)
  | literal (number : Nat) (fits : number < UInt64.size)

def Count.source : Count → Lean.Expr
  | .word source => .app (.const ``UInt64.toNat []) source
  | .literal number _ => Range.natLiteral number

def Count.scalar : Count → Lean.Expr
  | .word source => source
  | .literal number _ => Scalar.literalExpr number

inductive Count.Eval : Count → List Value → Nat → Prop where
  | word (value : EvalWith expression values result) : Eval (.word expression) values result.toNat
  | literal : Eval (.literal number fits) values number

inductive Count.Supported : List BindingKind → Count → Prop where
  | word (value : SupportedWith types expression) : Supported types (.word expression)
  | literal : Supported types (.literal number fits)

theorem Count.Supported.scalar {types count} (supported : Supported types count) :
    SupportedWith types count.scalar := by
  cases supported with
  | word value => exact value
  | literal => exact .ofNat

theorem Count.Supported.of_scalar (count : Count) {types}
    (supported : SupportedWith types count.scalar) : Supported types count := by
  cases count with
  | word source => exact .word supported
  | literal number fits => exact .literal

/-- Exact natural count after word lowering; the literal case cannot wrap. -/
theorem Count.Eval.of_scalar {count : Count} {values : List Value} {result : UInt64}
    (evaluated : EvalWith count.scalar values result) : Eval count values result.toNat := by
  cases count with
  | word source => exact .word evaluated
  | literal number fits =>
    generalize same : Count.scalar (.literal number fits) = source at evaluated
    cases evaluated <;>
      simp_all [Count.scalar, Scalar.literalExpr, Identity.run, Identity.pure, Identity.bind,
        Comparison.branch, CompoundGuard.branch, Guard.dependentBranch, Extremum.expr, Extremum.head,
        ManyFunction.bind, ManyCall.expr, Range.call, Range.head, Lean.mkAppN, Lean.mkApp]
    case ofNat =>
      subst number
      simpa only [Nat.mod_eq_of_lt fits] using (Count.Eval.literal (values := values) (number := _) (fits := fits))
    case complement operation a x head argument =>
      exact False.elim (head.not_ofNat number same.1.symm)
    case binary head f a x b y operation left right =>
      rw [← same.1.1] at operation
      cases operation
    case manyApply f call native function arguments =>
      have impossible := congrArg Lean.Expr.getAppFn same.1.1
      simp [LocalCall.head, Lean.Expr.getAppFn] at impossible

theorem Count.Supported.evaluates {types : List BindingKind} {count : Count}
    (supported : Supported types count) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ result, Eval count values result := by
  obtain ⟨word, evaluated⟩ := supported.scalar.evaluates values typed
  exact ⟨word.toNat, .of_scalar evaluated⟩

def Count.range (count first : Count) (stride : Nat) (positive : Lean.Expr) : Lean.Expr :=
  Lean.mkAppN (.const ``Std.Legacy.Range.mk []) #[first.source,
    count.source, Range.natLiteral stride, positive]

end LeanExe.Source.Scalar.Range.Exit
