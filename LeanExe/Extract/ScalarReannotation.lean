import LeanExe.Source.ScalarReannotation
import LeanExe.Extract.ScalarHead
import LeanExe.Extract.ScalarTypedLiteralInstance

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Recognize a standard word numeral, retaining all checks on its type and instance. -/
def annotatedNumeral? : Lean.Expr → Option Nat
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) type) numeral) evidence => do
      let result ← scalarResultType? type
      let number ← naturalLiteral? numeral
      if typedLiteralInstance? number result evidence then some number else none
  | _ => none

@[simp] theorem annotatedNumeral_accepts {number : Nat} {type : ResultType}
    {numeral evidence : Lean.Expr} (numberMeaning : NaturalLiteral number numeral)
    (instanceMeaning : TypedLiteralInstance number type evidence) :
    annotatedNumeral? (typedLiteralExpr type numeral evidence) = some number := by
  simp [annotatedNumeral?, typedLiteralExpr, naturalLiteral_accepts numberMeaning,
    typedLiteralInstance_accepts instanceMeaning]

theorem annotatedNumeral_sound {expression : Lean.Expr} {number : Nat}
    (accepted : annotatedNumeral? expression = some number) :
    ∃ type numeral evidence, expression = typedLiteralExpr type numeral evidence ∧
      NaturalLiteral number numeral ∧ TypedLiteralInstance number type evidence := by
  unfold annotatedNumeral? at accepted
  split at accepted
  · rename_i typeExpr numeral evidence
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨type, foundType, value, foundValue, matched⟩ := accepted
    split at matched
    · cases matched
      exact ⟨type, numeral, evidence, by simp [typedLiteralExpr, scalarResultType_sound foundType],
        naturalLiteral_sound foundValue, typedLiteralInstance_sound (by assumption)⟩
    · contradiction
  · contradiction

def reannotation? (source target : Lean.Expr) : Bool :=
  LeanExe.Source.ExprEquality.same source target ||
  (match annotatedNumeral? source, annotatedNumeral? target with
   | some first, some second => first == second
   | _, _ => false) ||
  (match source, target with
   | .app (.app sourceHead sourceLeft) sourceRight, .app (.app targetHead targetLeft) targetRight =>
       match ScalarPrimitive.ofHead? sourceHead, ScalarPrimitive.ofHead? targetHead with
       | some first, some second => decide (first = second) &&
           reannotation? sourceLeft targetLeft && reannotation? sourceRight targetRight
       | _, _ => false
   | .mdata _ source, .mdata _ target => reannotation? source target
   | _, _ => false)
termination_by sizeOf source

theorem ScalarPrimitive.denote_injective {first second : ScalarPrimitive}
    (same : first.denote = second.denote) : first = second := by
  have sampled := congrArg (fun f : UInt64 → UInt64 → UInt64 => (f 5 3, f 3 5)) same
  cases first <;> cases second <;> first | rfl | exact absurd sampled (by decide)

theorem reannotation_accepts {source target : Lean.Expr}
    (related : Reannotates source target) : reannotation? source target = true := by
  induction related with
  | same expression => rw [reannotation?.eq_def]; simp
  | binary sourceMeaning targetMeaning left right ihl ihr =>
    obtain ⟨first, sourceFound, sourceValue⟩ := sourceHead_recognized sourceMeaning
    obtain ⟨second, targetFound, targetValue⟩ := sourceHead_recognized targetMeaning
    have same := ScalarPrimitive.denote_injective (sourceValue.trans targetValue.symm)
    subst second
    rw [reannotation?.eq_def]
    simp [sourceFound, targetFound, ihl, ihr]
  | numeral sourceType targetType sourceNumber targetNumber sourceInstance targetInstance =>
    rw [reannotation?.eq_def]
    simp [annotatedNumeral_accepts sourceNumber sourceInstance,
      annotatedNumeral_accepts targetNumber targetInstance]
  | metadata related ih => rw [reannotation?.eq_def]; simp [ih]

theorem reannotation_sound {source target : Lean.Expr}
    (accepted : reannotation? source target = true) : Reannotates source target := by
  induction source using (measure (fun e : Lean.Expr => sizeOf e)).wf.induction generalizing target with
  | h source ih =>
    rw [reannotation?.eq_def] at accepted
    simp only [Bool.or_eq_true] at accepted
    rcases accepted with (same | numeral) | structural
    · exact LeanExe.Source.ExprEquality.same_eq_true.mp same ▸ Reannotates.same source
    · split at numeral
      · rename_i first second sourceFound targetFound
        have same : first = second := by simpa using numeral
        subst second
        obtain ⟨sourceType, sourceNumeral, sourceEvidence, rfl, sourceNumber, sourceInstance⟩ := annotatedNumeral_sound sourceFound
        obtain ⟨targetType, targetNumeral, targetEvidence, rfl, targetNumber, targetInstance⟩ := annotatedNumeral_sound targetFound
        exact .numeral sourceType targetType sourceNumber targetNumber sourceInstance targetInstance
      · contradiction
    · split at structural
      · rename_i sourceHead sourceLeft sourceRight targetHead targetLeft targetRight
        split at structural
        · rename_i first second sourceFound targetFound
          simp only [Bool.and_eq_true, decide_eq_true_eq] at structural
          obtain ⟨⟨rfl, left⟩, right⟩ := structural
          exact .binary (ScalarPrimitive.ofHead_sound sourceFound)
            (ScalarPrimitive.ofHead_sound targetFound)
            (ih _ (by change sizeOf _ < sizeOf _; simp; omega) left) (ih _ (by change sizeOf _ < sizeOf _; simp; omega) right)
        · contradiction
      · exact .metadata (ih _ (by change sizeOf _ < sizeOf _; simp; omega) structural)
      · contradiction

end LeanExe.Extract.Core
