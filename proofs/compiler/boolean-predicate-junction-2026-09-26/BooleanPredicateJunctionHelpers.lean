import LeanExe.Extract.ScalarBooleanWordNegation
import LeanExe.Extract.ScalarBooleanPredicateBindings

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def hasBooleanPredicate (locals : List ScalarBinding) (indices : List Nat) : Bool :=
  indices.any fun index => (locals[index]?.bind ScalarBinding.booleanPredicateFunction?).isSome

theorem hasBooleanPredicate_iff {locals : List ScalarBinding} {indices : List Nat} :
    hasBooleanPredicate locals indices = true ↔
      ∃ index, index ∈ indices ∧ ∃ function,
        locals[index]?.bind ScalarBinding.booleanPredicateFunction? = some function := by
  simp [hasBooleanPredicate, List.any_eq_true, Option.isSome_iff_exists]

theorem hasBooleanPredicate_false {locals : List ScalarBinding} {indices : List Nat}
    (absent : ∀ index, index ∈ indices →
      locals[index]?.bind ScalarBinding.booleanPredicateFunction? = none) :
    hasBooleanPredicate locals indices = false := by
  cases result : hasBooleanPredicate locals indices with
  | false => rfl
  | true =>
    obtain ⟨index, member, function, found⟩ := hasBooleanPredicate_iff.mp result
    rw [absent index member] at found
    contradiction

theorem hasBooleanPredicate_of_kind {locals : List ScalarBinding} {indices : List Nat}
    {index : Nat} (member : index ∈ indices)
    (present : (locals.map ScalarBinding.kind)[index]? = some .booleanPredicateFunction) :
    hasBooleanPredicate locals indices = true := by
  obtain ⟨function, found⟩ := scalarBooleanPredicateFunction_lookup present
  exact hasBooleanPredicate_iff.mpr ⟨index, member, function, by simp [found, ScalarBinding.booleanPredicateFunction?]⟩

theorem booleanJunction_children_size (n : Nat) (op : Junction) (left right : BooleanLocal) :
    sizeOf left.expr < sizeOf (BooleanLocal.junction n op left right).expr ∧
      sizeOf right.expr < sizeOf (BooleanLocal.junction n op left right).expr := by
  have bound := BooleanGuardNegation.expr_size n (op.booleanExpr left.expr right.expr)
  change sizeOf left.expr < sizeOf (BooleanGuardNegation.expr n (op.booleanExpr left.expr right.expr)) ∧ _
  cases op <;> simp [BooleanLocal.expr, Junction.booleanExpr] at bound ⊢ <;> omega

def booleanWordJunction (n : Nat) (op : Junction) (left right : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  booleanWordNegation n ((junctionPrimitive op).lower left right)

theorem booleanWordJunction_correct (n : Nat) (op : Junction) {left right : LeanExe.IR.Expr}
    {store : LeanExe.IR.ScalarStore} {a b : Bool}
    (first : left.ScalarEval store a.toUInt64 store)
    (second : right.ScalarEval store b.toUInt64 store) :
    (booleanWordJunction n op left right).ScalarEval store
      (GuardNegation.denote n (op.denote a b)).toUInt64 store := by
  have combined := (junctionPrimitive op).lower_correct first second
  rw [junctionPrimitive_denote] at combined
  exact booleanWordNegation_correct n combined

theorem booleanWordJunction_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (n : Nat) (op : Junction) {left right : LeanExe.IR.Expr}
    (first : P left) (second : P right) : P (booleanWordJunction n op left right) :=
  booleanWordNegation_holds P literal choice n (binary _ _ _ first second)

end LeanExe.Extract.Core
