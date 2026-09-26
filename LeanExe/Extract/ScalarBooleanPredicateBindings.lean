import LeanExe.Extract.ScalarBooleanLocalBindings

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- The distinct function domain determines how an argument is checked. -/
theorem scalarBooleanPredicate_none_of_predicate {locals : List ScalarBinding} {index : Nat}
    (present : (locals.map ScalarBinding.kind)[index]? = some .predicateFunction) :
    (locals[index]?.bind ScalarBinding.booleanPredicateFunction?) = none := by
  obtain ⟨function, found⟩ := scalarPredicateFunction_lookup present
  simp [found, ScalarBinding.booleanPredicateFunction?]

theorem ScalarBindingsMatch.no_booleanPredicate_of_predicate
    {locals : List ScalarBinding} {values : List Value} {store : LeanExe.IR.ScalarStore}
    {index : Nat} {function : UInt64 → Bool}
    (bindings : ScalarBindingsMatch locals values store)
    (source : values[index]? = some (.predicateFunction function)) :
    (locals[index]?.bind ScalarBinding.booleanPredicateFunction?) = none := by
  cases found : locals[index]?.bind ScalarBinding.booleanPredicateFunction? with
  | none => rfl
  | some compile =>
    obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
    have same := ScalarBinding.booleanPredicateFunction?_some.mp matched
    subst binding
    exact False.elim (bindings index _ _ present source)

theorem ScalarBindingsMatch.no_predicate_of_booleanPredicate
    {locals : List ScalarBinding} {values : List Value} {store : LeanExe.IR.ScalarStore}
    {index : Nat} {function : Bool → Bool}
    (bindings : ScalarBindingsMatch locals values store)
    (source : values[index]? = some (.booleanPredicateFunction function)) :
    (locals[index]?.bind ScalarBinding.predicateFunction?) = none := by
  cases found : locals[index]?.bind ScalarBinding.predicateFunction? with
  | none => rfl
  | some compile =>
    obtain ⟨binding, present, matched⟩ := Option.bind_eq_some_iff.mp found
    have same := ScalarBinding.predicateFunction?_some.mp matched
    subst binding
    exact False.elim (bindings index _ _ present source)

end LeanExe.Extract.Core
