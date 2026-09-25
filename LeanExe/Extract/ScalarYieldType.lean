import LeanExe.Source.ScalarYieldType

namespace LeanExe.Extract.Core

def scalarYieldType? : Lean.Expr → Option Lean.Expr
  | .app (.const ``ForInStep [.zero]) (.const ``UInt64 []) => some (.const ``UInt64 [])
  | .app (.const ``Id [.zero]) (.app (.const ``ForInStep [.zero]) (.const ``UInt64 [])) =>
      some (.app (.const ``Id [.zero]) (.const ``UInt64 []))
  | .forallE name domain result bi =>
      (scalarYieldType? result).map fun scalar => .forallE name domain scalar bi
  | _ => none

theorem scalarYieldType_accepts {source scalar : Lean.Expr}
    (mapped : LeanExe.Source.Scalar.Range.YieldType source scalar) :
    scalarYieldType? source = some scalar := by
  induction mapped with
  | step | identity => rfl
  | arrow _ ih => simp [scalarYieldType?, ih]

theorem scalarYieldType_sound {source scalar : Lean.Expr}
    (mapped : scalarYieldType? source = some scalar) :
    LeanExe.Source.Scalar.Range.YieldType source scalar := by
  induction source using scalarYieldType?.induct generalizing scalar with
  | case1 => cases mapped; exact .step
  | case2 => cases mapped; exact .identity
  | case3 name domain result bi ih =>
    simp only [scalarYieldType?, Option.map_eq_some_iff] at mapped
    obtain ⟨tail, ht, rfl⟩ := mapped
    exact .arrow (ih ht)
  | case4 => simp_all [scalarYieldType?]

theorem scalarYieldType_none {type : Lean.Expr} :
    scalarYieldType? type = none ↔ ¬ ∃ scalar, LeanExe.Source.Scalar.Range.YieldType type scalar := by
  constructor
  · intro absent ⟨scalar, mapped⟩
    have found := scalarYieldType_accepts mapped
    simp [absent] at found
  · intro absent
    cases found : scalarYieldType? type with
    | none => rfl
    | some scalar => exact False.elim (absent ⟨scalar, scalarYieldType_sound found⟩)

end LeanExe.Extract.Core
