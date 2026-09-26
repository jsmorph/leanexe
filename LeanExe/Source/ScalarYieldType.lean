import Lean

namespace LeanExe.Source.Scalar.Range

/-- Remove the yielding-step result wrapper, including in local continuation
types. Domains and binder information remain exactly as in the source. -/
inductive YieldType : Lean.Expr → Lean.Expr → Prop where
  | step : YieldType (.app (.const ``ForInStep [.zero]) (.const ``UInt64 [])) (.const ``UInt64 [])
  | identity : YieldType
      (.app (.const ``Id [.zero]) (.app (.const ``ForInStep [.zero]) (.const ``UInt64 [])))
      (.app (.const ``Id [.zero]) (.const ``UInt64 []))
  | arrow (result : YieldType source scalar) :
      YieldType (.forallE name domain source bi) (.forallE name domain scalar bi)

end LeanExe.Source.Scalar.Range
