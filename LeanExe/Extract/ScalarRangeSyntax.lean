import LeanExe.Source.ScalarRangeSyntax
import LeanExe.Source.ExprEquality

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar

/-- Remove the canonical final yield, retaining every strict scalar binding. -/
def scalarYield? : Lean.Expr → Option Lean.Expr
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero]))))
      (.app (.const ``ForInStep [.zero]) (.const ``UInt64 [])))
      (.app (.app (.const ``ForInStep.yield [.zero]) (.const ``UInt64 [])) value) => some value
  | .letE name type value body nondep =>
      (scalarYield? body).map fun scalar => .letE name type value scalar nondep
  | .mdata data body => (scalarYield? body).map (.mdata data)
  | _ => none

theorem scalarYield_accepts {source scalar : Lean.Expr} (h : Range.YieldScalar source scalar) :
    scalarYield? source = some scalar := by
  induction h with
  | yieldValue => rfl
  | letE _ ih => simp [scalarYield?, ih]
  | metadata _ ih => simp [scalarYield?, ih]

theorem scalarYield_sound {source scalar : Lean.Expr} (h : scalarYield? source = some scalar) :
    Range.YieldScalar source scalar := by
  induction source using scalarYield?.induct generalizing scalar with
  | case1 value => cases h; exact .yieldValue
  | case2 name type value body nondep ih =>
    simp only [scalarYield?, Option.map_eq_some_iff] at h
    obtain ⟨tail, ht, rfl⟩ := h
    exact .letE (ih ht)
  | case3 data body ih =>
    simp only [scalarYield?, Option.map_eq_some_iff] at h
    obtain ⟨tail, ht, rfl⟩ := h
    exact .metadata (ih ht)
  | case4 => simp_all [scalarYield?]

structure ScalarRangeView where
  count : Lean.Expr
  initial : Lean.Expr
  indexName : Lean.Name
  accumulatorName : Lean.Name
  indexBi : Lean.BinderInfo
  accumulatorBi : Lean.BinderInfo
  body : Lean.Expr

def ScalarRangeView.source (view : ScalarRangeView) : Lean.Expr :=
  Range.call view.count view.initial view.indexName view.accumulatorName
    view.indexBi view.accumulatorBi view.body

/-- Admit only the original standard range head and concrete unit-step range.
The Expr equality instance checks complete syntax and instance evidence. -/
def scalarRange? : Lean.Expr → Option ScalarRangeView
  | .app (.app (.app head
      (.app (.app (.app (.app (.const ``Std.Legacy.Range.mk []) start)
        (.app (.const ``UInt64.toNat []) count)) step) positive)) initial)
      (.lam indexName (.const ``Nat [])
        (.lam accumulatorName (.const ``UInt64 []) body accumulatorBi) indexBi) =>
      if head = Range.head ∧ start = Range.natLiteral 0 ∧ step = Range.natLiteral 1 ∧
          positive = .const ``Nat.zero_lt_one [] then
        some { count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body }
      else none
  | _ => none

theorem scalarRange_accepts (view : ScalarRangeView) :
    scalarRange? view.source = some view := by
  cases view
  simp [ScalarRangeView.source, Range.call, Range.range, Lean.mkAppN, Lean.mkApp, scalarRange?]

theorem scalarRange_sound {source : Lean.Expr} {view : ScalarRangeView}
    (matched : scalarRange? source = some view) : source = view.source := by
  unfold scalarRange? at matched
  split at matched
  · split at matched
    · rename_i exactSyntax
      obtain ⟨rfl, rfl, rfl, rfl⟩ := exactSyntax
      cases matched
      rfl
    · contradiction
  · contradiction

end LeanExe.Extract.Core
