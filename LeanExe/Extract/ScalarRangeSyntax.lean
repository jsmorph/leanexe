import LeanExe.Source.ScalarRangeSyntax
import LeanExe.Extract.ScalarYieldType
import LeanExe.Source.ExprEquality

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar

/-- Remove yielding result wrappers, including in local continuations and
branches. The scalar extractor subsequently checks the complete converted body. -/
def scalarYield? : Lean.Expr → Option Lean.Expr
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero]))))
      (.app (.const ``ForInStep [.zero]) (.const ``UInt64 [])))
      (.app (.app (.const ``ForInStep.yield [.zero]) (.const ``UInt64 [])) value) => some value
  | .letE name type value body nondep =>
      match _mapped : scalarYieldType? type with
      | none => (scalarYield? body).map fun scalar => .letE name type value scalar nondep
      | some scalarType => do
          let scalarValue ← scalarYield? value
          let scalarBody ← scalarYield? body
          pure (.letE name scalarType scalarValue scalarBody nondep)
  | .lam name domain body bi => (scalarYield? body).map fun scalar => .lam name domain scalar bi
  | .app (.app (.bvar index) (.const ``Unit.unit [])) argument =>
      some (.app (.app (.bvar index) (.const ``Unit.unit [])) argument)
  | .app (.app (.bvar index) (.const ``PUnit.unit [.succ .zero])) argument =>
      some (.app (.app (.bvar index) (.const ``PUnit.unit [.succ .zero])) argument)
  | .app (.bvar index) argument => some (.app (.bvar index) argument)
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
      condition) evidence) onTrue) onFalse =>
      match _mapped : scalarYieldType? type with
      | none => none
      | some scalarType => do
          let scalarTrue ← scalarYield? onTrue
          let scalarFalse ← scalarYield? onFalse
          pure (Range.branch scalarType condition evidence scalarTrue scalarFalse)
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) (.const ``UInt64 []))
        (.app (.const ``ForInStep [.zero]) (.const ``UInt64 []))) value)
      (.lam name (.const ``UInt64 []) body bi) =>
      (scalarYield? body).map fun scalar => Identity.bind name bi value scalar
  | .mdata data body => (scalarYield? body).map (.mdata data)
  | _ => none

theorem scalarYield_accepts {source scalar : Lean.Expr} (h : Range.YieldScalar source scalar) :
    scalarYield? source = some scalar := by
  induction h with
  | yieldValue => rfl
  | letE plain _ ih =>
    rw [scalarYield?, scalarYieldType_none.mpr plain]
    simp [ih]
  | letYield type _ _ iv ib =>
    rw [scalarYield?, scalarYieldType_accepts type]
    simp [iv, ib]
  | lambda _ ih => simp [scalarYield?, ih]
  | call => rfl
  | unitCall unitForm => cases unitForm <;> rfl
  | branch type _ _ it ie =>
    rw [Range.branch, scalarYield?, scalarYieldType_accepts type]
    simp [it, ie]
  | idBind _ ih => simp [Range.bindYield, scalarYield?, ih]
  | metadata _ ih => simp [scalarYield?, ih]

theorem scalarYield_sound {source scalar : Lean.Expr} (h : scalarYield? source = some scalar) :
    Range.YieldScalar source scalar := by
  induction source using scalarYield?.induct generalizing scalar with
  | case1 value => cases h; exact .yieldValue
  | case2 name type value body nondep absent ih =>
    rw [scalarYield?, absent] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨tail, ht, rfl⟩ := h
    exact .letE (scalarYieldType_none.mp absent) (ih ht)
  | case3 name type value body nondep scalarType mapped iv ib =>
    rw [scalarYield?, mapped] at h
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨scalarValue, hv, scalarBody, hb, rfl⟩ := h
    exact .letYield (scalarYieldType_sound mapped) (iv hv) (ib hb)
  | case4 name domain body bi ih =>
    simp only [scalarYield?, Option.map_eq_some_iff] at h
    obtain ⟨tail, ht, rfl⟩ := h
    exact .lambda (ih ht)
  | case5 index argument => cases h; exact .unitCall .unit
  | case6 index argument => cases h; exact .unitCall .punit
  | case7 index argument => cases h; exact .call
  | case8 type condition evidence onTrue onFalse absent =>
    rw [scalarYield?, absent] at h
    contradiction
  | case9 type condition evidence onTrue onFalse scalarType mapped it ie =>
    rw [scalarYield?, mapped] at h
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨scalarTrue, ht, scalarFalse, he, rfl⟩ := h
    exact .branch (scalarYieldType_sound mapped) (it ht) (ie he)
  | case10 value name body bi ih =>
    simp only [scalarYield?, Option.map_eq_some_iff] at h
    obtain ⟨tail, ht, rfl⟩ := h
    exact .idBind (ih ht)
  | case11 data body ih =>
    simp only [scalarYield?, Option.map_eq_some_iff] at h
    obtain ⟨tail, ht, rfl⟩ := h
    exact .metadata (ih ht)
  | case12 => simp_all [scalarYield?]

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
