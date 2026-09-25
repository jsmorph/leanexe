import LeanExe.Extract.ScalarExpr
import LeanExe.Extract.ScalarRangeSyntax
import LeanExe.Source.ScalarRangeSupported

namespace LeanExe.Extract.Core

/-- One dynamic loop with a scalar accumulator and a pure result computation.
The allocated slots are accumulator, index, and stop, in that order. -/
structure ScalarRangePlan where
  count : LeanExe.IR.Expr
  initial : LeanExe.IR.Expr
  step : LeanExe.IR.Expr
  result : LeanExe.IR.Expr
  deriving Repr

def ScalarRangePlan.body (plan : ScalarRangePlan) (slot : Nat) : LeanExe.IR.Stmt :=
  .seq (.assign (slot + 2) plan.count)
    (.seq (.assign slot plan.initial)
      (.seq (.assign (slot + 1) (.u64 0))
        (.seq (.while (.ltU64 (.local (slot + 1)) (.local (slot + 2)))
          (.seq (.assign slot plan.step)
            (.assign (slot + 1) (.u64Bin .add (.local (slot + 1)) (.u64 1)))))
          (.assign slot plan.result))))

def ScalarRangePlan.func (plan : ScalarRangePlan) (name : Lean.Name)
    (exportName : Option String) (arity : Nat) : LeanExe.IR.Func :=
  { sourceName := name, exportName, params := arity, locals := arity + 3
    body := plan.body arity, results := [.local arity] }

/-- Extract a single yielding range loop and surrounding pure computations.
The loop remains dynamic; its stop is evaluated once into a fresh local. -/
def extractScalarRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangePlan :=
  match scalarRange? source with
  | some view => do
      let count ← extractScalarExprWith locals view.count
      let initial ← extractScalarExprWith locals view.initial
      let scalar ← scalarYield? view.body
      let step ← extractScalarExprWith
        (.word (.local slot) :: .natural (.local (slot + 1)) :: locals) scalar
      pure { count, initial, step, result := .local slot }
  | none =>
      match source with
      | .app (.app (.const ``Id.run [.zero]) (.const ``UInt64 [])) body =>
          extractScalarRangeWith locals slot body
      | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
            (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
              (.const ``Id.instMonad [.zero])))) (.const ``UInt64 [])) body =>
          extractScalarRangeWith locals slot body
      | .letE _ (.const ``UInt64 []) value body _ => do
          let bound ← extractScalarExprWith locals value
          extractScalarRangeWith (.word bound :: locals) slot body
      | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
            (.const ``Id.instMonad [.zero]))) (.const ``UInt64 [])) (.const ``UInt64 [])) value)
          (.lam _ (.const ``UInt64 []) body _) =>
          match extractScalarExprWith locals value with
          | some bound => extractScalarRangeWith (.word bound :: locals) slot body
          | none => do
              let plan ← extractScalarRangeWith locals slot value
              let result ← extractScalarExprWith (.word plan.result :: locals) body
              pure { plan with result }
      | .mdata _ body => extractScalarRangeWith locals slot body
      | _ => none
termination_by sizeOf source

open LeanExe.Source.Scalar

theorem rangeSupported_excludes_pure {types : List BindingKind} {source : Lean.Expr}
    (supported : RangeSupportedWith types source) (locals : List ScalarBinding) :
    extractScalarExprWith locals source = none := by
  induction supported generalizing locals with
  | range => exact extractScalarExprWith_range _ _ _ _ _ _ _ _
  | letE value body ih =>
    rw [extractScalarExprWith]
    cases extractScalarExprWith locals _ <;> simp [ih]
  | idRun _ ih => simpa only [extractScalarExprWith_idRun] using ih locals
  | idPure _ ih => simpa only [extractScalarExprWith_idPure] using ih locals
  | bindRight value body ih =>
    rw [extractScalarExprWith_idBind]
    cases extractScalarExprWith locals _ <;> simp [ih]
  | bindLeft value body ih => simp [extractScalarExprWith_idBind, ih]
  | metadata _ ih => simpa only [extractScalarExprWith] using ih locals

theorem extractScalarRangeWith_call (locals : List ScalarBinding) (slot : Nat)
    (view : ScalarRangeView) : extractScalarRangeWith locals slot view.source = (do
      let count ← extractScalarExprWith locals view.count
      let initial ← extractScalarExprWith locals view.initial
      let scalar ← scalarYield? view.body
      let step ← extractScalarExprWith
        (.word (.local slot) :: .natural (.local (slot + 1)) :: locals) scalar
      pure { count, initial, step, result := .local slot }) := by
  rw [extractScalarRangeWith.eq_def, scalarRange_accepts]

@[simp] theorem extractScalarRangeWith_idRun (locals : List ScalarBinding) (slot : Nat) (body : Lean.Expr) :
    extractScalarRangeWith locals slot (Identity.run body) = extractScalarRangeWith locals slot body := by
  rw [Identity.run, extractScalarRangeWith]
  rfl

@[simp] theorem extractScalarRangeWith_idPure (locals : List ScalarBinding) (slot : Nat) (body : Lean.Expr) :
    extractScalarRangeWith locals slot (Identity.pure body) = extractScalarRangeWith locals slot body := by
  rw [Identity.pure, extractScalarRangeWith]
  rfl

theorem extractScalarRangeWith_letE (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarRangeWith locals slot (.letE name (.const ``UInt64 []) value body nondep) = (do
      let bound ← extractScalarExprWith locals value
      extractScalarRangeWith (.word bound :: locals) slot body) := by
  rw [extractScalarRangeWith]
  rfl

theorem extractScalarRangeWith_idBind (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (bi : Lean.BinderInfo) (value body : Lean.Expr) :
    extractScalarRangeWith locals slot (Identity.bind name bi value body) =
      (match extractScalarExprWith locals value with
      | some bound => extractScalarRangeWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) body
          pure { plan with result }) := by
  rw [Identity.bind, extractScalarRangeWith]
  rfl

@[simp] theorem extractScalarRangeWith_metadata (locals : List ScalarBinding) (slot : Nat)
    (data : Lean.MData) (body : Lean.Expr) :
    extractScalarRangeWith locals slot (.mdata data body) = extractScalarRangeWith locals slot body := by
  rw [extractScalarRangeWith]
  rfl

theorem extractScalarRangeWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : RangeSupportedWith types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarRangeWith locals slot source = some plan := by
  have extend {locals : List ScalarBinding} (total : ∀ binding ∈ locals, binding.Total)
      (value : LeanExe.IR.Expr) : ∀ binding ∈ ScalarBinding.word value :: locals, binding.Total := by
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · exact total binding member
  induction supported generalizing locals with
  | @range types count initial body scalar indexName accumulatorName indexBi accumulatorBi hc hi hy hs =>
    obtain ⟨c, ec⟩ := extractScalarExprWith_accepts hc locals typed total
    obtain ⟨i, ei⟩ := extractScalarExprWith_accepts hi locals typed total
    obtain ⟨s, es⟩ := extractScalarExprWith_accepts hs
      (.word (.local slot) :: .natural (.local (slot + 1)) :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    refine ⟨{ count := c, initial := i, step := s, result := .local slot }, ?_⟩
    have equation := extractScalarRangeWith_call locals slot
      { count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body }
    simpa [ScalarRangeView.source, ec, ei, scalarYield_accepts hy, es] using equation
  | letE value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (extend total bound)
    exact ⟨plan, by rw [extractScalarRangeWith_letE]; simp [hb, hp]⟩
  | idRun _ ih => simpa using ih locals typed total
  | idPure _ ih => simpa using ih locals typed total
  | bindRight value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (extend total bound)
    exact ⟨plan, by rw [extractScalarRangeWith_idBind, hb]; exact hp⟩
  | bindLeft value body ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (extend total plan.result)
    exact ⟨{ plan with result }, by
      rw [extractScalarRangeWith_idBind, rangeSupported_excludes_pure value]; simp [hp, hr]⟩
  | metadata _ ih => simpa using ih locals typed total

/-- Successful range extraction admits the independently stated source grammar. -/
theorem extractScalarRangeWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangePlan}
    (compiled : extractScalarRangeWith locals slot source = some plan) :
    RangeSupportedWith (locals.map ScalarBinding.kind) source := by
  induction locals, source using extractScalarRangeWith.induct generalizing plan with
  | case1 locals source view matched =>
    have same := scalarRange_sound matched
    subst source
    rw [extractScalarRangeWith_call] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨count, hc, initial, hi, scalar, hy, step, hs, _⟩ := compiled
    exact .range (extractScalarExprWith_supported hc) (extractScalarExprWith_supported hi)
      (scalarYield_sound hy) (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hs)
  | case2 locals body rejected ih =>
    change extractScalarRangeWith locals slot (Identity.run body) = some plan at compiled
    exact .idRun (ih (by simpa only [extractScalarRangeWith_idRun] using compiled))
  | case3 locals body rejected ih =>
    change extractScalarRangeWith locals slot (Identity.pure body) = some plan at compiled
    exact .idPure (ih (by simpa only [extractScalarRangeWith_idPure] using compiled))
  | case4 locals name value body nondep rejected ih =>
    rw [extractScalarRangeWith_letE] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hp⟩ := compiled
    exact .letE (extractScalarExprWith_supported hb) (by simpa [ScalarBinding.kind] using ih bound hp)
  | case5 locals value name body bi bound matched rejected ih =>
    change extractScalarRangeWith locals slot (Identity.bind name bi value body) = some plan at compiled
    rw [extractScalarRangeWith_idBind, matched] at compiled
    exact .bindRight (extractScalarExprWith_supported matched) (by simpa [ScalarBinding.kind] using ih compiled)
  | case6 locals value name body bi notPure rejected ih =>
    change extractScalarRangeWith locals slot (Identity.bind name bi value body) = some plan at compiled
    rw [extractScalarRangeWith_idBind, notPure] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, result, hr, _⟩ := compiled
    exact .bindLeft (ih hb) (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case7 locals data body rejected ih =>
    exact .metadata (ih (by simpa only [extractScalarRangeWith_metadata] using compiled))
  | case8 locals source rejected hrun hpure hlet hbind hmetadata =>
    rw [extractScalarRangeWith] at compiled <;> first | assumption | (simp [rejected] at compiled)

end LeanExe.Extract.Core
