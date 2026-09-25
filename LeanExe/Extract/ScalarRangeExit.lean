import LeanExe.Extract.ScalarStepAcceptance
import LeanExe.Extract.ScalarStepSupported
import LeanExe.Extract.ScalarRangeSyntax
import LeanExe.Source.ScalarRangeExitSupported
import LeanExe.IR.ScalarRangeExitSlots

namespace LeanExe.Extract.Core

/-- One dynamic loop with a scalar accumulator and a pure result computation.
The allocated slots are accumulator, index, stop, and exit decision, in that order. -/
structure ScalarRangeExitPlan where
  count : LeanExe.IR.Expr
  initial : LeanExe.IR.Expr
  step : LeanExe.IR.Expr
  done : LeanExe.IR.Expr
  result : LeanExe.IR.Expr
  deriving Repr

def ScalarRangeExitPlan.body (plan : ScalarRangeExitPlan) (slot : Nat) : LeanExe.IR.Stmt :=
  .seq (.assign (slot + 2) plan.count)
    (.seq (.assign slot plan.initial)
      (.seq (.assign (slot + 1) (.u64 0))
        (.seq (.assign (slot + 3) (.u64 0))
          (.seq (.while (LeanExe.IR.rangeCondition slot)
            (LeanExe.IR.rangeExitBody slot plan.step plan.done))
            (.assign slot plan.result)))))

def ScalarRangeExitPlan.func (plan : ScalarRangeExitPlan) (name : Lean.Name)
    (exportName : Option String) (arity : Nat) : LeanExe.IR.Func :=
  { sourceName := name, exportName, params := arity, locals := arity + 4
    body := plan.body arity, results := [.local arity] }

/-- Extract a single early-exit range loop and surrounding pure computations.
The loop remains dynamic; its stop is evaluated once into a fresh local. -/
def extractScalarRangeExitWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match scalarRange? source with
  | some view => do
      let count ← extractScalarExprWith locals view.count
      let initial ← extractScalarExprWith locals view.initial
      let code ← extractScalarStepWith
        (.scalar (.word (.local slot)) :: .scalar (.natural (.local (slot + 1))) ::
          locals.map ScalarStepBinding.scalar) view.body
      pure { count, initial, step := code.value, done := code.done, result := .local slot }
  | none =>
      match source with
      | .app (.app (.const ``Id.run [.zero]) (.const ``UInt64 [])) body =>
          extractScalarRangeExitWith locals slot body
      | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
            (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
              (.const ``Id.instMonad [.zero])))) (.const ``UInt64 [])) body =>
          extractScalarRangeExitWith locals slot body
      | .letE _ (.const ``UInt64 []) value body _ => do
          let bound ← extractScalarExprWith locals value
          extractScalarRangeExitWith (.word bound :: locals) slot body
      | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
            (.const ``Id.instMonad [.zero]))) (.const ``UInt64 [])) (.const ``UInt64 [])) value)
          (.lam _ (.const ``UInt64 []) body _) =>
          match extractScalarExprWith locals value with
          | some bound => extractScalarRangeExitWith (.word bound :: locals) slot body
          | none => do
              let plan ← extractScalarRangeExitWith locals slot value
              let result ← extractScalarExprWith (.word plan.result :: locals) body
              pure { plan with result }
      | .mdata _ body => extractScalarRangeExitWith locals slot body
      | _ => none
termination_by sizeOf source

open LeanExe.Source.Scalar

theorem rangeExitSupported_excludes_pure {types : List BindingKind} {source : Lean.Expr}
    (supported : Range.Exit.Supported types source) (locals : List ScalarBinding) :
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

theorem extractScalarRangeExitWith_call (locals : List ScalarBinding) (slot : Nat)
    (view : ScalarRangeView) : extractScalarRangeExitWith locals slot view.source = (do
      let count ← extractScalarExprWith locals view.count
      let initial ← extractScalarExprWith locals view.initial
      let code ← extractScalarStepWith
        (.scalar (.word (.local slot)) :: .scalar (.natural (.local (slot + 1))) ::
          locals.map ScalarStepBinding.scalar) view.body
      pure { count, initial, step := code.value, done := code.done, result := .local slot }) := by
  rw [extractScalarRangeExitWith.eq_def, scalarRange_accepts]

@[simp] theorem extractScalarRangeExitWith_idRun (locals : List ScalarBinding) (slot : Nat) (body : Lean.Expr) :
    extractScalarRangeExitWith locals slot (Identity.run body) = extractScalarRangeExitWith locals slot body := by
  rw [Identity.run, extractScalarRangeExitWith]
  rfl

@[simp] theorem extractScalarRangeExitWith_idPure (locals : List ScalarBinding) (slot : Nat) (body : Lean.Expr) :
    extractScalarRangeExitWith locals slot (Identity.pure body) = extractScalarRangeExitWith locals slot body := by
  rw [Identity.pure, extractScalarRangeExitWith]
  rfl

theorem extractScalarRangeExitWith_letE (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name (.const ``UInt64 []) value body nondep) = (do
      let bound ← extractScalarExprWith locals value
      extractScalarRangeExitWith (.word bound :: locals) slot body) := by
  rw [extractScalarRangeExitWith]
  rfl

theorem extractScalarRangeExitWith_idBind (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (bi : Lean.BinderInfo) (value body : Lean.Expr) :
    extractScalarRangeExitWith locals slot (Identity.bind name bi value body) =
      (match extractScalarExprWith locals value with
      | some bound => extractScalarRangeExitWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) body
          pure { plan with result }) := by
  rw [Identity.bind, extractScalarRangeExitWith]
  rfl

@[simp] theorem extractScalarRangeExitWith_metadata (locals : List ScalarBinding) (slot : Nat)
    (data : Lean.MData) (body : Lean.Expr) :
    extractScalarRangeExitWith locals slot (.mdata data body) = extractScalarRangeExitWith locals slot body := by
  rw [extractScalarRangeExitWith]
  rfl

theorem extractScalarRangeExitWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : Range.Exit.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarRangeExitWith locals slot source = some plan := by
  have extend {locals : List ScalarBinding} (total : ∀ binding ∈ locals, binding.Total)
      (value : LeanExe.IR.Expr) : ∀ binding ∈ ScalarBinding.word value :: locals, binding.Total := by
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · exact total binding member
  induction supported generalizing locals with
  | @range types count initial body indexName accumulatorName indexBi accumulatorBi hc hi hs =>
    obtain ⟨c, ec⟩ := extractScalarExprWith_accepts hc locals typed total
    obtain ⟨i, ei⟩ := extractScalarExprWith_accepts hi locals typed total
    obtain ⟨code, es⟩ := extractScalarStepWith_accepts hs
      (.scalar (.word (.local slot)) :: .scalar (.natural (.local (slot + 1))) ::
        locals.map ScalarStepBinding.scalar)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, List.map_map, Function.comp_def, ← typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact total original present)
    refine ⟨{ count := c, initial := i, step := code.value, done := code.done, result := .local slot }, ?_⟩
    have equation := extractScalarRangeExitWith_call locals slot
      { count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body }
    simpa [ScalarRangeView.source, ec, ei, es] using equation
  | letE value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (extend total bound)
    exact ⟨plan, by rw [extractScalarRangeExitWith_letE]; simp [hb, hp]⟩
  | idRun _ ih => simpa using ih locals typed total
  | idPure _ ih => simpa using ih locals typed total
  | bindRight value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (extend total bound)
    exact ⟨plan, by rw [extractScalarRangeExitWith_idBind, hb]; exact hp⟩
  | bindLeft value body ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (extend total plan.result)
    exact ⟨{ plan with result }, by
      rw [extractScalarRangeExitWith_idBind, rangeExitSupported_excludes_pure value]; simp [hp, hr]⟩
  | metadata _ ih => simpa using ih locals typed total

/-- Successful range extraction admits the independently stated source grammar. -/
theorem extractScalarRangeExitWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarRangeExitWith locals slot source = some plan) :
    Range.Exit.Supported (locals.map ScalarBinding.kind) source := by
  induction locals, source using extractScalarRangeExitWith.induct generalizing plan with
  | case1 locals source view matched =>
    have same := scalarRange_sound matched
    subst source
    rw [extractScalarRangeExitWith_call] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨count, hc, initial, hi, code, hs, _⟩ := compiled
    exact .range (extractScalarExprWith_supported hc) (extractScalarExprWith_supported hi)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind, List.map_map, Function.comp_def]
        using extractScalarStepWith_supported hs)
  | case2 locals body rejected ih =>
    change extractScalarRangeExitWith locals slot (Identity.run body) = some plan at compiled
    exact .idRun (ih (by simpa only [extractScalarRangeExitWith_idRun] using compiled))
  | case3 locals body rejected ih =>
    change extractScalarRangeExitWith locals slot (Identity.pure body) = some plan at compiled
    exact .idPure (ih (by simpa only [extractScalarRangeExitWith_idPure] using compiled))
  | case4 locals name value body nondep rejected ih =>
    rw [extractScalarRangeExitWith_letE] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hp⟩ := compiled
    exact .letE (extractScalarExprWith_supported hb) (by simpa [ScalarBinding.kind] using ih bound hp)
  | case5 locals value name body bi bound matched rejected ih =>
    change extractScalarRangeExitWith locals slot (Identity.bind name bi value body) = some plan at compiled
    rw [extractScalarRangeExitWith_idBind, matched] at compiled
    exact .bindRight (extractScalarExprWith_supported matched) (by simpa [ScalarBinding.kind] using ih compiled)
  | case6 locals value name body bi notPure rejected ih =>
    change extractScalarRangeExitWith locals slot (Identity.bind name bi value body) = some plan at compiled
    rw [extractScalarRangeExitWith_idBind, notPure] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, result, hr, _⟩ := compiled
    exact .bindLeft (ih hb) (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case7 locals data body rejected ih =>
    exact .metadata (ih (by simpa only [extractScalarRangeExitWith_metadata] using compiled))
  | case8 locals source rejected hrun hpure hlet hbind hmetadata =>
    rw [extractScalarRangeExitWith] at compiled <;> first | assumption | (simp [rejected] at compiled)

end LeanExe.Extract.Core
