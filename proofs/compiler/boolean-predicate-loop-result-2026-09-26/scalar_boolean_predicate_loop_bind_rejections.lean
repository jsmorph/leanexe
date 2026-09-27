import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word word .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let helper (body : Lean.Expr) := Lean.Expr.letE `predicate
    (.forallE `b boolean boolean .default) (.lam `b boolean (.bvar 0) .default) body false
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for outside in [false, true] do
    for binder in [Lean.BinderInfo.default, .implicit] do
      for flag in [false, true] do
        for wrapper in [none, some (BooleanWrapper.pure .boolean), some (.run .boolean), some (.metadata {})] do
          let action (value : Lean.Expr) := match wrapper with
            | none => value
            | some wrapper => wrapper.expr value
          let literal := booleanLiteralExpr flag
          let call := Lean.Expr.app (.bvar 0) literal
          let standard := BooleanIdentity.bind `flag binder (.bvar 0) (.bvar 0) word
          let evidence := standard.getAppArgs[1]!
          let explicit (levels : List Lean.Level) (monad instance_ input domain : Lean.Expr)
              (outputOverride : Option Lean.Expr) (value body output : Lean.Expr) :=
            Lean.mkAppN (.const ``Bind.bind levels)
              #[monad, instance_, input, outputOverride.getD output, action value, .lam `flag domain body binder]
          let make := explicit [.zero, .zero] (.const ``Id [.zero]) evidence boolean boolean none
          let wrap (form : Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr) (value result : Lean.Expr) :=
            let body := if outside then helper (form value
              (Range.call (.bvar 3) (.bvar 2) `i `a .default .default
                (Step.yieldDirect (LeanExe.Source.ExprProofBinder.lift 0
                  (LeanExe.Source.ExprProofBinder.lift 0 result)))) word)
              else Range.call (.bvar 1) (.bvar 0) `i `a .default .default
                (helper (form value (Step.yieldDirect result) (Step.resultType .word)))
            Lean.Expr.lam `count word (.lam `seed word body .default) .default
          let check (value result : Lean.Expr) :=
            extractScalarFunc `loopBooleanBind (some "entry") functionType (wrap make value result)
          for result in [toWord (.bvar 0), literalExpr 0] do
            unless (check call result).isSome do throwError "valid used/unused loop Boolean bind rejected"
            controls := controls + 1
            for value in [literalExpr 0, Lean.Expr.bvar 0, .bvar 1,
                .const `unsupportedValue [], .app (.bvar 0) (literalExpr 0),
                .app (.bvar 1) literal, .app (.bvar 0) (.bvar 1)] do
              unless (check value result).isNone do throwError "invalid used/unused loop Boolean bind accepted"
              rejected := rejected + 1
          for result in [Lean.Expr.bvar 0, .app (.bvar 0) literal, toWord (.bvar 1)] do
            unless (check call result).isNone do throwError "loop Boolean bind changed a value/function kind"
            rejected := rejected + 1
          let monad : Lean.Expr := .const ``Id [.zero]
          for form in [explicit [.zero, .zero] monad evidence word boolean none,
              explicit [.zero, .zero] monad evidence boolean word none,
              explicit [.zero, .zero] monad evidence boolean boolean (some boolean),
              explicit [.zero, .zero] monad evidence (.const ``Bool [.zero]) (.const ``Bool [.zero]) none,
              explicit [.zero, .zero] monad (.const `customBind []) boolean boolean none,
              explicit [.zero, .zero] (.const `customMonad []) evidence boolean boolean none,
              explicit [.succ .zero, .zero] monad evidence boolean boolean none] do
            unless (extractScalarFunc `invalidLoopBind (some "entry") functionType
                (wrap form call (toWord (.bvar 0)))).isNone do
              throwError "invalid loop Boolean bind type/instance/universe accepted"
            rejected := rejected + 1
  unless controls == 64 && rejected == 768 do throwError "unexpected counts {controls}, {rejected}"
  Lean.logInfo m!"{controls} loop Boolean bind admission controls and {rejected} type/instance/unused-value rejection tests passed"
