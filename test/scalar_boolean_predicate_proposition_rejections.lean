import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for scope in [0, 1, 2] do
    let index := if scope == 2 then 2 else 0
    let wordIndex := if scope == 2 then 0 else 1
    let yes : BooleanLocal := .predicate 0 index (booleanLiteralExpr true)
    let no : BooleanLocal := .predicate 0 index (booleanLiteralExpr false)
    let wrap (argument : Lean.Expr) :=
      let result := Lean.Expr.app (.const ``Bool.toUInt64 []) argument
      let helper (body : Lean.Expr) := Lean.Expr.letE `predicate
        (.forallE `b boolean boolean .default) (.lam `b boolean (.bvar 0) .default) body false
      let body := if scope == 0 then helper result else if scope == 1 then
        Range.call (.bvar 1) (.bvar 0) `i `a .default .default (helper (Step.yieldDirect result))
        else helper (Range.call (.bvar 2) (.bvar 1) `i `a .default .default (Step.yieldDirect result))
      Lean.Expr.lam `x word (.lam `y word body .default) .default
    let check (argument : Lean.Expr) := extractScalarFunc `predicateChoice (some "entry") functionType (wrap argument)
    for form in [BooleanChoiceForm.ordinary, .dependent ⟨`yesProof, `noProof, .default, .default⟩] do
      for flag in [false, true] do
        let make (yes no : BooleanLocal) :=
          (form.proposition 0 ⟨.canonical (.literal (.proposition 0 flag)), rfl⟩ yes no).expr
        unless (check (make yes no)).isSome do throwError "positive predicate proposition control rejected"
        controls := controls + 1
        for argument in [literalExpr 0, Lean.Expr.bvar index, .const `unsupportedArgument [], .bvar wordIndex] do
          let invalid : BooleanLocal := .predicate 0 index argument
          for body in [make invalid no, make yes invalid] do
            unless (check body).isNone do throwError "invalid active/inactive predicate proposition branch accepted"
            rejected := rejected + 1
    for flag in [false, true] do
      let left : Lean.Expr := .bvar wordIndex
      let right := literalExpr (if flag then 1 else 0)
      let condition := Comparison.lt.condition left right
      let evidence := Comparison.lt.evidence left right
      let make (yes no : Lean.Expr) := Lean.mkAppN (.const ``dite [.succ .zero])
        #[boolean, condition, evidence, .lam `yesProof condition yes .default,
          .lam `noProof (.app (.const ``Not []) condition) no .default]
      let liftedYes := LeanExe.Source.ExprProofBinder.lift 0 yes.expr
      let liftedNo := LeanExe.Source.ExprProofBinder.lift 0 no.expr
      for body in [make (.bvar 0) liftedNo, make liftedYes (.bvar 0)] do
        unless (check body).isNone do throwError "predicate proposition condition proof used as a Boolean value"
        rejected := rejected + 1
      let ordinary (levels : List Lean.Level) (type guard decision first : Lean.Expr) :=
        Lean.mkAppN (.const ``ite levels) #[type, guard, decision, first, no.expr]
      for body in [ordinary [.succ .zero] word condition evidence yes.expr,
          ordinary [.succ .zero] boolean condition (.const `unsupportedDecision []) yes.expr,
          ordinary [.succ .zero] boolean condition (Comparison.le.evidence left right) yes.expr,
          ordinary [.succ .zero] boolean condition (Comparison.lt.evidence right left) yes.expr,
          ordinary [.zero] boolean condition evidence yes.expr,
          ordinary [.succ .zero] boolean (Comparison.lt.condition (.bvar index) right)
            (Comparison.lt.evidence (.bvar index) right) yes.expr,
          ordinary [.succ .zero] boolean condition evidence (literalExpr 0)] do
        unless (check body).isNone do throwError "invalid proposition type, evidence or operand accepted"
        rejected := rejected + 1
  unless controls == 12 && rejected == 150 do throwError "unexpected counts {controls}, {rejected}"
  Lean.logInfo m!"{controls} predicate proposition admission controls and {rejected} branch/proof/evidence rejection tests passed"
