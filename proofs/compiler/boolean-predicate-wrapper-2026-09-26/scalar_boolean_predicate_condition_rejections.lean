import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for scope in [0, 1, 2] do
    let index := if scope == 2 then 2 else 0
    let wrap (result : Lean.Expr) :=
      let helper (body : Lean.Expr) := Lean.Expr.letE `predicate
        (.forallE `b boolean boolean .default) (.lam `b boolean (.bvar 0) .default) body false
      let body := if scope == 0 then helper result else if scope == 1 then
        Range.call (.bvar 1) (.bvar 0) `i `a .default .default (helper (Step.yieldDirect result))
        else helper (Range.call (.bvar 2) (.bvar 1) `i `a .default .default (Step.yieldDirect result))
      Lean.Expr.lam `x word (.lam `y word body .default) .default
    let check (value : Lean.Expr) := extractScalarFunc `predicateCondition (some "entry") functionType (wrap value)
    for flag in [false, true] do
      let pred : BooleanLocal := .predicate 0 index (booleanLiteralExpr flag)
      let guards : List BooleanLocalGuard := [⟨pred, rfl, .truth pred⟩,
        ⟨.equality 0 false pred (.literal 0 false), rfl, .equal pred (.literal 0 false) (by decide)⟩,
        ⟨.equality 0 true pred (.literal 0 false), rfl, .unequal pred (.literal 0 false)⟩]
      for guard in guards do
        for dependent in [false, true] do
          let make (levels : List Lean.Level) (type decision yes no : Lean.Expr) :=
            if dependent then Lean.mkAppN (.const ``dite levels)
              #[type, guard.condition, decision,
                .lam `yesProof guard.condition (LeanExe.Source.ExprProofBinder.lift 0 yes) .default,
                .lam `noProof (.app (.const ``Not []) guard.condition)
                  (LeanExe.Source.ExprProofBinder.lift 0 no) .default]
            else Lean.mkAppN (.const ``ite levels) #[type, guard.condition, decision, yes, no]
          let yes := literalExpr 7
          let no := literalExpr 11
          unless (check (make [.succ .zero] word guard.evidence yes no)).isSome do
            throwError "valid direct predicate condition rejected"
          controls := controls + 1
          for invalid in [booleanLiteralExpr true, Lean.Expr.bvar index,
              .const `unsupportedBranch [], toWord (.app (.bvar index) (literalExpr 0))] do
            for body in [make [.succ .zero] word guard.evidence invalid no,
                make [.succ .zero] word guard.evidence yes invalid] do
              unless (check body).isNone do throwError "invalid active/inactive condition branch accepted"
              rejected := rejected + 1
          for body in [make [.zero] word guard.evidence yes no,
              make [.succ .zero] boolean guard.evidence yes no,
              make [.succ .zero] word (.const `unsupportedDecision []) yes no] do
            unless (check body).isNone do throwError "invalid condition universe/type/evidence accepted"
            rejected := rejected + 1
          if dependent then
            let dependentBody (yes no : Lean.Expr) := Lean.mkAppN (.const ``dite [.succ .zero])
              #[word, guard.condition, guard.evidence,
                .lam `yesProof guard.condition yes .default,
                .lam `noProof (.app (.const ``Not []) guard.condition) no .default]
            for proofUse in [Lean.Expr.bvar 0, toWord (.bvar 0)] do
              for body in [dependentBody proofUse no, dependentBody yes proofUse] do
                unless (check body).isNone do throwError "condition proof used as a word/Boolean"
                rejected := rejected + 1
  unless controls == 36 && rejected == 468 do throwError "unexpected counts {controls}, {rejected}"
  Lean.logInfo m!"{controls} direct condition admission controls and {rejected} branch/type/evidence rejection tests passed"
