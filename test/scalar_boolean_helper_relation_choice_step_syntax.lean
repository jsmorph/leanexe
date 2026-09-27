import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let locals : List ScalarStepBinding := [.scalar (.word (.local 1)), .scalar (.word (.local 0))]
  let truth (value : Lean.Expr) := Lean.mkAppN (.const ``Eq [.succ .zero]) #[boolean, value, booleanLiteralExpr true]
  let decision (value : Lean.Expr) := Lean.mkAppN (.const ``instDecidableEqBool []) #[value, booleanLiteralExpr true]
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for depth in [0, 2] do
    let resultType := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
    for booleanInput in [false, true] do
      let input := if booleanInput then boolean else word
      let body : BooleanLocal := if booleanInput then
        .junction 0 .disjunction (.var 0 0) (.compare .eq (.bvar 2) (.bvar 1))
        else .compare .eq (.bvar 0) (.bvar 1)
      for nondep in [false, true] do
        for info in [Lean.BinderInfo.default, .implicit] do
          let shape : BooleanFunctionBinding := ⟨`f, `arg, info, info, resultType, nondep⟩
          let argumentX := if booleanInput then (BooleanLocal.compare .eq (.bvar 2) (literalExpr 0)).expr else .bvar 2
          let argumentY := if booleanInput then (BooleanLocal.compare .eq (.bvar 1) (literalExpr 0)).expr else literalExpr 0
          let callX := Lean.Expr.app (.bvar 0) argumentX
          let callY := Lean.Expr.app (.bvar 0) argumentY
          for disjoin in [false, true] do
            let continuation := Lean.Expr.app (.app (.const (if disjoin then ``Bool.or else ``Bool.and) []) callX) callY
            let original := booleanHelperExpr booleanInput shape `arg body.expr continuation
            let otherBody : BooleanLocal := if booleanInput then
              .junction 0 .disjunction (.var 0 0) (.compare .ne (.bvar 2) (.bvar 1))
              else .compare .ne (.bvar 0) (.bvar 1)
            let other := BooleanIdentity.pure (booleanHelperExpr booleanInput shape `arg otherBody.expr continuation) resultType
            let ordinary := (BooleanLocal.compare .eq (.bvar 1) (literalExpr 0)).expr
            for unequal in [false, true] do
              for proof in ([none, some ⟨`yesProof, `noProof, info, info⟩] : List (Option BooleanProofBranch)) do
                for placement in ([0, 1, 2, 3, 4] : List Nat) do
                  let rawChoice (annotation condition evidence td fd yes no : Lean.Expr) : Lean.Expr :=
                    match proof with
                    | none => Lean.mkAppN (.const ``ite [.succ .zero]) #[annotation, condition, evidence, yes, no]
                    | some shape => Lean.mkAppN (.const ``dite [.succ .zero]) #[annotation, condition, evidence,
                      .lam shape.trueName td (LeanExe.Source.ExprProofBinder.lift 0 yes) shape.trueInfo,
                      .lam shape.falseName fd (LeanExe.Source.ExprProofBinder.lift 0 no) shape.falseInfo]
                  let operands (value : Lean.Expr) :=
                    (if placement == 1 then ordinary else value,
                     if placement == 0 then ordinary else if placement == 1 then value else
                       if placement == 2 then other else booleanLiteralExpr (placement == 4),
                     if placement == 1 then ordinary else value,
                     if placement == 0 then ordinary else other)
                  let validChoice (left right yes no : Lean.Expr) :=
                    let condition := booleanRelationCondition unequal left right
                    rawChoice resultType.expr condition (booleanRelationEvidence unequal left right)
                      condition (.app (.const ``Not []) condition) yes no
                  let decorate (value : Lean.Expr) :=
                    let (left, right, yes, no) := operands value
                    validChoice left right yes no
                  let (relationLeft, relationRight, selectedYes, selectedNo) := operands original
                  let relationCondition := booleanRelationCondition unequal relationLeft relationRight
                  let relationEvidence := booleanRelationEvidence unequal relationLeft relationRight
                  let helper := decorate original
                  let isTruth := placement == 4 && !unequal
                  unless (booleanLocalOperands? helper).isNone &&
                      (booleanRelationSelection? helper).isSome == !isTruth &&
                      (booleanSelected? helper).isSome == isTruth &&
                      (booleanGuardedSelection? helper).isNone && (booleanRelated? helper).isNone &&
                      (booleanJoined? helper).isNone && (booleanNegated? helper).isNone &&
                      (booleanWrapped? helper).isNone && (booleanHelper? false helper).isNone &&
                      (booleanHelper? true helper).isNone do
                    throwError "relation/truth parser priority is incorrect"
                  controls := controls + 1
                  for mode in ([1, 2] : List Nat) do
                    let expression (value evidence td fd : Lean.Expr) : Lean.Expr :=
                      if mode == 1 then Lean.mkAppN (.const ``ite [.succ .zero]) #[Step.resultType .word, truth value, evidence, Step.doneDirect (.bvar 1), Step.yieldDirect (.bvar 0)]
                      else Lean.mkAppN (.const ``dite [.succ .zero]) #[Step.resultType .word, truth value, evidence,
                        .lam `proof td (Step.doneDirect (.bvar 2)) .default, .lam `proof fd (Step.yieldDirect (.bvar 1)) .default]
                    let make (value : Lean.Expr) := (expression value (decision value) (truth value) (.app (.const ``Not []) (truth value)))
                    let some code := extractScalarStepWith locals (make helper) |
                      throwError "inner helper rejected: Boolean input {booleanInput}, mode {mode}"
                    let module_ : LeanExe.IR.Module := { funcs := #[
                      { sourceName := `stepValue, exportName := none, params := 2, locals := 0, body := .skip, results := [code.value] },
                      { sourceName := `stepDone, exportName := none, params := 2, locals := 0, body := .skip, results := [code.done] }] }
                    for (x, y) in inputs do
                      let left := if booleanInput then x == 0 || x == y else x == y
                      let right := if booleanInput then y == 0 || x == y else 0 == y
                      let helperFlag := if disjoin then left || right else left && right
                      let otherLeft := if booleanInput then x == 0 || x != y else x != y
                      let otherRight := if booleanInput then y == 0 || x != y else 0 != y
                      let otherFlag := if disjoin then otherLeft || otherRight else otherLeft && otherRight
                      let ordinaryFlag := x == 0
                      let left := if placement == 1 then ordinaryFlag else helperFlag
                      let right := if placement == 0 then ordinaryFlag else if placement == 1 then helperFlag else
                        if placement == 2 then otherFlag else placement == 4
                      let condition := if unequal then decide (left ≠ right) else decide (left = right)
                      let yes := if placement == 1 then ordinaryFlag else helperFlag
                      let no := if placement == 0 then ordinaryFlag else otherFlag
                      let flag := if condition then yes else no
                      let expected := if flag then x else y
                      let actual := module_.evalFunc 0 [x, y]
                      unless actual == expected do throwError "inner helper mode {mode}: {actual}, expected {expected}"
                      unless module_.evalFunc 1 [x, y] == flag.toUInt64 do throwError "inner helper exit decision mismatch"
                      comparisons := comparisons + 2
                    let raw (annotation domain result body tail : Lean.Expr) := decorate (Lean.Expr.letE `f
                      (.forallE `arg annotation result info) (.lam `arg domain body info) tail nondep)
                    let badBody := if booleanInput then (BooleanLocal.compare .eq (.bvar 0) (.bvar 1)).expr else (BooleanLocal.var 0 0).expr
                    let invalid := [
                      raw (.const ``Nat []) input resultType.expr body.expr continuation,
                      raw input (.const ``Nat []) resultType.expr body.expr continuation,
                      raw input input word body.expr continuation,
                      raw input input (.const ``String []) body.expr continuation,
                      raw input input resultType.expr (.const `unsupportedBoolean []) continuation,
                      raw input input resultType.expr badBody continuation,
                      raw input input resultType.expr body.expr (.const `unsupportedBoolean []),
                      raw input input resultType.expr body.expr (Lean.Expr.app (.bvar 9) argumentX),
                      raw input input resultType.expr (.const `unsupportedBoolean []) (booleanLiteralExpr true),
                      raw input input resultType.expr badBody (booleanLiteralExpr false),
                      validChoice (booleanLiteralExpr true) (booleanLiteralExpr true) original (.const `unsupportedBoolean []),
                      validChoice (booleanLiteralExpr false) (booleanLiteralExpr true) (.const `unsupportedBoolean []) original,
                      validChoice (.const `unsupportedBoolean []) (.const `unsupportedBoolean []) original ordinary,
                      validChoice (literalExpr 0) ordinary original ordinary,
                      validChoice ordinary original (literalExpr 0) original,
                      validChoice ordinary original original (literalExpr 0),
                      rawChoice (.const ``Nat []) relationCondition relationEvidence relationCondition (.app (.const ``Not []) relationCondition) selectedYes selectedNo,
                      rawChoice word relationCondition relationEvidence relationCondition (.app (.const ``Not []) relationCondition) selectedYes selectedNo,
                      rawChoice resultType.expr relationCondition (.const `customDecision []) relationCondition (.app (.const ``Not []) relationCondition) selectedYes selectedNo,
                      Lean.mkAppN (.const `customChoice []) #[resultType.expr, relationCondition, relationEvidence, selectedYes, selectedNo],
                      rawChoice resultType.expr (Lean.mkAppN (.const (if unequal then ``Ne else ``Eq) [.zero]) #[boolean, relationLeft, relationRight]) relationEvidence relationCondition (.app (.const ``Not []) relationCondition) selectedYes selectedNo,
                      rawChoice resultType.expr (Lean.mkAppN (.const (if unequal then ``Ne else ``Eq) [.succ .zero]) #[word, relationLeft, relationRight]) relationEvidence relationCondition (.app (.const ``Not []) relationCondition) selectedYes selectedNo,
                      rawChoice resultType.expr relationCondition (booleanRelationEvidence unequal relationRight relationLeft) relationCondition (.app (.const ``Not []) relationCondition) selectedYes selectedNo,
                      rawChoice resultType.expr relationCondition (.mdata {} relationEvidence) relationCondition (.app (.const ``Not []) relationCondition) selectedYes selectedNo]
                    for (bad, index) in invalid.zipIdx do
                      unless (extractScalarStepWith locals (make bad)).isNone do
                        throwError "invalid inner helper case {index}, mode {mode} admitted"
                      rejected := rejected + 1
                    if let some innerShape := proof then
                      for (td, fd) in [(word, .app (.const ``Not []) relationCondition),
                          (relationCondition, word), (relationCondition, relationCondition)] do
                        let bad := rawChoice resultType.expr relationCondition relationEvidence td fd selectedYes selectedNo
                        unless (extractScalarStepWith locals (make bad)).isNone do throwError "invalid inner choice proof domain admitted"
                        rejected := rejected + 1
                      for (yes, no) in [(Lean.Expr.bvar 0, LeanExe.Source.ExprProofBinder.lift 0 selectedNo),
                          (LeanExe.Source.ExprProofBinder.lift 0 selectedYes, Lean.Expr.bvar 0),
                          (Lean.Expr.bvar 0, Lean.Expr.bvar 0)] do
                        let bad := Lean.mkAppN (.const ``dite [.succ .zero]) #[resultType.expr, relationCondition, relationEvidence,
                          .lam innerShape.trueName relationCondition yes innerShape.trueInfo,
                          .lam innerShape.falseName (.app (.const ``Not []) relationCondition) no innerShape.falseInfo]
                        unless (extractScalarStepWith locals (make bad)).isNone do throwError "used inner choice proof binder admitted"
                        rejected := rejected + 1
                    if mode != 0 then
                      for evidence in [.const `customDecision [], .mdata {} (decision helper), decision (booleanLiteralExpr true)] do
                        unless (extractScalarStepWith locals
                            (expression helper evidence (truth helper) (.app (.const ``Not []) (truth helper)))).isNone do
                          throwError "invalid helper decision admitted"
                        rejected := rejected + 1
                    if mode == 2 then
                      for (td, fd) in [(word, .app (.const ``Not []) (truth helper)),
                          (truth helper, word), (truth helper, truth helper)] do
                        unless (extractScalarStepWith locals
                            (expression helper (decision helper) td fd)).isNone do
                          throwError "invalid helper proof domain admitted"
                        rejected := rejected + 1
  unless comparisons == 35840 && rejected == 40320 && controls == 640 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/relation-choice Boolean helper step IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"
