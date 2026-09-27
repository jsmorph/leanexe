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
            for negations in [1, 2, 3] do
              let decorate (value : Lean.Expr) := BooleanGuardNegation.expr negations
                (if negations == 2 then BooleanIdentity.run value resultType else value)
              let helper := decorate original
              unless (booleanLocalOperands? helper).isNone && (booleanNegated? helper).isSome &&
                  (booleanWrapped? helper).isNone && (booleanHelper? false helper).isNone && (booleanHelper? true helper).isNone do
                throwError "helper parser priority or input kind is incorrect"
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
                  let flag := GuardNegation.denote negations (if disjoin then left || right else left && right)
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
                  .app (.const ``Bool.not [.zero]) original,
                  .app (.const `customNot []) original,
                  .app (.const ``Bool.not []) (literalExpr 0),
                  .app (.const ``Bool.not []) (.bvar 1)]
                for (bad, index) in invalid.zipIdx do
                  unless (extractScalarStepWith locals (make bad)).isNone do
                    throwError "invalid inner helper case {index}, mode {mode} admitted"
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
  unless comparisons == 5376 && rejected == 3552 && controls == 96 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/negated Boolean helper step IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"
