import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word body .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for binder in [Lean.BinderInfo.default, .implicit] do
    for inputDepth in [0, 2] do
      let bt := (List.range inputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
      let wt := (List.range inputDepth).foldl (fun t _ => ResultType.identity t) .word
      for resultDepth in [0, 2] do
        let result := (List.range resultDepth).foldl (fun t _ => BooleanType.identity t) .boolean
        for wordInput in [false, true] do
          let input := if wordInput then wt.expr else bt.expr
          for negations in [0, 1, 2, 3] do
            for pureValue in [false, true] do
              for flag in [false, true] do
                let fBody : BooleanLocal := .junction 0 .conjunction
                  (.var 0 0) (.compare .ne (.bvar 2) (.bvar 1))
                let outer (body : Lean.Expr) := Lean.Expr.letE `f
                  (.forallE `b boolean boolean binder) (.lam `b boolean fBody.expr binder) body false
                let rawValue := if wordInput then Lean.Expr.app (.app (.const ``UInt64.add []) (.bvar 2))
                  (literalExpr flag.toUInt64.toNat) else .app (.bvar 0) (booleanLiteralExpr flag)
                let value := if pureValue then
                  (if wordInput then Identity.pure rawValue wt else BooleanIdentity.pure rawValue bt) else rawValue
                let arg := if wordInput then (BooleanLocal.compare .eq (.bvar 0) (.bvar 2)).expr else
                  BooleanGuardNegation.expr 1 (.bvar 0)
                let body := BooleanIdentity.pure (.app (.bvar 1) arg) result
                let make (input domain output evidence value body : Lean.Expr) := outer (toWord
                  (BooleanGuardNegation.expr negations
                    (Lean.mkAppN (.const ``Bind.bind [.zero, .zero]) #[.const ``Id [.zero], evidence,
                      input, output, value, .lam `saved domain body binder])))
                let standard := Lean.Expr.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
                  (.const ``Id.instMonad [.zero])
                let source := make input input result.expr standard value body
                let some func := extractScalarFunc `booleanResultBind (some "entry") functionType (wrap source) |
                  throwError "Boolean result bind rejected"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (x, y) in inputs do
                  let argument := if wordInput then x + flag.toUInt64 == y else !(flag && x != y)
                  let expected := (GuardNegation.denote negations (argument && x != y)).toUInt64
                  let actual := module_.evalFunc 0 [x, y]
                  unless actual == expected do throwError "Boolean result bind {actual}, expected {expected}"
                  comparisons := comparisons + 1
                unless (extractScalarFunc `unusedBind (some "entry") functionType
                    (wrap (make input input result.expr standard value (BooleanIdentity.pure (booleanLiteralExpr true) result)))).isSome do
                  throwError "valid unused Boolean result bind rejected"
                controls := controls + 1
                let invalidValue := if wordInput then booleanLiteralExpr flag else literalExpr 0
                let invalidBody := if wordInput then Lean.Expr.bvar 0 else literalExpr 0
                for source in [make input (.const ``Nat []) result.expr standard value body,
                    make (.const ``Nat []) input result.expr standard value body,
                    make input input word standard value body,
                    make input input (.const ``Nat []) standard value body,
                    make input input result.expr (.bvar 0) value body,
                    make input input result.expr (.const `customBind []) value body,
                    make input input result.expr standard invalidValue body,
                    make input input result.expr standard value invalidBody,
                    make input input result.expr standard value (.app (.bvar 0) (booleanLiteralExpr true)),
                    make input input result.expr standard value (.app (.bvar 1) (literalExpr 0)),
                    make input input result.expr standard (.const `unsupportedUnusedAction []) (booleanLiteralExpr true)] do
                  unless (extractScalarFunc `invalidResultBind (some "entry") functionType (wrap source)).isNone do
                    throwError "invalid Boolean result bind admitted"
                  rejected := rejected + 1
                -- A changed universe on the standard Bind head is not admitted.
                let wrongUniverse := outer (toWord (Lean.mkAppN (.const ``Bind.bind [.succ .zero, .zero])
                  #[.const ``Id [.zero], standard, input, result.expr, value, .lam `saved input body binder]))
                unless (extractScalarFunc `invalidBindUniverse (some "entry") functionType (wrap wrongUniverse)).isNone do
                  throwError "Bind accepted wrong universe"
                rejected := rejected + 1
  unless comparisons == 3584 && rejected == 3072 && controls == 256 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean result-bind IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"
