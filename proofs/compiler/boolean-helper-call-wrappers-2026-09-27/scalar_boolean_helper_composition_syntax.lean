import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let divide (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.div []) a) b
  let modulo (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mod []) a) b
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for flagFirst in [false, true] do
    let domains := if flagFirst then [boolean, word] else [word, boolean]
    let kinds := if flagFirst then [PublicArgument.boolean, .word] else [.word, .boolean]
    let flagIndex := if flagFirst then 1 else 0
    let wordIndex := if flagFirst then 0 else 1
    for inputDepth in ([0, 2] : List Nat) do
      let annotate (base : Lean.Expr) := (List.range inputDepth).foldl
        (fun current _ => Lean.Expr.app (.const ``Id [.zero]) current) base
      for resultDepth in ([0, 2] : List Nat) do
        let resultType := (List.range resultDepth).foldl (fun t _ => BooleanType.identity t) .boolean
        for typeBinder in [Lean.BinderInfo.default, .strictImplicit] do
          for valueBinder in [Lean.BinderInfo.implicit, .instImplicit] do
            for nondep in [false, true] do
              for metadata in [false, true] do
                for tailForm in ([0, 1, 2, 3, 4] : List Nat) do
                  let signature := domains.foldr
                    (fun input rest => Lean.Expr.forallE `parameter input rest typeBinder) resultType.expr
                  let wrap (body : Lean.Expr) := domains.foldr
                    (fun input rest => Lean.Expr.lam `parameter input rest valueBinder) body
                  let first : BooleanLocal := .junction 0 .conjunction (.var 0 0)
                    (.junction 0 .conjunction (.var 0 (flagIndex + 1))
                      (.compare .ne (.bvar (wordIndex + 1)) (literalExpr 7)))
                  let second : BooleanLocal := .predicate 0 1
                    (BooleanLocal.compare .ne (.bvar 0) (.bvar (wordIndex + 2))).expr
                  let helper (input domain output value body : Lean.Expr) :=
                    Lean.Expr.letE `helper (.forallE `typeInput input output typeBinder)
                      (.lam `valueInput domain value valueBinder) body nondep
                  let firstArgument := divide (.bvar (wordIndex + 2)) (literalExpr 3)
                  let secondArgument := modulo (.bvar (wordIndex + 2)) (literalExpr 7)
                  let left : BooleanLocal := .predicate 0 0 firstArgument
                  let right : BooleanLocal := .predicate 0 0 secondArgument
                  let fFlag : BooleanLocal := .predicate 0 1 (BooleanLocal.var 1 (flagIndex + 2)).expr
                  let fEven : BooleanLocal := .predicate 0 1
                    (BooleanLocal.compare .eq (modulo (.bvar (wordIndex + 2)) (literalExpr 2)) (literalExpr 0)).expr
                  let tail : Lean.Expr := if tailForm == 0 then (BooleanLocal.junction 0 .disjunction left right).expr
                    else if tailForm == 1 then (BooleanLocal.equality 0 false left fFlag).expr
                    else if tailForm == 2 then (BooleanLocal.junction 1 .conjunction left fEven).expr
                    else if tailForm == 3 then BooleanIdentity.pure
                      (BooleanLocal.junction 0 .disjunction left right).expr resultType
                    else (BooleanLocal.binding 0 `saved (.letE nondep) left
                      (.junction 0 .conjunction (.equality 0 true (.var 0 0)
                        (.predicate 0 1 (secondArgument.liftLooseBVars 0 1)))
                        (.var 0 (flagIndex + 3)))).expr
                  let setup (firstValue secondValue tail : Lean.Expr) :=
                    helper (annotate boolean) (annotate boolean) resultType.expr
                      (BooleanIdentity.pure firstValue resultType)
                      (helper (annotate word) (annotate word) resultType.expr
                        (BooleanIdentity.pure secondValue resultType) tail)
                  let body := setup first.expr second.expr tail
                  let body := if metadata then Lean.Expr.mdata {} body else body
                  let source := wrap body
                  let some func := extractScalarFunc `booleanHelperComposition (some "entry") signature source |
                    throwError "Boolean composition rejected: {flagFirst}, {inputDepth}, {resultDepth}, {tailForm}"
                  let some plan := extractScalarBooleanRangeWith (publicBindings kinds) 2 body |
                    throwError "direct Boolean composition rejected"
                  let direct := plan.func `booleanHelperComposition (some "entry") 2
                  unless direct == func do throwError "public/direct plans differ"
                  controls := controls + 1
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  let directModule : LeanExe.IR.Module := { funcs := #[direct] }
                  for (x, y) in inputs do
                    let rawFlag := if flagFirst then x else y
                    let rawWord := if flagFirst then y else x
                    let flag := rawFlag != 0
                    let f := fun b => b && flag && rawWord != 7
                    let g := fun n => f (n != rawWord)
                    let left := g (rawWord / 3)
                    let right := g (rawWord % 7)
                    let expected := (if tailForm == 0 || tailForm == 3 then left || right
                      else if tailForm == 1 then left == f (!flag)
                      else if tailForm == 2 then !(left && f (rawWord % 2 == 0))
                      else (left != right) && flag).toUInt64
                    let actual := module_.evalFunc 0 [x, y]
                    unless actual == expected && directModule.evalFunc 0 [x, y] == expected do
                      throwError "Boolean composition {tailForm}: {actual}, expected {expected}"
                    comparisons := comparisons + 2
                  let extra (input domain output value : Lean.Expr) := wrap
                    (helper input domain output value (body.liftLooseBVars 0 1))
                  let some control := extractScalarFunc `booleanHelperComposition (some "entry") signature
                      (extra (annotate boolean) (annotate boolean) resultType.expr
                        (BooleanIdentity.pure (booleanLiteralExpr true) resultType)) |
                    throwError "valid unused helper rejected"
                  unless control == func do throwError "unused helper changes Boolean result"
                  controls := controls + 1
                  let bad := Lean.Expr.const `unsupportedBooleanHelper []
                  let invalid := [
                    setup bad second.expr tail,
                    setup first.expr bad tail,
                    setup first.expr (literalExpr 0) tail,
                    setup first.expr (.bvar (wordIndex + 2)) tail,
                    setup first.expr second.expr bad,
                    setup first.expr second.expr (.bvar 0),
                    setup first.expr second.expr (literalExpr 0),
                    setup first.expr second.expr (.app (.bvar 0) (booleanLiteralExpr true)),
                    setup first.expr second.expr (.app (.bvar 1) (literalExpr 0)),
                    setup first.expr second.expr (.app (.bvar 7) firstArgument),
                    setup bad second.expr (booleanLiteralExpr false),
                    setup first.expr bad (booleanLiteralExpr false),
                    helper (annotate boolean) (annotate word) resultType.expr first.expr tail,
                    helper (annotate word) (annotate boolean) resultType.expr first.expr tail,
                    helper (annotate boolean) (annotate boolean) (.const ``Nat []) first.expr tail,
                    helper (annotate boolean) (annotate boolean) resultType.expr
                      (BooleanLocal.junction 0 .disjunction (.literal 0 true) (.predicate 0 99 (booleanLiteralExpr true))).expr tail]
                  for invalidBody in invalid do
                    if (extractScalarFunc `invalidBooleanHelper none signature (wrap invalidBody)).isSome then
                      throwError "invalid Boolean helper admitted"
                    rejected := rejected + 1
                  for invalidSource in [extra (annotate boolean) (annotate word) resultType.expr first.expr,
                      extra (annotate boolean) (annotate boolean) resultType.expr bad,
                      extra (annotate boolean) (annotate boolean) (.const ``Nat []) first.expr] do
                    if (extractScalarFunc `invalidUnusedBooleanHelper none signature invalidSource).isSome then
                      throwError "invalid unused Boolean helper admitted"
                    rejected := rejected + 1
  unless comparisons == 17920 && rejected == 12160 && controls == 1280 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/IR comparisons, {rejected} invalid-input checks and {controls} controls passed"
