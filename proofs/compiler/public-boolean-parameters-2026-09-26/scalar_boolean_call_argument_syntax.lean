import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word body .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let sub (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.sub []) a) b
  let indexWord (i : Nat) : Lean.Expr := .app (.const ``UInt64.ofNat []) (.bvar i)
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let rangeInputs : List (UInt64 × UInt64) :=
    ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
      ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for scope in ([0, 1, 2] : List Nat) do -- Scalar, step-local, and before the loop.
    for kind in (if scope == 1 then [0, 1, 2] else [0, 1] : List Nat) do -- Word, Bool, step result.
      for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
        for inputDepth in [1, 3] do
          for resultDepth in [0, 2] do
            for nondep in [false, true] do
              for flag in [false, true] do
                for used in [false, true] do
                  for form in ([0, 1, 2] : List Nat) do
                    let input := (List.range inputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
                    let wt := (List.range resultDepth).foldl (fun t _ => ResultType.identity t) .word
                    let bt := (List.range resultDepth).foldl (fun t _ => BooleanType.identity t) .boolean
                    let result := if kind == 0 then wt.expr else if kind == 1 then bt.expr else Step.resultType wt
                    let left : Lean.Expr := .bvar (if scope == 0 then 3 else 2)
                    let right : Lean.Expr := if scope == 1 then indexWord 3 else .bvar (if scope == 0 then 2 else 3)
                    let guard : BooleanLocalGuard := { value := .var 0 0, expanded := rfl }
                    let boolBody : BooleanLocal := .junction 0 .conjunction (.var 0 0) (.compare .ne left right)
                    let value := if kind == 0 then guard.branch word (add left right) (sub left right)
                      else if kind == 1 then boolBody.expr
                      else guard.branch (Step.resultType .word)
                        (Step.doneDirect (add left (literalExpr 7)))
                        (Step.yieldDirect (add (add left right) (literalExpr 1)))
                    let callAt (i : Nat) (argument : Lean.Expr) := Lean.Expr.app (.bvar i) argument
                    let predicateIndex := if scope == 2 then 3 else 1
                    let predicateCall (argument : Lean.Expr) := callAt predicateIndex argument
                    let first := predicateCall (booleanLiteralExpr flag)
                    let nested := predicateCall first
                    let argument := if form == 0 then first else if form == 1 then nested else
                      let choose : BooleanLocalGuard := { value := .predicate 0 predicateIndex (booleanLiteralExpr flag), expanded := rfl }
                      choose.branch boolean (predicateCall (booleanLiteralExpr false)) (predicateCall (booleanLiteralExpr true))
                    let call := callAt (if scope == 2 then 2 else 0) argument
                    let callWord := if kind == 1 then toWord call else call
                    let unused := if scope == 2 then add (.bvar 0) (indexWord 1) else add left right
                    let body := if kind == 2 then (if used then call else Step.yieldDirect unused)
                      else if scope == 0 then (if used then callWord else unused)
                      else Step.yieldDirect (if used then callWord else unused)
                    let helper (input result domain value body : Lean.Expr) :=
                      Lean.Expr.letE `helper (.forallE `typeInput input result binder)
                        (.lam `valueInput domain value binder)
                        (if scope == 2 then Range.call (.bvar 3) (.bvar 2) `i `a .default .default body else body) nondep
                    let predicateBody : BooleanLocal := .junction 0 .disjunction (.var 1 0)
                      (.compare .eq (.bvar (if scope == 0 then 2 else 1)) (literalExpr 0))
                    let predicate (expression : Lean.Expr) := Lean.Expr.letE `predicate
                      (.forallE `flag boolean boolean binder) (.lam `flag boolean predicateBody.expr binder) expression nondep
                    let source (expression : Lean.Expr) := wrap
                      (if scope == 1 then Range.call (.bvar 1) (.bvar 0) `i `a .default .default (predicate expression)
                       else predicate expression)
                    let some func := extractScalarFunc `booleanCallArgumentSyntax (some "entry") functionType
                        (source (helper input.expr result input.expr value body)) |
                      throwError "Boolean-call argument rejected: scope={scope}, kind={kind}, input={inputDepth}, result={resultDepth}, used={used}"
                    let module_ : LeanExe.IR.Module := { funcs := #[func] }
                    for (x, y) in (if scope == 0 then inputs else rangeInputs) do
                      let argumentFlag (captured : UInt64) :=
                        let f := fun b : Bool => !b || captured == 0
                        if form == 0 then f flag else if form == 1 then f (f flag)
                        else if f flag then f false else f true
                      let resultWord (a b : UInt64) :=
                        let selected := argumentFlag a
                        if kind == 0 then (if selected then a + b else a - b)
                        else (selected && a != b).toUInt64
                      let expected := if scope == 0 then (if used then resultWord x y else x + y)
                        else forIn (m := Id) [:x.toNat] y fun i a =>
                          if !used then .yield (a + UInt64.ofNat i)
                          else if kind == 2 then
                            if argumentFlag a then .done (a + 7) else .yield (a + UInt64.ofNat i + 1)
                          else .yield (if scope == 1 then resultWord a (UInt64.ofNat i) else resultWord y x)
                      let actual := module_.evalFunc 0 [x, y]
                      unless actual == expected do throwError "Boolean-call argument scope={scope}, kind={kind}: {actual}, expected {expected}"
                      comparisons := comparisons + 1
                    let wrongCall := callAt (if scope == 2 then 2 else 0) (literalExpr 7)
                    let wrongBody := if kind == 2 then wrongCall else
                      let wordCall := if kind == 1 then toWord wrongCall else wrongCall
                      if scope == 0 then wordCall else Step.yieldDirect wordCall
                    let argumentBody (arg : Lean.Expr) :=
                      let application := callAt (if scope == 2 then 2 else 0) arg
                      if kind == 2 then application else
                        let result := if kind == 1 then toWord application else application
                        if scope == 0 then result else Step.yieldDirect result
                    let validChoice := booleanChoiceExpr false (booleanLiteralExpr true)
                      (booleanLiteralExpr true) first nested
                    unless (extractScalarFunc `validChoiceArgument (some "entry") functionType
                        (source (helper input.expr result input.expr value (argumentBody validChoice)))).isSome do
                      throwError "valid constant-choice argument rejected"
                    controls := controls + 1
                    let badArguments : List Lean.Expr :=
                      [predicateCall (literalExpr 7), .bvar predicateIndex,
                       callAt 99 (booleanLiteralExpr true), predicateCall (.const `unsupportedArgument []),
                       predicateCall (.app (.const ``UInt64.ofNat []) (.lit (.natVal 0))),
                       booleanChoiceExpr false (booleanLiteralExpr true) (booleanLiteralExpr true)
                         first (.const `unsupportedUnusedBranch [])]
                    let invalid : List Lean.Expr :=
                      [helper input.expr result boolean value body,
                       helper boolean result input.expr value body,
                       helper input.expr result (BooleanType.identity input).expr value body,
                       helper (.app (.const ``Id [.zero]) (.const ``Nat [])) result
                         (.app (.const ``Id [.zero]) (.const ``Nat [])) value body,
                       helper (.app (.const ``Id [.succ .zero]) boolean) result
                         (.app (.const ``Id [.succ .zero]) boolean) value body,
                       helper (.app (.const `CustomId [.zero]) boolean) result
                         (.app (.const `CustomId [.zero]) boolean) value body,
                       helper input.expr (.const ``Nat []) input.expr value body,
                       helper input.expr result input.expr (.const `unsupportedHelper []) body,
                       helper input.expr result input.expr (.bvar 99) body,
                       helper input.expr result input.expr (.app (.bvar 0) (.bvar 1)) body,
                       helper input.expr result input.expr (if kind == 0 then booleanLiteralExpr true else literalExpr 7) body,
                       helper input.expr result input.expr value wrongBody] ++
                      badArguments.map (fun argument => helper input.expr result input.expr value (argumentBody argument))
                    for invalidSource in invalid do
                      if (extractScalarFunc `invalidBooleanCallArgument (some "entry") functionType (source invalidSource)).isSome then
                        throwError "invalid Boolean-call argument admitted: scope={scope}, kind={kind}"
                      rejected := rejected + 1
  unless comparisons == 56832 && rejected == 48384 && controls == 2688 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean-call-argument syntax comparisons and {rejected} invalid-input tests and {controls} admission controls passed"
