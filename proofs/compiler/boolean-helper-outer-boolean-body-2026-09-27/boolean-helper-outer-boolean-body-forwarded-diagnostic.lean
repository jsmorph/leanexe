import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let modWord (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mod []) a) b
  let indexWord := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar 1)
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for booleanInput in [false, true] do
    for inputDepth in ([0, 2] : List Nat) do
      for resultDepth in ([0, 2] : List Nat) do
        for flagFirst in [false, true] do
          let domains := if flagFirst then [boolean, word] else [word, boolean]
          let kinds := if flagFirst then [PublicArgument.boolean, .word] else [.word, .boolean]
          let flagIndex := if flagFirst then 1 else 0
          let wordIndex := if flagFirst then 0 else 1
          let inputType := (List.range inputDepth).foldl
            (fun value _ => Lean.Expr.app (.const ``Id [.zero]) value) (if booleanInput then boolean else word)
          let resultType := (List.range resultDepth).foldl (fun value _ => BooleanType.identity value) .boolean
          for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
            for kind in ([0, 1, 2] : List Nat) do
              for mode in ([0, 1, 2] : List Nat) do
                for wrapped in [false, true] do
                  let signature := domains.foldr (fun input rest => Lean.Expr.forallE `parameter input rest binder) resultType.expr
                  let wrap (body : Lean.Expr) := domains.foldr (fun input rest => Lean.Expr.lam `parameter input rest binder) body
                  let shape : BooleanFunctionBinding := ⟨`run, `input, binder, binder, resultType, false⟩
                  let flagArgument : BooleanLocal := .junction 0 .disjunction (.var 1 flagIndex)
                    (.compare .eq (modWord (.bvar wordIndex) (literalExpr 3)) (literalExpr 0))
                  let argument := if booleanInput then flagArgument.expr else
                    add (modWord (.bvar wordIndex) (literalExpr 13)) (toWord (.bvar flagIndex))
                  let flag : BooleanLocal := if booleanInput then .var 0 0 else .var 0 (flagIndex + 1)
                  let count := if booleanInput then modWord (.bvar (wordIndex + 1)) (literalExpr 17) else .bvar 0
                  let initial := add (.bvar (wordIndex + 1)) (toWord flag.expr)
                  let advanced := add (add (.bvar 0) indexWord) (literalExpr 1)
                  let step := if kind == 0 then Step.yieldDirect advanced
                    else if kind == 1 then Step.branch .beq .word (modWord advanced (literalExpr 7)) (literalExpr 0)
                      (Step.doneDirect advanced) (Step.yieldDirect advanced)
                    else Step.branch .beq .word (modWord indexWord (literalExpr 2)) (literalExpr 0)
                      (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                  let loop := Range.call count initial `i `a binder binder step
                  let tail : BooleanLocal := .junction 0 .disjunction
                    (.compare .eq (modWord (.bvar 0) (literalExpr 7)) (literalExpr 0))
                    (.var 0 (if booleanInput then 1 else flagIndex + 2))
                  let loopBody := Lean.Expr.letE `value word loop tail.expr false
                  let scalar : BooleanLocal := .compare .eq (modWord (.bvar (wordIndex + 1)) (literalExpr 5)) (literalExpr 0)
                  let other : BooleanLocal := .var 1 (if booleanInput then 0 else flagIndex + 1)
                  let functionBody := if mode == 0 then loopBody else
                    BooleanRange.choiceExpr resultType flag.condition flag.evidence
                      (if mode == 2 then other.expr else loopBody) scalar.expr
                  let wordInput := (List.range inputDepth).foldl (fun value _ => ResultType.identity value) .word
                  let boolInput := (List.range inputDepth).foldl (fun value _ => BooleanType.identity value) .boolean
                  let forwarded : BooleanCall booleanInput := match booleanInput with
                    | false => .forwardWord wordInput resultType `argument binder
                    | true => .forwardBoolean boolInput resultType `argument binder
                  let call := if wrapped then BooleanCall.wrapped (.run resultType) forwarded else forwarded
                  let body := shape.callExpr call `selected inputType argument functionBody
                  let some func := extractScalarFunc `directContinuation (some "entry") signature (wrap body) |
                    throwError "direct continuation rejected: {booleanInput}, {inputDepth}, {resultDepth}, {flagFirst}, {kind}, {mode}"
                  let some plan := extractScalarBooleanRangeWith (publicBindings kinds) 2 body |
                    throwError "direct range continuation rejected"
                  let direct := plan.func `directContinuation (some "entry") 2
                  let some control := extractScalarBooleanRangeWith (publicBindings kinds) 2
                      (.letE `selected inputType argument functionBody false) |
                    throwError "direct binding control rejected"
                  unless mode == 2 || direct == control.func `directContinuation (some "entry") 2 do
                    throwError "local function call changed its argument binding"
                  controls := controls + 1
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  let directModule : LeanExe.IR.Module := { funcs := #[direct] }
                  let controlModule : LeanExe.IR.Module := { funcs := #[control.func `directContinuation (some "entry") 2] }
                  for (x, y) in inputs do
                    let rawFlag := if flagFirst then x else y
                    let rawWord := if flagFirst then y else x
                    let publicFlag := rawFlag != 0
                    let selected := if booleanInput then !publicFlag || rawWord % 3 == 0 else publicFlag
                    let stop := if booleanInput then rawWord % 17 else rawWord % 13 + publicFlag.toUInt64
                    let initial := rawWord + selected.toUInt64
                    let value : UInt64 := Id.run <| forIn (m := Id) [:stop.toNat] initial fun i a =>
                      let advanced := a + i.toUInt64 + 1
                      if kind == 0 then .yield advanced
                      else if kind == 1 then if advanced % 7 == 0 then .done advanced else .yield advanced
                      else .yield (if i % 2 == 0 then a else advanced)
                    let expected := (if mode == 0 then value % 7 == 0 || selected
                      else if selected then (if mode == 2 then !selected else value % 7 == 0 || selected)
                      else rawWord % 5 == 0).toUInt64
                    for actual in [module_.evalFunc 0 [x, y], directModule.evalFunc 0 [x, y], controlModule.evalFunc 0 [x, y]] do
                      unless actual == expected && (actual == 0 || actual == 1) do
                        throwError "direct continuation result {actual}, expected {expected}"
                      comparisons := comparisons + 1
                  let bad := Lean.Expr.const `unsupportedDirectContinuation []
                  let raw (domain result : Lean.Expr) (value tail : Lean.Expr) :=
                    Lean.Expr.letE `run (.forallE `input inputType result binder)
                      (.lam `selected domain value binder) tail false
                  let lifted := LeanExe.Source.ExprProofBinder.lift 0 argument
                  let forward (input domain output value callback : Lean.Expr) (instanceName : Lean.Name) :=
                    Lean.Expr.app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
                      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
                        (.const instanceName [.zero]))) input) output) value)
                      (.lam `argument domain callback binder)
                  let callback : Lean.Expr := .app (.bvar 1) (.bvar 0)
                  let wrong := if booleanInput then word else boolean
                  let invalid := [
                    raw inputType resultType.expr functionBody (forward inputType wrong resultType.expr lifted callback ``Id.instMonad),
                    raw inputType resultType.expr functionBody (forward wrong wrong resultType.expr lifted callback ``Id.instMonad),
                    raw inputType resultType.expr functionBody (forward inputType inputType word lifted callback ``Id.instMonad),
                    raw inputType resultType.expr functionBody (forward inputType inputType resultType.expr lifted callback `customMonad),
                    raw inputType resultType.expr functionBody (forward inputType inputType resultType.expr lifted (.app (.bvar 0) (.bvar 0)) ``Id.instMonad),
                    raw inputType resultType.expr functionBody (forward inputType inputType resultType.expr lifted (.app (.bvar 1) (.bvar 1)) ``Id.instMonad),
                    raw inputType resultType.expr functionBody (forward inputType inputType resultType.expr lifted (.bvar 0) ``Id.instMonad),
                    raw inputType resultType.expr functionBody (forward inputType inputType resultType.expr (.bvar 0) callback ``Id.instMonad),
                    raw inputType resultType.expr functionBody (forward inputType inputType resultType.expr bad callback ``Id.instMonad),
                    raw inputType resultType.expr functionBody (forward inputType inputType (.app (.const ``Id [.succ .zero]) boolean) lifted callback ``Id.instMonad),
                    shape.callExpr call `selected inputType bad functionBody,
                    shape.callExpr call `selected inputType argument bad,
                    shape.callExpr call `selected inputType (if booleanInput then .bvar wordIndex else .bvar flagIndex) functionBody,
                    raw inputType word functionBody (.app (.bvar 0) lifted),
                    raw (if booleanInput then word else boolean) resultType.expr functionBody (.app (.bvar 0) lifted),
                    raw inputType resultType.expr functionBody (.app (.bvar 0) (.bvar 0)),
                    raw inputType resultType.expr functionBody (.app (.bvar 1) lifted),
                    raw inputType (.app (.const ``Id [.succ .zero]) boolean) functionBody (.app (.bvar 0) lifted),
                    shape.callExpr call `selected (.const `customInput []) argument functionBody,
                    shape.callExpr call `selected inputType argument (.letE `value word bad tail.expr false)]
                  for (value, invalidIndex) in invalid.zipIdx do
                    if (extractScalarFunc `invalidDirectContinuation (some "entry") signature (wrap value)).isSome then
                      throwError "invalid direct continuation accepted at {invalidIndex}: {booleanInput}, {inputDepth}, {kind}, {mode}"
                    rejected := rejected + 1
  unless comparisons == 48384 && rejected == 23040 && controls == 1152 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/forwarded-continuation syntax comparisons, {rejected} invalid-input tests and {controls} binding controls passed"
