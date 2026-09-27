import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let locals : List ScalarStepBinding := [.scalar (.word (.local 1)), .scalar (.word (.local 0))]
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word body .default) .default
  let leaf (unequal : Bool) (left right : Lean.Expr) : Lean.Elab.Term.TermElabM BooleanPropositionLeaf := do
    let some guard := booleanPropositionLeaf? (booleanRelationCondition unequal left right) |
      throwError "Boolean relation leaf rejected"
    pure guard
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
    let result := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
    for booleanInput in [false, true] do
      let input := if booleanInput then boolean else word
      let body : BooleanLocal := if booleanInput then
        .junction 0 .disjunction (.var 0 0) (.compare .eq (.bvar 2) (.bvar 1))
        else .compare .eq (.bvar 0) (.bvar 1)
      for nondep in [false, true] do
        for info in [Lean.BinderInfo.default, .implicit] do
          let innerShape : BooleanFunctionBinding := ⟨`g, `arg, info, info, result, nondep⟩
          let innerBody := body.expr.liftLooseBVars 0 1
          let first := if booleanInput then booleanLiteralExpr false else literalExpr 0
          let second := if booleanInput then booleanLiteralExpr true else literalExpr 1
          let innerTail := Lean.Expr.app (.app (.const ``Bool.or []) (.app (.bvar 0) first)) (.app (.bvar 0) second)
          let nestedBody := booleanHelperExpr booleanInput innerShape `arg innerBody innerTail
          let binding : GuardLet := ⟨`f, .predicate booleanInput `arg info result,
            .lam `arg input nestedBody info, nondep⟩
          let argumentX := if booleanInput then (BooleanLocal.compare .eq (.bvar 2) (literalExpr 0)).expr else .bvar 2
          let argumentY := if booleanInput then (BooleanLocal.compare .eq (.bvar 1) (literalExpr 0)).expr else literalExpr 0
          let callX := Lean.Expr.app (.bvar 0) argumentX
          let callY := Lean.Expr.app (.bvar 0) argumentY
          let truth ← leaf false callX (booleanLiteralExpr true)
          let equal ← leaf false callX callY
          let unequal ← leaf true callX callY
          let sum := Lean.Expr.app (.app (.const ``UInt64.add []) (.bvar 2)) (.bvar 1)
          let savedWord : GuardLet := ⟨`saved, .word .word, sum, nondep⟩
          let nestedArg := if booleanInput then (BooleanLocal.compare .eq (.bvar 0) (literalExpr 0)).expr else .bvar 0
          let nestedWord ← leaf false (.app (.bvar 1) nestedArg) (booleanLiteralExpr true)
          let savedFlag : GuardLet := ⟨`saved, .boolean result, callX, nondep⟩
          let nestedFlag ← leaf false (.bvar 0) (callY.liftLooseBVars 0 1)
          let left := fun x y : UInt64 => if booleanInput then x == 0 || x == y else x == y
          let right := fun x y : UInt64 => if booleanInput then y == 0 || x == y else 0 == y
          let forms : List (Guard × (UInt64 → UInt64 → Bool)) := [
            (.letSaved 0 binding truth, left),
            (.letSaved 0 binding equal, fun x y => left x y == right x y),
            (.letSaved 0 binding unequal, fun x y => left x y != right x y),
            (.letGuard 0 binding (.literal (.proposition 0 true)), fun _ _ => true),
            (.letGuard 0 binding (.letSaved 0 savedWord nestedWord),
              fun x y => if booleanInput then x + y == 0 || x == y else x + y == y),
            (.letGuard 0 binding (.letSaved 0 savedFlag nestedFlag), fun x y => left x y == right x y)]
          for (base, expectedBase) in forms do
            for n in [0, 1] do
              let negated := (List.range n).foldl (fun guard _ => guard.negate) base
              let less : Guard := .compare .lt (.bvar 1) (.bvar 0)
              for (guard, shape) in [negated, .junction 0 .conjunction negated less, .junction 1 .disjunction less negated].zipIdx do
                let some parsed := guardOperands? guard.condition | throwError "predicate let condition rejected"
                unless LeanExe.Source.ExprEquality.same parsed.condition guard.condition && guardDecision? guard guard.evidence do
                  throwError "predicate let condition or evidence changed"
                controls := controls + 1
                let malformedBodies := [.const `unsupportedBoolean [], literalExpr 0, .bvar 9,
                  (if booleanInput then (BooleanLocal.compare .eq (.bvar 0) (.bvar 1)).expr else (BooleanLocal.var 0 0).expr)]
                let invalidBindings := malformedBodies.map (fun bad => { binding with value := .lam `arg input bad info }) ++
                  [{ binding with value := .lam `arg (.const ``Nat []) body.expr info },
                   { binding with value := .const `unsupportedFunction [] },
                   { binding with value := .bvar 9 }]
                for mode in ([0, 1, 2, 3, 4, 5, 6] : List Nat) do
                  let expression (condition evidence td fd : Lean.Expr) : Lean.Expr :=
                    if mode == 0 then Lean.mkAppN (.const ``ite [.succ .zero]) #[word, condition, evidence, .bvar 1, .bvar 0]
                    else if mode == 1 then Lean.mkAppN (.const ``dite [.succ .zero]) #[word, condition, evidence,
                      .lam `proof td (.bvar 2) info, .lam `proof fd (.bvar 1) info]
                    else if mode == 2 then toWord (Lean.mkAppN (.const ``Decidable.decide []) #[condition, evidence])
                    else if mode == 3 then toWord (Lean.mkAppN (.const ``ite [.succ .zero]) #[result.expr, condition, evidence,
                      booleanLiteralExpr true, booleanLiteralExpr false])
                    else if mode == 4 then toWord (Lean.mkAppN (.const ``dite [.succ .zero]) #[result.expr, condition, evidence,
                      .lam `proof td (booleanLiteralExpr true) info, .lam `proof fd (booleanLiteralExpr false) info])
                    else if mode == 5 then Lean.mkAppN (.const ``ite [.succ .zero]) #[Step.resultType .word, condition, evidence,
                      Step.doneDirect (.bvar 1), Step.yieldDirect (.bvar 0)]
                    else Lean.mkAppN (.const ``dite [.succ .zero]) #[Step.resultType .word, condition, evidence,
                      .lam `proof td (Step.doneDirect (.bvar 2)) info, .lam `proof fd (Step.yieldDirect (.bvar 1)) info]
                  let make (g : Guard) (evidence : Lean.Expr) :=
                    expression g.condition evidence g.condition (.app (.const ``Not []) g.condition)
                  let compile (value : Lean.Expr) : Option LeanExe.IR.Module := do
                    if mode < 5 then
                      let func ← extractScalarFunc `predicateLet (some "entry") functionType (wrap value)
                      pure { funcs := #[func] }
                    else
                      let code ← extractScalarStepWith locals value
                      pure { funcs := #[
                        { sourceName := `stepValue, exportName := none, params := 2, locals := 0, body := .skip, results := [code.value] },
                        { sourceName := `stepDone, exportName := none, params := 2, locals := 0, body := .skip, results := [code.done] }] }
                  let some module_ := compile (make guard guard.evidence) |
                    throwError "predicate let rejected: Boolean input {booleanInput}, mode {mode}, shape {shape}, depth {depth}"
                  for (x, y) in inputs do
                    let baseValue := GuardNegation.denote n (expectedBase x y)
                    let flag := if shape == 0 then baseValue else if shape == 1 then baseValue && x < y else !(x < y || baseValue)
                    let expected := if mode < 2 || mode > 4 then (if flag then x else y) else flag.toUInt64
                    let actual := module_.evalFunc 0 [x, y]
                    unless actual == expected do throwError "predicate let mode {mode}: {actual}, expected {expected}"
                    comparisons := comparisons + 1
                    if mode > 4 then
                      unless module_.evalFunc 1 [x, y] == flag.toUInt64 do throwError "predicate let exit decision mismatch"
                      comparisons := comparisons + 1
                  for badBinding in invalidBindings do
                    for badGuard in ([.letSaved n badBinding truth, .letGuard n badBinding (.literal (.proposition 0 true))] : List Guard) do
                      unless (compile (make badGuard badGuard.evidence)).isNone do
                        throwError "invalid predicate body admitted, including unused helper: mode {mode}"
                      rejected := rejected + 1
                  for bad in [make guard (.const `customDecision []), make guard (.mdata {} guard.evidence),
                      make guard (.app (.const ``Not []) guard.evidence)] do
                    unless (compile bad).isNone do throwError "invalid predicate evidence admitted"
                    rejected := rejected + 1
                  if mode == 1 || mode == 4 || mode == 6 then
                    let negative := Lean.Expr.app (.const ``Not []) guard.condition
                    for (yes, no) in [(word, negative), (negative, negative), (guard.condition, word), (guard.condition, guard.condition)] do
                      unless (compile (expression guard.condition guard.evidence yes no)).isNone do
                        throwError "invalid predicate-let proof domain admitted"
                      rejected := rejected + 1
          for invalidType in [.const ``Nat [], .const ``String [],
              .forallE `arg word word info, .forallE `arg (.const ``Nat []) boolean info,
              .forallE `arg boolean (.const ``String []) info,
              .forallE `arg (.const ``Bool [.zero]) boolean info,
              .forallE `arg word (.bvar 0) info] do
            let condition := Lean.Expr.letE `f invalidType binding.value (booleanRelationCondition false callX (booleanLiteralExpr true)) nondep
            unless (guardOperands? condition).isNone do throwError "invalid predicate function type admitted"
            rejected := rejected + 1
  unless comparisons == 72576 && rejected == 75568 && controls == 576 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/nested predicate-let IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"
