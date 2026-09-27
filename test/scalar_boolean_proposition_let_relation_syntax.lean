import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
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
    let bt := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
    let wt := (List.range depth).foldl (fun t _ => ResultType.identity t) .word
    for flag in [false, true] do
      let fBody : BooleanLocal := .junction 0 .disjunction (.var 0 0) (.compare .eq (.bvar 2) (.bvar 1))
      let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word
        (.letE `f (.forallE `b boolean bt.expr .default) (.lam `b boolean fBody.expr .default)
          (.letE `flag bt.expr (booleanLiteralExpr flag) body false) false) .default) .default
      for nondep in [false, true] do
        let boolBinding : GuardLet := ⟨`saved, .boolean bt, .app (.bvar 1) (.bvar 0), nondep⟩
        let sum := Lean.Expr.app (.app (.const ``UInt64.add []) (.bvar 3)) (.bvar 2)
        let wordBinding : GuardLet := ⟨`saved, .word wt, sum, nondep⟩
        let innerWord : GuardLet := ⟨`saved, .word wt,
          .app (.app (.const ``UInt64.add []) (.bvar 4)) (toWord (.bvar 0)), nondep⟩
        let innerBool : GuardLet := ⟨`saved, .boolean bt, BooleanGuardNegation.expr 1 (.bvar 0), nondep⟩
        for unequal in [false, true] do
          let saved ← leaf unequal (.bvar 0) (.bvar 1)
          let inverse ← leaf unequal (BooleanGuardNegation.expr 1 (.bvar 0)) (.bvar 1)
          let wordFlag : BooleanLocal := .compare .eq (.bvar 0) (.bvar 4)
          let wordRelation ← leaf unequal wordFlag.expr (.bvar 1)
          let wordCall ← leaf unequal (.app (.bvar 2) wordFlag.expr) (.bvar 1)
          let nestedRelation ← leaf unequal ((BooleanLocal.compare .ne (.bvar 0) (.bvar 4)).expr) (.bvar 1)
          let unusedWord ← leaf unequal (.bvar 1) (booleanLiteralExpr false)
          let unusedBoolean ← leaf unequal (booleanLiteralExpr false) (booleanLiteralExpr false)
          let rel := fun a b : Bool => if unequal then a != b else a == b
          let forms : List (Guard × (UInt64 → UInt64 → Bool)) :=
            [(.letSaved 0 boolBinding saved, fun x y => rel (flag || x == y) flag),
             (.letSaved 0 boolBinding inverse, fun x y => rel (!(flag || x == y)) flag),
             (.letSaved 0 wordBinding wordRelation, fun x y => rel (x + y == x) flag),
             (.letSaved 0 wordBinding wordCall, fun x y => rel ((x + y == x) || x == y) flag),
             (.letGuard 0 boolBinding (.letSaved 0 innerWord nestedRelation),
               fun x y => rel (x + (flag || x == y).toUInt64 != y) (flag || x == y)),
             (.letSaved 0 wordBinding unusedWord, fun _ _ => rel flag false),
             (.letSaved 0 boolBinding unusedBoolean, fun _ _ => rel false false),
             (.letGuard 0 boolBinding (.letSaved 0 innerBool saved),
               fun x y => rel (!(flag || x == y)) (flag || x == y))]
          for (base, expectedBase) in forms do
            for n in [0, 1, 2] do
              let negated := (List.range n).foldl (fun guard _ => guard.negate) base
              let less : Guard := .compare .lt (.bvar 3) (.bvar 2)
              let guards := [negated, .junction 0 .conjunction negated less, .junction 1 .disjunction less negated]
              for (guard, shape) in guards.zipIdx do
                let badBoolean : Guard := .letGuard n { boolBinding with value := .const `unsupportedBoolean [] }
                  (.literal (.proposition 0 true))
                let badWord : Guard := .letGuard n { wordBinding with value := .const `unsupportedWord [] }
                  (.literal (.proposition 0 false))
                let wrongKind : Guard := .letSaved n { boolBinding with value := .bvar 3 } saved
                let missing : Guard := .letSaved n { boolBinding with value := .bvar 9 } saved
                let wrongBody : Guard := .letGuard n wordBinding (.letSaved 0 innerBool saved)
                for mode in ([0, 1, 2, 3, 4] : List Nat) do
                  let value (condition evidence trueDomain falseDomain : Lean.Expr) : Lean.Expr :=
                    if mode == 0 then
                      Lean.mkAppN (.const ``ite [.succ .zero]) #[word, condition, evidence, .bvar 3, .bvar 2]
                    else if mode == 1 then
                      Lean.mkAppN (.const ``dite [.succ .zero]) #[word, condition, evidence,
                        .lam `proof trueDomain (.bvar 4) .default, .lam `proof falseDomain (.bvar 3) .default]
                    else if mode == 2 then toWord (Lean.mkAppN (.const ``Decidable.decide []) #[condition, evidence])
                    else if mode == 3 then
                      toWord (Lean.mkAppN (.const ``ite [.succ .zero]) #[boolean, condition, evidence,
                        booleanLiteralExpr true, booleanLiteralExpr false])
                    else toWord (Lean.mkAppN (.const ``dite [.succ .zero]) #[boolean, condition, evidence,
                      .lam `proof trueDomain (booleanLiteralExpr true) .default,
                      .lam `proof falseDomain (booleanLiteralExpr false) .default])
                  let make (g : Guard) (evidence : Lean.Expr) :=
                    wrap (value g.condition evidence g.condition (.app (.const ``Not []) g.condition))
                  let some func := extractScalarFunc `propositionLet (some "entry") functionType (make guard guard.evidence) |
                    throwError "proposition let mode {mode}, shape {shape} rejected"
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (x, y) in inputs do
                    let baseValue := GuardNegation.denote n (expectedBase x y)
                    let result := if shape == 0 then baseValue else if shape == 1 then baseValue && x < y else !(x < y || baseValue)
                    let expected := if mode < 2 then (if result then x else y) else result.toUInt64
                    let actual := module_.evalFunc 0 [x, y]
                    unless actual == expected do throwError "proposition let mode {mode}: {actual}, expected {expected}"
                    comparisons := comparisons + 1
                  for (bad, invalidCase) in [make guard (.const `customDecision []), make guard (.mdata {} guard.evidence),
                      make guard (.app (.app (.const ``instDecidableEqBool []) (.bvar 9)) (booleanLiteralExpr true)), make badBoolean badBoolean.evidence,
                      make badWord badWord.evidence, make wrongKind wrongKind.evidence,
                      make missing missing.evidence, make wrongBody wrongBody.evidence].zipIdx do
                    unless (extractScalarFunc `invalidLet (some "entry") functionType bad).isNone do
                      throwError "invalid proposition let case {invalidCase}, mode {mode}, shape {shape} admitted"
                    rejected := rejected + 1
                  if mode == 1 || mode == 4 then
                    let negative := Lean.Expr.app (.const ``Not []) guard.condition
                    for (yes, no) in [(word, negative), (negative, negative), (guard.condition, word), (guard.condition, guard.condition)] do
                      unless (extractScalarFunc `invalidDomain (some "entry") functionType
                          (wrap (value guard.condition guard.evidence yes no))).isNone do
                        throwError "invalid proposition-let proof domain admitted"
                      rejected := rejected + 1
                let some parsed := guardOperands? guard.condition | throwError "proposition let parser rejected its own condition"
                unless (LeanExe.Source.ExprEquality.same parsed.condition guard.condition) &&
                    (guardDecision? guard guard.evidence) do
                  throwError "proposition let changed its condition or evidence"
                controls := controls + 1
        for invalidType in [.const ``Nat [], .const ``String [], .forallE `n word word .default] do
          let condition := Lean.Expr.letE `saved invalidType boolBinding.value (booleanRelationCondition false (.bvar 0) (.bvar 1)) nondep
          unless (guardOperands? condition).isNone do throwError "invalid proposition-let type admitted"
          rejected := rejected + 1
  unless comparisons == 80640 && rejected == 55320 && controls == 1152 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/proposition-let relation IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"
