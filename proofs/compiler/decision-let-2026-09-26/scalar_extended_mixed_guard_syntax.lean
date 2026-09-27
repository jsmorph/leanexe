import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let truth (value : Lean.Expr) := Lean.Expr.app (.app (.app (.const ``Eq [.succ .zero]) boolean) value) (booleanLiteralExpr true)
  let makeLeaf (value : Lean.Expr) (bn pn : Nat) : Lean.Elab.Term.TermElabM SavedBooleanGuard := do
    let some guard := savedBooleanGuard? (GuardNegation.condition pn (truth (BooleanGuardNegation.expr bn value))) |
      throwError "extended Boolean leaf rejected"
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
    for flag in [false, true] do
      let fBody : BooleanLocal := .junction 0 .disjunction (.var 1 0) (.compare .eq (.bvar 2) (.bvar 1))
      let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word
        (.letE `f (.forallE `b boolean bt.expr .default) (.lam `b boolean fBody.expr .default)
          (.letE `flag bt.expr (booleanLiteralExpr flag) body false) false) .default) .default
      let call : BooleanLocal := .predicate 0 1 (.bvar 0)
      let flagExpr : BooleanLocal := .var 0 0
      let afterBind : BooleanLocal := .predicate 0 2 (BooleanGuardNegation.expr 1 (.bvar 0))
      let afterWord : BooleanLocal := .predicate 0 2 ((BooleanLocal.compare .eq (.bvar 0) (.bvar 4)).expr)
      let sum := Lean.Expr.app (.app (.const ``UInt64.add []) (.bvar 3)) (.bvar 2)
      let proposition : PropositionGuard := ⟨.canonical (.compare .lt (.bvar 3) (.bvar 2)), rfl⟩
      let forms : List (BooleanLocal × (UInt64 → UInt64 → Bool)) :=
        [(.junction 0 .conjunction call flagExpr, fun x y => (!flag || x == y) && flag),
         (.choice 0 false flagExpr (.literal 0 true) call call.negate,
           fun x y => if flag then !flag || x == y else !(!flag || x == y)),
         (.proposition 0 proposition call call.negate,
           fun x y => if x < y then !flag || x == y else !(!flag || x == y)),
         (.binding 0 `saved (.letE false) call afterBind bt, fun x y => (!flag || x == y) || x == y),
         (.wordBinding 0 `saved (.letE false) sum afterWord, fun x y => !(x + y == x) || x == y),
         (.binding 0 `saved (.monadic .default bt) (.wrapped 0 (.pure bt) call)
           (.wrapped 0 (.pure bt) afterBind) bt, fun x y => (!flag || x == y) || x == y),
         (.wrapped 0 (.metadata {}) (.wrapped 0 (.run bt) (.wrapped 0 (.pure bt) call)),
           fun x y => !flag || x == y),
         (.relationDecision 0 false call flagExpr, fun x y => (!flag || x == y) == flag)]
      for (expression, expectedLeaf) in forms do
        for op in [Junction.conjunction, .disjunction] do
          for (bn, pn, n) in [(0, 0, 0), (1, 0, 1), (0, 1, 2), (2, 2, 3)] do
            let first ← makeLeaf expression.expr bn pn
            let second ← makeLeaf (.bvar 0) (bn + 1) (pn + 1)
            let less : Guard := .compare .lt (.bvar 3) (.bvar 2)
            let trees (a : SavedBooleanGuard) : List Guard :=
              [.savedLeft n op a less, .savedRight n op less a, .savedBoth n op a second]
            let badWord ← makeLeaf (.bvar 3) bn pn
            let missing ← makeLeaf (.bvar 9) bn pn
            let badArgument ← makeLeaf (.app (.bvar 1) (literalExpr 0)) bn pn
            let unused ← makeLeaf (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) (booleanLiteralExpr true) false) bn pn
            let valid := trees first
            let invalidTrees := (trees badWord).zip ((trees missing).zip ((trees badArgument).zip (trees unused)))
            for (guard, badWord, missing, badArgument, unused) in valid.zip invalidTrees do
              for mode in ([0, 1, 2] : List Nat) do
                let value (condition evidence trueDomain falseDomain : Lean.Expr) : Lean.Expr :=
                  if mode == 0 then
                    Lean.mkAppN (.const ``ite [.succ .zero]) #[word, condition, evidence, .bvar 3, .bvar 2]
                  else if mode == 1 then
                    Lean.mkAppN (.const ``dite [.succ .zero]) #[word, condition, evidence,
                      .lam `proof trueDomain (.bvar 4) .default, .lam `proof falseDomain (.bvar 3) .default]
                  else toWord (Lean.mkAppN (.const ``Decidable.decide []) #[condition, evidence])
                let make (g : Guard) (evidence : Lean.Expr) :=
                  wrap (value g.condition evidence g.condition (.app (.const ``Not []) g.condition))
                let some func := extractScalarFunc `extendedMixed (some "entry") functionType (make guard guard.evidence) |
                  throwError "extended mixed guard mode {mode} rejected"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (x, y) in inputs do
                  let native (operand : Lean.Expr) : UInt64 :=
                    if LeanExe.Source.ExprEquality.same operand first.operand then
                      (GuardNegation.denote bn (expectedLeaf x y)).toUInt64
                    else if LeanExe.Source.ExprEquality.same operand second.operand then
                      (GuardNegation.denote (bn + 1) flag).toUInt64
                    else if LeanExe.Source.ExprEquality.same operand (.bvar 3) then x else y
                  let result := guard.denote native
                  let expected := if mode < 2 then (if result then x else y) else result.toUInt64
                  let actual := module_.evalFunc 0 [x, y]
                  unless actual == expected do throwError "extended guard mode {mode}: {actual}, expected {expected}"
                  comparisons := comparisons + 1
                for bad in [make guard (.const `customDecision []), make guard (.mdata {} guard.evidence),
                    make badWord badWord.evidence, make missing missing.evidence,
                    make badArgument badArgument.evidence, make unused unused.evidence] do
                  unless (extractScalarFunc `invalidExtended (some "entry") functionType bad).isNone do
                    throwError "invalid extended mixed guard admitted"
                  rejected := rejected + 1
                if mode == 1 then
                  let negative := Lean.Expr.app (.const ``Not []) guard.condition
                  for (yes, no) in [(word, negative), (negative, negative), (guard.condition, word), (guard.condition, guard.condition)] do
                    unless (extractScalarFunc `invalidDomain (some "entry") functionType
                        (wrap (value guard.condition guard.evidence yes no))).isNone do
                      throwError "invalid extended proof domain admitted"
                    rejected := rejected + 1
              unless (guardOperands? first.condition).isNone &&
                  (savedBooleanGuard? (BooleanGuard.literal 0 true).condition).isNone do
                throwError "extended leaf changed the existing Boolean parser"
              controls := controls + 1
  unless comparisons == 32256 && rejected == 16896 && controls == 768 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/extended mixed-guard IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"
