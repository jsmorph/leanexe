import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let relation (unequal : Bool) (left right : Lean.Expr) :=
    Lean.mkAppN (.const (if unequal then ``Ne else ``Eq) [.succ .zero]) #[boolean, left, right]
  let leaf (unequal : Bool) (left right : Lean.Expr) : Lean.Elab.Term.TermElabM BooleanPropositionLeaf := do
    let original := relation unequal left right
    let some parsed := booleanPropositionLeaf? original | throwError "relation leaf rejected"
    unless LeanExe.Source.ExprEquality.same parsed.condition original do throwError "relation source changed"
    pure parsed
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
    for binder in [Lean.BinderInfo.default, .implicit] do
      let helper : BooleanLocal := .junction 0 .conjunction (.var 0 0) (.compare .ne (.bvar 2) (literalExpr 0))
      let flag : BooleanLocal := .compare .ne (.bvar 2) (literalExpr 0)
      let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word
        (.letE `f (.forallE `b boolean bt.expr binder) (.lam `b boolean helper.expr binder)
          (.letE `flag bt.expr flag.expr body false) false) .default) .default
      let equal : BooleanLocal := .compare .eq (.bvar 3) (.bvar 2)
      let call : BooleanLocal := .predicate 0 1 equal.expr
      let leftForms : List (BooleanLocal × (UInt64 → UInt64 → Bool)) :=
        [(call, fun x y => x == y && x != 0),
         (.wrapped 0 (.run bt) (.wrapped 0 (.pure bt) equal.negate), fun x y => !(x == y))]
      let rightForms : List (BooleanLocal × (UInt64 → UInt64 → Bool)) :=
        [(.var 0 0, fun x _ => x != 0), (.literal 0 false, fun _ _ => false)]
      for (left, leftNative) in leftForms do
        for (right, rightNative) in rightForms do
          for unequal in [false, true] do
            let first ← leaf unequal left.expr right.expr
            let second ← leaf (!unequal) right.expr left.expr
            let badWord ← leaf unequal (.bvar 3) right.expr
            let badMissing ← leaf unequal left.expr (.bvar 99)
            for op in [Junction.conjunction, .disjunction] do
              for n in [0, 2] do
                let less : Guard := .compare .lt (.bvar 3) (.bvar 2)
                let trees (a : BooleanPropositionLeaf) : List Guard :=
                  [.savedLeft n op a less, .savedRight n op less a, .savedBoth n op a second,
                   .localNegation n a,
                   .junction n op (.savedLeft 0 .conjunction a less) (.localNegation 0 second)]
                let expectations : List (UInt64 → UInt64 → Bool) :=
                  let rel := fun x y => if unequal then leftNative x y != rightNative x y else leftNative x y == rightNative x y
                  let other := fun x y => !(rel x y)
                  [fun x y => GuardNegation.denote n (op.denote (rel x y) (x < y)),
                   fun x y => GuardNegation.denote n (op.denote (x < y) (rel x y)),
                   fun x y => GuardNegation.denote n (op.denote (rel x y) (other x y)),
                   fun x y => GuardNegation.denote (n + 1) (rel x y),
                   fun x y => GuardNegation.denote n (op.denote ((rel x y) && x < y) (!(other x y)))]
                for (guard, expectedGuard, wrongWord, missing) in
                    (trees first).zip (expectations.zip ((trees badWord).zip (trees badMissing))) do
                  let some parsed := guardOperands? guard.condition | throwError "compound guard parser rejected"
                  unless LeanExe.Source.ExprEquality.same parsed.condition guard.condition &&
                      guardDecision? guard guard.evidence do throwError "compound syntax or evidence changed"
                  controls := controls + 1
                  for mode in ([0, 1, 2, 3, 4] : List Nat) do
                    let value (condition evidence yesDomain noDomain : Lean.Expr) : Lean.Expr :=
                      if mode == 0 then
                        Lean.mkAppN (.const ``ite [.succ .zero]) #[word, condition, evidence, .bvar 3, .bvar 2]
                      else if mode == 1 then
                        Lean.mkAppN (.const ``dite [.succ .zero]) #[word, condition, evidence,
                          .lam `proof yesDomain (.bvar 4) binder, .lam `proof noDomain (.bvar 3) binder]
                      else if mode == 2 then toWord (Lean.mkAppN (.const ``Decidable.decide []) #[condition, evidence])
                      else if mode == 3 then
                        toWord (Lean.mkAppN (.const ``ite [.succ .zero]) #[boolean, condition, evidence,
                          booleanLiteralExpr true, booleanLiteralExpr false])
                      else toWord (Lean.mkAppN (.const ``dite [.succ .zero]) #[boolean, condition, evidence,
                        .lam `proof yesDomain (booleanLiteralExpr true) binder,
                        .lam `proof noDomain (booleanLiteralExpr false) binder])
                    let make (g : Guard) (evidence : Lean.Expr) :=
                      wrap (value g.condition evidence g.condition (.app (.const ``Not []) g.condition))
                    let some func := extractScalarFunc `booleanRelation (some "entry") functionType (make guard guard.evidence) |
                      throwError "compound Boolean relation mode {mode} rejected"
                    let module_ : LeanExe.IR.Module := { funcs := #[func] }
                    for (x, y) in inputs do
                      let expected := if mode < 2 then (if expectedGuard x y then x else y) else (expectedGuard x y).toUInt64
                      let actual := module_.evalFunc 0 [x, y]
                      unless actual == expected do throwError "relation mode {mode}: {actual}, expected {expected}, input {x}, {y}"
                      comparisons := comparisons + 1
                    for bad in [make guard (.const `customDecision []), make guard (.mdata {} guard.evidence),
                        make guard (.app (.app (.const ``instDecidableEqBool []) left.expr) right.expr),
                        make wrongWord wrongWord.evidence, make missing missing.evidence] do
                      unless (extractScalarFunc `invalidRelation (some "entry") functionType bad).isNone do
                        throwError "invalid compound relation admitted"
                      rejected := rejected + 1
                    if mode == 1 || mode == 4 then
                      let negative := Lean.Expr.app (.const ``Not []) guard.condition
                      for (yes, no) in [(word, negative), (negative, negative), (guard.condition, word), (guard.condition, guard.condition)] do
                        unless (extractScalarFunc `invalidDomain (some "entry") functionType
                            (wrap (value guard.condition guard.evidence yes no))).isNone do
                          throwError "invalid relation proof domain admitted"
                        rejected := rejected + 1
            -- A bare relation stays on the existing scalar Boolean path.
            unless (guardOperands? first.condition).isNone do throwError "standalone relation routing changed"
            let standalone := wrap (toWord (Lean.mkAppN (.const ``Decidable.decide []) #[first.condition, first.evidence]))
            unless (extractScalarFunc `standalone (some "entry") functionType standalone).isSome do
              throwError "existing standalone relation rejected"
            controls := controls + 1
            for head in [.const ``Eq [], .const ``Ne [.zero], .const ``Eq [.succ (.succ .zero)]] do
              let bad := Lean.mkAppN head #[boolean, left.expr, right.expr]
              unless (booleanPropositionLeaf? bad).isNone do throwError "incorrect relation universe admitted"
              rejected := rejected + 1
            let wrongType := Lean.mkAppN (.const ``Eq [.succ .zero]) #[word, left.expr, right.expr]
            unless (booleanPropositionLeaf? wrongType).isNone do throwError "word relation parsed as Boolean"
            rejected := rejected + 1
  unless comparisons == 44800 && rejected == 21248 && controls == 672 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean proposition IR comparisons, {rejected} invalid-input tests and {controls} controls passed"
