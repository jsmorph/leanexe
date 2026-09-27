import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let makeLeaf (index bn pn : Nat) (argument : Option Lean.Expr) : Lean.Elab.Term.TermElabM SavedBooleanGuard := do
    let base := match argument with | none => Lean.Expr.bvar index | some arg => .app (.bvar index) arg
    let value := BooleanGuardNegation.expr bn base
    let condition := GuardNegation.condition pn
      (.app (.app (.app (.const ``Eq [.succ .zero]) boolean) value) (booleanLiteralExpr true))
    let some guard := savedBooleanGuard? condition | throwError "local Boolean leaf rejected"
    pure guard
  let wrongLeaf (guard : SavedBooleanGuard) := GuardNegation.evidence guard.propNegations
    (.app (.app (.app (.const ``Eq [.succ .zero]) boolean) (.bvar 9)) (booleanLiteralExpr true))
    (.app (.app (.const ``instDecidableEqBool []) (.bvar 9)) (booleanLiteralExpr true))
  let sourceAdd := Lean.Expr.app (.app (classHead ScalarPrimitive.add.classNames
    (.identity .word) .word .word .word) (.bvar 3)) (.bvar 2)
  let targetAdd := Lean.Expr.app (.app (.const ``UInt64.add []) (.bvar 3)) (.bvar 2)
  let rec decision (badSaved : Bool) (tree : Guard) : Lean.Expr :=
    match tree with
    | .compare op left right =>
        op.evidenceWith left right (if LeanExe.Source.ExprEquality.same left sourceAdd then targetAdd else left) right
    | .junction n op left right =>
        GuardNegation.evidence n (op.condition left.condition right.condition)
          (op.evidence left.condition right.condition (decision badSaved left) (decision badSaved right))
    | .savedLeft n op left right =>
        let saved := if badSaved then wrongLeaf left else left.evidence
        GuardNegation.evidence n (op.condition left.condition right.condition)
          (op.evidence left.condition right.condition saved (decision badSaved right))
    | .savedRight n op left right =>
        let saved := if badSaved then wrongLeaf right else right.evidence
        GuardNegation.evidence n (op.condition left.condition right.condition)
          (op.evidence left.condition right.condition (decision badSaved left) saved)
    | .savedBoth n op left right =>
        let saved := if badSaved then wrongLeaf left else left.evidence
        GuardNegation.evidence n (op.condition left.condition right.condition)
          (op.evidence left.condition right.condition saved right.evidence)
    | guard => guard.evidence
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for depth in [0, 2] do
    let bt := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
    for (firstFlag, secondFlag) in [(false, false), (false, true), (true, false), (true, true)] do
      let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word
        (.letE `first bt.expr (booleanLiteralExpr firstFlag)
          (.letE `second bt.expr (booleanLiteralExpr secondFlag) body false) false) .default) .default
      for op in [Junction.conjunction, .disjunction] do
        for (bn, pn, n) in [(0, 0, 0), (1, 0, 1), (0, 1, 2), (2, 2, 3)] do
          let first ← makeLeaf 1 bn pn none
          let second ← makeLeaf 0 (bn + 1) (pn + 1) none
          let less : Guard := .compare (.lt (.identity .word)) sourceAdd (.bvar 2)
          let equal : Guard := .compare .eq (.bvar 3) (.bvar 2)
          let trees (a b : SavedBooleanGuard) : List Guard :=
            [.savedLeft n op a less, .savedRight n op equal b, .savedBoth n op a b,
             .junction n op (.savedLeft 1 .conjunction a less) (.savedRight 2 .disjunction equal b)]
          let valid := trees first second
          let wordLeaves := trees (← makeLeaf 3 bn pn none) (← makeLeaf 2 (bn + 1) (pn + 1) none)
          let missingLeaves := trees (← makeLeaf 7 bn pn none) (← makeLeaf 8 (bn + 1) (pn + 1) none)
          for (guard, badWord, missing) in valid.zip (wordLeaves.zip missingLeaves) do
            unless (guardOperands? guard.condition).isSome && guardDecision? guard guard.evidence do
              throwError "saved mixed guard parser rejected"
            for mode in ([0, 1, 2, 3, 4] : List Nat) do
              let value (condition evidence trueDomain falseDomain : Lean.Expr) : Lean.Expr :=
                if mode == 0 then
                  Lean.mkAppN (.const ``ite [.succ .zero]) #[word, condition, evidence, .bvar 3, .bvar 2]
                else if mode == 1 then
                  Lean.mkAppN (.const ``dite [.succ .zero]) #[word, condition, evidence,
                    .lam `proof trueDomain (.bvar 4) .default, .lam `proof falseDomain (.bvar 3) .default]
                else if mode == 2 then
                  toWord (Lean.mkAppN (.const ``Decidable.decide []) #[condition, evidence])
                else if mode == 3 then
                  toWord (Lean.mkAppN (.const ``ite [.succ .zero])
                    #[boolean, condition, evidence, booleanLiteralExpr true, booleanLiteralExpr false])
                else toWord (Lean.mkAppN (.const ``dite [.succ .zero]) #[boolean, condition, evidence,
                  .lam `proof trueDomain (booleanLiteralExpr true) .default,
                  .lam `proof falseDomain (booleanLiteralExpr false) .default])
              let make (guard : Guard) (evidence : Lean.Expr) :=
                wrap (value guard.condition evidence guard.condition (.app (.const ``Not []) guard.condition))
              let some func := extractScalarFunc `savedMixed (some "entry") functionType (make guard (decision false guard)) |
                throwError "saved mixed guard mode {mode} rejected"
              let module_ : LeanExe.IR.Module := { funcs := #[func] }
              for (x, y) in inputs do
                let native (operand : Lean.Expr) : UInt64 :=
                  if LeanExe.Source.ExprEquality.same operand first.operand then
                    (GuardNegation.denote bn firstFlag).toUInt64
                  else if LeanExe.Source.ExprEquality.same operand second.operand then
                    (GuardNegation.denote (bn + 1) secondFlag).toUInt64
                  else if LeanExe.Source.ExprEquality.same operand sourceAdd then x + y
                  else if LeanExe.Source.ExprEquality.same operand (.bvar 3) then x else y
                let result := guard.denote native
                let expected := if mode < 2 then (if result then x else y) else result.toUInt64
                let actual := module_.evalFunc 0 [x, y]
                unless actual == expected do throwError "mixed guard mode {mode}: {actual}, expected {expected}"
                comparisons := comparisons + 1
              for bad in [make guard (.const `customDecision []), make guard (.bvar 0),
                  make guard (.mdata {} guard.evidence), make guard (GuardNegation.evidence 1 guard.condition guard.evidence),
                  make badWord badWord.evidence, make missing missing.evidence, make guard (decision true guard)] do
                unless (extractScalarFunc `invalidMixed (some "entry") functionType bad).isNone do
                  throwError "invalid mixed guard admitted"
                rejected := rejected + 1
              if mode == 1 || mode == 4 then
                let negative := Lean.Expr.app (.const ``Not []) guard.condition
                for (yes, no) in [(word, negative), (negative, negative), (guard.condition, word), (guard.condition, guard.condition)] do
                  unless (extractScalarFunc `invalidDomain (some "entry") functionType
                      (wrap (value guard.condition guard.evidence yes no))).isNone do
                    throwError "invalid mixed guard proof domain admitted"
                  rejected := rejected + 1
            unless (guardOperands? first.condition).isNone && (guardOperands? second.condition).isNone do
              throwError "saved flag changed the separate Boolean-condition parser"
            controls := controls + 1
  unless comparisons == 17920 && rejected == 11008 && controls == 256 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/saved mixed-guard IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"
