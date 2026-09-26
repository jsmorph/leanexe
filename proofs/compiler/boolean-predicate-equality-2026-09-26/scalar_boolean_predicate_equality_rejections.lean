import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let yes := booleanLiteralExpr true
  let no := booleanLiteralExpr false
  let standard := Lean.mkAppN (.const ``instBEqOfDecidableEq [.zero])
    #[boolean, .const ``instDecidableEqBool []]
  let wrongInstance := Lean.mkAppN (.const ``instBEqOfDecidableEq [.zero])
    #[word, .const ``instDecidableEqUInt64 []]
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for scope in [0, 1, 2] do
    let index := if scope == 2 then 2 else 0
    let call := Lean.Expr.app (.bvar index) yes
    let wrap (argument : Lean.Expr) :=
      let result := Lean.Expr.app (.const ``Bool.toUInt64 []) argument
      let helper (body : Lean.Expr) := Lean.Expr.letE `predicate
        (.forallE `b boolean boolean .default) (.lam `b boolean (.bvar 0) .default) body false
      let body := if scope == 0 then helper result else if scope == 1 then
        Range.call (.bvar 1) (.bvar 0) `i `a .default .default (helper (Step.yieldDirect result))
        else helper (Range.call (.bvar 2) (.bvar 1) `i `a .default .default (Step.yieldDirect result))
      Lean.Expr.lam `x word (.lam `y word body .default) .default
    let check (argument : Lean.Expr) := extractScalarFunc `predicateEquality (some "entry") functionType (wrap argument)
    for unequal in [false, true] do
      for valid in [booleanEqualityExpr unequal call no, booleanRelationDecisionExpr unequal call no] do
        unless (check valid).isSome do throwError "positive predicate equality control rejected"
        controls := controls + 1
    for head in [``BEq.beq, ``_root_.bne] do
      let make (levels : List Lean.Level) (type evidence left right : Lean.Expr) :=
        Lean.mkAppN (.const head levels) #[type, evidence, left, right]
      for invalid in [make [.zero] boolean (.bvar index) call no,
          make [.zero] boolean wrongInstance call no,
          make [.zero] boolean standard call (literalExpr 1),
          make [.succ .zero] boolean standard call no,
          make [.zero] word standard call no] do
        unless (check invalid).isNone do throwError "invalid predicate BEq accepted"
        rejected := rejected + 1
    for unequal in [false, true] do
      let proposition := booleanRelationCondition unequal call no
      let evidence := booleanRelationEvidence unequal call no
      let make (levels : List Lean.Level) (condition decision : Lean.Expr) :=
        Lean.mkAppN (.const ``Decidable.decide levels) #[condition, decision]
      for invalid in [make [.zero] proposition evidence,
          make [] proposition (.const `unsupportedDecision []),
          make [] proposition (booleanRelationEvidence unequal yes no),
          booleanRelationDecisionExpr unequal call (literalExpr 1)] do
        unless (check invalid).isNone do throwError "invalid predicate decision accepted"
        rejected := rejected + 1
  unless controls == 12 && rejected == 54 do throwError "unexpected counts {controls}, {rejected}"
  Lean.logInfo m!"{controls} predicate equality admission controls and {rejected} instance/type rejection tests passed"
