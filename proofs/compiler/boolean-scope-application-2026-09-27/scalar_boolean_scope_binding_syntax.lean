import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let signature := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let truth (value : Lean.Expr) := Lean.mkAppN (.const ``Eq [.succ .zero]) #[boolean, value, booleanLiteralExpr true]
  let decision (value : Lean.Expr) := Lean.mkAppN (.const ``instDecidableEqBool []) #[value, booleanLiteralExpr true]
  let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word body .default) .default
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
    let wordType := (List.range depth).foldl (fun type _ => ResultType.identity type) .word
    let boolType := (List.range depth).foldl (fun type _ => BooleanType.identity type) .boolean
    for scopeBoolean in [false, true] do
      let domain := if scopeBoolean then boolType.expr else wordType.expr
      let rawValue := if scopeBoolean then (BooleanLocal.compare .eq (.bvar 1) (.bvar 0)).expr
        else Lean.Expr.app (.app (.const ``UInt64.add []) (.bvar 1)) (.bvar 0)
      for helperBoolean in [false, true] do
        let helperDomain := if helperBoolean then boolType.expr else wordType.expr
        for nondep in [false, true] do
          for info in [Lean.BinderInfo.default, .implicit] do
            let shape : BooleanFunctionBinding := ⟨`f, `arg, info, info, boolType, nondep⟩
            for wrappers in [0, 1, 2] do
              let bound := if wrappers == 0 then rawValue else if scopeBoolean then
                  (if wrappers == 1 then BooleanIdentity.pure rawValue boolType
                   else BooleanIdentity.run (.mdata {} (BooleanIdentity.pure rawValue boolType)) (.identity boolType))
                else (if wrappers == 1 then Identity.pure rawValue wordType
                   else Identity.run (.mdata {} (Identity.pure rawValue wordType)) (.identity wordType))
              for unused in [false, true] do
                let function : BooleanLocal := if unused then
                    (if helperBoolean then .var 0 0 else .compare .eq (.bvar 0) (.bvar 2))
                  else if scopeBoolean then
                    (if helperBoolean then .equality 0 false (.var 0 0) (.var 0 1)
                     else .junction 0 .disjunction (.var 0 1) (.compare .eq (.bvar 0) (.bvar 2)))
                  else (if helperBoolean then .junction 0 .disjunction (.var 0 0) (.compare .eq (.bvar 1) (.bvar 2))
                    else .compare .eq (.bvar 0) (.bvar 1))
                let argumentX := if helperBoolean then (BooleanLocal.compare .eq (.bvar 3) (literalExpr 0)).expr else .bvar 3
                let argumentY := if helperBoolean then (BooleanLocal.compare .eq (.bvar 2) (literalExpr 0)).expr else .bvar 2
                for disjoin in [false, true] do
                  let continuation := Lean.Expr.app (.app (.const (if disjoin then ``Bool.or else ``Bool.and) [])
                    (.app (.bvar 0) argumentX)) (.app (.bvar 0) argumentY)
                  let helper (body : Lean.Expr) := booleanHelperExpr helperBoolean shape `arg body continuation helperDomain
                  let body := helper function.expr
                  let scope (type value body : Lean.Expr) := Lean.Expr.letE `saved type value body nondep
                  let source := scope domain bound body
                  unless (booleanLocalOperands? source).isNone && (booleanScopeBinding? scopeBoolean source).isSome &&
                      (booleanScopeBinding? (!scopeBoolean) source).isNone do
                    throwError "scope binding admission or kind is incorrect"
                  controls := controls + 1
                  for mode in ([0, 1, 2] : List Nat) do
                    let expression (value evidence td fd : Lean.Expr) : Lean.Expr :=
                      if mode == 0 then toWord value
                      else if mode == 1 then Lean.mkAppN (.const ``ite [.succ .zero]) #[word, truth value, evidence, .bvar 1, .bvar 0]
                      else Lean.mkAppN (.const ``dite [.succ .zero]) #[word, truth value, evidence,
                        .lam `proof td (.bvar 2) info, .lam `proof fd (.bvar 1) info]
                    let make (value : Lean.Expr) := wrap (expression value (decision value) (truth value) (.app (.const ``Not []) (truth value)))
                    let some func := extractScalarFunc `scopeBinding (some "entry") signature (make source) |
                      throwError "scope binding rejected: Boolean {scopeBoolean}, helper {helperBoolean}, mode {mode}"
                    let module_ : LeanExe.IR.Module := { funcs := #[func] }
                    for (x, y) in inputs do
                      let native (n : UInt64) := if unused then
                          (if helperBoolean then n == 0 else n == y)
                        else if scopeBoolean then
                          (if helperBoolean then (n == 0) == (x == y) else x == y || n == y)
                        else (if helperBoolean then n == 0 || x + y == y else n == x + y)
                      let flag := if disjoin then native x || native y else native x && native y
                      let expected := if mode == 0 then flag.toUInt64 else if flag then x else y
                      let actual := module_.evalFunc 0 [x, y]
                      unless actual == expected do throwError "scope binding mode {mode}: {actual} != {expected}"
                      comparisons := comparisons + 1
                    let unknown := Lean.Expr.const `unsupportedScope []
                    let badKind := if scopeBoolean then literalExpr 0 else booleanLiteralExpr true
                    let wrongBody := if helperBoolean then (BooleanLocal.compare .eq (.bvar 0) (.bvar 2)).expr else (BooleanLocal.var 0 0).expr
                    let badDomain := Lean.Expr.app (.const ``Id [.succ .zero]) (if scopeBoolean then boolean else word)
                    let badHelper := Lean.Expr.letE `f (.forallE `arg (.const ``Nat []) boolType.expr info)
                      (.lam `arg (.const ``Nat []) function.expr info) continuation nondep
                    let badTail := booleanHelperExpr helperBoolean shape `arg function.expr (.app (.bvar 9) argumentX) helperDomain
                    for bad in [scope (.const ``Nat []) bound body, scope badDomain bound body,
                        scope (.app (.const ``Id [.zero]) (.const ``Nat [])) bound body,
                        scope domain unknown body, scope domain badKind body,
                        scope domain bound unknown, scope domain bound (literalExpr 0), scope domain bound (.bvar 9),
                        scope domain bound (helper unknown), scope domain bound badHelper,
                        scope domain bound (helper wrongBody), scope domain bound badTail] do
                      unless (extractScalarFunc `invalidScope none signature (make bad)).isNone do
                        throwError "invalid scope binding admitted"
                      rejected := rejected + 1
                    if mode != 0 then
                      for evidence in [.const `customDecision [], .mdata {} (decision source), decision (booleanLiteralExpr true)] do
                        unless (extractScalarFunc `invalidDecision none signature
                            (wrap (expression source evidence (truth source) (.app (.const ``Not []) (truth source))))).isNone do
                          throwError "invalid scope decision admitted"
                        rejected := rejected + 1
                    if mode == 2 then
                      for (td, fd) in [(word, .app (.const ``Not []) (truth source)),
                          (truth source, word), (truth source, truth source)] do
                        unless (extractScalarFunc `invalidDomain none signature
                            (wrap (expression source (decision source) td fd))).isNone do
                          throwError "invalid scope proof domain admitted"
                        rejected := rejected + 1
  unless comparisons == 16128 && rejected == 17280 && controls == 384 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/general Boolean scope binding IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"
