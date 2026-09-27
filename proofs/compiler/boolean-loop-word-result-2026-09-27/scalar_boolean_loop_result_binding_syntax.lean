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
  for monadic in [false, true] do
    for annotationDepth in ([0, 2] : List Nat) do
      let type := (List.range annotationDepth).foldl (fun value _ => BooleanType.identity value) .boolean
      for flagFirst in [false, true] do
        let domains := if flagFirst then [boolean, word] else [word, boolean]
        let kinds := if flagFirst then [PublicArgument.boolean, .word] else [.word, .boolean]
        let flagIndex := if flagFirst then 1 else 0
        let wordIndex := if flagFirst then 0 else 1
        for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
          for kind in ([0, 1, 2] : List Nat) do
            for mode in ([0, 1, 2] : List Nat) do
              for tailForm in ([0, 1, 2, 3] : List Nat) do
                for wrapped in [false, true] do
                  let signature := domains.foldr (fun input rest => Lean.Expr.forallE `parameter input rest binder) type.expr
                  let wrap (body : Lean.Expr) := domains.foldr (fun input rest => Lean.Expr.lam `parameter input rest binder) body
                  let flag : BooleanLocal := .var 0 flagIndex
                  let initial := add (.bvar wordIndex) (toWord flag.expr)
                  let advanced := add (add (.bvar 0) indexWord) (literalExpr 1)
                  let step := if kind == 0 then Step.yieldDirect advanced
                    else if kind == 1 then Step.branch .beq .word (modWord advanced (literalExpr 7)) (literalExpr 0)
                      (Step.doneDirect advanced) (Step.yieldDirect advanced)
                    else Step.branch .beq .word (modWord indexWord (literalExpr 2)) (literalExpr 0)
                      (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                  let loop := Range.call (modWord (.bvar wordIndex) (literalExpr 17)) initial `i `a binder binder step
                  let loopTail : BooleanLocal := .junction 0 .disjunction
                    (.compare .eq (modWord (.bvar 0) (literalExpr 7)) (literalExpr 0)) (.var 0 (flagIndex + 1))
                  let loopBody := Lean.Expr.letE `value word loop loopTail.expr false
                  let scalar : BooleanLocal := .compare .eq (modWord (.bvar wordIndex) (literalExpr 5)) (literalExpr 0)
                  let other : BooleanLocal := .var 1 flagIndex
                  let action := if mode == 0 then loopBody else
                    BooleanRange.choiceExpr type flag.condition flag.evidence
                      (if mode == 2 then other.expr else loopBody) scalar.expr
                  let action := if wrapped then (BooleanWrapper.run type).expr ((BooleanWrapper.pure type).expr action) else action
                  let tail : BooleanLocal := if tailForm == 0 then .var 1 0
                    else if tailForm == 1 then .junction 0 .conjunction (.var 0 0) (.var 0 (flagIndex + 1))
                    else if tailForm == 2 then .equality 0 true (.var 0 0) (.var 0 (flagIndex + 1))
                    else .binding 0 `saved (.letE flagFirst) (.var 1 0)
                      (.junction 0 .disjunction (.var 0 0) (.var 0 (flagIndex + 2)))
                  let bindBody (value tail : Lean.Expr) := if monadic then
                      BooleanRange.bindBoolean `saved binder type type value tail
                    else Lean.Expr.letE `saved type.expr value tail flagFirst
                  let body := bindBody action tail.expr
                  let some func := extractScalarFunc `booleanResultBinding (some "entry") signature (wrap body) |
                    throwError "result binding rejected: {monadic}, {annotationDepth}, {flagFirst}, {kind}, {mode}, {tailForm}, {wrapped}"
                  let some plan := extractScalarBooleanRangeWith (publicBindings kinds) 2 body |
                    throwError "direct result binding rejected"
                  let direct := plan.func `booleanResultBinding (some "entry") 2
                  let some control := extractScalarBooleanRangeWith (publicBindings kinds) 2
                      (.letE `saved boolean action tail.expr flagFirst) |
                    throwError "lexical control rejected"
                  unless direct == control.func `booleanResultBinding (some "entry") 2 do
                    throwError "monadic result binding changed the loop plan"
                  controls := controls + 1
                  if mode == 2 && annotationDepth == 0 then
                    let some bound := extractScalarExprWith (publicBindings kinds) (toWord action) |
                      throwError "all-scalar choice did not exercise whole-path fallback: {monadic}, {annotationDepth}, {flagFirst}, {kind}, {mode}, {tailForm}, {wrapped}"
                    if (extractScalarBooleanRangeWith (.boolean bound :: publicBindings kinds) 2 tail.expr).isSome then
                      throwError "scalar tail unexpectedly contains a loop plan"
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  let directModule : LeanExe.IR.Module := { funcs := #[direct] }
                  for (x, y) in inputs do
                    let rawFlag := if flagFirst then x else y
                    let rawWord := if flagFirst then y else x
                    let flag := rawFlag != 0
                    let initial := rawWord + flag.toUInt64
                    let value : UInt64 := Id.run <| forIn (m := Id) [:(rawWord % 17).toNat] initial fun i a =>
                      let advanced := a + i.toUInt64 + 1
                      if kind == 0 then .yield advanced
                      else if kind == 1 then if advanced % 7 == 0 then .done advanced else .yield advanced
                      else .yield (if i % 2 == 0 then a else advanced)
                    let result := if mode == 0 then value % 7 == 0 || flag
                      else if flag then (if mode == 2 then !flag else value % 7 == 0 || flag)
                      else rawWord % 5 == 0
                    let expected := (if tailForm == 0 then !result
                      else if tailForm == 1 then result && flag
                      else if tailForm == 2 then result != flag
                      else !result || flag).toUInt64
                    for actual in [module_.evalFunc 0 [x, y], directModule.evalFunc 0 [x, y]] do
                      unless actual == expected && (actual == 0 || actual == 1) do
                        throwError "result binding produced {actual}, expected {expected}"
                      comparisons := comparisons + 1
                  let bad := Lean.Expr.const `unsupportedBooleanResultBinding []
                  let bindHead := Lean.Expr.const ``Bind.bind [.zero, .zero]
                  let bindInstance := Lean.mkAppN (.const ``Monad.toBind [.zero, .zero])
                    #[.const ``Id [.zero], .const ``Id.instMonad [.zero]]
                  let raw (head input domain output evidence : Lean.Expr) := Lean.mkAppN head
                    #[.const ``Id [.zero], evidence, input, output, action, .lam `saved domain tail.expr binder]
                  let invalid := [
                    bindBody bad tail.expr,
                    bindBody action bad,
                    bindBody (.bvar 999) tail.expr,
                    bindBody action (.bvar 999),
                    bindBody (.bvar wordIndex) tail.expr,
                    bindBody action (.bvar (wordIndex + 1)),
                    bindBody (BooleanRange.choiceExpr type flag.condition flag.evidence action bad) tail.expr,
                    raw bindHead type.expr word type.expr bindInstance,
                    raw bindHead type.expr type.expr word bindInstance,
                    raw bindHead (.app (.const ``Id [.succ .zero]) boolean)
                      (.app (.const ``Id [.succ .zero]) boolean) type.expr bindInstance,
                    raw bindHead type.expr type.expr type.expr (.const `customBindInstance []),
                    raw (.const ``Bind.bind [.zero]) type.expr type.expr type.expr bindInstance,
                    raw (.const `customBind [.zero, .zero]) type.expr type.expr type.expr bindInstance,
                    Lean.Expr.letE `saved (.app (.const ``Id [.succ .zero]) boolean) action tail.expr flagFirst,
                    bindBody (.letE `unused word bad (action.liftLooseBVars 0 1) false) tail.expr]
                  for value in invalid do
                    if (extractScalarFunc `invalidBooleanResultBinding (some "entry") signature (wrap value)).isSome then
                      throwError "invalid result binding accepted: {monadic}, {annotationDepth}, {kind}, {mode}, {tailForm}"
                    rejected := rejected + 1
  unless comparisons == 64512 && rejected == 34560 && controls == 2304 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/result-binding syntax comparisons, {rejected} invalid-input tests and {controls} binding controls passed"
