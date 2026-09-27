import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let sub (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.sub []) a) b
  let modWord (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mod []) a) b
  let indexWord := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar 1)
  let operations : List Comparison := [.eq, .ne, .lt, .le, .gt, .ge, .beq, .bne]
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for booleanArm in [false, true] do
    for scalarArm in ([0, 1, 2, 3] : List Nat) do
      for conditionKind in List.range 12 do
        for nested in [false, true] do
          for annotationDepth in ([0, 2] : List Nat) do
            for flagFirst in [false, true] do
              let domains := if flagFirst then [boolean, word] else [word, boolean]
              let resultType := (List.range annotationDepth).foldl (fun value _ => ResultType.identity value) .word
              let flagIndex := if flagFirst then 1 else 0
              let wordIndex := if flagFirst then 0 else 1
              for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
                for kind in ([0, 1, 2] : List Nat) do
                  let signature := domains.foldr (fun input rest => Lean.Expr.forallE `parameter input rest binder) resultType.expr
                  let wrap (body : Lean.Expr) := domains.foldr (fun input rest => Lean.Expr.lam `parameter input rest binder) body
                  let comparison := operations[conditionKind]?.getD .beq
                  let left := modWord (.bvar wordIndex) (literalExpr 7)
                  let right := toWord (.bvar flagIndex)
                  let guardValue : BooleanLocal := if conditionKind == 8 then .var 0 flagIndex
                    else if conditionKind == 9 then .var 1 flagIndex
                    else .literal 0 (conditionKind == 10)
                  let condition := if conditionKind < 8 then comparison.condition left right else guardValue.condition
                  let evidence := if conditionKind < 8 then comparison.evidence left right else guardValue.evidence
                  let innerCondition := Comparison.lt.condition (.bvar wordIndex) (literalExpr 7)
                  let innerEvidence := Comparison.lt.evidence (.bvar wordIndex) (literalExpr 7)
                  let branch (first : Bool) (badCount badTail : Bool) := Id.run do
                    let divisor := if first then 17 else 11
                    let count := if badCount then .bvar flagIndex else modWord (.bvar wordIndex) (literalExpr divisor)
                    let initial := if first then add (.bvar wordIndex) (toWord (.bvar flagIndex)) else sub (.bvar wordIndex) (literalExpr 3)
                    let advanced := add (add (.bvar 0) indexWord) (literalExpr (if first then 1 else 3))
                    let step := if kind == 0 then Step.yieldDirect advanced
                      else if kind == 1 then Step.branch .beq .word (modWord advanced (literalExpr 7)) (literalExpr 0)
                        (Step.doneDirect advanced) (Step.yieldDirect advanced)
                      else Step.branch .beq .word (modWord indexWord (literalExpr 2)) (literalExpr 0)
                        (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                    let loop := Range.call count initial `i `a binder binder step
                    let tail : BooleanLocal := if first then .junction 0 .disjunction
                        (.compare .eq (modWord (.bvar 0) (literalExpr 7)) (literalExpr 0)) (.var 0 (flagIndex + 1))
                      else .junction 0 .conjunction
                        (.compare .eq (modWord (.bvar 0) (literalExpr 5)) (literalExpr 1)) (.var 1 (flagIndex + 1))
                    return if booleanArm then Lean.Expr.letE `flag boolean
                      (.letE `value word loop tail.expr false)
                      (if badTail then .bvar 0 else add (toWord (.bvar 0)) (.bvar (wordIndex + 1))) false
                    else Lean.Expr.letE `value word loop
                      (if badTail then .bvar (flagIndex + 1) else add (.bvar 0) (.bvar (wordIndex + 1))) false
                  let scalarYes := add (.bvar wordIndex) (literalExpr 7)
                  let scalarNo := sub (.bvar wordIndex) (literalExpr 3)
                  let yes := if scalarArm == 0 || scalarArm == 2 then scalarYes else branch true false false
                  let no := if scalarArm == 1 || scalarArm == 2 then scalarNo else branch false false false
                  let chosen := if nested then WordRange.choiceExpr resultType innerCondition innerEvidence no yes else yes
                  let body := WordRange.choiceExpr resultType condition evidence chosen no
                  let some func := extractScalarFunc `wordLoopCondition (some "entry") signature (wrap body) |
                    throwError "word loop condition rejected: {conditionKind}, {nested}, {annotationDepth}, {flagFirst}, {kind}"
                  let some control := extractScalarFunc `wordLoopCondition (some "entry") signature
                      (wrap (.mdata {} (Identity.run (Identity.pure body resultType) resultType))) |
                    throwError "wrapped condition rejected"
                  unless control == func do throwError "wrappers changed conditional loop"
                  controls := controls + 1
                  let argumentKinds : List PublicArgument := if flagFirst then [.boolean, .word] else [.word, .boolean]
                  let some plan := extractScalarWordRangeWith (publicBindings argumentKinds) 2 body |
                    throwError "direct range extraction rejected word loop condition"
                  let rangeModule : LeanExe.IR.Module := { funcs := #[plan.func `rangeControl (some "entry") 2] }
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (x, y) in inputs do
                    let rawFlag := if flagFirst then x else y
                    let rawWord := if flagFirst then y else x
                    let flag := rawFlag != 0
                    let selected := if conditionKind < 8 then comparison.denote (rawWord % 7) flag.toUInt64
                      else if conditionKind == 8 then flag
                      else if conditionKind == 9 then !flag
                      else conditionKind == 10
                    let first := selected && (!nested || !(rawWord < 7))
                    let stop := rawWord % (if first then 17 else 11)
                    let initial := if first then rawWord + flag.toUInt64 else rawWord - 3
                    let value : UInt64 := Id.run <| forIn (m := Id) [:stop.toNat] initial fun i a =>
                      let advanced := a + i.toUInt64 + (if first then 1 else 3)
                      if kind == 0 then .yield advanced
                      else if kind == 1 then if advanced % 7 == 0 then .done advanced else .yield advanced
                      else .yield (if i % 2 == 0 then a else advanced)
                    let loopResult := if booleanArm then
                        (if first then value % 7 == 0 || flag else value % 5 == 1 && !flag).toUInt64 + rawWord
                      else value + rawWord
                    let expected := if first then
                        if scalarArm == 0 || scalarArm == 2 then rawWord + 7 else loopResult
                      else if scalarArm == 1 || scalarArm == 2 then rawWord - 3 else loopResult
                    let actual := module_.evalFunc 0 [x, y]
                    let rangeActual := rangeModule.evalFunc 0 [x, y]
                    unless actual == expected && rangeActual == expected do
                      throwError "word loop condition result {actual}, expected {expected}"
                    comparisons := comparisons + 2
                  let bad := Lean.Expr.const `unsupportedMixedCondition []
                  let raw (head : Lean.Name) (level : Lean.Level) (type : Lean.Expr) :=
                    Lean.Expr.app (.app (.app (.app (.app (.const head [level]) type) condition) evidence) chosen) no
                  let invalid := [
                    WordRange.choiceExpr resultType condition evidence bad no,
                    WordRange.choiceExpr resultType condition evidence chosen bad,
                    WordRange.choiceExpr resultType bad evidence chosen no,
                    WordRange.choiceExpr resultType condition bad chosen no,
                    raw ``ite (.succ .zero) boolean,
                    raw ``ite (.succ .zero) (.app (.const ``Id [.succ .zero]) word),
                    raw `customIte (.succ .zero) resultType.expr,
                    raw ``ite .zero resultType.expr,
                    WordRange.choiceExpr resultType condition evidence (branch true false true) no,
                    WordRange.choiceExpr resultType condition evidence chosen (branch false true false),
                    WordRange.choiceExpr resultType condition evidence (.bvar flagIndex) no,
                    WordRange.choiceExpr resultType condition evidence chosen (.bvar flagIndex),
                    WordRange.choiceExpr resultType (BooleanLocal.literal 0 true).condition
                      (BooleanLocal.literal 0 true).evidence chosen bad,
                    WordRange.choiceExpr resultType (BooleanLocal.literal 0 false).condition
                      (BooleanLocal.literal 0 false).evidence bad no]
                  for value in invalid do
                    if (extractScalarFunc `invalidWordLoopCondition (some "entry") signature (wrap value)).isSome then
                      throwError "invalid word loop condition accepted: {conditionKind}, {kind}"
                    rejected := rejected + 1
  unless comparisons == 258048 && rejected == 129024 && controls == 9216 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/public and direct range word-loop conditional comparisons, {rejected} invalid-input tests and {controls} wrapper controls passed"
