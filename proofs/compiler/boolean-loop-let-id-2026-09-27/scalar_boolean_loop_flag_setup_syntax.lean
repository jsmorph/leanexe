import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let modWord (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mod []) a) b
  let indexWord (i : Nat) := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar i)
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for depth in ([1, 3] : List Nat) do
    for form in ([0, 1, 2] : List Nat) do
      for annotationDepth in ([0, 2] : List Nat) do
        for flagFirst in [false, true] do
          let domains := if flagFirst then [boolean, word] else [word, boolean]
          let inputType := (List.range annotationDepth).foldl (fun value _ => BooleanType.identity value) .boolean
          let resultType := (List.range annotationDepth).foldl (fun value _ => BooleanType.identity value) .boolean
          let flagIndex := if flagFirst then 1 else 0
          let wordIndex := if flagFirst then 0 else 1
          for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
            for kind in ([0, 1, 2] : List Nat) do
              for tailForm in ([0, 1, 2] : List Nat) do
                for wrapped in [false, true] do
                  let signature := domains.foldr
                    (fun input rest => Lean.Expr.forallE `parameter input rest binder) resultType.expr
                  let wrap (body : Lean.Expr) := domains.foldr
                    (fun input rest => Lean.Expr.lam `parameter input rest binder) body
                  let flag : BooleanLocal := .var 0 2
                  let choose : BooleanLocalGuard := { value := flag, expanded := rfl }
                  let even : BooleanLocal := .junction 0 .conjunction flag
                    (.compare .eq (modWord (indexWord 1) (literalExpr 2)) (literalExpr 0))
                  let skip : BooleanLocalGuard := { value := even, expanded := rfl }
                  let advanced := add (add (.bvar 0) (indexWord 1)) (toWord (.bvar 2))
                  let step := if kind == 0 then choose.branch (Step.resultType .word)
                      (Step.yieldDirect advanced) (Step.yieldDirect (add (.bvar 0) (literalExpr 3)))
                    else if kind == 1 then choose.branch (Step.resultType .word)
                      (Step.doneDirect (add (.bvar 0) (literalExpr 7))) (Step.yieldDirect advanced)
                    else skip.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                  let loop := Range.call (modWord (.bvar (wordIndex + depth)) (literalExpr 17))
                    (add (.bvar (wordIndex + depth)) (toWord (.bvar 0))) `i `a binder binder step
                  let equal : BooleanLocal := .compare .eq (.bvar 0)
                    (add (.bvar (wordIndex + depth + 1)) (toWord (.bvar 1)))
                  let tail : BooleanLocal := if tailForm == 0 then equal
                    else if tailForm == 1 then .junction 0 .disjunction equal (.var 0 1)
                    else .binding 0 `saved (.letE false) equal (.var 1 0)
                  let result (tail : Lean.Expr) := if wrapped then
                      BooleanIdentity.run (BooleanRange.bind `value binder .word resultType loop tail) resultType
                    else Lean.Expr.letE `value word loop tail false
                  let firstFlag : BooleanLocal := .junction 0 .disjunction (.var 1 flagIndex)
                    (.compare .eq (modWord (.bvar wordIndex) (literalExpr 3)) (literalExpr 0))
                  let first := firstFlag.expr
                  let setupSource (mode : Nat) (first body : Lean.Expr) := Id.run do
                    let mut current := body
                    for offset in (List.range depth).reverse do
                      let value := if offset == 0 then first
                        else (BooleanLocal.junction 0 .conjunction (.var 1 0)
                          (.compare .ne (.bvar (wordIndex + offset)) (literalExpr 7))).expr
                      current := if mode == 0 || (mode == 2 && offset % 2 == 0) then
                          Lean.Expr.letE `saved boolean value current (offset % 2 == 0)
                        else BooleanRange.bindBoolean `saved binder inputType resultType (BooleanIdentity.pure value inputType) current
                    return wrap current
                  let some func := extractScalarFunc `booleanLoopFlagSetup (some "entry") signature (setupSource form first (result tail.expr)) |
                    throwError "flag setup rejected: {depth}, {form}, {annotationDepth}, {flagFirst}, {kind}, {tailForm}"
                  let some control := extractScalarFunc `booleanLoopFlagSetup (some "entry") signature (setupSource 0 first (result tail.expr)) |
                    throwError "lexical setup control rejected"
                  unless control == func do throwError "monadic setup changes compiled loop"
                  controls := controls + 1
                  let some unwrapped := collectLambdas (setupSource form first (result tail.expr)) 2 |
                    throwError "missing syntax parameters"
                  let bindHead := Lean.Expr.const ``Bind.bind [.zero, .zero]
                  let bindInstance := Lean.mkAppN (.const ``Monad.toBind [.zero, .zero])
                    #[.const ``Id [.zero], .const ``Id.instMonad [.zero]]
                  let extra (head input domain output evidence : Lean.Expr) := wrap (Lean.mkAppN head
                    #[.const ``Id [.zero], evidence, input, output, first,
                      .lam `unused domain (unwrapped.liftLooseBVars 0 1) binder])
                  let some extraControl := extractScalarFunc `booleanLoopFlagSetup (some "entry") signature
                      (extra bindHead inputType.expr inputType.expr resultType.expr bindInstance) |
                    throwError "unused Boolean bind control rejected"
                  unless extraControl == func do throwError "unused Boolean setup changes loop IR"
                  controls := controls + 1
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (x, y) in inputs do
                    let rawFlag := if flagFirst then x else y
                    let rawWord := if flagFirst then y else x
                    let flag := (List.range (depth - 1)).foldl
                      (fun value _ => !value && rawWord != 7) (!(rawFlag != 0) || rawWord % 3 == 0)
                    let initial := rawWord + flag.toUInt64
                    let value : UInt64 := Id.run <| forIn (m := Id) [:(rawWord % 17).toNat] initial fun i a =>
                      if kind == 0 then .yield (if flag then a + i.toUInt64 + flag.toUInt64 else a + 3)
                      else if kind == 1 then
                        if flag then .done (a + 7) else .yield (a + i.toUInt64 + flag.toUInt64)
                      else .yield (if flag && i % 2 == 0 then a else a + i.toUInt64 + flag.toUInt64)
                    let same := value == initial
                    let expected := (if tailForm == 0 then same else if tailForm == 1 then same || flag else !same).toUInt64
                    let actual := module_.evalFunc 0 [x, y]
                    unless actual == expected && (actual == 0 || actual == 1) do
                      throwError "flag setup result: {actual}, expected {expected}"
                    comparisons := comparisons + 1
                  let firstFlag : BooleanLocalGuard := { value := .var 0 flagIndex, expanded := rfl }
                  let invalid := [
                    extra bindHead inputType.expr word resultType.expr bindInstance,
                    extra bindHead inputType.expr inputType.expr word bindInstance,
                    extra bindHead (.app (.const ``Id [.succ .zero]) boolean)
                      (.app (.const ``Id [.succ .zero]) boolean) resultType.expr bindInstance,
                    extra bindHead inputType.expr inputType.expr resultType.expr (.const `customFlagBindInstance []),
                    extra (.const ``Bind.bind [.zero]) inputType.expr inputType.expr resultType.expr bindInstance,
                    extra (.const `customFlagBind [.zero, .zero]) inputType.expr inputType.expr resultType.expr bindInstance,
                    setupSource form (.bvar wordIndex) (result tail.expr),
                    setupSource form (.const `unsupportedWordSetup []) (result tail.expr),
                    setupSource form (.bvar 99) (result tail.expr),
                    setupSource form (firstFlag.branch boolean first (.const `unsupportedDeadSetup [])) (result tail.expr),
                    setupSource form (.letE `unused word (.bvar flagIndex) (first.liftLooseBVars 0 1) false) (result tail.expr),
                    setupSource form first (result (.bvar 0)),
                    setupSource form first (result (.const `unsupportedBooleanSetupTail [])),
                    setupSource form first (result (BooleanLocal.var 0 (wordIndex + depth + 1)).expr)]
                  for value in invalid do
                    if (extractScalarFunc `invalidBooleanLoopFlagSetup (some "entry") signature value).isSome then
                      throwError "invalid flag setup accepted: {depth}, {form}, {kind}"
                    rejected := rejected + 1
  unless comparisons == 24192 && rejected == 24192 && controls == 3456 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean loop flag-setup syntax comparisons, {rejected} invalid-input tests and {controls} lexical/unused setup controls passed"
