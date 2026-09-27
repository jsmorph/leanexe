import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

-- helper input id predicate
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
  for inputDepth in ([0, 2] : List Nat) do
    let annotate (base : Lean.Expr) := (List.range inputDepth).foldl
      (fun current _ => Lean.Expr.app (.const ``Id [.zero]) current) base
    for booleanInput in [false, true] do
      for depth in ([1, 2] : List Nat) do
        for annotationDepth in ([0, 2] : List Nat) do
          for flagFirst in [false, true] do
            let helperDomain := if booleanInput then boolean else word
            let domains := if flagFirst then [boolean, word] else [word, boolean]
            let resultType := (List.range annotationDepth).foldl (fun value _ => BooleanType.identity value) .boolean
            let flagIndex := if flagFirst then 1 else 0
            let wordIndex := if flagFirst then 0 else 1
            for typeBinder in [Lean.BinderInfo.default, .strictImplicit] do
              for valueBinder in [Lean.BinderInfo.implicit, .instImplicit] do
                for nondep in [false, true] do
                  for kind in ([0, 1, 2] : List Nat) do
                    for tailForm in ([0, 1, 2] : List Nat) do
                      let signature := domains.foldr
                        (fun input rest => Lean.Expr.forallE `parameter input rest typeBinder) word
                      let wrap (body : Lean.Expr) := domains.foldr
                        (fun input rest => Lean.Expr.lam `parameter input rest valueBinder) body
                      let flag : BooleanLocal := .var 0 (flagIndex + depth + 2)
                      let choose : BooleanLocalGuard := { value := flag, expanded := rfl }
                      let even : BooleanLocal := .junction 0 .conjunction flag
                        (.compare .eq (modWord (indexWord 1) (literalExpr 2)) (literalExpr 0))
                      let skip : BooleanLocalGuard := { value := even, expanded := rfl }
                      let parity : BooleanLocal := .compare .eq (modWord (indexWord 1) (literalExpr 2)) (literalExpr 0)
                      let argument := if booleanInput then parity.expr else add (.bvar 0) (indexWord 1)
                      let advanced := add (.bvar 0) (toWord (.app (.bvar 2) argument))
                      let step := if kind == 0 then choose.branch (Step.resultType .word)
                          (Step.yieldDirect advanced) (Step.yieldDirect (add (.bvar 0) (literalExpr 3)))
                        else if kind == 1 then choose.branch (Step.resultType .word)
                          (Step.doneDirect (add (.bvar 0) (literalExpr 7))) (Step.yieldDirect advanced)
                        else skip.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                      let loop := Range.call (modWord (.bvar (wordIndex + depth)) (literalExpr 17))
                        (toWord (.app (.bvar 0) (.bvar ((if booleanInput then flagIndex else wordIndex) + depth)))) `i `a valueBinder valueBinder step
                      let argument := if booleanInput then
                        (BooleanLocal.compare .eq (modWord (.bvar 0) (literalExpr 2)) (literalExpr 0)).expr
                        else .bvar 0
                      let equal : BooleanLocal := .predicate 0 1 argument
                      let tail : BooleanLocal := if tailForm == 0 then equal
                        else if tailForm == 1 then .junction 0 .disjunction equal (.var 0 (flagIndex + depth + 1))
                        else .binding 0 `saved (.letE nondep) equal (.var 1 0)
                      let result (tail : Lean.Expr) := Lean.Expr.letE `flag boolean
                        (.letE `value word loop tail nondep)
                        (add (toWord (.bvar 0)) (add (.bvar (wordIndex + depth + 1)) (literalExpr 7))) nondep
                      let first : BooleanLocal := if booleanInput then
                        .junction 0 .disjunction (.junction 0 .conjunction (.var 0 0) (.var 0 (flagIndex + 1)))
                          (.compare .eq (modWord (.bvar (wordIndex + 1)) (literalExpr 3)) (literalExpr 0))
                        else .junction 0 .disjunction
                          (.compare .eq (modWord (.bvar 0) (literalExpr 3)) (modWord (.bvar (wordIndex + 1)) (literalExpr 3)))
                          (.var 0 (flagIndex + 1))
                      let first := first.expr
                      let setupSource (first body : Lean.Expr) := Id.run do
                        let mut current := body
                        for offset in (List.range depth).reverse do
                          let value := if offset == 0 then first
                            else (BooleanLocal.junction 0 .disjunction
                             (.predicate 0 1 (if booleanInput then (BooleanLocal.var 1 0).expr else add (.bvar 0) (literalExpr 3)))
                             (.var 1 (flagIndex + offset + 1))).expr
                          current := Lean.Expr.letE `helper (.forallE `x (annotate helperDomain) resultType.expr typeBinder)
                            (.lam `x (annotate helperDomain) (BooleanIdentity.pure value resultType) valueBinder) current nondep
                        return wrap current
                      let source := setupSource first (result tail.expr)
                      let some func := extractScalarFunc `booleanLoopPredicateHelpers (some "entry") signature source |
                        throwError "Boolean-result helper rejected: {depth}, {annotationDepth}, {flagFirst}, {kind}, {tailForm}"
                      let some unwrapped := collectLambdas source 2 | throwError "missing parameters"
                      let kinds := if flagFirst then [PublicArgument.boolean, .word] else [.word, .boolean]
                      let some plan := extractScalarBooleanWordRangeWith (publicBindings kinds) 2 unwrapped |
                        throwError "direct word helper path rejected"
                      let direct := plan.func `booleanLoopPredicateHelpers (some "entry") 2
                      unless direct == func do throwError "public and direct word helper plans differ"
                      controls := controls + 1
                      let directModule : LeanExe.IR.Module := { funcs := #[direct] }
                      let extra (input domain output value : Lean.Expr) := wrap (.letE `unused
                        (.forallE `x (annotate input) output typeBinder) (.lam `x (annotate domain) value valueBinder)
                        (unwrapped.liftLooseBVars 0 1) nondep)
                      let some control := extractScalarFunc `booleanLoopPredicateHelpers (some "entry") signature
                          (extra helperDomain helperDomain resultType.expr (BooleanIdentity.pure first resultType)) |
                        throwError "valid unused helper rejected"
                      unless control == func do throwError "unused helper changes compiled loop"
                      controls := controls + 1
                      let module_ : LeanExe.IR.Module := { funcs := #[func] }
                      for (x, y) in inputs do
                        let rawFlag := if flagFirst then x else y
                        let rawWord := if flagFirst then y else x
                        let flag := rawFlag != 0
                        let wordFunction : UInt64 → Bool := (List.range (depth - 1)).foldl
                          (fun previous _ => fun value => previous (value + 3) || !flag)
                          (fun value => value % 3 == rawWord % 3 || flag)
                        let booleanFunction : Bool → Bool := (List.range (depth - 1)).foldl
                          (fun previous _ => fun value => previous (!value) || !flag)
                          (fun value => (value && flag) || rawWord % 3 == 0)
                        let initial := (if booleanInput then booleanFunction flag else wordFunction rawWord).toUInt64
                        let value : UInt64 := Id.run <| forIn (m := Id) [:(rawWord % 17).toNat] initial fun i a =>
                          let advanced := a + (if booleanInput then booleanFunction (i % 2 == 0) else wordFunction (a + i.toUInt64)).toUInt64
                          if kind == 0 then .yield (if flag then advanced else a + 3)
                          else if kind == 1 then
                            if flag then .done (a + 7) else .yield advanced
                          else .yield (if flag && i % 2 == 0 then a else advanced)
                        let same := if booleanInput then booleanFunction (value % 2 == 0) else wordFunction value
                        let expected := (if tailForm == 0 then same else if tailForm == 1 then same || flag else !same).toUInt64 + rawWord + 7
                        let actual := module_.evalFunc 0 [x, y]
                        unless actual == expected && directModule.evalFunc 0 [x, y] == expected do
                          throwError "Boolean-result helper result: {actual}, expected {expected}"
                        comparisons := comparisons + 2
                      let firstFlag : BooleanLocalGuard := { value := .var 0 (flagIndex + 1), expanded := rfl }
                      let bad := Lean.Expr.const `unsupportedPredicateHelpers []
                      let invalid := [
                        setupSource bad (result tail.expr),
                        setupSource (.bvar (wordIndex + 1)) (result tail.expr),
                        setupSource (.bvar 99) (result tail.expr),
                        setupSource (firstFlag.branch boolean first bad) (result tail.expr),
                        setupSource (.letE `unused boolean (.bvar (wordIndex + 1)) (first.liftLooseBVars 0 1) nondep) (result tail.expr),
                        setupSource first (result (.bvar 0)),
                        extra boolean word resultType.expr first,
                        extra word boolean resultType.expr first,
                        extra helperDomain helperDomain word first,
                        extra helperDomain helperDomain (.app (.const ``Id [.succ .zero]) boolean) first,
                        extra helperDomain helperDomain (.app (.const `CustomId [.zero]) boolean) first,
                        extra helperDomain helperDomain resultType.expr bad,
                       extra (.app (.const ``Id [.succ .zero]) helperDomain) helperDomain resultType.expr first,
                       extra helperDomain (.app (.const `CustomId [.zero]) helperDomain) resultType.expr first,
                       extra (.app (.const ``Id [.zero]) helperDomain) helperDomain resultType.expr first,
                       extra (.const ``Nat []) (.const ``Nat []) resultType.expr first]
                      for value in invalid do
                        if (extractScalarFunc `invalidBooleanLoopPredicateHelpers (some "entry") signature value).isSome then
                          throwError "invalid Boolean-result helper accepted: {depth}, {kind}"
                        rejected := rejected + 1
  unless comparisons == 64512 && rejected == 36864 && controls == 4608 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean-to-word loop Boolean-result-helper Id-input syntax comparisons, {rejected} invalid-input tests and {controls} direct-plan and unused-helper controls passed"

