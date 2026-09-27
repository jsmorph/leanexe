import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

-- helper input id word
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
    for depth in ([1, 2] : List Nat) do
      for annotationDepth in ([0, 2] : List Nat) do
        for flagFirst in [false, true] do
          let domains := if flagFirst then [boolean, word] else [word, boolean]
          let resultType := (List.range annotationDepth).foldl (fun value _ => ResultType.identity value) .word
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
                    let advanced := Lean.Expr.app (.bvar 2) (add (.bvar 0) (indexWord 1))
                    let step := if kind == 0 then choose.branch (Step.resultType .word)
                        (Step.yieldDirect advanced) (Step.yieldDirect (add (.bvar 0) (literalExpr 3)))
                      else if kind == 1 then choose.branch (Step.resultType .word)
                        (Step.doneDirect (add (.bvar 0) (literalExpr 7))) (Step.yieldDirect advanced)
                      else skip.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                    let loop := Range.call (modWord (.bvar (wordIndex + depth)) (literalExpr 17))
                      (.app (.bvar 0) (.bvar (wordIndex + depth))) `i `a valueBinder valueBinder step
                    let equal : BooleanLocal := .compare .eq (.bvar 0)
                      (.app (.bvar 1) (.bvar (wordIndex + depth + 1)))
                    let tail : BooleanLocal := if tailForm == 0 then equal
                      else if tailForm == 1 then .junction 0 .disjunction equal (.var 0 (flagIndex + depth + 1))
                      else .binding 0 `saved (.letE nondep) equal (.var 1 0)
                    let result (tail : Lean.Expr) := Lean.Expr.letE `flag boolean
                      (.letE `value word loop tail nondep)
                      (add (toWord (.bvar 0)) (add (.bvar (wordIndex + depth + 1)) (literalExpr 7))) nondep
                    let first := add (add (.bvar 0) (.bvar (wordIndex + 1))) (toWord (.bvar (flagIndex + 1)))
                    let setupSource (first body : Lean.Expr) := Id.run do
                      let selected : BooleanLocal := .var 0 (flagIndex + depth)
                      let mut current := WordRange.choiceExpr .word selected.condition selected.evidence body
                        (add (.bvar (wordIndex + depth)) (literalExpr 13))
                      for offset in (List.range depth).reverse do
                        let value := if offset == 0 then first
                          else add (.app (.bvar 1) (add (.bvar 0) (literalExpr 3))) (.bvar (wordIndex + offset + 1))
                        current := Lean.Expr.letE `helper (.forallE `x (annotate word) resultType.expr typeBinder)
                          (.lam `x (annotate word) (Identity.pure value resultType) valueBinder) current nondep
                      return wrap current
                    let source := setupSource first (result tail.expr)
                    let some func := extractScalarFunc `booleanLoopWordHelper (some "entry") signature source |
                      throwError "word helper rejected: {depth}, {annotationDepth}, {flagFirst}, {kind}, {tailForm}"
                    let some unwrapped := collectLambdas source 2 | throwError "missing parameters"
                    let kinds := if flagFirst then [PublicArgument.boolean, .word] else [.word, .boolean]
                    let some plan := extractScalarWordRangeWith (publicBindings kinds) 2 unwrapped |
                      throwError "direct word helper path rejected"
                    let direct := plan.func `booleanLoopWordHelper (some "entry") 2
                    unless direct == func do throwError "public and direct word helper plans differ"
                    controls := controls + 1
                    let directModule : LeanExe.IR.Module := { funcs := #[direct] }
                    let extra (input domain output value : Lean.Expr) := wrap (.letE `unused
                      (.forallE `x (annotate input) output typeBinder) (.lam `x (annotate domain) value valueBinder)
                      (unwrapped.liftLooseBVars 0 1) nondep)
                    let some control := extractScalarFunc `booleanLoopWordHelper (some "entry") signature
                        (extra word word resultType.expr (Identity.pure first resultType)) |
                      throwError "valid unused helper rejected"
                    unless control == func do throwError "unused helper changes compiled loop"
                    controls := controls + 1
                    let module_ : LeanExe.IR.Module := { funcs := #[func] }
                    for (x, y) in inputs do
                      let rawFlag := if flagFirst then x else y
                      let rawWord := if flagFirst then y else x
                      let flag := rawFlag != 0
                      let f : UInt64 → UInt64 := (List.range (depth - 1)).foldl
                        (fun previous _ => fun value => previous (value + 3) + rawWord)
                        (fun value => value + rawWord + flag.toUInt64)
                      let initial := f rawWord
                      let value : UInt64 := Id.run <| forIn (m := Id) [:(rawWord % 17).toNat] initial fun i a =>
                        if kind == 0 then .yield (if flag then f (a + i.toUInt64) else a + 3)
                        else if kind == 1 then
                          if flag then .done (a + 7) else .yield (f (a + i.toUInt64))
                        else .yield (if flag && i % 2 == 0 then a else f (a + i.toUInt64))
                      let same := value == initial
                      let expected := (if tailForm == 0 then same else if tailForm == 1 then same || flag else !same).toUInt64 + rawWord + 7
                      let expected := if flag then expected else rawWord + 13
                      let actual := module_.evalFunc 0 [x, y]
                      unless actual == expected && directModule.evalFunc 0 [x, y] == expected do
                        throwError "word helper result: {actual}, expected {expected}"
                      comparisons := comparisons + 2
                    let firstFlag : BooleanLocalGuard := { value := .var 0 (flagIndex + 1), expanded := rfl }
                    let bad := Lean.Expr.const `unsupportedWordHelper []
                    let invalid := [
                      setupSource bad (result tail.expr),
                      setupSource (.bvar (flagIndex + 1)) (result tail.expr),
                      setupSource (.bvar 99) (result tail.expr),
                      setupSource (firstFlag.branch word first bad) (result tail.expr),
                      setupSource (.letE `unused word (.bvar (flagIndex + 1)) (first.liftLooseBVars 0 1) nondep) (result tail.expr),
                      setupSource first (result (.bvar 0)),
                      extra boolean word resultType.expr first,
                      extra word boolean resultType.expr first,
                      extra word word boolean first,
                      extra word word (.app (.const ``Id [.succ .zero]) word) first,
                      extra word word (.app (.const `CustomId [.zero]) word) first,
                      extra word word resultType.expr bad,
                      extra (.app (.const ``Id [.succ .zero]) word) word resultType.expr first,
                      extra word (.app (.const `CustomId [.zero]) word) resultType.expr first,
                      extra (.app (.const ``Id [.zero]) word) word resultType.expr first,
                      extra (.const ``Nat []) (.const ``Nat []) resultType.expr first]
                    for value in invalid do
                      if (extractScalarFunc `invalidBooleanLoopWordHelper (some "entry") signature value).isSome then
                        throwError "invalid word helper accepted: {depth}, {kind}"
                      rejected := rejected + 1
  unless comparisons == 32256 && rejected == 18432 && controls == 2304 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/word conditional loop word-helper Id-input syntax comparisons, {rejected} invalid-input tests and {controls} direct-plan and unused-helper controls passed"

-- helper input id boolean
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
    for depth in ([1, 2] : List Nat) do
      for annotationDepth in ([0, 2] : List Nat) do
        for flagFirst in [false, true] do
          let domains := if flagFirst then [boolean, word] else [word, boolean]
          let resultType := (List.range annotationDepth).foldl (fun value _ => ResultType.identity value) .word
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
                    let advanced := add (.bvar 0) (.app (.bvar 2) parity.expr)
                    let step := if kind == 0 then choose.branch (Step.resultType .word)
                        (Step.yieldDirect advanced) (Step.yieldDirect (add (.bvar 0) (literalExpr 3)))
                      else if kind == 1 then choose.branch (Step.resultType .word)
                        (Step.doneDirect (add (.bvar 0) (literalExpr 7))) (Step.yieldDirect advanced)
                      else skip.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                    let loop := Range.call (modWord (.bvar (wordIndex + depth)) (literalExpr 17))
                      (.app (.bvar 0) (.bvar (flagIndex + depth))) `i `a valueBinder valueBinder step
                    let equal : BooleanLocal := .compare .eq (.bvar 0)
                      (.app (.bvar 1) (.bvar (flagIndex + depth + 1)))
                    let tail : BooleanLocal := if tailForm == 0 then equal
                      else if tailForm == 1 then .junction 0 .disjunction equal (.var 0 (flagIndex + depth + 1))
                      else .binding 0 `saved (.letE nondep) equal (.var 1 0)
                    let result (tail : Lean.Expr) := Lean.Expr.letE `flag boolean
                      (.letE `value word loop tail nondep)
                      (add (toWord (.bvar 0)) (add (.bvar (wordIndex + depth + 1)) (literalExpr 7))) nondep
                    let first := add (add (toWord (.bvar 0)) (.bvar (wordIndex + 1))) (toWord (.bvar (flagIndex + 1)))
                    let setupSource (first body : Lean.Expr) := Id.run do
                      let selected : BooleanLocal := .var 0 (flagIndex + depth)
                      let mut current := WordRange.choiceExpr .word selected.condition selected.evidence body
                        (add (.bvar (wordIndex + depth)) (literalExpr 13))
                      for offset in (List.range depth).reverse do
                        let value := if offset == 0 then first
                          else add (.app (.bvar 1) (.app (.const ``Bool.not []) (.bvar 0))) (.bvar (wordIndex + offset + 1))
                        current := Lean.Expr.letE `helper (.forallE `x (annotate boolean) resultType.expr typeBinder)
                          (.lam `x (annotate boolean) (Identity.pure value resultType) valueBinder) current nondep
                      return wrap current
                    let source := setupSource first (result tail.expr)
                    let some func := extractScalarFunc `booleanLoopBooleanHelper (some "entry") signature source |
                      throwError "Boolean-input helper rejected: {depth}, {annotationDepth}, {flagFirst}, {kind}, {tailForm}"
                    let some unwrapped := collectLambdas source 2 | throwError "missing parameters"
                    let kinds := if flagFirst then [PublicArgument.boolean, .word] else [.word, .boolean]
                    let some plan := extractScalarWordRangeWith (publicBindings kinds) 2 unwrapped |
                      throwError "direct word helper path rejected"
                    let direct := plan.func `booleanLoopBooleanHelper (some "entry") 2
                    unless direct == func do throwError "public and direct word helper plans differ"
                    controls := controls + 1
                    let directModule : LeanExe.IR.Module := { funcs := #[direct] }
                    let extra (input domain output value : Lean.Expr) := wrap (.letE `unused
                      (.forallE `x (annotate input) output typeBinder) (.lam `x (annotate domain) value valueBinder)
                      (unwrapped.liftLooseBVars 0 1) nondep)
                    let some control := extractScalarFunc `booleanLoopBooleanHelper (some "entry") signature
                        (extra boolean boolean resultType.expr (Identity.pure first resultType)) |
                      throwError "valid unused helper rejected"
                    unless control == func do throwError "unused helper changes compiled loop"
                    controls := controls + 1
                    let module_ : LeanExe.IR.Module := { funcs := #[func] }
                    for (x, y) in inputs do
                      let rawFlag := if flagFirst then x else y
                      let rawWord := if flagFirst then y else x
                      let flag := rawFlag != 0
                      let f : Bool → UInt64 := (List.range (depth - 1)).foldl
                        (fun previous _ => fun value => previous (!value) + rawWord)
                        (fun value => value.toUInt64 + rawWord + flag.toUInt64)
                      let initial := f flag
                      let value : UInt64 := Id.run <| forIn (m := Id) [:(rawWord % 17).toNat] initial fun i a =>
                        if kind == 0 then .yield (if flag then a + f (i % 2 == 0) else a + 3)
                        else if kind == 1 then
                          if flag then .done (a + 7) else .yield (a + f (i % 2 == 0))
                        else .yield (if flag && i % 2 == 0 then a else a + f (i % 2 == 0))
                      let same := value == initial
                      let expected := (if tailForm == 0 then same else if tailForm == 1 then same || flag else !same).toUInt64 + rawWord + 7
                      let expected := if flag then expected else rawWord + 13
                      let actual := module_.evalFunc 0 [x, y]
                      unless actual == expected && directModule.evalFunc 0 [x, y] == expected do
                        throwError "Boolean-input helper result: {actual}, expected {expected}"
                      comparisons := comparisons + 2
                    let firstFlag : BooleanLocalGuard := { value := .var 0 (flagIndex + 1), expanded := rfl }
                    let bad := Lean.Expr.const `unsupportedBooleanHelper []
                    let invalid := [
                      setupSource bad (result tail.expr),
                      setupSource (.bvar (flagIndex + 1)) (result tail.expr),
                      setupSource (.bvar 99) (result tail.expr),
                      setupSource (firstFlag.branch word first bad) (result tail.expr),
                      setupSource (.letE `unused word (.bvar (flagIndex + 1)) (first.liftLooseBVars 0 1) nondep) (result tail.expr),
                      setupSource first (result (.bvar 0)),
                      extra boolean word resultType.expr first,
                      extra word boolean resultType.expr first,
                      extra boolean boolean boolean first,
                      extra boolean boolean (.app (.const ``Id [.succ .zero]) word) first,
                      extra boolean boolean (.app (.const `CustomId [.zero]) word) first,
                      extra boolean boolean resultType.expr bad,
                      extra (.app (.const ``Id [.succ .zero]) boolean) boolean resultType.expr first,
                      extra boolean (.app (.const `CustomId [.zero]) boolean) resultType.expr first,
                      extra (.app (.const ``Id [.zero]) boolean) boolean resultType.expr first,
                      extra (.const ``Nat []) (.const ``Nat []) resultType.expr first]
                    for value in invalid do
                      if (extractScalarFunc `invalidBooleanLoopBooleanHelper (some "entry") signature value).isSome then
                        throwError "invalid Boolean-input helper accepted: {depth}, {kind}"
                      rejected := rejected + 1
  unless comparisons == 32256 && rejected == 18432 && controls == 2304 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/word conditional loop Boolean-input-helper Id-input syntax comparisons, {rejected} invalid-input tests and {controls} direct-plan and unused-helper controls passed"

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
                        let selected : BooleanLocal := .var 0 (flagIndex + depth)
                        let mut current := WordRange.choiceExpr .word selected.condition selected.evidence body
                          (add (.bvar (wordIndex + depth)) (literalExpr 13))
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
                      let some plan := extractScalarWordRangeWith (publicBindings kinds) 2 unwrapped |
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
                        let expected := if flag then expected else rawWord + 13
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
  Lean.logInfo m!"{comparisons} native/word conditional loop Boolean-result-helper Id-input syntax comparisons, {rejected} invalid-input tests and {controls} direct-plan and unused-helper controls passed"

-- many helpers
run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let multiply (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mul []) a) b
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
  for arity in ([2, 3, 5] : List Nat) do
    let apply (function : Lean.Expr) (arguments : List Lean.Expr) := arguments.foldl Lean.Expr.app function
    let arguments (first : Lean.Expr) := first :: (List.range (arity - 1)).map (fun j => literalExpr (j + 2))
    for depth in ([1, 2] : List Nat) do
      for annotationDepth in ([0, 2] : List Nat) do
        for flagFirst in [false, true] do
          let domains := if flagFirst then [boolean, word] else [word, boolean]
          let resultType := (List.range annotationDepth).foldl (fun value _ => ResultType.identity value) .word
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
                    let advanced := apply (.bvar 2) (arguments (add (.bvar 0) (indexWord 1)))
                    let step := if kind == 0 then choose.branch (Step.resultType .word)
                        (Step.yieldDirect advanced) (Step.yieldDirect (add (.bvar 0) (literalExpr 3)))
                      else if kind == 1 then choose.branch (Step.resultType .word)
                        (Step.doneDirect (add (.bvar 0) (literalExpr 7))) (Step.yieldDirect advanced)
                      else skip.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                    let loop := Range.call (modWord (.bvar (wordIndex + depth)) (literalExpr 17))
                      (apply (.bvar 0) (arguments (.bvar (wordIndex + depth)))) `i `a valueBinder valueBinder step
                    let equal : BooleanLocal := .compare .eq (.bvar 0)
                      (apply (.bvar 1) (arguments (.bvar (wordIndex + depth + 1))))
                    let tail : BooleanLocal := if tailForm == 0 then equal
                      else if tailForm == 1 then .junction 0 .disjunction equal (.var 0 (flagIndex + depth + 1))
                      else .binding 0 `saved (.letE nondep) equal (.var 1 0)
                    let result (tail : Lean.Expr) := Lean.Expr.letE `flag boolean
                      (.letE `value word loop tail nondep)
                      (add (toWord (.bvar 0)) (add (.bvar (wordIndex + depth + 1)) (literalExpr 7))) nondep
                    let parameters := (List.range arity).foldl
                      (fun sum j => add sum (multiply (literalExpr (j + 1)) (.bvar (arity - 1 - j)))) (literalExpr 0)
                    let first := add (add parameters (.bvar (wordIndex + arity))) (toWord (.bvar (flagIndex + arity)))
                    let setupSource (first body : Lean.Expr) := Id.run do
                      let selected : BooleanLocal := .var 0 (flagIndex + depth)
                      let mut current := WordRange.choiceExpr .word selected.condition selected.evidence body
                        (add (.bvar (wordIndex + depth)) (literalExpr 13))
                      for offset in (List.range depth).reverse do
                        let value := if offset == 0 then first
                          else add (apply (.bvar arity) ((List.range arity).map
                          (fun j => add (.bvar (arity - 1 - j)) (literalExpr (j + 1))))) (.bvar (wordIndex + offset + arity))
                        current := Lean.Expr.letE `helper
                          ((List.range arity).foldr (fun _ tail => .forallE `x word tail typeBinder) resultType.expr)
                          ((List.range arity).foldr (fun _ tail => .lam `x word tail valueBinder) (Identity.pure value resultType)) current nondep
                      return wrap current
                    let source := setupSource first (result tail.expr)
                    let some func := extractScalarFunc `booleanLoopManyHelpers (some "entry") signature source |
                      throwError "multiple-argument helper rejected: {depth}, {annotationDepth}, {flagFirst}, {kind}, {tailForm}"
                    let some unwrapped := collectLambdas source 2 | throwError "missing parameters"
                    let kinds := if flagFirst then [PublicArgument.boolean, .word] else [.word, .boolean]
                    let some plan := extractScalarWordRangeWith (publicBindings kinds) 2 unwrapped |
                      throwError "direct word helper path rejected"
                    let direct := plan.func `booleanLoopManyHelpers (some "entry") 2
                    unless direct == func do throwError "public and direct word helper plans differ"
                    controls := controls + 1
                    let directModule : LeanExe.IR.Module := { funcs := #[direct] }
                    let extra (input domain output value : Lean.Expr) := wrap (.letE `unused
                      ((List.range arity).foldr (fun _ tail => .forallE `x input tail typeBinder) output)
                      ((List.range arity).foldr (fun _ tail => .lam `x domain tail valueBinder) value)
                      (unwrapped.liftLooseBVars 0 1) nondep)
                    let some control := extractScalarFunc `booleanLoopManyHelpers (some "entry") signature
                        (extra word word resultType.expr (Identity.pure first resultType)) |
                      throwError "valid unused helper rejected"
                    unless control == func do throwError "unused helper changes compiled loop"
                    controls := controls + 1
                    let module_ : LeanExe.IR.Module := { funcs := #[func] }
                    for (x, y) in inputs do
                      let rawFlag := if flagFirst then x else y
                      let rawWord := if flagFirst then y else x
                      let flag := rawFlag != 0
                      let nativeArguments (first : UInt64) := first :: (List.range (arity - 1)).map (fun j => UInt64.ofNat (j + 2))
                      let f : List UInt64 → UInt64 := (List.range (depth - 1)).foldl
                        (fun previous _ => fun values => previous (values.zipIdx.map (fun (value, j) => value + UInt64.ofNat (j + 1))) + rawWord)
                        (fun values => (values.zipIdx.foldl (fun sum (value, j) => sum + UInt64.ofNat (j + 1) * value) 0) + rawWord + flag.toUInt64)
                      let initial := f (nativeArguments rawWord)
                      let value : UInt64 := Id.run <| forIn (m := Id) [:(rawWord % 17).toNat] initial fun i a =>
                        if kind == 0 then .yield (if flag then f (nativeArguments (a + i.toUInt64)) else a + 3)
                        else if kind == 1 then
                          if flag then .done (a + 7) else .yield (f (nativeArguments (a + i.toUInt64)))
                        else .yield (if flag && i % 2 == 0 then a else f (nativeArguments (a + i.toUInt64)))
                      let same := value == initial
                      let expected := (if tailForm == 0 then same else if tailForm == 1 then same || flag else !same).toUInt64 + rawWord + 7
                      let expected := if flag then expected else rawWord + 13
                      let actual := module_.evalFunc 0 [x, y]
                      unless actual == expected && directModule.evalFunc 0 [x, y] == expected do
                        throwError "multiple-argument helper result: {actual}, expected {expected}"
                      comparisons := comparisons + 2
                    let firstFlag : BooleanLocalGuard := { value := .var 0 (flagIndex + arity), expanded := rfl }
                    let bad := Lean.Expr.const `unsupportedManyHelpers []
                    let invalid := [
                      setupSource bad (result tail.expr),
                      setupSource (.bvar (flagIndex + arity)) (result tail.expr),
                      setupSource (.bvar 99) (result tail.expr),
                      setupSource (firstFlag.branch word first bad) (result tail.expr),
                      setupSource (.letE `unused word (.bvar (flagIndex + arity)) (first.liftLooseBVars 0 1) nondep) (result tail.expr),
                      setupSource first (result (.bvar 0)),
                      extra boolean word resultType.expr first,
                      extra word boolean resultType.expr first,
                      extra word word boolean first,
                      extra word word (.app (.const ``Id [.succ .zero]) word) first,
                      extra word word (.app (.const `CustomId [.zero]) word) first,
                      extra word word resultType.expr bad]
                    for value in invalid do
                      if (extractScalarFunc `invalidBooleanLoopManyHelpers (some "entry") signature value).isSome then
                        throwError "invalid multiple-argument helper accepted: {depth}, {kind}"
                      rejected := rejected + 1
  unless comparisons == 48384 && rejected == 20736 && controls == 3456 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/word conditional loop multiple-argument-helper syntax comparisons, {rejected} invalid-input tests and {controls} direct-plan and unused-helper controls passed"

-- unit helpers
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
  for unitForm in ([.unit, .punit] : List UnitSyntax) do
    for depth in ([1, 2] : List Nat) do
      for annotationDepth in ([0, 2] : List Nat) do
        for flagFirst in [false, true] do
          let domains := if flagFirst then [boolean, word] else [word, boolean]
          let resultType := (List.range annotationDepth).foldl (fun value _ => ResultType.identity value) .word
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
                    let advanced := Lean.Expr.app (.app (.bvar 2) unitForm.value) (add (.bvar 0) (indexWord 1))
                    let step := if kind == 0 then choose.branch (Step.resultType .word)
                        (Step.yieldDirect advanced) (Step.yieldDirect (add (.bvar 0) (literalExpr 3)))
                      else if kind == 1 then choose.branch (Step.resultType .word)
                        (Step.doneDirect (add (.bvar 0) (literalExpr 7))) (Step.yieldDirect advanced)
                      else skip.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                    let loop := Range.call (modWord (.bvar (wordIndex + depth)) (literalExpr 17))
                      (.app (.app (.bvar 0) unitForm.value) (.bvar (wordIndex + depth))) `i `a valueBinder valueBinder step
                    let equal : BooleanLocal := .compare .eq (.bvar 0)
                      (.app (.app (.bvar 1) unitForm.value) (.bvar (wordIndex + depth + 1)))
                    let tail : BooleanLocal := if tailForm == 0 then equal
                      else if tailForm == 1 then .junction 0 .disjunction equal (.var 0 (flagIndex + depth + 1))
                      else .binding 0 `saved (.letE nondep) equal (.var 1 0)
                    let result (tail : Lean.Expr) := Lean.Expr.letE `flag boolean
                      (.letE `value word loop tail nondep)
                      (add (toWord (.bvar 0)) (add (.bvar (wordIndex + depth + 1)) (literalExpr 7))) nondep
                    let first := add (add (.bvar 0) (.bvar (wordIndex + 2))) (toWord (.bvar (flagIndex + 2)))
                    let setupSource (first body : Lean.Expr) := Id.run do
                      let selected : BooleanLocal := .var 0 (flagIndex + depth)
                      let mut current := WordRange.choiceExpr .word selected.condition selected.evidence body
                        (add (.bvar (wordIndex + depth)) (literalExpr 13))
                      for offset in (List.range depth).reverse do
                        let value := if offset == 0 then first
                          else add (.app (.app (.bvar 2) unitForm.value) (add (.bvar 0) (literalExpr 3))) (.bvar (wordIndex + offset + 2))
                        current := Lean.Expr.letE `helper (.forallE `unit unitForm.type (.forallE `x word resultType.expr typeBinder) typeBinder)
                          (.lam `unit unitForm.type (.lam `x word (Identity.pure value resultType) valueBinder) valueBinder) current nondep
                      return wrap current
                    let source := setupSource first (result tail.expr)
                    let some func := extractScalarFunc `booleanLoopUnitHelpers (some "entry") signature source |
                      throwError "Unit-prefixed helper rejected: {depth}, {annotationDepth}, {flagFirst}, {kind}, {tailForm}"
                    let some unwrapped := collectLambdas source 2 | throwError "missing parameters"
                    let kinds := if flagFirst then [PublicArgument.boolean, .word] else [.word, .boolean]
                    let some plan := extractScalarWordRangeWith (publicBindings kinds) 2 unwrapped |
                      throwError "direct word helper path rejected"
                    let direct := plan.func `booleanLoopUnitHelpers (some "entry") 2
                    unless direct == func do throwError "public and direct word helper plans differ"
                    controls := controls + 1
                    let directModule : LeanExe.IR.Module := { funcs := #[direct] }
                    let extra (unitInput unitDomain input domain output value : Lean.Expr) := wrap (.letE `unused
                      (.forallE `unit unitInput (.forallE `x input output typeBinder) typeBinder)
                      (.lam `unit unitDomain (.lam `x domain value valueBinder) valueBinder)
                      (unwrapped.liftLooseBVars 0 1) nondep)
                    let some control := extractScalarFunc `booleanLoopUnitHelpers (some "entry") signature
                        (extra unitForm.type unitForm.type word word resultType.expr (Identity.pure first resultType)) |
                      throwError "valid unused helper rejected"
                    unless control == func do throwError "unused helper changes compiled loop"
                    controls := controls + 1
                    let module_ : LeanExe.IR.Module := { funcs := #[func] }
                    for (x, y) in inputs do
                      let rawFlag := if flagFirst then x else y
                      let rawWord := if flagFirst then y else x
                      let flag := rawFlag != 0
                      let f : UInt64 → UInt64 := (List.range (depth - 1)).foldl
                        (fun previous _ => fun value => previous (value + 3) + rawWord)
                        (fun value => value + rawWord + flag.toUInt64)
                      let initial := f rawWord
                      let value : UInt64 := Id.run <| forIn (m := Id) [:(rawWord % 17).toNat] initial fun i a =>
                        if kind == 0 then .yield (if flag then f (a + i.toUInt64) else a + 3)
                        else if kind == 1 then
                          if flag then .done (a + 7) else .yield (f (a + i.toUInt64))
                        else .yield (if flag && i % 2 == 0 then a else f (a + i.toUInt64))
                      let same := value == initial
                      let expected := (if tailForm == 0 then same else if tailForm == 1 then same || flag else !same).toUInt64 + rawWord + 7
                      let expected := if flag then expected else rawWord + 13
                      let actual := module_.evalFunc 0 [x, y]
                      unless actual == expected && directModule.evalFunc 0 [x, y] == expected do
                        throwError "Unit-prefixed helper result: {actual}, expected {expected}"
                      comparisons := comparisons + 2
                    let firstFlag : BooleanLocalGuard := { value := .var 0 (flagIndex + 2), expanded := rfl }
                    let bad := Lean.Expr.const `unsupportedUnitHelpers []
                    let invalid := [
                      setupSource bad (result tail.expr),
                      setupSource (.bvar (flagIndex + 2)) (result tail.expr),
                      setupSource (.bvar 99) (result tail.expr),
                      setupSource (firstFlag.branch word first bad) (result tail.expr),
                      setupSource (.letE `unused word (.bvar (flagIndex + 2)) (first.liftLooseBVars 0 1) nondep) (result tail.expr),
                      setupSource first (result (.bvar 0)),
                      extra unitForm.type unitForm.type boolean word resultType.expr first,
                      extra unitForm.type unitForm.type word boolean resultType.expr first,
                      extra unitForm.type unitForm.type word word boolean first,
                      extra unitForm.type unitForm.type word word (.app (.const ``Id [.succ .zero]) word) first,
                      extra unitForm.type unitForm.type word word (.app (.const `CustomId [.zero]) word) first,
                      extra unitForm.type unitForm.type word word resultType.expr bad,
                      setupSource (.bvar 1) (result tail.expr),
                      extra (.const ``PUnit [.zero]) (.const ``PUnit [.zero]) word word resultType.expr first,
                      extra (.const `CustomUnit []) (.const `CustomUnit []) word word resultType.expr first,
                      extra unitForm.type boolean word word resultType.expr first]
                    for value in invalid do
                      if (extractScalarFunc `invalidBooleanLoopUnitHelpers (some "entry") signature value).isSome then
                        throwError "invalid Unit-prefixed helper accepted: {depth}, {kind}"
                      rejected := rejected + 1
  unless comparisons == 32256 && rejected == 18432 && controls == 2304 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/word conditional loop Unit-prefixed-helper syntax comparisons, {rejected} invalid-input tests and {controls} direct-plan and unused-helper controls passed"
