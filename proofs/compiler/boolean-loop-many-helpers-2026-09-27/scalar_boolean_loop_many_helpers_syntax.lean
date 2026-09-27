import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

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
          for typeBinder in [Lean.BinderInfo.default, .implicit] do
            for valueBinder in [Lean.BinderInfo.default, .implicit] do
              for nondep in [false, true] do
                for kind in ([0, 1, 2] : List Nat) do
                  for tailForm in ([0, 1, 2] : List Nat) do
                    let signature := domains.foldr
                      (fun input rest => Lean.Expr.forallE `parameter input rest typeBinder) boolean
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
                    let result (tail : Lean.Expr) := Lean.Expr.letE `value word loop tail nondep
                    let parameters := (List.range arity).foldl
                      (fun sum j => add sum (multiply (literalExpr (j + 1)) (.bvar (arity - 1 - j)))) (literalExpr 0)
                    let first := add (add parameters (.bvar (wordIndex + arity))) (toWord (.bvar (flagIndex + arity)))
                    let setupSource (first body : Lean.Expr) := Id.run do
                      let mut current := body
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
                      let expected := (if tailForm == 0 then same else if tailForm == 1 then same || flag else !same).toUInt64
                      let actual := module_.evalFunc 0 [x, y]
                      unless actual == expected && (actual == 0 || actual == 1) do
                        throwError "multiple-argument helper result: {actual}, expected {expected}"
                      comparisons := comparisons + 1
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
  unless comparisons == 24192 && rejected == 20736 && controls == 1728 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean loop multiple-argument-helper syntax comparisons, {rejected} invalid-input tests and {controls} unused helper controls passed"
