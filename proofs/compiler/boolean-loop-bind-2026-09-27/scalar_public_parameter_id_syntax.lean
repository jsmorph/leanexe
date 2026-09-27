import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let mul (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mul []) a) b
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons := 0
  let mut rejected := 0
  let mut controls := 0
  for inputDepth in ([1, 3] : List Nat) do
    for arity in ([1, 2, 3] : List Nat) do
      for mask in List.range (2 ^ arity - 1) do
        let kinds := (List.range arity).map fun index => (mask + 1) / 2 ^ index % 2 == 1
        let reverse := kinds.reverse
        let booleanIndex := reverse.idxOf true
        let wordIndex := reverse.idxOf false
        for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
          for typeMetadata in [false, true] do
            for valueMetadata in [false, true] do
              for depth in ([0, 2] : List Nat) do
                for negations in ([0, 1, 2] : List Nat) do
                  let resultType (result : Lean.Expr) :=
                    let inner := (List.range depth).foldl (fun value _ => Lean.Expr.app (.const ``Id [.zero]) value) result
                    if typeMetadata then Lean.Expr.mdata {} inner else inner
                  let signature (domains : List Lean.Expr) (result : Lean.Expr) := domains.foldr
                    (fun input rest => Lean.Expr.forallE `parameter input rest binder) (resultType result)
                  let plainDomains := kinds.map fun flag => if flag then boolean else word
                  let domains := plainDomains.map fun input => (List.range inputDepth).foldl
                    (fun value _ => Lean.Expr.app (.const ``Id [.zero]) value) input
                  let wrap (value : Lean.Expr) :=
                    let lambdas := domains.foldr (fun input rest => Lean.Expr.lam `parameter input rest binder) value
                    if valueMetadata then Lean.Expr.mdata {} lambdas else lambdas
                  let weighted := (List.range arity).foldl (fun sum index =>
                    let value : Lean.Expr := if reverse[index]! then toWord (.bvar index) else .bvar index
                    add sum (mul (literalExpr (index + 2)) value)) (literalExpr 7)
                  let flag : BooleanLocal := .var negations booleanIndex
                  let body := (BooleanLocal.junction 0 .disjunction flag (.compare .eq weighted (literalExpr 7))).expr
                  let some boolFunc := extractScalarFunc `publicParameters (some "entry")
                      (signature domains boolean) (wrap body) |
                    throwError "Boolean public body rejected: {arity}, {mask}, {negations}"
                  let some convertedFunc := extractScalarFunc `publicParameters (some "entry")
                      (signature domains word) (wrap (toWord body)) |
                    throwError "converted public body rejected"
                  let some wordFunc := extractScalarFunc `publicParameters (some "entry")
                      (signature domains word) (wrap weighted) |
                    throwError "mixed public word body rejected"
                  unless boolFunc == convertedFunc && boolFunc.params == arity do
                    throwError "Boolean public result conversion differs"
                  let plainLambdas := plainDomains.foldr
                    (fun input rest => Lean.Expr.lam `parameter input rest binder) body
                  let some plainFunc := extractScalarFunc `publicParameters (some "entry")
                      (signature domains boolean) plainLambdas | throwError "equal base-domain lambda rejected"
                  unless plainFunc == boolFunc do throwError "Id-domain lambda changes IR"
                  controls := controls + 2
                  for (x, y) in inputs do
                    let args := (List.range arity).map fun index => if index % 2 == 0 then x else y
                    let raw := args.reverse
                    let decoded := (List.range arity).map fun index =>
                      if reverse[index]! then (raw[index]! != 0).toUInt64 else raw[index]!
                    let sum := (List.range arity).foldl (fun acc index =>
                      acc + UInt64.ofNat (index + 2) * decoded[index]!) 7
                    let chosen := GuardNegation.denote negations (raw[booleanIndex]! != 0)
                    let expected := (chosen || sum == 7).toUInt64
                    for (func, expected) in [(boolFunc, expected), (convertedFunc, expected), (wordFunc, sum)] do
                      let module_ : LeanExe.IR.Module := { funcs := #[func] }
                      let actual := module_.evalFunc 0 args
                      unless actual == expected do
                        throwError "public parameters {arity}/{mask}: {actual}, expected {expected}"
                      comparisons := comparisons + 1
                  let badBool := Lean.Expr.const `unsupportedPublicBool []
                  let badWord := Lean.Expr.bvar booleanIndex
                  let wrongDomains := domains.set 0 (if kinds[0]! then word else boolean)
                  let wrongLambdas := wrongDomains.foldr
                    (fun input rest => Lean.Expr.lam `parameter input rest binder) body
                  let invalidUniverse := (domains.set 0 (.const ``UInt64 [.zero])).foldr
                    (fun input rest => Lean.Expr.lam `parameter input rest binder) body
                  let invalid : List (Lean.Expr × Lean.Expr) :=
                    [(signature (domains.set 0 (.app (.const `CustomId [.zero]) boolean)) boolean, wrap body),
                     (signature (domains.set 0 (.app (.const ``Id [.zero, .zero]) boolean)) boolean, wrap body),
                     (signature (domains.set 0 (.app (.const ``Id [.zero]) (.forallE `x word boolean binder))) boolean, wrap body),
                     (signature (domains.set 0 (.mdata {} boolean)) boolean, wrap body),
                     (signature domains boolean, wrongLambdas),
                     (signature domains boolean, invalidUniverse),
                     (signature domains word, wrap badWord),
                     (signature domains boolean, wrap weighted),
                     (signature domains word, wrap (add weighted badWord)),
                     (signature domains boolean, wrap (.bvar 99)),
                     (signature domains boolean, wrap badBool),
                     (signature domains boolean, body),
                     (signature domains boolean, wrap (.lam `extra word body binder)),
                     (signature domains (.const ``Nat []), wrap body),
                     (signature domains (.const ``Bool [.zero]), wrap body),
                     (signature (domains.set 0 (.const ``Nat [])) boolean, wrap body),
                     (signature (domains.set 0 (.app (.const ``Id [.succ .zero]) boolean)) boolean, wrap body),
                     (signature (domains.set 0 (.const ``Bool [.zero])) boolean, wrap body),
                     (signature domains boolean, wrap (BooleanLocal.junction 0 .disjunction
                       (.literal 0 true) (.compare .eq badWord (literalExpr 7))).expr),
                     (signature domains boolean, wrap (.letE `unused word badWord body false))] ++
                    (if reverse.contains false then
                      [(signature domains boolean, wrap (.bvar wordIndex)),
                       (signature domains word, wrap (toWord (.bvar wordIndex)))] else [])
                  for (type, source) in invalid do
                    if (extractScalarFunc `invalidPublicParameters (some "entry") type source).isSome then
                      throwError "invalid public parameter use admitted: arity={arity}, mask={mask}"
                    rejected := rejected + 1
  unless comparisons == 88704 && rejected == 45312 && controls == 4224 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/public parameter-Id syntax comparisons, {rejected} invalid-input tests and {controls} result-conversion controls passed"
