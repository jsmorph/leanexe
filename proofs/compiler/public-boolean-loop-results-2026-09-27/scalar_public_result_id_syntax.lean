import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
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
    for arity in ([0, 1, 2, 3] : List Nat) do
      for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
        for typeMetadata in [false, true] do
          for valueMetadata in [false, true] do
            for negations in [0, 1, 2] do
              for form in ([0, 1, 2, 3] : List Nat) do
                let resultType (result : Lean.Expr) :=
                  let inner := (List.range depth).foldl (fun value _ => Lean.Expr.app (.const ``Id [.zero])
                    (if typeMetadata then .mdata {} value else value)) result
                  if typeMetadata then Lean.Expr.mdata {} inner else inner
                let signature (input result : Lean.Expr) := (List.range arity).foldr
                  (fun _ rest => Lean.Expr.forallE `parameter input rest binder) (resultType result)
                let wrap (input value : Lean.Expr) :=
                  let lambdas := (List.range arity).foldr
                    (fun _ rest => Lean.Expr.lam `parameter input rest binder) value
                  if valueMetadata then Lean.Expr.mdata {} lambdas else lambdas
                let left : Lean.Expr := if arity == 0 then literalExpr 42 else .bvar 0
                let right : Lean.Expr := if arity < 2 then literalExpr 7 else .bvar (arity - 1)
                let equal : BooleanLocal := .compare .eq left right
                let value : BooleanLocal := if form == 0 then .compare .ne left right
                  else if form == 1 then .junction 0 .disjunction equal (.compare .eq left (literalExpr 0))
                  else if form == 2 then .binding 0 `flag (.letE false) equal (.var 0 0)
                  else .wordBinding 0 `word (.letE true) left
                    (.compare .eq (.bvar 0) (right.liftLooseBVars 0 1))
                let body := BooleanGuardNegation.expr negations value.expr
                let some booleanFunc := extractScalarFunc `publicResultIdSyntax (some "entry")
                    (signature word boolean) (wrap word body) |
                  throwError "public Boolean signature/body rejected at arity {arity}, form {form}"
                let some wordFunc := extractScalarFunc `publicResultIdSyntax (some "entry")
                    (signature word word) (wrap word (toWord body)) |
                  throwError "existing converted-word result rejected"
                unless booleanFunc.params == arity && booleanFunc == wordFunc do
                  throwError "public result encoding differs from explicit Boolean conversion"
                controls := controls + 1
                let arguments := if arity == 0 then [[]] else inputs.map fun (x, y) =>
                  (List.range arity).map fun index => if index % 2 == 0 then x else y
                for args in arguments do
                  let leftValue := if arity == 0 then (42 : UInt64) else args.reverse.head!
                  let rightValue := if arity < 2 then (7 : UInt64) else args.head!
                  let base := if form == 0 then leftValue != rightValue
                    else if form == 1 then leftValue == rightValue || leftValue == 0
                    else leftValue == rightValue
                  let expected := (GuardNegation.denote negations base).toUInt64
                  for func in [booleanFunc, wordFunc] do
                    let module_ : LeanExe.IR.Module := { funcs := #[func] }
                    let actual := module_.evalFunc 0 args
                    unless actual == expected && (actual == 0 || actual == 1) do
                      throwError "public result: {actual}, expected {expected}, arity {arity}"
                    comparisons := comparisons + 1
                let invalid : List (Lean.Expr × Lean.Expr) :=
                  [(signature word (.const ``Nat []), wrap word body),
                   (signature word (.app (.const ``Id [.succ .zero]) boolean), wrap word body),
                   (signature word (.const ``Bool [.zero]), wrap word body),
                   (signature word boolean, wrap word (literalExpr 7)),
                   (signature word boolean, wrap word (.const `unsupportedBooleanBody [])),
                   (signature word boolean, wrap word (.bvar 99)),
                   (signature word boolean, wrap word (.lam `extra word body .default)),
                   (signature word word, wrap word (booleanLiteralExpr true)),
                   (signature word (.app (.const `CustomId [.zero]) boolean), wrap word body),
                   (signature word (.app (.const ``Id [.zero, .zero]) boolean), wrap word body),
                   (signature word (.app (.const ``Id [.zero]) (.forallE `extra word boolean binder)), wrap word body)] ++
                  (if arity == 0 then [] else
                    [(signature boolean boolean, wrap boolean body),
                     (signature (.const ``Nat []) boolean, wrap (.const ``Nat []) body),
                     (signature word boolean, body)])
                for (type, source) in invalid do
                  if (extractScalarFunc `invalidPublicResultId (some "entry") type source).isSome then
                    throwError "invalid public result accepted at arity {arity}"
                  rejected := rejected + 1
  unless comparisons == 33024 && rejected == 20352 && controls == 1536 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/public result-Id syntax comparisons, {rejected} invalid-input tests and {controls} word-result controls passed"
