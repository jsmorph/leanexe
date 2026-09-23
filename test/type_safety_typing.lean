import LeanExe.TypeSafety

/-!
Executable typing regressions. Raw inference and public admission deliberately
have different ambient-formation boundaries. These examples exercise that
distinction, exact source types, and rejection of malformed unused inputs.
-/

namespace LeanExe.TypeSafety.TypingTests

example : infer [] [] [] .unit = some .unit := by rfl
example : infer [] [] [] (.bool true) = some .bool := by rfl
example : infer [] [] [] (.nat (nat64Limit - 1)) = some .nat64 := by rfl
example : infer [] [] [] (.nat nat64Limit) = none := by rfl
example : infer [] [] [] (.var 0) = none := by rfl
example : infer [] [] [.nat64] (.var 0) = some .nat64 := by rfl

-- Sum alternatives are explicit and contribute to the exact inferred type.
example : infer [] [] [] (.inl .bool (.nat 7)) = some (.sum .nat64 .bool) := by rfl
example : infer [] [] [] (.inr .nat64 (.bool true)) = some (.sum .nat64 .bool) := by rfl
example : infer [] [] [] (.inl (.data 0) (.nat 7)) = none := by rfl
example : infer [] [] [] (.sumCase (.inl .unit (.nat 7))
    (.var 0) (.unitCase (.var 0) (.nat 0))) = some .nat64 := by rfl
example : infer [] [] [] (.sumCase (.inl .unit (.nat 7))
    (.var 0) (.bool true)) = none := by rfl

-- Branch consistency, eliminator shapes, and local binding are checked.
example : infer [] [] [] (.ifE (.bool true) (.nat 1) (.bool false)) = none := by rfl
example : infer [] [] [] (.ifE (.nat 0) (.nat 1) (.nat 2)) = none := by rfl
example : infer [] [] [] (.letE (.nat 1) (.add (.var 0) (.var 0))) = some .nat64 := by rfl
example : infer [] [] [] (.split (.pair (.nat 1) (.bool true))
    (.pair (.var 1) (.var 0))) = some (.prod .bool .nat64) := by rfl
example : infer [] [] [] (.unitCase (.nat 1) .unit) = none := by rfl
example : infer [] [] [] (.fst (.nat 1)) = none := by rfl

-- Checked array results retain precise element types.
example : infer [] [] [] (.arrayEmpty .nat64) = some (.array .nat64) := by rfl
example : infer [] [] [] (.arrayGet? (.arrayEmpty .nat64) (.nat 0)) =
    some (.sum .unit .nat64) := by rfl
example : infer [] [] [] (.arraySet? (.arrayEmpty .nat64) (.nat 0) (.nat 9)) =
    some (.sum .unit (.array .nat64)) := by rfl
example : infer [] [] [] (.arraySize .unit) = none := by rfl
example : infer [] [] [] (.arrayGet? (.arrayEmpty .nat64) (.bool true)) = none := by rfl
example : infer [] [] [] (.arrayPush? (.arrayEmpty .bool) (.nat 1)) = none := by rfl
example : infer [] [] [] (.arrayAppend? (.arrayEmpty .bool) (.arrayEmpty .nat64)) = none := by rfl

-- Raw judgments do not validate their ambient inputs; public admission does.
example : inferRaw [] [] [.data 0] (.var 0) = some (.data 0) := by rfl
example : infer [] [] [.data 0] (.var 0) = none := by rfl
example : inferRaw [] [] [.data 0] .unit = some .unit := by rfl
example : infer [] [] [.data 0] .unit = none := by rfl
example : infer [] [⟨[], .data 0⟩] [] .unit = none := by rfl
example : infer [[[.data 1]]] [] [] .unit = none := by rfl

def oneNatSignature : Signatures := [⟨[.nat64], .nat64⟩]
example : infer [] oneNatSignature [] (.call 0 [.nat 7]) = some .nat64 := by rfl
example : infer [] oneNatSignature [] (.call 1 [.nat 7]) = none := by rfl
example : infer [] oneNatSignature [] (.call 0 []) = none := by rfl
example : infer [] oneNatSignature [] (.call 0 [.nat 7, .nat 8]) = none := by rfl
example : infer [] oneNatSignature [] (.call 0 [.bool true]) = none := by rfl

def voidDecls : DataDecls := [[]]
def pairDecls : DataDecls := [[[.nat64, .bool]]]
def twoDecls : DataDecls := [[[], []]]

example : infer voidDecls [] [.data 0] (.dataCase 0 .nat64 (.var 0) []) =
    some .nat64 := by rfl
example : infer voidDecls [] [] (.arrayEmpty (.data 0)) = some (.array (.data 0)) := by rfl
example : infer voidDecls [] [.data 0] (.dataCase 0 (.data 1) (.var 0) []) = none := by rfl
example : infer pairDecls [] [] (.dataCtor 0 0 [.nat 7, .bool true]) = some (.data 0) := by rfl
example : infer pairDecls [] [] (.dataCtor 0 0 [.nat 7]) = none := by rfl
example : infer pairDecls [] [] (.dataCtor 0 1 []) = none := by rfl
example : infer pairDecls [] [] (.dataCtor 0 0 [.bool true, .nat 7]) = none := by rfl
example : infer pairDecls [] [.data 0] (.dataCase 0 .bool (.var 0) [(2, .var 1)]) =
    some .bool := by rfl
example : infer pairDecls [] [.data 0] (.dataCase 0 .bool (.var 0) [(1, .var 0)]) = none := by rfl
example : infer pairDecls [] [.data 0] (.dataCase 0 .nat64 (.var 0) []) = none := by rfl
example : infer pairDecls [] [.data 0] (.dataCase 0 .nat64 (.var 0)
    [(2, .var 0), (0, .nat 0)]) = none := by rfl
example : infer twoDecls [] [] (.dataCase 0 .nat64 (.dataCtor 0 0 [])
    [(0, .nat 7), (0, .bool true)]) = none := by rfl

-- Whole-program checking includes exact alignment and all ambient formation.
example : programWellTyped [] [] [] = true := by rfl
example : programWellTyped [] [.var 0] oneNatSignature = true := by rfl
example : programWellTyped [] [] oneNatSignature = false := by rfl
example : programWellTyped [] [.unit] [] = false := by rfl
example : programWellTyped [] [.bool true] oneNatSignature = false := by rfl
example : programWellTyped [] [.unit] [⟨[.data 0], .unit⟩] = false := by rfl
example : programWellTyped [[[.data 1]]] [.unit] [⟨[], .unit⟩] = false := by rfl

-- Well-typed general recursion is accepted without a termination claim.
example : programWellTyped [] [.call 0 []] [⟨[], .unit⟩] = true := by rfl
example : profileProgramWellTyped [] [.call 0 []] [⟨[], .unit⟩] = true := by rfl

-- Relevance is a further source restriction, separate from ordinary typing.
example : programWellTyped [] [.nat 7] oneNatSignature = true := by rfl
example : profileProgramWellTyped [] [.nat 7] oneNatSignature = false := by rfl
example : profileProgramWellTyped [] [.add (.var 0) (.var 0)] oneNatSignature = true := by rfl
example : profileExpressionWellTyped [] [] [] (.letE (.nat 1) (.nat 2)) .nat64 = false := by rfl
example : profileExpressionWellTyped [] [] []
    (.letE (.nat 1) (.add (.var 0) (.var 0))) .nat64 = true := by rfl
example : profileExpressionWellTyped [] [] []
    (.fst (.pair (.nat 1) (.bool true))) .nat64 = false := by rfl
example : profileExpressionWellTyped pairDecls [] [.data 0]
    (.dataCase 0 .bool (.var 0) [(2, .var 1)]) .bool = false := by rfl

-- Executable admission supplies the premises of arbitrary-finite-execution safety.
example (execution : Steps [] (initial (.add (.nat 1) (.nat 2))) final) :
    StateTyped [] [] final .nat64 ∧ ¬ Stuck [] final :=
  checked_type_safety rfl rfl execution

example (execution : Steps [] (initial
    (.letE (.nat 1) (.add (.var 0) (.var 0)))) final) :
    StateTyped [] [] final .nat64 ∧ ¬ Stuck [] final :=
  profile_checked_type_safety rfl rfl execution

end LeanExe.TypeSafety.TypingTests
