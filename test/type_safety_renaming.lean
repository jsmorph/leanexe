import LeanExe.TypeSafety

/-!
Capture-avoidance regressions. These check syntax and typing boundaries; general
operational correspondence and profile preservation are separate obligations.
-/
namespace LeanExe.TypeSafety.RenamingTests

def move : Renaming := fun index => index + 2
def merge : Renaming := fun _ => 0

example : Renaming.lift move 0 = 0 := by rfl
example : Renaming.lift move 1 = 3 := by rfl
example : Renaming.liftN 3 move 2 = 2 := by rfl
example : Renaming.liftN 3 move 3 = 5 := by rfl
example : Renaming.liftN 3 merge 5 = 3 := by rfl
example : Expr.rename move (.letE (.var 0) (.pair (.var 0) (.var 1))) =
    .letE (.var 2) (.pair (.var 0) (.var 3)) := by rfl
example : Expr.rename move (.split (.var 0) (.pair (.var 1) (.var 2))) =
    .split (.var 2) (.pair (.var 1) (.var 4)) := by rfl
example : Expr.rename move (.sumCase (.var 0) (.pair (.var 0) (.var 1)) (.var 2)) =
    .sumCase (.var 2) (.pair (.var 0) (.var 3)) (.var 4) := by rfl
example : Expr.rename move (.natCase (.var 0) (.var 1) (.pair (.var 0) (.var 2))) =
    .natCase (.var 2) (.var 3) (.pair (.var 0) (.var 4)) := by rfl
example : Expr.rename move (.unitCase (.var 0) (.var 1)) =
    .unitCase (.var 2) (.var 3) := by rfl
example : Expr.rename move (.dataCase 7 (.data 8) (.var 0)
    [(0, .var 0), (1, .pair (.var 0) (.var 1)), (3, .pair (.var 2) (.var 3))]) =
    .dataCase 7 (.data 8) (.var 2)
      [(0, .var 2), (1, .pair (.var 0) (.var 3)), (3, .pair (.var 2) (.var 5))] := by rfl

-- Variable maps do not rename nominal/function identities or type annotations.
example : Expr.rename move (.call 9 [.var 0, .var 1]) = .call 9 [.var 2, .var 3] := by rfl
example : Expr.rename move (.dataCtor 4 5 [.var 0, .var 1]) = .dataCtor 4 5 [.var 2, .var 3] := by rfl
example : Expr.rename move (.inl (.data 4) (.var 0)) = .inl (.data 4) (.var 2) := by rfl
example : Expr.rename move (.arrayEmpty (.data 4)) = .arrayEmpty (.data 4) := by rfl
example : Expr.rename move (.wordCast .w8 .w32 (.var 0)) = .wordCast .w8 .w32 (.var 2) := by rfl
example : Expr.rename move (.structEq (.var 0) (.var 1)) = .structEq (.var 2) (.var 3) := by rfl
example : Expr.rename move (.arraySet? (.var 0) (.var 1) (.var 2)) =
    .arraySet? (.var 2) (.var 3) (.var 4) := by rfl

-- Merging free variables must not capture them in a newly introduced binder.
example : Expr.rename merge (.letE (.var 2) (.pair (.var 0) (.pair (.var 1) (.var 3)))) =
    .letE (.var 0) (.pair (.var 0) (.pair (.var 1) (.var 1))) := by rfl
example : Expr.rename move (.letE (.var 0) (.letE (.var 1) (.pair (.var 1) (.var 2)))) =
    .letE (.var 2) (.letE (.var 3) (.pair (.var 1) (.var 4))) := by rfl
example : infer [] [] [.bool, .unit, .nat64]
    (Expr.rename move (.add (.var 0) (.nat 1))) = some .nat64 := by rfl
example : infer [] [] [.bool, .unit, .prod .nat64 .bool]
    (Expr.rename move (.split (.var 0) (.pair (.var 1) (.var 0)))) =
    some (.prod .bool .nat64) := by rfl

-- Forward context transport alone does not imply an equivalence of raw inference.
example : inferRaw [] [] [] (.var 4) = none := by rfl
example : inferRaw [] [] [.bool] (Expr.rename merge (.var 4)) = some .bool := by rfl
example : inferRaw [] [] [.data 99] (Expr.rename move .unit) = some .unit := by rfl
example : infer [] [] [.data 99] (Expr.rename move .unit) = none := by rfl

end LeanExe.TypeSafety.RenamingTests
