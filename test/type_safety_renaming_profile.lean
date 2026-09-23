import LeanExe.TypeSafety

/-!
Renaming preserves introduced-binding relevance even when free variables merge.
It does not make newly inserted function parameters used.
-/
namespace LeanExe.TypeSafety.RenamingProfileTests

def merge : Renaming := fun _ => 0
def shift : Renaming := fun index => index + 2

def freePair : Expr := .pair (.var 1) (.var 2)
example : uses 0 freePair = false := by rfl
example : uses 0 (freePair.rename merge) = true := by rfl
example : uses 1 (freePair.rename merge) = false := by rfl
example : uses 3 (freePair.rename shift) = true := by rfl
example : uses 4 (freePair.rename shift) = true := by rfl
example : uses 2 (freePair.rename shift) = false := by rfl
example : usesArgs 0 (renameArgs merge [.var 2, .var 5]) = true := by rfl
example : usesBranches 0 (renameBranches merge [(0, .var 3), (2, .var 4)]) = true := by rfl

-- Merged outer variables cannot turn an ignored local binder into a used one.
def ignoredLet : Expr := .letE .unit (.pair (.var 1) (.var 2))
def ignoredSplit : Expr := .split (.var 0) (.pair (.var 0) (.var 2))
def ignoredNatPred : Expr := .natCase (.var 0) .unit (.var 1)
def ignoredField : Expr := .dataCase 0 .unit (.var 0) [(2, .pair (.var 0) (.var 2))]
example : admissible ignoredLet = false := by rfl
example : admissible (ignoredLet.rename merge) = false := by rfl
example : admissible (ignoredSplit.rename merge) = false := by rfl
example : admissible (ignoredNatPred.rename merge) = false := by rfl
example : admissible (ignoredField.rename merge) = false := by rfl
example : admissible ((.ifE (.bool false) (.fst (.pair .unit .unit)) .unit : Expr).rename merge) =
    false := by rfl

-- Used binders survive shifts and merging; duplication and branch-local uses remain allowed.
example : admissible ((.letE .unit (.pair (.var 0) (.var 3)) : Expr).rename merge) = true := by rfl
example : admissible ((.letE .unit (.pair (.var 0) (.var 0)) : Expr).rename shift) = true := by rfl
example : admissible ((.letE .unit (.ifE (.bool true) (.var 0) .unit) : Expr).rename shift) = true := by rfl
example : admissible ((.split (.var 0) (.pair (.var 1) (.pair (.var 0) (.var 3))) : Expr).rename merge) =
    true := by rfl
example : admissible ((.dataCase 0 .unit (.var 0) [(0, .unit),
    (2, .pair (.var 0) (.pair (.var 1) (.var 4)))] : Expr).rename merge) = true := by rfl

-- Only an explicitly preserved prefix has unchanged parameter-use checks.
def prefixBody : Expr := .pair (.var 0) (.pair (.var 1) (.var 4))
example : parametersUsed 2 prefixBody = true := by rfl
example : parametersUsed 2 (prefixBody.rename (Renaming.liftN 2 merge)) = true := by rfl
example : uses 0 (Expr.rename (Renaming.liftN 2 merge) (.var 4)) = false := by rfl
example : uses 1 (Expr.rename (Renaming.liftN 2 merge) (.var 4)) = false := by rfl
example : uses 2 (Expr.rename (Renaming.liftN 2 merge) (.var 4)) = true := by rfl
example : parametersUsed 1 (.var 0) = true := by rfl
example : parametersUsed 2 (Expr.rename (fun index => index + 1) (.var 0)) = false := by rfl
example : admissible (Expr.rename (fun index => index + 1) (.var 0)) = true := by rfl

end LeanExe.TypeSafety.RenamingProfileTests
