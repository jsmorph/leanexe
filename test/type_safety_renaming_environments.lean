import LeanExe.TypeSafety

/-!
Exact environment lookup correspondence includes absent indices. The examples
exercise merging, insertion below a prefix, and the distinction from type maps.
-/
namespace LeanExe.TypeSafety.RenamingEnvironmentTests

example : EnvCorresponds (fun index => index) [.nat 7, .bool false] [.nat 7, .bool false] :=
  EnvCorresponds.refl _
example : EnvCorresponds (fun _ => 0) [] [] := EnvCorresponds.empty _
example : EnvCorresponds (fun index => index + 2) [.nat 7] [.bool true, .unit, .nat 7] :=
  EnvCorresponds.shift _ [.bool true, .unit]
example : EnvCorresponds (Renaming.liftN 2 (fun index => index + 2))
    [.nat 9, .bool false, .nat 7] [.nat 9, .bool false, .bool true, .unit, .nat 7] :=
  (EnvCorresponds.shift [.nat 7] [.bool true, .unit]).prefix [.nat 9, .bool false]

-- A merge is allowed when both present and absent lookups agree.
example : EnvCorresponds Nat.pred [.nat 7, .nat 7] [.nat 7] := by
  intro index
  cases index with
  | zero => rfl
  | succ index => cases index <;> rfl
example : ¬ EnvCorresponds Nat.pred [.nat 7, .nat 8] [.nat 7] := by
  intro corresponding
  have impossible := corresponding 1
  cases impossible
example : ¬ EnvCorresponds (fun _ => 0) [.nat 7] [.nat 7] := by
  intro corresponding
  have impossible := corresponding 1
  cases impossible
example : ¬ EnvCorresponds (fun _ => 0) [] [.unit] := by
  intro corresponding
  have impossible := corresponding 0
  cases impossible

-- Missing indices remain missing even after inserting available values.
example : lookup ([.bool true, .unit, .nat 7] : Env) (1 + 2) = none := by rfl
example : lookup ([.nat 9, .bool false, .bool true, .unit, .nat 7] : Env)
    (Renaming.liftN 2 (fun index => index + 2) 3) = none := by rfl

-- Identical raw sum values do not imply identical type contexts.
def ambiguous : Value := .inl (.nat 0)
example : ValueTyped [] ambiguous (.sum .nat64 .unit) := .inl (.nat (by decide)) .unit
example : ValueTyped [] ambiguous (.sum .nat64 .bool) := .inl (.nat (by decide)) .bool
example : EnvCorresponds (fun index => index) [ambiguous] [ambiguous] := EnvCorresponds.refl _
example : ¬ RenamingTyped [.sum .nat64 .unit] [.sum .nat64 .bool] (fun index => index) := by
  intro typed
  have impossible := typed (index := 0) rfl
  cases impossible

-- Branch lookup preserves absence, arity, and which prefix remains protected.
def branches : List (Nat × Expr) := [(0, .var 0), (2, .pair (.var 0) (.var 2))]
example : lookup (renameBranches (fun index => index + 2) branches) 0 = some (0, .var 2) := by rfl
example : lookup (renameBranches (fun index => index + 2) branches) 1 =
    some (2, .pair (.var 0) (.var 4)) := by rfl
example : lookup (renameBranches (fun index => index + 2) branches) 2 = none := by rfl

end LeanExe.TypeSafety.RenamingEnvironmentTests
