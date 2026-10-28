import Verified.Examples.TypedTrees

/-! Every theorem of the example of trees whose records hold typed fields uses only the axioms
`propext`, `Classical.choice`, and `Quot.sound`: the theorems that `verified_compile` adds under
`compiled`, and the conversions' laws, the encodings, the well-formedness theorems, and the match
lemmas that `verified_recursive_type` derives for the recursive types.  Every recursive type of
the example has its well-formedness theorem, which shows that each record of each of its values
meets the conditions of the representation on the value alone. -/

open Lean Elab Command in
elab "check_typed_tree_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let pre := `Verified.Examples.TypedTrees
  let theorems := (← getEnv).constants.fold (init := #[]) fun acc name info =>
    if pre.isPrefixOf name && info matches .thmInfo _ then acc.push name else acc
  if theorems.size < 150 then
    throwError "found only {theorems.size} theorems under {pre}"
  let spaces := (← getEnv).constants.fold (init := #[]) fun acc name info =>
    match name, info with
    | .str space "toTree", .defnInfo _ => if pre.isPrefixOf name then acc.push space else acc
    | _, _ => acc
  if spaces.isEmpty then
    throwError "found no recursive type under {pre}"
  for space in spaces do
    unless (← getEnv).find? (space ++ `wellFormed) matches some (.thmInfo _) do
      throwError "{space} has no theorem wellFormed"
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo (m!"typed tree axiom check passed for {theorems.size} theorems and the " ++
    m!"well-formedness theorems of {spaces.size} recursive types")

check_typed_tree_axioms
