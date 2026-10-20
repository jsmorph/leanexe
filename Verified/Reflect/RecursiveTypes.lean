import Verified.Reflect.Definitions
import Mathlib.Tactic.FinCases

namespace Verified.Reflect

open Lean Meta Elab Command

private def fieldFamily (values : Array Term) : CommandElabM Term := do
  `(([$values,*]).get)

def deriveRecursiveType (layout : RecursiveLayout) : CommandElabM Unit :=
    withScope (fun scope => { scope with currNamespace := .anonymous }) do
  if (← getEnv).contains (layout.decl `toTree) then return
  let root (name : Name) := mkIdent name
  let flatten := root (layout.decl `toTree)
  let unflatten := root (layout.decl `fromTree)
  let left := root (layout.decl `from_to)
  let right := root (layout.decl `to_from)
  let encoding := root (layout.decl `encoding)
  let native := root layout.name
  let empty := root layout.empty
  let node := root layout.node
  let shape : Term ← if layout.shape = listShape then `(Verified.listShape)
    else `(Verified.Reflect.reflectedTreeShape $(quote layout.shape.fields) rfl)
  let fields := (List.range layout.shape.fields.length).toArray.map fun i =>
    mkIdent (Name.mkSimple s!"field{i}")
  let mut words : Array Term := #[]
  let mut children : Array Term := #[]
  let mut decoded : Array Term := #[]
  for i in [:fields.size] do
    let field := fields[i]!
    if layout.shape.fields[i]! then
      children := children.push (← `($flatten $field))
      decoded := decoded.push (← `($unflatten (children ⟨$(quote (children.size - 1)), by decide⟩)))
    else
      words := words.push field
      decoded := decoded.push (← `(words ⟨$(quote (words.size - 1)), by decide⟩))
  let wordFn ← fieldFamily words
  let childFn ← fieldFamily children
  let pattern ← `($node $fields*)
  let value ← `($node $decoded*)
  elabCommand (← `(def $flatten : $native → Verified.Tree $shape
    | $empty => Verified.Tree.nil
    | $pattern => Verified.Tree.node $wordFn $childFn))
  elabCommand (← `(def $unflatten : Verified.Tree $shape → $native
    | .nil => $empty
    | .node words children => $value))
  elabCommand (← `(theorem $left (value : $native) : $unflatten ($flatten value) = value := by
    induction value <;> simp_all [$flatten:term, $unflatten:term, List.get]))
  elabCommand (← `(theorem $right (value : Verified.Tree $shape) : $flatten ($unflatten value) = value := by
    induction value with
    | nil => rfl
    | node words children ih =>
      simp only [$unflatten:term, $flatten:term]
      congr 1 <;> funext i <;> fin_cases i <;> simp [ih, List.get] <;> rfl))
  let encodeFn ← liftTermElabM do
    let type := mkConst layout.name
    let inst ← synthInstance (mkApp (mkConst ``LeanExe.Pipeline.Encode) type)
    let encode ← mkAppOptM ``LeanExe.Pipeline.Encode.encode #[some type, some inst]
    withTransparency .instances (whnf encode)
  let .const encodeName _ := encodeFn.getAppFn
    | throwError "verified_compile: recursive encoding of {layout.name} must name its function"
  let encode := mkIdent encodeName
  elabCommand (← `(theorem $encoding (value : $native) :
      LeanExe.Pipeline.Encode.encode value = ($flatten value).toNode := by
    induction value <;> simp_all [LeanExe.Pipeline.Encode.encode, $encode:term, $flatten:term,
      Verified.Tree.toNode, Verified.treeSlots, Verified.listShape,
      Verified.Reflect.reflectedTreeShape, Verified.TreeShape.words, Verified.TreeShape.children,
      List.get]))

def prepareRecursiveTypes (names : Array Name) : CommandElabM Unit := do
  let mut types : List Name := []
  for name in names do
    let info ← getConstInfo name
    for type in info.type.getUsedConstants do
      unless types.contains type do
        types := type :: types
        if let some layout ← liftTermElabM (recursiveLayout? (mkConst type)) then
          deriveRecursiveType layout

end Verified.Reflect
