import Verified.Reflect.Definitions
import Verified.Reflect.RecursiveMatch
import Mathlib.Tactic.FinCases

namespace Verified.Reflect

open Lean Meta Elab Command

private def fieldFamily (values : Array Term) : CommandElabM Term := do
  `(([$values,*]).get)

open Lean.Parser.Term in
/-- `toTree` and `fromTree` between a recursive type and `Tree` of its shape, the laws that they
are inverse, and the agreement of the type's `Encode` instance with `Tree.toNode`. -/
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
  let shape ← shapeTerm layout.shape
  let records := layout.shape.records
  let mut toAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut fromAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut rightCases : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for (ctor, kinds) in layout.ctors do
    let fields := fieldNames kinds.length
    let pattern ← `($(mkIdent ctor) $fields*)
    match layout.record? ctor with
    | none =>
      toAlts := toAlts.push (← `(matchAltExpr| | $pattern => Verified.Tree.nil rfl))
      fromAlts := fromAlts.push (← `(matchAltExpr| | .nil _ => $(mkIdent ctor)))
    | some r =>
      let record ← recordTerm layout.shape r
      let mut words : Array Term := #[]
      let mut children : Array Term := #[]
      let mut decoded : Array Term := #[]
      for i in [:fields.size] do
        let field := fields[i]!
        if kinds[i]! then
          children := children.push (← `($flatten $field))
          let k := quote (children.size - 1)
          decoded := decoded.push (← `($unflatten
            (children ⟨$k, (by decide : $k < ($shape).children $record)⟩)))
        else
          words := words.push field
          let k := quote (words.size - 1)
          decoded := decoded.push (← `(words ⟨$k, (by decide : $k < ($shape).words $record)⟩))
      toAlts := toAlts.push (← `(matchAltExpr| | $pattern =>
        Verified.Tree.node $record $(← fieldFamily words) $(← fieldFamily children)))
      fromAlts := fromAlts.push (← `(matchAltExpr| | .node ⟨$(quote r.val), _⟩ words children =>
        $(mkIdent ctor) $decoded*))
      rightCases := rightCases.push (← `(matchAltExpr| | ⟨$(quote r.val), _⟩, words, children, ih =>
        by
          simp only [$unflatten:term, $flatten:term, Verified.listCell]
          congr 1 <;> funext i <;> fin_cases i <;> simp [ih, List.get] <;> rfl))
  let recordsCount : Term ← `(($shape).records)
  let outOfRange ← `(by
    have : $recordsCount = $(quote records) := by decide
    omega)
  if layout.null?.isNone then
    fromAlts := fromAlts.push (← `(matchAltExpr| | .nil h => absurd h (by decide)))
  fromAlts := fromAlts.push (← `(matchAltExpr| | .node ⟨_ + $(quote records), h⟩ _ _ =>
    absurd h $outOfRange))
  rightCases := rightCases.push (← `(matchAltExpr| | ⟨_ + $(quote records), h⟩, _, _, _ =>
    absurd h $outOfRange))
  elabCommand (← `(def $flatten : $native → Verified.Tree $shape := fun value =>
    match value with $toAlts:matchAlt*))
  elabCommand (← `(def $unflatten : Verified.Tree $shape → $native := fun value =>
    match value with $fromAlts:matchAlt*))
  elabCommand (← `(theorem $left (value : $native) : $unflatten ($flatten value) = value := by
    induction value <;> simp_all [$flatten:term, $unflatten:term, Verified.listCell, List.get]))
  let nilCase ← if layout.null?.isSome then `(tactic| rfl)
    else `(tactic| exact absurd h (by decide))
  elabCommand (← `(theorem $right (value : Verified.Tree $shape) :
      $flatten ($unflatten value) = value := by
    induction value with
    | nil h => $nilCase:tactic
    | node r words children ih =>
      exact match r, words, children, ih with $rightCases:matchAlt*))
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
    induction value <;> simp_all only [LeanExe.Pipeline.Encode.encode, $encode:term,
      $flatten:term] <;> rfl))

def prepareRecursiveTypes (names : Array Name) : CommandElabM Unit := do
  let mut types : List Name := []
  for name in names do
    let info ← getConstInfo name
    for type in info.type.getUsedConstants do
      unless types.contains type do
        types := type :: types
        if let some layout ← liftTermElabM (recursiveLayout? (mkConst type)) then
          deriveRecursiveType layout
          deriveRecursiveMatch layout

end Verified.Reflect
