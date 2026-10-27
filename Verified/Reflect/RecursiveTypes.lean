import Verified.Reflect.Definitions
import Verified.Reflect.RecursiveMatch
import Mathlib.Tactic.FinCases

namespace Verified.Reflect

open Lean Meta Elab Command

private def fieldFamily (values : Array Term) : CommandElabM Term := do
  `(([$values,*]).get)

/-- The word family of record constructor `r` with the word fields `words` of the elements
`elems`: the list of the words when every field of the shape is a word or a child, and otherwise
`TreeShape.wordsOf`. -/
def wordFamilyTerm (shape : TreeShape) (r : Fin shape.records) (elems : Array Elem)
    (words : Array Term) : CommandElabM Term := do
  if shape.allWords then return ← `(([$words,*]).get)
  let entries ← (elems.zip words).mapM fun (e, w) => `(⟨$(quote e), $w⟩)
  `(Verified.TreeShape.wordsOf $(← shapeTerm shape) $(← recordTerm shape r) [$entries,*])

/-- How `fromTree` rebuilds a flat field from its leaves: the leaf at a position among the
field's leaves, a pair, or a structure's constructor applied to its fields. -/
inductive Rebuild where
  | leaf (k : Nat)
  | pair (a b : Rebuild)
  | ctor (name : Name) (fields : List Rebuild)

/-- The rebuilding of the component of a flat field of type `type` whose leaves have paths in the
field's flattening that extend `pre`, with `paths` the paths of the field's leaves.  A structure
rebuilds when its `Flat` tuple holds each field, and an enumeration or a sum does not rebuild. -/
partial def rebuild? (type : Lean.Expr) (pre : List Bool) (paths : List (List Bool)) :
    MetaM (Option Rebuild) := do
  let type ← withReducible (whnf type)
  if (fieldElem? type).isSome then return (paths.findIdx? (· == pre)).map .leaf
  if let (``Prod, #[a, b]) := type.getAppFnArgs then
    let some ra ← rebuild? a (pre ++ [false]) paths | return none
    let some rb ← rebuild? b (pre ++ [true]) paths | return none
    return some (.pair ra rb)
  let some (ctor, _) ← structOf? type | return none
  let some (β, inst) ← flatInstance? type | return none
  let tree ← flatTree type β inst ctor
  let fieldTypes ← forallTelescope ctor.type fun xs _ => xs.toList.mapM inferType
  let mut fields := []
  for (fieldType, j) in fieldTypes.zipIdx do
    let some (_, steps) := tree.find? (·.1 == j) | return none
    let some field ← rebuild? fieldType (pre ++ steps) paths | return none
    fields := fields ++ [field]
  return some (.ctor ctor.name fields)

/-- The term that `rebuild` gives with the word of position `k` among the field's leaves as
`word k`. -/
partial def Rebuild.term (word : Nat → CommandElabM Term) : Rebuild → CommandElabM Term
  | .leaf k => word k
  | .pair a b => do `(($(← a.term word), $(← b.term word)))
  | .ctor name fields => do `($(mkCIdent name) $(← fields.toArray.mapM (·.term word))*)

open Lean.Parser.Term in
/-- `toTree` from a recursive type to `Tree` of its shape and the agreement of the type's `Encode`
instance with `Tree.toNode`, and, unless a field holds an enumeration or a sum, `fromTree` and the
laws that `toTree` and `fromTree` are inverse. -/
def deriveRecursiveType (layout : RecursiveLayout) : CommandElabM Unit :=
    withScope (fun scope => { scope with currNamespace := .anonymous }) do
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
  let mut inverse := true
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
      let mut elems : Array Elem := #[]
      let mut children : Array Term := #[]
      let mut decoded : Array Term := #[]
      for i in [:fields.size] do
        let field := fields[i]!
        let wordAt (k : Nat) : CommandElabM Term :=
          `(words ⟨$(quote k), (by decide : $(quote k) < ($shape).words $record)⟩)
        match kinds[i]! with
        | .child =>
          children := children.push (← `($flatten $field))
          let k := quote (children.size - 1)
          decoded := decoded.push (← `($unflatten
            (children ⟨$k, (by decide : $k < ($shape).children $record)⟩)))
        | .leaf _ => decoded := decoded.push (← wordAt words.size)
        | .flat type leaves =>
          let paths := leaves.map fun (_, segments) => segments.flatten
          match ← liftTermElabM (rebuild? type [] paths) with
          | some rebuild =>
            let start := words.size
            decoded := decoded.push (← rebuild.term fun k => wordAt (start + k))
          | none => inverse := false
        for (e, w) in ← nativeWordTerms field kinds[i]! do
          words := words.push w
          elems := elems.push e
      toAlts := toAlts.push (← `(matchAltExpr| | $pattern =>
        Verified.Tree.node $record $(← wordFamilyTerm layout.shape r elems words)
          $(← fieldFamily children)))
      fromAlts := fromAlts.push (← `(matchAltExpr| | .node ⟨$(quote r.val), _⟩ words children =>
        $(mkIdent ctor) $decoded*))
      rightCases := rightCases.push (← `(matchAltExpr| | ⟨$(quote r.val), _⟩, words, children, ih =>
        by
          simp only [$unflatten:term, $flatten:term, Verified.listCell]
          congr 1 <;> funext i <;> fin_cases i <;>
            simp [ih, List.get, Verified.TreeShape.wordsOf] <;>
            first | rfl | (intro h; exact absurd rfl h)))
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
  if inverse then
    elabCommand (← `(def $unflatten : Verified.Tree $shape → $native := fun value =>
      match value with $fromAlts:matchAlt*))
    elabCommand (← `(theorem $left (value : $native) : $unflatten ($flatten value) = value := by
      induction value <;> simp_all [$flatten:term, $unflatten:term, Verified.listCell, List.get] <;>
        repeat' constructor))
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

syntax (name := verifiedRecursiveType) "verified_recursive_type " ident : command

/-- `verified_recursive_type T` derives the declarations through which `verified_compile` compiles
programs over the recursive type `T`: the conversion to the tree of `T`'s layout, the agreement of
`T`'s `Encode` instance with the layout, the lemmas of a match on `T`, and, unless a field of `T`
holds an enumeration or a sum, the conversion back and the laws that the two are inverse.  The
command follows `T`'s `Encode` instance, once, and every module that compiles a program over `T`
imports the module that runs it. -/
@[command_elab verifiedRecursiveType]
def elabVerifiedRecursiveType : CommandElab
  | `(verified_recursive_type $type) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo type
    let some layout ← liftTermElabM (recursiveLayout? (mkConst name))
      | throwError "verified_recursive_type: {name} is not a recursive type that the compiler \
          supports"
    if (← getEnv).contains (layout.decl `toTree) then
      throwError "verified_recursive_type: {name} already has its declarations"
    deriveRecursiveType layout
    deriveRecursiveMatch layout
  | _ => throwUnsupportedSyntax

/-- Checks that each recursive type that the types of the definitions `names` use, directly or
through the `Flat` tuple of a sum, has the declarations of `verified_recursive_type`. -/
def requireRecursiveTypes (names : Array Name) : CommandElabM Unit := do
  let mut types : List Name := []
  let mut pending : List Name := []
  for name in names do
    pending := pending ++ (← getConstInfo name).type.getUsedConstants.toList
  repeat
    let type :: rest := pending | break
    pending := rest
    if types.contains type then continue
    types := type :: types
    if let some layout ← liftTermElabM (recursiveLayout? (mkConst type)) then
      unless (← getEnv).contains (layout.decl `toTree) do
        throwError "verified_compile: {type} needs `verified_recursive_type {type}` after its \
          `Encode` instance, in a module that the program imports"
    let tuple ← liftTermElabM do
      if (← sumName? (mkConst type)).isNone then return none
      return (← flatInstance? (mkConst type)).map (·.1)
    if let some β := tuple then
      pending := pending ++ β.getUsedConstants.toList

end Verified.Reflect
