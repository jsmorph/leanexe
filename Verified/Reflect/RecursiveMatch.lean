import Verified.Reflect.Definitions
import Verified.Reflect.TailListLemmas

namespace Verified.Reflect

open Lean Meta Elab Command

/-- The term of a shape: `listShape`, or the shape of the constructors' field kinds. -/
def shapeTerm (shape : TreeShape) : CommandElabM Term :=
  if shape = listShape then `(Verified.listShape)
  else `(Verified.Reflect.reflectedTreeShape $(quote shape.ctors) rfl)

/-- The term of record constructor `r` of a shape. -/
def recordTerm (shape : TreeShape) (r : Fin shape.records) : CommandElabM Term := do
  if shape = listShape then `(Verified.listCell)
  else `(Verified.Reflect.reflectedRecord $(← shapeTerm shape) $(quote r.val) rfl)

/-- The Lean type of a word field's element. -/
def elemTypeTerm : Elem → CommandElabM Term
  | .word => `(UInt64)
  | .bool => `(Bool)
  | .float => `(Float)
  | .float32 => `(Float32)
  | .prod a b => do `($(← elemTypeTerm a) × $(← elemTypeTerm b))

/-- The Lean type of a field of a constructor of the recursive type `native`. -/
def nativeTypeTerm (native : Ident) : NativeField → CommandElabM Term
  | .child => pure native
  | .leaf e => elemTypeTerm e
  | .flat type _ => pure (mkCIdent type.constName!)
  | .array e => do `(Array $(← elemTypeTerm e))
  | .bytes => `(LeanExe.Bytes)

/-- The leaf of `field` with segments `segments`, as `leafTerm` builds it. -/
def leafSyntax (field : Term) (segments : List (List Bool)) : CommandElabM Term := do
  let mut term := field
  for (steps, i) in segments.zipIdx do
    if i > 0 then term ← `(LeanExe.Pipeline.Flat.flat $term)
    for step in steps do
      term ← if step then `(Prod.snd $term) else `(Prod.fst $term)
  return term

/-- The words of the field `field` of the kind `kind`, each with its element. -/
def nativeWordTerms (field : Term) : NativeField → CommandElabM (Array (Elem × Term))
  | .child | .array _ | .bytes => pure #[]
  | .leaf e => pure #[(e, field)]
  | .flat _ leaves => leaves.toArray.mapM fun (e, segments) =>
    return (e, ← leafSyntax field segments)

/-- The array family of record constructor `r` with the array fields `entries`, each a pair of an
element and a field: `TreeShape.arraysOf`, or `noFields` when the record has no array fields. -/
def arrayFamilyTerm (shape : TreeShape) (r : Fin shape.records) (entries : Array Term) :
    CommandElabM Term := do
  if entries.isEmpty then return ← `(Verified.noFields rfl)
  `(Verified.TreeShape.arraysOf $(← shapeTerm shape) $(← recordTerm shape r) [$entries,*])

/-- The buffer family of record constructor `r` with the buffer fields `buffers`: the list of
the fields, or `noFields` when the record has no buffer fields. -/
def bufferFamilyTerm (buffers : Array Term) : CommandElabM Term := do
  if buffers.isEmpty then return ← `(Verified.noFields rfl)
  `(([$buffers,*]).get)

/-- The field variables of a constructor with `n` fields. -/
def fieldNames (n : Nat) : Array Ident :=
  (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"field{i}")

/-- The pieces of one constructor in the lemmas of a match: its record constructor, when it is
one, the names and types of its fields, and its word and child families. -/
private structure CtorParts where
  record : Option Term
  fields : Array Ident
  types : Array Term
  boundEnv : Term
  deriving Inhabited

/-- The lemmas that relate a match on a recursive type to `Expr.treeCase` and
`TailBody.treeCase`: its value, cost, and frame checks, and the fixed point of a tail call. -/
def deriveRecursiveMatch (layout : RecursiveLayout) : CommandElabM Unit :=
    withScope (fun scope => { scope with currNamespace := .anonymous }) do
  let eqName := mkIdent (layout.decl `case_eq)
  if (← getEnv).contains eqName.getId then return
  let boundName := mkIdent (layout.decl `case_bound)
  let fitsName := mkIdent (layout.decl `case_fits)
  let native := mkIdent layout.name
  let flatten := mkIdent (layout.decl `toTree)
  let casesOn := mkIdent (layout.name ++ `casesOn)
  let shape ← shapeTerm layout.shape
  let parts ← layout.ctors.toArray.mapM fun (ctor, kinds) => do
    let fields := fieldNames kinds.length
    let types : Array Term ← kinds.toArray.mapM (nativeTypeTerm native)
    let mut words : Array Term := #[]
    let mut entries : Array Term := #[]
    let mut children : Array Term := #[]
    let mut arrays : Array Term := #[]
    let mut buffers : Array Term := #[]
    for i in [:fields.size] do
      if kinds[i]! matches .child then children := children.push (← `($flatten $(fields[i]!)))
      if let .array e := kinds[i]! then
        arrays := arrays.push (← `(⟨$(quote e), $(fields[i]!)⟩))
      if kinds[i]! matches .bytes then buffers := buffers.push fields[i]!
      for (e, w) in ← nativeWordTerms fields[i]! kinds[i]! do
        words := words.push w
        entries := entries.push (← `(⟨$(quote e), $w⟩))
    let record ← match layout.record? ctor with
      | none => pure none
      | some r => some <$> recordTerm layout.shape r
    let boundEnv ← match layout.record? ctor, record with
      | some r, some record =>
        let arrayFamily ← arrayFamilyTerm layout.shape r arrays
        let bufferFamily ← bufferFamilyTerm buffers
        if layout.shape.allWords then
          `(Verified.Env.treeFields $shape $record ([$words,*]).get $arrayFamily
            $bufferFamily ([$children,*]).get env)
        else
          `(Verified.Env.treeFields $shape $record
            (Verified.TreeShape.wordsOf $shape $record [$entries,*]) $arrayFamily
            $bufferFamily ([$children,*]).get env)
      | _, _ => `(env)
    return ({ record, fields, types, boundEnv } : CtorParts)
  let bindAll (part : CtorParts) (body : Term) : CommandElabM Term := do
    let mut result := body
    for i in (List.range part.fields.size).reverse do
      result ← `(∀ ($(part.fields[i]!) : $(part.types[i]!)), $result)
    return result
  let lambdaAll (part : CtorParts) (body : Term) : CommandElabM Term := do
    let mut result := body
    for i in (List.range part.fields.size).reverse do
      result ← `(fun ($(part.fields[i]!) : $(part.types[i]!)) => $result)
    return result
  let arrows (part : CtorParts) (result : Term) : CommandElabM Term := do
    let mut result := result
    for type in part.types.toList.reverse do result ← `($type → $result)
    return result
  let primitive (result value : Term) (minors : Array Term) : CommandElabM Term :=
    `($casesOn (motive := fun _ => $result) $value $minors*)
  let names (base : String) : Array Ident :=
    parts.mapIdx fun j _ => mkIdent (Name.mkSimple s!"{base}{j}")
  let branchVars := names "b"
  let hyps := names "h"
  -- The value of a match.
  let β ← `(β)
  let mut eqBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for j in [:parts.size] do
    eqBinders := eqBinders.push
      (← `(bracketedBinder| ($(branchVars[j]!) : $(← arrows parts[j]! β))))
  for j in [:parts.size] do
    let part := parts[j]!
    let b := branchVars[j]!
    let stmt ← match part.record with
      | none => `((empty rfl).denote funs env = flatten $b)
      | some record => bindAll part (← `(
          (nodes $record).denote funs $(part.boundEnv) = flatten ($b $(part.fields)*)))
    eqBinders := eqBinders.push (← `(bracketedBinder| ($(hyps[j]!) : $stmt)))
  elabCommand (← `(theorem $eqName
      {S : List Verified.Sig} {Γ : List Verified.Ty} {t : Verified.Ty}
      {funs : Verified.Funs S} {env : Verified.Env Γ} {β : Type}
      (x : Verified.Var Γ (.tree $shape))
      (empty : ($shape).hasNull = true → Verified.Expr S Γ t)
      (nodes : (r : Fin ($shape).records) → Verified.Expr S (($shape).context r Γ) t)
      (flatten : β → t.denote) (value : $native) $eqBinders*
      (hx : env.get x = $flatten value) :
      (Verified.Expr.treeCase x empty nodes).denote funs env =
        flatten $(← primitive β (← `(value)) branchVars) := by
    cases value <;> simp_all only [Verified.Expr.denote, $flatten:term]))
  -- The cost of a match.
  let resultMode ← `(Verified.recordsJoin
    (fun r => (nodes r).mode (($shape).modes r (Verified.modeAt modes x.index) modes))
    (if h : ($shape).hasNull = true then (empty h).mode modes else .borrowed))
  let costVars := names "N"
  let rootVars := names "C"
  let rootHyps := names "hc"
  let mut boundBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut costMinors : Array Term := #[]
  for j in [:parts.size] do
    let part := parts[j]!
    let N := costVars[j]!
    match part.record with
    | none =>
      boundBinders := boundBinders.push (← `(bracketedBinder| ($N : Nat)))
      boundBinders := boundBinders.push (← `(bracketedBinder| ($(hyps[j]!) :
        (empty rfl).allocs funs flags bounds modes paid live env +
          Verified.coerceCost t ((empty rfl).mode modes) $resultMode
            ((empty rfl).denote funs env) = $N)))
      costMinors := costMinors.push N
    | some record =>
      let C := rootVars[j]!
      boundBinders := boundBinders.push (← `(bracketedBinder| ($C : Nat)))
      boundBinders := boundBinders.push (← `(bracketedBinder| ($N : $(← arrows part (← `(Nat))))))
      boundBinders := boundBinders.push (← `(bracketedBinder| ($(rootHyps[j]!) :
        x.cost modes (fun i => live i || (nodes $record).uses (i + ($shape).bindCount $record))
          (env.get x) = $C)))
      let modes' ← `(($shape).modes $record (Verified.modeAt modes x.index) modes)
      let stmt ← bindAll part (← `(
        (nodes $record).allocs funs flags bounds $modes'
          (List.replicate (($shape).bindCount $record) false ++ paid)
          (Verified.shift (($shape).bindCount $record) live) $(part.boundEnv) +
        Verified.coerceCost t ((nodes $record).mode $modes') $resultMode
          ((nodes $record).denote funs $(part.boundEnv)) = $N $(part.fields)*))
      boundBinders := boundBinders.push (← `(bracketedBinder| ($(hyps[j]!) : $stmt)))
      costMinors := costMinors.push (← lambdaAll part (← `($C + $N $(part.fields)*)))
  elabCommand (← `(theorem $boundName
      {S : List Verified.Sig} {Γ : List Verified.Ty} {t : Verified.Ty}
      {funs : Verified.Funs S} {env : Verified.Env Γ}
      {flags : Verified.Flags S} {bounds : Verified.Bounds S}
      {modes : List Verified.Mode} {paid : List Bool} {live : Nat → Bool}
      (x : Verified.Var Γ (.tree $shape))
      (empty : ($shape).hasNull = true → Verified.Expr S Γ t)
      (nodes : (r : Fin ($shape).records) → Verified.Expr S (($shape).context r Γ) t)
      (value : $native) $boundBinders*
      (hx : env.get x = $flatten value) :
      (Verified.Expr.treeCase x empty nodes).allocs funs flags bounds modes paid live env =
        $(← primitive (← `(Nat)) (← `(value)) costMinors) := by
    cases value <;> simp_all only [Verified.Expr.allocs, $flatten:term, Nat.add_assoc]))
  -- The frame check of a match.
  let mut fitsBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for j in [:parts.size] do
    let part := parts[j]!
    let N := costVars[j]!
    match part.record with
    | none =>
      fitsBinders := fitsBinders.push (← `(bracketedBinder| ($N : Bool)))
      fitsBinders := fitsBinders.push (← `(bracketedBinder| ($(hyps[j]!) :
        (empty rfl).fits funs fits env = $N)))
    | some record =>
      fitsBinders := fitsBinders.push (← `(bracketedBinder| ($N : $(← arrows part (← `(Bool))))))
      let stmt ← bindAll part (← `(
        (nodes $record).fits funs fits $(part.boundEnv) = $N $(part.fields)*))
      fitsBinders := fitsBinders.push (← `(bracketedBinder| ($(hyps[j]!) : $stmt)))
  elabCommand (← `(theorem $fitsName
      {S : List Verified.Sig} {Γ : List Verified.Ty} {t : Verified.Ty}
      {funs : Verified.Funs S} {env : Verified.Env Γ} {fits : Verified.Fits S}
      (x : Verified.Var Γ (.tree $shape))
      (empty : ($shape).hasNull = true → Verified.Expr S Γ t)
      (nodes : (r : Fin ($shape).records) → Verified.Expr S (($shape).context r Γ) t)
      (value : $native) $fitsBinders*
      (hx : env.get x = $flatten value) :
      (Verified.Expr.treeCase x empty nodes).fits funs fits env =
        $(← primitive (← `(Bool)) (← `(value)) costVars) := by
    cases value <;> simp_all only [Verified.Expr.fits, $flatten:term]))
  -- The step of a tail call through a match, and its fixed point.
  let tailEqName := mkIdent (layout.decl `tail_case_eq)
  let tailFixedName := mkIdent (layout.decl `tail_case_fixed)
  let sumType ← `(Sum α β)
  let stepVars := names "s"
  let mut tailBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for j in [:parts.size] do
    tailBinders := tailBinders.push
      (← `(bracketedBinder| ($(stepVars[j]!) : $(← arrows parts[j]! sumType))))
  for j in [:parts.size] do
    let part := parts[j]!
    let s := stepVars[j]!
    let stmt ← match part.record with
      | none => `((empty rfl).denote funs env = Sum.map φ ψ $s)
      | some record => bindAll part (← `(
          (nodes $record).denote funs $(part.boundEnv) = Sum.map φ ψ ($s $(part.fields)*)))
    tailBinders := tailBinders.push (← `(bracketedBinder| ($(hyps[j]!) : $stmt)))
  elabCommand (← `(theorem $tailEqName
      {S : List Verified.Sig} {Γ params : List Verified.Ty} {result : Verified.Ty}
      {funs : Verified.Funs S} {env : Verified.Env Γ} {α β : Type}
      (φ : α → Verified.Env params) (ψ : β → result.denote)
      (x : Verified.Var Γ (.tree $shape))
      (empty : ($shape).hasNull = true → Verified.TailBody S params result Γ)
      (nodes : (r : Fin ($shape).records) →
        Verified.TailBody S params result (($shape).context r Γ))
      (value : $native) $tailBinders*
      (hx : env.get x = $flatten value) :
      (Verified.TailBody.treeCase x empty nodes).denote funs env =
        Sum.map φ ψ $(← primitive sumType (← `(value)) stepVars) := by
    cases value <;> simp_all only [Verified.TailBody.denote, $flatten:term]))
  let mut fixedBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for j in [:parts.size] do
    fixedBinders := fixedBinders.push
      (← `(bracketedBinder| ($(branchVars[j]!) : $(← arrows parts[j]! β))))
  for j in [:parts.size] do
    fixedBinders := fixedBinders.push
      (← `(bracketedBinder| ($(stepVars[j]!) : $(← arrows parts[j]! sumType))))
  for j in [:parts.size] do
    let part := parts[j]!
    let stmt ← bindAll part (← `($(branchVars[j]!) $(part.fields)* =
      ($(stepVars[j]!) $(part.fields)*).elim meaning id))
    fixedBinders := fixedBinders.push (← `(bracketedBinder| ($(hyps[j]!) : $stmt)))
  elabCommand (← `(theorem $tailFixedName {α β : Type} (meaning : α → β)
      (value : $native) $fixedBinders* :
      $(← primitive β (← `(value)) branchVars) =
        ($(← primitive sumType (← `(value)) stepVars)).elim meaning id := by
    cases value <;> simp_all only []))

end Verified.Reflect
