import Verified.Reflect.Definitions

namespace Verified.Reflect

open Lean Meta Elab Command

def deriveRecursiveMatch (layout : RecursiveLayout) : CommandElabM Unit :=
    withScope (fun scope => { scope with currNamespace := .anonymous }) do
  let eqName := mkIdent (layout.decl `case_eq)
  if (← getEnv).contains eqName.getId then return
  let boundName := mkIdent (layout.decl `case_bound)
  let fitsName := mkIdent (layout.decl `case_fits)
  let native := mkIdent layout.name
  let flatten := mkIdent (layout.decl `toTree)
  let casesOn := mkIdent (layout.name ++ `casesOn)
  let info ← getConstInfoInduct layout.name
  let shape : Term ← if layout.shape = listShape then `(Verified.listShape)
    else `(Verified.Reflect.reflectedTreeShape $(quote layout.shape.fields) rfl)
  let fields := (List.range layout.shape.fields.length).toArray.map fun i =>
    mkIdent (Name.mkSimple s!"field{i}")
  let types : Array Term ← layout.shape.fields.toArray.mapM fun child =>
    if child then pure native else `(UInt64)
  let bindAll (body : Term) : CommandElabM Term := do
    let mut result := body
    for i in (List.range fields.size).reverse do
      result ← `(∀ ($(fields[i]!) : $(types[i]!)), $result)
    return result
  let lambdaAll (body : Term) : CommandElabM Term := do
    let mut result := body
    for i in (List.range fields.size).reverse do
      result ← `(fun ($(fields[i]!) : $(types[i]!)) => $result)
    return result
  let arrows (result : Term) : CommandElabM Term := do
    let mut result := result
    for type in types.toList.reverse do result ← `($type → $result)
    return result
  let primitive (result value empty branch : Term) : CommandElabM Term :=
    if info.ctors.head! == layout.empty then
      `($casesOn (motive := fun _ => $result) $value $empty $branch)
    else `($casesOn (motive := fun _ => $result) $value $branch $empty)
  let mut words : Array Term := #[]
  let mut children : Array Term := #[]
  for i in [:fields.size] do
    if layout.shape.fields[i]! then children := children.push (← `($flatten $(fields[i]!)))
    else words := words.push fields[i]!
  let wordFn ← `(([$words,*]).get)
  let childFn ← `(([$children,*]).get)
  let boundEnv ← `(Verified.Env.treeFields $shape $wordFn $childFn env)
  let β ← `(β)
  let branchType ← arrows β
  let caseValue ← primitive β (← `(value)) (← `(a)) (← `(b))
  let nodeEq ← bindAll (← `(node.denote funs $boundEnv = flatten (b $fields*)))
  elabCommand (← `(theorem $eqName
      {S : List Verified.Sig} {Γ : List Verified.Ty} {t : Verified.Ty}
      {funs : Verified.Funs S} {env : Verified.Env Γ} {β : Type}
      (x : Verified.Var Γ (.tree $shape))
      (empty : Verified.Expr S Γ t) (node : Verified.Expr S (($shape).context Γ) t)
      (flatten : β → t.denote) (value : $native) (a : β) (b : $branchType)
      (hx : env.get x = $flatten value)
      (he : empty.denote funs env = flatten a) (hn : $nodeEq) :
      (Verified.Expr.treeCase x empty node).denote funs env = flatten $caseValue := by
    cases value <;> simp_all only [Verified.Expr.denote, $flatten:term]))
  let natBranch ← arrows (← `(Nat))
  let resultMode ← `((empty.mode modes).join
    (node.mode (($shape).modes (Verified.modeAt modes x.index) modes)))
  let nodeCost ← bindAll (← `(
    node.allocs funs flags bounds (($shape).modes (Verified.modeAt modes x.index) modes)
      (List.replicate ($shape).bindCount false ++ paid) (Verified.shift ($shape).bindCount live)
      $boundEnv + Verified.coerceCost t
      (node.mode (($shape).modes (Verified.modeAt modes x.index) modes)) $resultMode
      (node.denote funs $boundEnv) = N $fields*))
  let costCase ← primitive (← `(Nat)) (← `(value)) (← `(E))
    (← lambdaAll (← `(C + N $fields*)))
  elabCommand (← `(theorem $boundName
      {S : List Verified.Sig} {Γ : List Verified.Ty} {t : Verified.Ty}
      {funs : Verified.Funs S} {env : Verified.Env Γ}
      {flags : Verified.Flags S} {bounds : Verified.Bounds S}
      {modes : List Verified.Mode} {paid : List Bool} {live : Nat → Bool}
      (x : Verified.Var Γ (.tree $shape))
      (empty : Verified.Expr S Γ t) (node : Verified.Expr S (($shape).context Γ) t)
      (value : $native) (C E : Nat) (N : $natBranch)
      (hx : env.get x = $flatten value)
      (hc : x.cost modes (fun i => live i || node.uses (i + ($shape).bindCount)) (env.get x) = C)
      (he : empty.allocs funs flags bounds modes paid live env +
        Verified.coerceCost t (empty.mode modes) $resultMode (empty.denote funs env) = E)
      (hn : $nodeCost) :
      (Verified.Expr.treeCase x empty node).allocs funs flags bounds modes paid live env =
        $costCase := by
    cases value <;> simp_all only [Verified.Expr.allocs, $flatten:term, Nat.add_assoc]))
  let boolBranch ← arrows (← `(Bool))
  let nodeFits ← bindAll (← `(node.fits funs fits $boundEnv = N $fields*))
  let fitsCase ← primitive (← `(Bool)) (← `(value)) (← `(E)) (← `(N))
  elabCommand (← `(theorem $fitsName
      {S : List Verified.Sig} {Γ : List Verified.Ty} {t : Verified.Ty}
      {funs : Verified.Funs S} {env : Verified.Env Γ} {fits : Verified.Fits S}
      (x : Verified.Var Γ (.tree $shape))
      (empty : Verified.Expr S Γ t) (node : Verified.Expr S (($shape).context Γ) t)
      (value : $native) (E : Bool) (N : $boolBranch)
      (hx : env.get x = $flatten value)
      (he : empty.fits funs fits env = E) (hn : $nodeFits) :
      (Verified.Expr.treeCase x empty node).fits funs fits env = $fitsCase := by
    cases value <;> simp_all only [Verified.Expr.fits, $flatten:term]))

end Verified.Reflect
