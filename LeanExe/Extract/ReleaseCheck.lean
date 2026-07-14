import Lean
import LeanExe.Extract.Values

open Lean

namespace LeanExe.Extract.Core

def runtimeReleaseArgs? (expr : Expr) : Option (List Expr) :=
  match appFnArgs expr.consumeMData with
  | (.const name _, args) =>
      if name == ``LeanExe.Runtime.release then some args else none
  | _ => none

inductive ReleaseProvenance where
  | freshAllocation
  | freshHelper (name : Name)
  | ownerZero
  deriving BEq, Repr

def ReleaseProvenance.text : ReleaseProvenance → String
  | .freshAllocation => "direct fresh allocation"
  | .freshHelper name => s!"fresh helper result from {name}"
  | .ownerZero => "statically owner-zero array"

structure ReleaseJudgment where
  declaration : Name
  expression : String
  provenance : ReleaseProvenance
  deriving BEq, Repr

inductive ReleaseBindingOrigin where
  | accepted (provenance : ReleaseProvenance)
  | unresolved (reason : String)
  deriving BEq, Repr

structure ReleaseBinding where
  name : Name
  origin : ReleaseBindingOrigin
  escape : Option String := none
  deriving BEq, Repr

partial def expressionLabel (ctx : Context) (bindings : List ReleaseBinding) (expr : Expr) : String :=
  match expr.consumeMData with
  | .bvar index =>
      match bindings[index]? with
      | some binding => binding.name.toString (escape := false)
      | none => s!"bvar {index}"
  | _ =>
      match appFnArgs expr.consumeMData with
      | (.const name _, args) =>
          match ctx.env.getProjectionFnInfo? name, args.reverse.head? with
          | some _, some target =>
              s!"{expressionLabel ctx bindings target}.{name.toString (escape := false)}"
          | _, _ => reprStr expr
      | _ => reprStr expr

def releaseRootType? (env : Environment) (type : Expr) : Bool :=
  match typeAtom? env type with
  | some (.array _) => true
  | some (.recVariant _ _) => true
  | _ => false

def heapBearingType? (env : Environment) (type : Expr) : Bool :=
  match typeAtom? env type with
  | some ty => !(tyReleaseOwnerSlotOffsets ty).isEmpty
  | none => false

def branchSelectedExpr? (value : Expr) : Bool :=
  match appFnArgs value.consumeMData with
  | (.const name _, _) =>
      name == ``ite || name == ``dite ||
        match name with
        | .str _ component => component.startsWith "match_"
        | _ => false
  | _ => false

def directFreshReleaseExpr? (ctx : Context) (type value : Expr) : Bool :=
  if !releaseRootType? ctx.env type then
    false
  else
    match appFnArgs value.consumeMData with
    | (.const name _, _) =>
        name == ``Array.replicate ||
          name == ``List.toArray ||
          name == ``Array.mk ||
          match ctx.env.find? name with
          | some (.ctorInfo _) => true
          | _ => false
    | _ => false

def freshHelperReleaseExpr? (ctx : Context) (value : Expr) : Option Name :=
  match appFnArgs value.consumeMData with
  | (.const name _, _) => do
      let index ← functionIndex? ctx name
      let offsets ← ctx.freshResultOwnerOffsets[index]?
      if offsets.contains 0 then some name else none
  | _ => none

def arraySizeArgument? (expr : Expr) : Option Expr :=
  match appFnArgs expr.consumeMData with
  | (.const name _, args) =>
      if name == ``Array.size then args.reverse.head? else none
  | _ => none

def staticallyOwnerZeroExpr? (bindings : List ReleaseBinding) (value : Expr) : Bool :=
  match appFnArgs value.consumeMData with
  | (.const name _, args) =>
      if name != ``Array.setIfInBounds then
        false
      else
        match args.reverse with
        | _newValue :: index :: array :: _ =>
            match arraySizeArgument? index with
            | some sizedArray =>
                if sizedArray.consumeMData != array.consumeMData then
                  false
                else
                  match array.consumeMData with
                  | .bvar sourceIndex =>
                      match bindings[sourceIndex]? with
                      | some { origin := .accepted .ownerZero, .. } => true
                      | _ => false
                  | _ => false
            | none => false
        | _ => false
  | _ => false

def conditionallyOwnedArrayExpr? (value : Expr) : Bool :=
  match appFnArgs value.consumeMData with
  | (.const name _, _) =>
      [``Array.pop, ``Array.reverse, ``Array.setIfInBounds].contains name
  | _ => false

def releaseOrigin
    (ctx : Context)
    (bindings : List ReleaseBinding)
    (type value : Expr) :
    ReleaseBindingOrigin :=
  if directFreshReleaseExpr? ctx type value then
    .accepted .freshAllocation
  else if staticallyOwnerZeroExpr? bindings value then
    .accepted .ownerZero
  else
    match freshHelperReleaseExpr? ctx value with
    | some name => .accepted (.freshHelper name)
    | none =>
        if branchSelectedExpr? value then
          .unresolved "ownership is branch-dependent"
        else if conditionallyOwnedArrayExpr? value then
          .unresolved "the array operation may return either a borrowed or an owned root"
        else
          match value.consumeMData with
          | .proj .. => .unresolved "the released root comes from a structure field"
          | .bvar .. => .unresolved "the root is an alias rather than a fresh handoff"
          | _ =>
              match appFnArgs value.consumeMData with
              | (.const name _, _) =>
                  if ctx.env.getProjectionFnInfo? name |>.isSome then
                    .unresolved "the released root comes from a structure field"
                  else
                    .unresolved s!"{name} has no fresh-root ownership justification"
              | _ => .unresolved "the root provenance is unsupported"

def markReleaseBindingEscape
    (bindings : List ReleaseBinding)
    (index : Nat)
    (reason : String) :
    List ReleaseBinding :=
  bindings.zipIdx.map fun (binding, candidate) =>
    if candidate == index then { binding with escape := some reason } else binding

def markHeapBindingEscapes
    (ctx : Context)
    (name : Name)
    (type value : Expr)
    (bindings : List ReleaseBinding) :
    List ReleaseBinding :=
  if !heapBearingType? ctx.env type then
    bindings
  else
    bindings.zipIdx.foldl
      (fun current item =>
        if containsBVar item.snd value then
          markReleaseBindingEscape current item.snd
            s!"copied into heap-bearing binding {name.toString (escape := false)}"
        else
          current)
      bindings

def releaseCheckError
    (declaration : Name)
    (expression provenance reason : String) :
    String :=
  s!"unsafe Runtime.release in {declaration}: released expression {expression}; provenance: {provenance}; reason: {reason}"

def validateReleaseAt
    (ctx : Context)
    (declaration : Name)
    (bindings : List ReleaseBinding)
    (args : List Expr)
    (body : Expr) :
    Except String ReleaseJudgment := do
  let (type, value) ←
    match args.reverse with
    | value :: type :: _ => .ok (type, value)
    | _ => .error s!"malformed Runtime.release application in {declaration}"
  let label := expressionLabel ctx bindings value
  match value.consumeMData with
  | .bvar index =>
      let binding ←
        match bindings[index]? with
        | some binding => .ok binding
        | none =>
            .error (releaseCheckError declaration label "unbound" "the released variable is unbound")
      if containsBVar (index + 1) body then
        .error <| releaseCheckError declaration label
          (match binding.origin with
          | .accepted provenance => provenance.text
          | .unresolved reason => reason)
          "the root is used after release or released more than once"
      else
        match binding.escape with
        | some reason =>
            .error <| releaseCheckError declaration label "escaped root" reason
        | none =>
            match binding.origin with
            | .accepted provenance =>
                .ok { declaration := declaration, expression := label, provenance := provenance }
            | .unresolved reason =>
                .error <| releaseCheckError declaration label "unresolved" reason
  | _ =>
      match releaseOrigin ctx bindings type value with
      | .accepted provenance =>
          .ok { declaration := declaration, expression := label, provenance := provenance }
      | .unresolved reason =>
          .error <| releaseCheckError declaration label "unresolved" reason

mutual
  partial def validateReleaseExpr
      (ctx : Context)
      (declaration : Name)
      (bindings : List ReleaseBinding)
      (expr : Expr) :
      Except String (Array ReleaseJudgment) := do
    match expr.consumeMData with
    | .letE name type value body _ =>
        match runtimeReleaseArgs? value with
        | some args =>
            let judgment ← validateReleaseAt ctx declaration bindings args body
            let bodyJudgments ←
              validateReleaseExpr ctx declaration
                ({ name := name, origin := .unresolved "release result is scalar" } :: bindings)
                body
            .ok (#[judgment] ++ bodyJudgments)
        | none =>
            let valueJudgments ← validateReleaseExpr ctx declaration bindings value
            let escapedBindings := markHeapBindingEscapes ctx name type value bindings
            let binding : ReleaseBinding :=
              { name := name, origin := releaseOrigin ctx escapedBindings type value }
            let bodyJudgments ←
              validateReleaseExpr ctx declaration (binding :: escapedBindings) body
            .ok (valueJudgments ++ bodyJudgments)
    | .lam name _ body _ =>
        validateReleaseExpr ctx declaration
          ({ name := name, origin := .unresolved "ownership comes from a function parameter" } :: bindings)
          body
    | .app fn arg =>
        match runtimeReleaseArgs? expr with
        | some _ =>
            .error <| releaseCheckError declaration (expressionLabel ctx bindings expr) "unsupported"
              "Runtime.release must be the complete value of a let binding"
        | none =>
            let fnJudgments ← validateReleaseExpr ctx declaration bindings fn
            let argJudgments ← validateReleaseExpr ctx declaration bindings arg
            .ok (fnJudgments ++ argJudgments)
    | .proj _ _ value => validateReleaseExpr ctx declaration bindings value
    | _ => .ok #[]
end

partial def validateReleaseDeclaration
    (ctx : Context)
    (entry declaration : Name)
    (bindings : List ReleaseBinding)
    (expr : Expr) :
    Except String (Array ReleaseJudgment) := do
  match expr.consumeMData with
  | .lam name type body _ =>
      let origin :=
        if declaration == entry && releaseRootType? ctx.env type then
          .accepted .ownerZero
        else
          .unresolved "ownership comes from a function parameter"
      validateReleaseDeclaration ctx entry declaration ({ name := name, origin := origin } :: bindings) body
  | _ => validateReleaseExpr ctx declaration bindings expr

def validateModuleReleases
    (ctx : Context)
    (entry : Name)
    (names : List Name) :
    Except String (Array ReleaseJudgment) := do
  let mut judgments := #[]
  for name in names do
    let info ←
      match ctx.env.find? name with
      | some info => .ok info
      | none => .error s!"declaration disappeared during release checking: {name}"
    match info.value? with
    | some value =>
        let specialized := betaSpecializeExpr ctx.env ctx.root 32 value
        judgments := judgments ++ (← validateReleaseDeclaration ctx entry name [] specialized)
    | none => pure ()
  .ok judgments

end LeanExe.Extract.Core
