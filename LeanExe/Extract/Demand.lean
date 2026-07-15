import Lean
import Init.Data.ByteArray.Extra
import LeanExe.Extract.Patterns
import LeanExe.IR.Core

open Lean

namespace LeanExe.Extract.Core

def insertNat (value : Nat) (items : List Nat) : List Nat :=
  if items.contains value then items else value :: items

def unionNat (left right : List Nat) : List Nat :=
  right.foldl (fun acc value => insertNat value acc) left

def intersectNat (left right : List Nat) : List Nat :=
  left.filter (fun value => right.contains value)

def decPositive (items : List Nat) : List Nat :=
  items.foldr
    (fun value acc =>
      match value with
      | 0 => acc
      | next + 1 => insertNat next acc)
    []

structure Demand where
  may : List Nat
  must : List Nat
  mayTrap : Bool
  deriving BEq, Repr, Inhabited

def Demand.empty : Demand :=
  { may := [], must := [], mayTrap := false }

def Demand.trap : Demand :=
  { may := [], must := [], mayTrap := true }

def Demand.bvar (index : Nat) : Demand :=
  { may := [index], must := [index], mayTrap := false }

def Demand.always (left right : Demand) : Demand :=
  {
    may := unionNat left.may right.may,
    must := unionNat left.must right.must,
    mayTrap := left.mayTrap || right.mayTrap
  }

def Demand.branch (cond thenDemand elseDemand : Demand) : Demand :=
  {
    may := unionNat cond.may (unionNat thenDemand.may elseDemand.may),
    must := unionNat cond.must (intersectNat thenDemand.must elseDemand.must),
    mayTrap := cond.mayTrap || thenDemand.mayTrap || elseDemand.mayTrap
  }

def Demand.letE (value body : Demand) : Demand :=
  let boundMay := body.may.contains 0
  let boundMust := body.must.contains 0
  {
    may :=
      unionNat (decPositive body.may)
        (if boundMay then value.may else []),
    must :=
      unionNat (decPositive body.must)
        (if boundMust then value.must else []),
    mayTrap := body.mayTrap || (boundMay && value.mayTrap)
  }

structure DemandSummary where
  mayDemand : List Bool
  mustDemand : List Bool
  selfMayTrap : Bool
  deriving BEq, Repr, Inhabited

def boolAt (items : List Bool) (index : Nat) : Bool :=
  match items[index]? with
  | some value => value
  | none => false

def bvarForParam (paramCount paramIndex : Nat) : Nat :=
  paramCount - paramIndex - 1

def DemandSummary.recursive (paramCount : Nat) : DemandSummary :=
  {
    mayDemand := List.replicate paramCount true,
    mustDemand := (List.range paramCount).map (fun index => index == 0),
    selfMayTrap := false
  }

def DemandSummary.fromDemand (paramCount : Nat) (demand : Demand) : DemandSummary :=
  {
    mayDemand :=
      (List.range paramCount).map
        (fun index => demand.may.contains (bvarForParam paramCount index)),
    mustDemand :=
      (List.range paramCount).map
        (fun index => demand.must.contains (bvarForParam paramCount index)),
    selfMayTrap := demand.mayTrap
  }

def decDemand (demand : Demand) : Demand :=
  {
    may := decPositive demand.may,
    must := decPositive demand.must,
    mayTrap := demand.mayTrap
  }

def enumerateAux {α : Type} : List α → Nat → List (Nat × α)
  | [], _ => []
  | item :: rest, index => (index, item) :: enumerateAux rest (index + 1)

def enumerate {α : Type} (items : List α) : List (Nat × α) :=
  enumerateAux items 0

def boolAndExpr (left right : IRExpr) : IRExpr :=
  .ite (boolCond left) right (.u64 0)

def boolAndExprs : List IRExpr → IRExpr
  | [] => .u64 1
  | expr :: rest => rest.foldl boolAndExpr expr

partial def valueTopLetsWithBody (value : ExtractedValue) : List ValueLet × ExtractedValue :=
  match value with
  | .letE slot expr body =>
      let parts := valueTopLetsWithBody body
      (.expr slot expr :: parts.fst, parts.snd)
  | .letCall slots index args body =>
      let parts := valueTopLetsWithBody body
      (.call slots index args :: parts.fst, parts.snd)
  | other => ([], other)

mutual
partial def structuralEqFieldsExpr
    (nextLocal : Nat)
    (fields : List Ty)
    (leftFields rightFields : List ExtractedValue) :
    Except String (IRExpr × Nat) := do
  if leftFields.length != fields.length || rightFields.length != fields.length then
    .error "structural equality value shape mismatch"
  else
    let rec loop : List (Ty × (ExtractedValue × ExtractedValue)) → Nat → List IRExpr →
        Except String (List IRExpr × Nat)
      | [], next, exprs => .ok (exprs.reverse, next)
      | item :: rest, next, exprs => do
          let result ← structuralEqValueExpr next item.fst item.snd.fst item.snd.snd
          loop rest result.snd (result.fst :: exprs)
    let result ← loop (fields.zip (leftFields.zip rightFields)) nextLocal []
    .ok (boolAndExprs result.fst, result.snd)

partial def structuralEqVariantExpr
    (nextLocal : Nat)
    (name : Name)
    (ctors : List (List Ty))
    (left right : ExtractedValue) :
    Except String (IRExpr × Nat) := do
  let leftParts ← variantPartsWithLets name left
  let rightParts ← variantPartsWithLets name right
  let leftTag := leftParts.snd.fst
  let rightTag := rightParts.snd.fst
  let leftCtors := leftParts.snd.snd
  let rightCtors := rightParts.snd.snd
  if leftCtors.length != ctors.length || rightCtors.length != ctors.length then
    .error s!"inductive equality value shape mismatch: {name}"
  else
    let rec loop :
        List (Nat × (List Ty × (List ExtractedValue × List ExtractedValue))) →
          Nat → List IRExpr → Except String (List IRExpr × Nat)
      | [], next, exprs => .ok (exprs.reverse, next)
      | item :: rest, next, exprs => do
          let payload ← structuralEqFieldsExpr next item.snd.fst item.snd.snd.fst item.snd.snd.snd
          let expr := .ite (.eqU64 leftTag (.u64 item.fst)) payload.fst (.u64 1)
          loop rest payload.snd (expr :: exprs)
    let payloadResult ← loop (enumerate (ctors.zip (leftCtors.zip rightCtors))) nextLocal []
    let body := .ite (.eqU64 leftTag rightTag) (boolAndExprs payloadResult.fst) (.u64 0)
    .ok (wrapExprLets (leftParts.fst ++ rightParts.fst) body, payloadResult.snd)

partial def structuralEqSumExpr
    (nextLocal : Nat)
    (leftTy rightTy : Ty)
    (left right : ExtractedValue) :
    Except String (IRExpr × Nat) := do
  let leftParts ← sumPartsWithLets left
  let rightParts ← sumPartsWithLets right
  let leftTag := leftParts.snd.fst
  let rightTag := rightParts.snd.fst
  let leftPayload ←
    structuralEqValueExpr nextLocal leftTy leftParts.snd.snd.fst rightParts.snd.snd.fst
  let rightPayload ←
    structuralEqValueExpr leftPayload.snd rightTy leftParts.snd.snd.snd rightParts.snd.snd.snd
  let payload :=
    boolAndExprs [
      .ite (.eqU64 leftTag (.u64 0)) leftPayload.fst (.u64 1),
      .ite (.eqU64 leftTag (.u64 1)) rightPayload.fst (.u64 1)
    ]
  let body := .ite (.eqU64 leftTag rightTag) payload (.u64 0)
  .ok (wrapExprLets (leftParts.fst ++ rightParts.fst) body, rightPayload.snd)

partial def structuralEqValueExpr
    (nextLocal : Nat)
    (ty : Ty)
    (left right : ExtractedValue) :
    Except String (IRExpr × Nat) := do
  let leftTop := valueTopLetsWithBody left
  let rightTop := valueTopLetsWithBody right
  let result ←
    match ty with
    | .unit | .bool | .u8 | .u32 | .u64 | .nat => do
        let leftExpr ← scalarValue leftTop.snd
        let rightExpr ← scalarValue rightTop.snd
        .ok (boolExpr (.eqU64 leftExpr rightExpr), nextLocal)
    | .product leftTy rightTy => do
        let leftFirst ← productField 0 leftTop.snd
        let leftSecond ← productField 1 leftTop.snd
        let rightFirst ← productField 0 rightTop.snd
        let rightSecond ← productField 1 rightTop.snd
        let firstExpr ← structuralEqValueExpr nextLocal leftTy leftFirst rightFirst
        let secondExpr ← structuralEqValueExpr firstExpr.snd rightTy leftSecond rightSecond
        .ok (boolAndExpr firstExpr.fst secondExpr.fst, secondExpr.snd)
    | .sum leftTy rightTy =>
        structuralEqSumExpr nextLocal leftTy rightTy leftTop.snd rightTop.snd
    | .struct name _ fields => do
        let leftFields ← enumerate fields |>.mapM fun item => structField name item.fst leftTop.snd
        let rightFields ← enumerate fields |>.mapM fun item => structField name item.fst rightTop.snd
        structuralEqFieldsExpr nextLocal fields leftFields rightFields
    | .variant name _ ctors =>
        structuralEqVariantExpr nextLocal name ctors leftTop.snd rightTop.snd
    | .byteArray => do
        let leftParts ← byteArrayPartsWithLets leftTop.snd
        let rightParts ← byteArrayPartsWithLets rightTop.snd
        let body :=
          wrapExprLets (leftParts.fst ++ rightParts.fst)
            (.byteArrayEq leftParts.snd.fst leftParts.snd.snd rightParts.snd.fst rightParts.snd.snd)
        .ok (body, nextLocal)
    | .array item => do
        if !supportedEqType item then
          .error s!"Array equality is unsupported for item type: {reprStr item}"
        else
          let width ←
            match arrayElementSlots? item with
            | some width => .ok width
            | none => .error s!"unsupported array equality item layout: {reprStr item}"
          let leftExpr ← scalarValue leftTop.snd
          let rightExpr ← scalarValue rightTop.snd
          let leftStart := nextLocal
          let rightStart := nextLocal + width
          let predicateNext := nextLocal + 2 * width
          let leftItem ← arrayLocalValue item leftStart
          let rightItem ← arrayLocalValue item rightStart
          let predicate ← structuralEqValueExpr predicateNext item leftItem rightItem
          .ok (.arrayEqSlots width leftExpr rightExpr leftStart rightStart predicate.fst,
            predicate.snd)
    | .recVariant name _ =>
        .error s!"recursive inductive equality is unsupported: {name}"
  .ok (wrapExprLets (leftTop.fst ++ rightTop.fst) result.fst, result.snd)
end

def bindStrictSlots (slots : List IRExpr) (nextLocal : Nat) : StrictSlots :=
  let indexed := enumerate slots
  {
    lets := indexed.map fun item => .expr (nextLocal + item.fst) item.snd
    slots := indexed.map fun item => .local (nextLocal + item.fst)
    nextLocal := nextLocal + slots.length
  }

mutual
partial def demandExpr
    (ctx : Context)
    (visiting : List Name)
    (expr : Expr) : Demand :=
  match expr.consumeMData with
  | .bvar index => .bvar index
  | .letE _ _ value body _ => Demand.letE (demandExpr ctx visiting value) (demandExpr ctx visiting body)
  | .mdata _ body => demandExpr ctx visiting body
  | .proj ``Prod index body => demandProductField ctx visiting index body
  | .proj _ _ body => demandExpr ctx visiting body
  | .lam _ _ _ _ => .empty
  | .forallE _ _ _ _ => .empty
  | _ =>
      match scalarLiteralExpr? expr with
      | some _ => .empty
      | none =>
          match appFnArgs expr with
          | (.const ``ite _, [_ty, condExpr, _, thenExpr, elseExpr]) =>
              Demand.branch
                (demandCond ctx visiting condExpr)
                (demandExpr ctx visiting thenExpr)
                (demandExpr ctx visiting elseExpr)
          | (.const ``dite _, [_ty, condExpr, _, thenArm, elseArm]) =>
              Demand.branch
                (demandCond ctx visiting condExpr)
                (demandUnitExprArm ctx visiting thenArm)
                (demandUnitExprArm ctx visiting elseArm)
          | (.const ``Decidable.decide _, [prop, _inst]) =>
              demandCond ctx visiting prop
          | (.const ``Id.run _, args) =>
              match args.reverse with
              | value :: _ => demandExpr ctx visiting value
              | _ => .empty
          | (.const ``Pure.pure _, args) =>
              match args, args.reverse with
              | monadTy :: _, value :: _ =>
                  match supportedMonadType? ctx.env monadTy with
                  | some .id => demandExpr ctx visiting value
                  | some .option => demandExpr ctx visiting value
                  | some (.except _) => demandExpr ctx visiting value
                  | none => .empty
              | _, _ => .empty
          | (.const ``Bind.bind _, args) =>
              match args, args.reverse with
              | monadTy :: _, bindFn :: value :: _ =>
                  match supportedMonadType? ctx.env monadTy with
                  | some .id =>
                      match collectLambdas bindFn 1 with
                      | some body =>
                          Demand.letE (demandExpr ctx visiting value) (demandExpr ctx visiting body)
                      | none => .empty
                  | some .option =>
                      Demand.branch
                        (demandExpr ctx visiting value)
                        .empty
                        (demandOptionSomeArm ctx visiting bindFn)
                  | some (.except _) =>
                      Demand.branch
                        (demandExpr ctx visiting value)
                        .empty
                        (demandOptionSomeArm ctx visiting bindFn)
                  | none => .empty
              | _, _ => .empty
          | (.const ``Functor.map _, args) =>
              match args, args.reverse with
              | monadTy :: _, value :: mapFn :: _ =>
                  match supportedMonadType? ctx.env monadTy with
                  | some .option =>
                      Demand.branch
                        (demandExpr ctx visiting value)
                        .empty
                        (demandOptionSomeArm ctx visiting mapFn)
                  | some (.except _) =>
                      Demand.branch
                        (demandExpr ctx visiting value)
                        .empty
                        (demandOptionSomeArm ctx visiting mapFn)
                  | _ => .empty
              | _, _ => .empty
          | (.const ``Prod.fst _, args) =>
              match args.reverse with
              | product :: _ => demandProductField ctx visiting 0 product
              | _ => .empty
          | (.const ``Prod.snd _, args) =>
              match args.reverse with
              | product :: _ => demandProductField ctx visiting 1 product
              | _ => .empty
          | (.const ``id _, args) =>
              match args.reverse with
              | value :: _ => demandExpr ctx visiting value
              | _ => .empty
          | (.const ``ByteArray.size _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.isEmpty _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.extract _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.push _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.append _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.set! _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.set _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.mk _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``String.toUTF8 _, _args) =>
              .empty
          | (.const ``ByteArray.copySlice _, args) =>
              match args.reverse with
              | _exact :: copyLen :: destOff :: dest :: srcOff :: src :: _ =>
                  [src, srcOff, dest, destOff, copyLen].foldl
                    (fun acc arg => Demand.always acc (demandExpr ctx visiting arg))
                    .empty
              | _ => .empty
          | (.const ``ByteArray.findIdx? _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.foldl _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.foldlM _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.toUInt64LE! _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.toUInt64BE! _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.get! _, _) => .trap
          | (.const ``ByteArray.get _, args) =>
              match args.reverse with
              | _proof :: index :: array :: _ =>
                  Demand.always
                    (demandExpr ctx visiting array)
                    (demandExpr ctx visiting index)
              | _ => .empty
          | (.const ``Array.size _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.isEmpty _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.push _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.pop _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.eraseIdxIfInBounds _, args) =>
              match args.reverse with
              | index :: array :: _ =>
                  Demand.always (demandExpr ctx visiting array) (demandExpr ctx visiting index)
              | _ => .empty
          | (.const ``Array.eraseIdx _, args) =>
              match args.reverse with
              | _proof :: index :: array :: _ =>
                  Demand.always (demandExpr ctx visiting array) (demandExpr ctx visiting index)
              | _ => .empty
          | (.const ``Array.swapIfInBounds _, args) =>
              match args.reverse with
              | right :: left :: array :: _ =>
                  Demand.always
                    (Demand.always (demandExpr ctx visiting array) (demandExpr ctx visiting left))
                    (demandExpr ctx visiting right)
              | _ => .empty
          | (.const ``Array.swap _, args) =>
              match args.reverse with
              | _rightProof :: _leftProof :: right :: left :: array :: _ =>
                  Demand.always
                    (Demand.always (demandExpr ctx visiting array) (demandExpr ctx visiting left))
                    (demandExpr ctx visiting right)
              | _ => .empty
          | (.const ``Array.reverse _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.insertIdx _, args) =>
              match args.reverse with
              | _proof :: value :: index :: array :: _ =>
                Demand.always
                  (Demand.always
                    (demandExpr ctx visiting array)
                    (demandExpr ctx visiting index))
                  (demandExpr ctx visiting value)
              | _ => .empty
          | (.const ``Array.append _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``HAppend.hAppend _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.map _, args) =>
              match args.reverse with
              | array :: mapFn :: _ =>
                  Demand.always (demandExpr ctx visiting array)
                    (demandOptionSomeArm ctx visiting mapFn)
              | _ => .empty
          | (.const ``Array.findIdx? _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.find? _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.any _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.all _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.filter _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.foldl _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.foldlM _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.foldr _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.insertIdxIfInBounds _, args) =>
              match args.reverse with
              | value :: index :: array :: _ =>
                  Demand.branch
                    (Demand.always (demandExpr ctx visiting array) (demandExpr ctx visiting index))
                    (demandExpr ctx visiting value)
                    .empty
              | _ => .empty
          | (.const ``Array.insertIdx! _, args) =>
              match args.reverse with
              | value :: index :: array :: _ =>
                  Demand.branch
                    (Demand.always (demandExpr ctx visiting array) (demandExpr ctx visiting index))
                    (demandExpr ctx visiting value)
                    .trap
              | _ => .empty
          | (.const ``Array.modify _, args) =>
              match args.reverse with
              | modifyFn :: index :: array :: _ =>
                  Demand.branch
                    (Demand.always (demandExpr ctx visiting array) (demandExpr ctx visiting index))
                    (demandOptionSomeArm ctx visiting modifyFn)
                    .empty
              | _ => .empty
          | (.const ``Array.extract _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.empty _, _) => .empty
          | (.const ``Array.mkEmpty _, _) => .empty
          | (.const ``Array.emptyWithCapacity _, _) => .empty
          | (.const ``Array.singleton _, args) =>
              match args.reverse with
              | value :: _ => demandExpr ctx visiting value
              | _ => .empty
          | (.const ``Array.get!Internal _, _) => .trap
          | (.const ``GetElem?.getElem! _, _) => .trap
          | (.const ``GetElem.getElem _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.back! _, _) => .trap
          | (.const ``Array.back _, args) =>
              match args.reverse with
              | _proof :: array :: _ => demandExpr ctx visiting array
              | _ => .empty
          | (.const ``Array.set _, args) =>
              match args.reverse with
              | _proof :: value :: index :: array :: _ =>
                  Demand.always
                    (Demand.always
                      (demandExpr ctx visiting array)
                      (demandExpr ctx visiting index))
                    (demandExpr ctx visiting value)
              | _ => .empty
          | (.const ``Array.setIfInBounds _, args) =>
              match args.reverse with
              | value :: index :: array :: _ =>
                  Demand.branch
                    (Demand.always (demandExpr ctx visiting array) (demandExpr ctx visiting index))
                    (demandExpr ctx visiting value)
                    .empty
              | _ => .empty
          | (.const ``Array.swapAt _, args) =>
              match args.reverse with
              | _proof :: value :: index :: array :: _ =>
                  Demand.always
                    (Demand.always
                      (demandExpr ctx visiting array)
                      (demandExpr ctx visiting index))
                    (demandExpr ctx visiting value)
              | _ => .empty
          | (.const ``Array.getD _, args) =>
              match args.reverse with
              | defaultValue :: index :: array :: _ =>
                  let arrayDemand := demandExpr ctx visiting array
                  let indexDemand := demandExpr ctx visiting index
                  let defaultDemand := demandExpr ctx visiting defaultValue
                  Demand.branch (Demand.always arrayDemand indexDemand) .empty defaultDemand
              | _ => .empty
          | (.const ``Array.back? _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Option.orElse _, args) =>
              match optionOrElseArgs? ctx.env (.const ``Option.orElse []) args with
              | some (optionValue, fallback) =>
                  Demand.branch
                    (demandExpr ctx visiting optionValue)
                    (demandUnitExprArm ctx visiting fallback)
                    .empty
              | none => .empty
          | (.const ``HOrElse.hOrElse _, args) =>
              match optionOrElseArgs? ctx.env (.const ``HOrElse.hOrElse []) args with
              | some (optionValue, fallback) =>
                  Demand.branch
                    (demandExpr ctx visiting optionValue)
                    (demandUnitExprArm ctx visiting fallback)
                    .empty
              | none =>
                  match exceptOrElseArgs? ctx.env (.const ``HOrElse.hOrElse []) args with
                  | some (exceptValue, fallback) =>
                      Demand.branch
                        (demandExpr ctx visiting exceptValue)
                        (demandUnitExprArm ctx visiting fallback)
                        .empty
                  | none =>
                      args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Option.getD _, args) =>
              match args.reverse with
              | defaultValue :: optionValue :: _ =>
                  let defaultDemand := demandExpr ctx visiting defaultValue
                  Demand.branch
                    (demandExpr ctx visiting optionValue)
                    defaultDemand
                    .empty
              | _ => .empty
          | (.const ``Option.get! _, args) =>
              match args.reverse with
              | optionValue :: _ => demandOptionGet ctx visiting optionValue
              | _ => .empty
          | (.const ``Option.elim _, args) =>
              match args.reverse with
              | someArm :: defaultValue :: optionValue :: _ =>
                  Demand.branch
                    (demandExpr ctx visiting optionValue)
                    (demandExpr ctx visiting defaultValue)
                    (demandOptionSomeArm ctx visiting someArm)
              | _ => .empty
          | (.const ``Option.map _, args) =>
              match args.reverse with
              | optionValue :: mapFn :: _ =>
                  Demand.branch
                    (demandExpr ctx visiting optionValue)
                    .empty
                    (demandOptionSomeArm ctx visiting mapFn)
              | _ => .empty
          | (.const ``Option.filter _, args) =>
              match args.reverse with
              | optionValue :: predicate :: _ =>
                  Demand.branch
                    (demandExpr ctx visiting optionValue)
                    .empty
                    (demandOptionSomeCondArm ctx visiting predicate)
              | _ => .empty
          | (.const ``Option.any _, args) =>
              match args.reverse with
              | optionValue :: predicate :: _ =>
                  Demand.branch
                    (demandExpr ctx visiting optionValue)
                    .empty
                    (demandOptionSomeCondArm ctx visiting predicate)
              | _ => .empty
          | (.const ``Option.all _, args) =>
              match args.reverse with
              | optionValue :: predicate :: _ =>
                  Demand.branch
                    (demandExpr ctx visiting optionValue)
                    .empty
                    (demandOptionSomeCondArm ctx visiting predicate)
              | _ => .empty
          | (.const ``Except.map _, args) =>
              match args.reverse with
              | exceptValue :: mapFn :: _ =>
                  Demand.branch
                    (demandExpr ctx visiting exceptValue)
                    .empty
                    (demandOptionSomeArm ctx visiting mapFn)
              | _ => .empty
          | (.const ``Except.mapError _, args) =>
              match args.reverse with
              | exceptValue :: mapFn :: _ =>
                  Demand.branch
                    (demandExpr ctx visiting exceptValue)
                    (demandOptionSomeArm ctx visiting mapFn)
                    .empty
              | _ => .empty
          | (.const ``Except.bind _, args) =>
              match args.reverse with
              | bindFn :: exceptValue :: _ =>
                  Demand.branch
                    (demandExpr ctx visiting exceptValue)
                    .empty
                    (demandOptionSomeArm ctx visiting bindFn)
              | _ => .empty
          | (.const ``Except.toOption _, args) =>
              match args.reverse with
              | exceptValue :: _ => demandExpr ctx visiting exceptValue
              | _ => .empty
          | (.const ``Except.isOk _, args) =>
              match args.reverse with
              | exceptValue :: _ => demandExceptTag ctx visiting exceptValue
              | _ => .empty
          | (.const ``Option.bind _, args) =>
              match args.reverse with
              | bindFn :: optionValue :: _ =>
                  Demand.branch
                    (demandExpr ctx visiting optionValue)
                    .empty
                    (demandOptionSomeArm ctx visiting bindFn)
              | _ => .empty
          | (.const ``Array.set! _, _) => .trap
          | (.const ``Array.eraseIdx! _, _) => .trap
          | (.const primitive _, args) =>
              match boolMatcherArgs? ctx.env (.const primitive []) args with
              | some (scrutinee, falseArm, trueArm) =>
                  Demand.branch
                    (demandCond ctx visiting scrutinee)
                    (demandUnitExprArm ctx visiting trueArm)
                    (demandUnitExprArm ctx visiting falseArm)
              | none =>
                  match exceptMatcherArgs? ctx.env (.const primitive []) args with
                  | some (scrutinee, errorArm, okArm) =>
                      Demand.branch
                        (demandExpr ctx visiting scrutinee)
                        (demandOptionSomeArm ctx visiting errorArm)
                        (demandOptionSomeArm ctx visiting okArm)
                  | none =>
                      match optionMatcherArgs? ctx.env (.const primitive []) args with
                      | some (scrutinee, noneArm, someArm) =>
                          Demand.branch
                            (demandExpr ctx visiting scrutinee)
                            (demandOptionNoneArm ctx visiting noneArm)
                            (demandOptionSomeArm ctx visiting someArm)
                      | none =>
                          match natMatcherArgs? ctx.env (.const primitive []) args with
                          | some (scrutinee, zeroArm, succArm) =>
                              Demand.branch
                                (demandExpr ctx visiting scrutinee)
                                (demandUnitExprArm ctx visiting zeroArm)
                                (demandNatSuccExprArm ctx visiting succArm)
                          | none =>
                              match productMatcherArgs? ctx.env (.const primitive []) args with
                              | some (scrutinee, arm) =>
                                  demandProductExprArm ctx visiting scrutinee arm
                              | none =>
                                  if (functionIndex? ctx primitive).isSome || localInlineFunction? ctx primitive then
                                      demandCall ctx visiting primitive args
                                  else
                                      match primitiveArgPair? args with
                                      | some (left, right) =>
                                          Demand.always
                                            (demandExpr ctx visiting left)
                                            (demandExpr ctx visiting right)
                                      | none =>
                                          args.foldl
                                            (fun acc arg => Demand.always acc (demandExpr ctx visiting arg))
                                            .empty
          | (fn, args) =>
              (fn :: args).foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty

partial def demandProductField
    (ctx : Context)
    (visiting : List Name)
    (index : Nat)
    (expr : Expr) : Demand :=
  match appFnArgs expr with
  | (.const ``Prod.mk _, args) =>
      match args.reverse with
      | right :: left :: _ =>
          if index == 0 then demandExpr ctx visiting left
          else if index == 1 then demandExpr ctx visiting right
          else .empty
      | _ => .empty
  | (.const ``Array.swapAt _, args) =>
      match args.reverse with
      | _proof :: value :: arrayIndex :: array :: _ =>
          let arrayDemand := demandExpr ctx visiting array
          let indexDemand := demandExpr ctx visiting arrayIndex
          if index == 0 then
            Demand.always arrayDemand indexDemand
          else if index == 1 then
            Demand.always (Demand.always arrayDemand indexDemand) (demandExpr ctx visiting value)
          else
            .empty
      | _ => .empty
  | _ => demandExpr ctx visiting expr

partial def demandOptionGet
    (ctx : Context)
    (visiting : List Name)
    (expr : Expr) : Demand :=
  match expr.consumeMData with
  | .bvar index => { may := [index], must := [index], mayTrap := true }
  | .letE _ _ value body _ => Demand.letE (demandExpr ctx visiting value) (demandOptionGet ctx visiting body)
  | .mdata _ body => demandOptionGet ctx visiting body
  | _ =>
      match appFnArgs expr with
      | (.const ``Option.none _, _) => .trap
      | (.const ``Option.some _, args) =>
          match args.reverse with
          | value :: _ => demandExpr ctx visiting value
          | _ => .empty
      | _ =>
          let demand := demandExpr ctx visiting expr
          { demand with mayTrap := true }

partial def demandExceptTag
    (ctx : Context)
    (visiting : List Name)
    (expr : Expr) : Demand :=
  match expr.consumeMData with
  | .bvar index => .bvar index
  | .letE _ _ value body _ => Demand.letE (demandExpr ctx visiting value) (demandExceptTag ctx visiting body)
  | .mdata _ body => demandExceptTag ctx visiting body
  | _ =>
      match appFnArgs expr with
      | (.const ``Except.error _, _) => .empty
      | (.const ``Except.ok _, _) => .empty
      | _ => demandExpr ctx visiting expr

partial def demandCond
    (ctx : Context)
    (visiting : List Name)
    (expr : Expr) : Demand :=
  match expr.consumeMData with
  | .bvar index => .bvar index
  | .letE _ _ value body _ => Demand.letE (demandExpr ctx visiting value) (demandCond ctx visiting body)
  | .mdata _ body => demandCond ctx visiting body
  | .const ``Bool.true _ => .empty
  | .const ``Bool.false _ => .empty
  | .const ``True _ => .empty
  | .const ``False _ => .empty
  | _ =>
      match appFnArgs expr with
      | (.const ``Eq _, [ty, left, right]) =>
          match typeAtom? ctx.env ty with
          | some eqTy =>
              if supportedEqType eqTy then
                Demand.always (demandExpr ctx visiting left) (demandExpr ctx visiting right)
              else
                .empty
          | none => .empty
      | (.const ``Decidable.decide _, [prop, _inst]) => demandCond ctx visiting prop
      | (.const ``dite _, [_ty, condExpr, _, thenArm, elseArm]) =>
          Demand.branch
            (demandCond ctx visiting condExpr)
            (demandUnitCondArm ctx visiting thenArm)
            (demandUnitCondArm ctx visiting elseArm)
      | (.const ``And _, [left, right]) =>
          let leftDemand := demandCond ctx visiting left
          let rightDemand := demandCond ctx visiting right
          {
            may := unionNat leftDemand.may rightDemand.may,
            must := leftDemand.must,
            mayTrap := leftDemand.mayTrap || rightDemand.mayTrap
          }
      | (.const ``Or _, [left, right]) =>
          let leftDemand := demandCond ctx visiting left
          let rightDemand := demandCond ctx visiting right
          {
            may := unionNat leftDemand.may rightDemand.may,
            must := leftDemand.must,
            mayTrap := leftDemand.mayTrap || rightDemand.mayTrap
          }
      | (.const ``Not _, [arg]) => demandCond ctx visiting arg
      | (.const ``BEq.beq _, args) =>
          match primitiveArgPair? args with
          | some (left, right) =>
              Demand.always
                (demandExpr ctx visiting left)
                (demandExpr ctx visiting right)
          | none => .empty
      | (.const ``LT.lt _, args) =>
          match primitiveArgPair? args with
          | some (left, right) =>
              Demand.always
                (demandExpr ctx visiting left)
                (demandExpr ctx visiting right)
          | none => .empty
      | (.const ``LE.le _, args) =>
          match primitiveArgPair? args with
          | some (left, right) =>
              Demand.always
                (demandExpr ctx visiting left)
                (demandExpr ctx visiting right)
          | none => .empty
      | (.const ``GT.gt _, args) =>
          match primitiveArgPair? args with
          | some (left, right) =>
              Demand.always
                (demandExpr ctx visiting left)
                (demandExpr ctx visiting right)
          | none => .empty
      | (.const ``GE.ge _, args) =>
          match primitiveArgPair? args with
          | some (left, right) =>
              Demand.always
                (demandExpr ctx visiting left)
                (demandExpr ctx visiting right)
          | none => .empty
      | (.const ``Bool.not _, [arg]) => demandCond ctx visiting arg
      | (.const ``Except.isOk _, args) =>
          match args.reverse with
          | exceptValue :: _ => demandExceptTag ctx visiting exceptValue
          | _ => .empty
      | (.const ``Bool.or _, [left, right]) =>
          let leftDemand := demandCond ctx visiting left
          let rightDemand := demandCond ctx visiting right
          {
            may := unionNat leftDemand.may rightDemand.may,
            must := leftDemand.must,
            mayTrap := leftDemand.mayTrap || rightDemand.mayTrap
          }
      | (.const ``Bool.and _, [left, right]) =>
          let leftDemand := demandCond ctx visiting left
          let rightDemand := demandCond ctx visiting right
          {
            may := unionNat leftDemand.may rightDemand.may,
            must := leftDemand.must,
            mayTrap := leftDemand.mayTrap || rightDemand.mayTrap
          }
      | (.const name _, args) =>
          match boolMatcherArgs? ctx.env (.const name []) args with
          | some (scrutinee, falseArm, trueArm) =>
              Demand.branch
                (demandCond ctx visiting scrutinee)
                (demandUnitCondArm ctx visiting trueArm)
                (demandUnitCondArm ctx visiting falseArm)
          | none =>
              match exceptMatcherArgs? ctx.env (.const name []) args with
              | some (scrutinee, errorArm, okArm) =>
                  Demand.branch
                    (demandExpr ctx visiting scrutinee)
                    (demandOptionSomeCondArm ctx visiting errorArm)
                    (demandOptionSomeCondArm ctx visiting okArm)
              | none =>
                  match natMatcherArgs? ctx.env (.const name []) args with
                  | some (scrutinee, zeroArm, succArm) =>
                      Demand.branch
                        (demandExpr ctx visiting scrutinee)
                        (demandUnitCondArm ctx visiting zeroArm)
                        (demandNatSuccCondArm ctx visiting succArm)
                  | none =>
                      match productMatcherArgs? ctx.env (.const name []) args with
                      | some (scrutinee, arm) =>
                          demandProductCondArm ctx visiting scrutinee arm
                      | none =>
                          if (functionIndex? ctx name).isSome || localInlineFunction? ctx name then
                            demandCall ctx visiting name args
                          else
                            args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
      | _ => demandExpr ctx visiting expr

partial def demandProductArmFromBody
    (ctx : Context)
    (visiting : List Name)
    (scrutinee : Expr)
    (bodyDemand : Demand) : Demand :=
  let leftMay := bodyDemand.may.contains 1
  let rightMay := bodyDemand.may.contains 0
  let leftMust := bodyDemand.must.contains 1
  let rightMust := bodyDemand.must.contains 0
  let outer := decDemand (decDemand bodyDemand)
  let leftDemand := demandProductField ctx visiting 0 scrutinee
  let rightDemand := demandProductField ctx visiting 1 scrutinee
  {
    may :=
      unionNat outer.may
        (unionNat
          (if leftMay then leftDemand.may else [])
          (if rightMay then rightDemand.may else [])),
    must :=
      unionNat outer.must
        (unionNat
          (if leftMust then leftDemand.must else [])
          (if rightMust then rightDemand.must else [])),
    mayTrap :=
      outer.mayTrap ||
        (leftMay && leftDemand.mayTrap) ||
        (rightMay && rightDemand.mayTrap)
  }

partial def demandProductExprArm
    (ctx : Context)
    (visiting : List Name)
    (scrutinee arm : Expr) : Demand :=
  match collectLambdas arm 2 with
  | some body => demandProductArmFromBody ctx visiting scrutinee (demandExpr ctx visiting body)
  | none => .empty

partial def demandProductCondArm
    (ctx : Context)
    (visiting : List Name)
    (scrutinee arm : Expr) : Demand :=
  match collectLambdas arm 2 with
  | some body => demandProductArmFromBody ctx visiting scrutinee (demandCond ctx visiting body)
  | none => .empty

partial def demandCall
    (ctx : Context)
    (visiting : List Name)
    (name : Name)
    (args : List Expr) : Demand :=
  let summary := demandSummary ctx visiting name
  let indexed := enumerate args
  indexed.foldl
    (fun acc item =>
      let argDemand := demandExpr ctx visiting item.snd
      {
        may :=
          unionNat acc.may
            (if boolAt summary.mayDemand item.fst then argDemand.may else []),
        must :=
          unionNat acc.must
            (if boolAt summary.mustDemand item.fst then argDemand.must else []),
        mayTrap :=
          acc.mayTrap ||
            (boolAt summary.mayDemand item.fst && argDemand.mayTrap)
      })
    { may := [], must := [], mayTrap := summary.selfMayTrap }

partial def demandOptionNoneArm
    (ctx : Context)
    (visiting : List Name)
    (noneArm : Expr) : Demand :=
  match collectLambdas noneArm 1 with
  | some body => decDemand (demandExpr ctx visiting body)
  | none => demandExpr ctx visiting noneArm

partial def demandOptionSomeArm
    (ctx : Context)
    (visiting : List Name)
    (someArm : Expr) : Demand :=
  match collectLambdas someArm 1 with
  | some body => decDemand (demandExpr ctx visiting body)
  | none => .empty

partial def demandNatSuccExprArm
    (ctx : Context)
    (visiting : List Name)
    (succArm : Expr) : Demand :=
  match collectLambdas succArm 1 with
  | some body => decDemand (demandExpr ctx visiting body)
  | none => .empty

partial def demandUnitExprArm
    (ctx : Context)
    (visiting : List Name)
    (arm : Expr) : Demand :=
  match collectLambdas arm 1 with
  | some body => decDemand (demandExpr ctx visiting body)
  | none => demandExpr ctx visiting arm

partial def demandUnitCondArm
    (ctx : Context)
    (visiting : List Name)
    (arm : Expr) : Demand :=
  match collectLambdas arm 1 with
  | some body => decDemand (demandCond ctx visiting body)
  | none => demandCond ctx visiting arm

partial def demandNatSuccCondArm
    (ctx : Context)
    (visiting : List Name)
    (succArm : Expr) : Demand :=
  match collectLambdas succArm 1 with
  | some body => decDemand (demandCond ctx visiting body)
  | none => .empty

partial def demandOptionSomeCondArm
    (ctx : Context)
    (visiting : List Name)
    (someArm : Expr) : Demand :=
  match collectLambdas someArm 1 with
  | some body => decDemand (demandCond ctx visiting body)
  | none => .empty

partial def demandSummary
    (ctx : Context)
    (visiting : List Name)
    (name : Name) : DemandSummary :=
  match ctx.env.find? name with
  | none => { mayDemand := [], mustDemand := [], selfMayTrap := true }
  | some info =>
      match supportedInlineFunction? ctx.env info with
      | none => { mayDemand := [], mustDemand := [], selfMayTrap := true }
      | some sig =>
          if containsConstant ``Nat.brecOn info ||
              containsConstant ``WellFounded.Nat.fix info ||
              containsConstant name info then
            DemandSummary.recursive sig.params.length
          else if visiting.contains name then
            DemandSummary.recursive sig.params.length
          else
            match info.value? with
            | none => { mayDemand := List.replicate sig.params.length true, mustDemand := [], selfMayTrap := true }
            | some value =>
                match collectLambdas value sig.params.length with
                | none => { mayDemand := List.replicate sig.params.length true, mustDemand := [], selfMayTrap := true }
                | some body =>
                    DemandSummary.fromDemand sig.params.length (demandExpr ctx (name :: visiting) body)
end

def mayTrapExpr (ctx : Context) (expr : Expr) : Bool :=
  (demandExpr ctx [] expr).mayTrap

def strictCallSafe (ctx : Context) (name : Name) (args : List Expr) : Bool :=
  let summary := demandSummary ctx [] name
  let indexed := enumerate args
  indexed.all fun item =>
    !mayTrapExpr ctx item.snd || boolAt summary.mustDemand item.fst

def strictCallMaterializationSafe (ctx : Context) (params : List Ty) (args : List Expr) : Bool :=
  params.zip args |>.all fun item =>
    internalSlots item.fst == 1 || !mayTrapExpr ctx item.snd

def strictRecursiveCallCheck (ctx : Context) (name : Name) (args : List Expr) :
    Except String Unit := do
  let summary := demandSummary ctx [] name
  let indexed := enumerate args
  for item in indexed do
    if mayTrapExpr ctx item.snd && !boolAt summary.mustDemand item.fst then
      .error s!"strict call may evaluate an argument not demanded by callee: {name}"
  .ok ()

def strictCallMaterializationCheck
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (args : List Expr) :
    Except String Unit := do
  for item in params.zip args do
    if internalSlots item.fst != 1 && mayTrapExpr ctx item.snd then
      .error s!"strict call may materialize trapping structured argument fields: {name}"
  .ok ()

end LeanExe.Extract.Core
