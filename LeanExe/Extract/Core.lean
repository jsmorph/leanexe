import Lean
import LeanExe.Extract.Env
import LeanExe.IR.Core

open Lean

namespace LeanExe.Extract.Core

abbrev Ty := LeanExe.IR.Ty
abbrev IRExpr := LeanExe.IR.Expr
abbrev IRCond := LeanExe.IR.Cond
abbrev IRStmt := LeanExe.IR.Stmt
abbrev IRFunc := LeanExe.IR.Func
abbrev IRModule := LeanExe.IR.Module

structure Signature where
  params : List Ty
  result : Ty
  deriving BEq, Repr

inductive ExtractedValue where
  | scalar (expr : IRExpr)
  | byteArray (ptr len : IRExpr)
  | product (left right : ExtractedValue)
  | option (tag : IRExpr) (payload : ExtractedValue)
  deriving BEq, Repr

inductive Binding where
  | slot (index : Nat)
  | value (value : ExtractedValue)
  | thunk (locals : List Binding) (expr : Expr)
  | recursor
  deriving BEq, Repr

structure Context where
  env : Environment
  names : Array Name

partial def appFnArgsAux (expr : Expr) (args : List Expr) : Expr × List Expr :=
  match expr.consumeMData with
  | .app fn arg => appFnArgsAux fn (arg :: args)
  | other => (other, args)

def appFnArgs (expr : Expr) : Expr × List Expr :=
  appFnArgsAux expr []

def isConst (name : Name) (expr : Expr) : Bool :=
  expr.consumeMData.isConstOf name

def isBVar (index : Nat) (expr : Expr) : Bool :=
  match expr.consumeMData with
  | .bvar candidate => candidate == index
  | _ => false

partial def containsBVar (index : Nat) (expr : Expr) : Bool :=
  if isBVar index expr then
    true
  else
    match expr.consumeMData with
    | .app fn arg => containsBVar index fn || containsBVar index arg
    | .lam _ type body _ => containsBVar (index + 1) type || containsBVar (index + 1) body
    | .forallE _ type body _ => containsBVar index type || containsBVar (index + 1) body
    | .letE _ type value body _ =>
        containsBVar index type ||
          containsBVar index value ||
          containsBVar (index + 1) body
    | .mdata _ body => containsBVar index body
    | .proj _ _ body => containsBVar index body
    | _ => false

def natLit? (expr : Expr) : Option Nat :=
  match expr.consumeMData with
  | .lit (.natVal value) => some value
  | _ => none

def ofNat? (typeName : Name) (expr : Expr) : Option Nat :=
  match appFnArgs expr with
  | (.const ``OfNat.ofNat _, [ty, value, _]) =>
      if isConst typeName ty then natLit? value else none
  | _ => none

def constNatValue? (env : Environment) (name : Name) : Option Nat :=
  match env.find? name with
  | none => none
  | some info =>
      match info.value? with
      | none => none
      | some value => ofNat? ``Nat value

def runtimeNatLimit : Nat :=
  2 ^ 64

def boundedNatExpr (value : Nat) : Except String IRExpr :=
  if value < runtimeNatLimit then
    .ok (.u64 value)
  else
    .error s!"Nat literal exceeds bounded runtime representation: {value}"

def scalarLiteralExpr? (expr : Expr) : Option (Except String IRExpr) :=
  match ofNat? ``UInt64 expr with
  | some value => some (.ok (.u64 value))
  | none =>
      match ofNat? ``UInt8 expr with
      | some value => some (.ok (.u64 (value % 256)))
      | none =>
          match ofNat? ``Nat expr with
          | some value => some (boundedNatExpr value)
          | none => none

partial def typeAtom? (expr : Expr) : Option Ty :=
  if isConst ``UInt64 expr then
    some .u64
  else if isConst ``Nat expr then
    some .nat
  else if isConst ``Bool expr then
    some .bool
  else if isConst ``UInt8 expr then
    some .u8
  else if isConst ``UInt32 expr then
    some .u32
  else if isConst ``ByteArray expr then
    some .byteArray
  else
    match appFnArgs expr with
    | (.const ``Array _, [item]) => typeAtom? item |>.map .array
    | (.const ``Prod _, [left, right]) =>
        match typeAtom? left, typeAtom? right with
        | some leftTy, some rightTy => some (.product leftTy rightTy)
        | _, _ => none
    | (.const ``Option _, [item]) => typeAtom? item |>.map (fun itemTy => .sum .unit itemTy)
    | _ => none

def supportedAbiType : Ty → Bool
  | .bool => true
  | .u64 => true
  | .nat => true
  | .array .u64 => true
  | _ => false

def supportedParamAbiType : Ty → Bool
  | .byteArray => true
  | ty => supportedAbiType ty

def supportedResultAbiType : Ty → Bool :=
  supportedAbiType

def supportedInternalValueType : Ty → Bool
  | .bool => true
  | .u8 => true
  | .u64 => true
  | .nat => true
  | .array .u64 => true
  | _ => false

def supportedInternalParamType : Ty → Bool
  | .byteArray => true
  | ty => supportedInternalValueType ty

def supportedInternalResultType : Ty → Bool :=
  supportedInternalValueType

def abiSlots : Ty → Nat
  | .byteArray => 2
  | _ => 1

def abiParamCount (params : List Ty) : Nat :=
  params.foldl (fun total ty => total + abiSlots ty) 0

partial def peelForall (expr : Expr) : List Expr × Expr :=
  match expr.consumeMData with
  | .forallE _ domain body _ =>
      let rest := peelForall body
      (domain :: rest.fst, rest.snd)
  | other => ([], other)

def functionTypeWith?
    (paramSupported resultSupported : Ty → Bool)
    (type : Expr) : Option Signature :=
  let parts := peelForall type
  match typeAtom? parts.snd with
  | some result =>
      let params? := parts.fst.mapM typeAtom?
      match params? with
      | some params =>
          if resultSupported result && params.all paramSupported then
            some { params := params, result := result }
          else
            none
      | none => none
  | none => none

def entryFunctionType? (type : Expr) : Option Signature :=
  functionTypeWith? supportedParamAbiType supportedResultAbiType type

def functionType? (type : Expr) : Option Signature :=
  functionTypeWith? supportedInternalParamType supportedInternalResultType type

def supportedEntryFunction? (info : ConstantInfo) : Option Signature :=
  if info.isUnsafe || info.isPartial then
    none
  else
    entryFunctionType? info.type

def supportedFunction? (info : ConstantInfo) : Option Signature :=
  if info.isUnsafe || info.isPartial then
    none
  else
    functionType? info.type

def supportedLocalType : Ty → Bool
  | .bool => true
  | .u8 => true
  | .u64 => true
  | .nat => true
  | .byteArray => true
  | .array .u64 => true
  | .product left right => supportedLocalType left && supportedLocalType right
  | .sum .unit payload => supportedLocalType payload
  | _ => false

def pushName (names : List Name) (name : Name) : List Name :=
  if names.contains name then names else names ++ [name]

def usedConstantsOf (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  let fromValue :=
    match info.value? with
    | some value => value.getUsedConstants
    | none => #[]
  fromValue.foldl
    (fun acc name => if acc.contains name then acc else acc.push name)
    fromType

def containsConstant (name : Name) (info : ConstantInfo) : Bool :=
  info.value? |>.any (fun value => value.getUsedConstants.contains name)

partial def collectLambdas (expr : Expr) : Nat → Option Expr
  | 0 => some expr
  | count + 1 =>
      match expr.consumeMData with
      | .lam _ _ body _ => collectLambdas body count
      | _ => none

partial def collectReachable
    (env : Environment)
    (root entry : Name)
    (seen : List Name)
    (names : List Name) :
    Except String (List Name × List Name) := do
  if seen.contains entry then
    return (seen, names)
  let info ←
    match env.find? entry with
    | some info => .ok info
    | none => .error s!"entry not found: {entry}"
  let sig ←
    match supportedFunction? info with
    | some sig => .ok sig
    | none => .error s!"unsupported function type or declaration: {entry}"
  let mut nextSeen := pushName seen entry
  let mut nextNames := names
  for dep in usedConstantsOf info do
    if dep.getRoot == root then
      match env.find? dep with
      | some depInfo =>
          if dep != entry && (supportedFunction? depInfo |>.isSome) then
            let result ← collectReachable env root dep nextSeen nextNames
            nextSeen := result.fst
            nextNames := result.snd
      | none => pure ()
  let _ := sig
  return (nextSeen, pushName nextNames entry)

def functionIndex? (ctx : Context) (name : Name) : Option Nat :=
  let rec loop (index : Nat) : Option Nat :=
    if h : index < ctx.names.size then
      if ctx.names[index] == name then some index else loop (index + 1)
    else
      none
  loop 0

def lookupBinding (locals : List Binding) (index : Nat) : Except String Binding :=
  match locals[index]? with
  | some binding => .ok binding
  | none => .error s!"unbound de Bruijn variable: {index}"

def primitiveArgPair? (args : List Expr) : Option (Expr × Expr) :=
  match args.reverse with
  | right :: left :: _ => some (left, right)
  | _ => none

def primitiveResultType? (args : List Expr) : Option Ty :=
  match args with
  | _leftType :: _rightType :: resultType :: _ => typeAtom? resultType
  | _ => none

def primitiveReceiverType? (args : List Expr) : Option Ty :=
  match args with
  | ty :: _ => typeAtom? ty
  | _ => none

def boolExpr (cond : IRCond) : IRExpr :=
  .ite cond (.u64 1) (.u64 0)

def boolCond (expr : IRExpr) : IRCond :=
  .not (.eqU64 expr (.u64 0))

def u8WrapExpr (expr : IRExpr) : IRExpr :=
  .u64Bin .bitAnd expr (.u64 255)

def supportedEqType : Ty → Bool
  | .bool => true
  | .u8 => true
  | .u64 => true
  | .nat => true
  | _ => false

def scalarValue (value : ExtractedValue) : Except String IRExpr :=
  match value with
  | .scalar expr => .ok expr
  | .byteArray _ _ => .error "ByteArray value used where scalar value is required"
  | .product _ _ => .error "product value used where scalar value is required"
  | .option _ _ => .error "option value used where scalar value is required"

def byteArrayParts (value : ExtractedValue) : Except String (IRExpr × IRExpr) :=
  match value with
  | .byteArray ptr len => .ok (ptr, len)
  | .scalar _ => .error "scalar value used where ByteArray value is required"
  | .product _ _ => .error "product value used where ByteArray value is required"
  | .option _ _ => .error "option value used where ByteArray value is required"

def productField (index : Nat) (value : ExtractedValue) : Except String ExtractedValue :=
  match value with
  | .product left right =>
      if index == 0 then
        .ok left
      else if index == 1 then
        .ok right
      else
        .error s!"unsupported product projection index: {index}"
  | .scalar _ => .error "scalar value used where product value is required"
  | .byteArray _ _ => .error "ByteArray value used where product value is required"
  | .option _ _ => .error "option value used where product value is required"

def optionParts (value : ExtractedValue) : Except String (IRExpr × ExtractedValue) :=
  match value with
  | .option tag payload => .ok (tag, payload)
  | .scalar _ => .error "scalar value used where option value is required"
  | .byteArray _ _ => .error "ByteArray value used where option value is required"
  | .product _ _ => .error "product value used where option value is required"

partial def defaultValue : Ty → Except String ExtractedValue
  | .bool => .ok (.scalar (.u64 0))
  | .u8 => .ok (.scalar (.u64 0))
  | .u64 => .ok (.scalar (.u64 0))
  | .nat => .ok (.scalar (.u64 0))
  | .byteArray => .ok (.byteArray (.u64 0) (.u64 0))
  | .array .u64 => .ok (.scalar (.u64 0))
  | .product left right => do
      .ok (.product (← defaultValue left) (← defaultValue right))
  | .sum .unit payload => do
      .ok (.option (.u64 0) (← defaultValue payload))
  | other => .error s!"unsupported default value type: {reprStr other}"

partial def valueIte
    (cond : IRCond)
    (thenValue elseValue : ExtractedValue) :
    Except String ExtractedValue :=
  match thenValue, elseValue with
  | .scalar thenExpr, .scalar elseExpr => .ok (.scalar (.ite cond thenExpr elseExpr))
  | .byteArray thenPtr thenLen, .byteArray elsePtr elseLen =>
      .ok (.byteArray (.ite cond thenPtr elsePtr) (.ite cond thenLen elseLen))
  | .product thenLeft thenRight, .product elseLeft elseRight => do
      .ok (.product
        (← valueIte cond thenLeft elseLeft)
        (← valueIte cond thenRight elseRight))
  | .option thenTag thenPayload, .option elseTag elsePayload => do
      .ok (.option
        (.ite cond thenTag elseTag)
        (← valueIte cond thenPayload elsePayload))
  | _, _ => .error "if branches have incompatible structured value shapes"

def flattenAbiValue (ty : Ty) (value : ExtractedValue) : Except String (List IRExpr) :=
  match ty with
  | .bool => scalarValue value |>.map (fun expr => [expr])
  | .u8 => scalarValue value |>.map (fun expr => [expr])
  | .u64 => scalarValue value |>.map (fun expr => [expr])
  | .nat => scalarValue value |>.map (fun expr => [expr])
  | .array .u64 => scalarValue value |>.map (fun expr => [expr])
  | .byteArray => do
      let parts ← byteArrayParts value
      .ok [parts.fst, parts.snd]
  | other => .error s!"unsupported ABI value type: {reprStr other}"

def bindingForParam (slot : Nat) : Ty → Binding
  | .byteArray => .value (.byteArray (.local slot) (.local (slot + 1)))
  | _ => .slot slot

partial def sourceParamBindingsFrom (slot : Nat) : List Ty → List Binding
  | [] => []
  | ty :: rest => bindingForParam slot ty :: sourceParamBindingsFrom (slot + abiSlots ty) rest

def sourceParamBindings (params : List Ty) : List Binding :=
  sourceParamBindingsFrom 0 params

partial def abiTargetsFrom (slot : Nat) : List Ty → List (Ty × List Nat)
  | [] => []
  | ty :: rest =>
      let slots := (List.range (abiSlots ty)).map (fun offset => slot + offset)
      (ty, slots) :: abiTargetsFrom (slot + abiSlots ty) rest

def abiTargets (params : List Ty) : List (Ty × List Nat) :=
  abiTargetsFrom 0 params

def optionConstructorType? (args : List Expr) : Option Ty :=
  match args with
  | ty :: _ => typeAtom? ty
  | [] => none

def isMatcherName (candidate : Name) : Bool :=
  match candidate with
  | .str _ component => component.startsWith "match_"
  | _ => false

def generatedMatcherScrutineeType? (env : Environment) (name : Name) : Option Ty :=
  if !isMatcherName name then
    none
  else
    match env.find? name with
    | some info =>
        match (peelForall info.type).fst with
        | _motive :: scrutineeType :: _ => typeAtom? scrutineeType
        | _ => none
    | none => none

def optionMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Option.casesOn || name == ``Option.rec then
        match args.reverse with
        | someArm :: noneArm :: scrutinee :: _ => some (scrutinee, noneArm, someArm)
        | _ => none
      else
        match generatedMatcherScrutineeType? env name with
        | some (.sum .unit _) =>
            match args with
            | [_motive, scrutinee, noneArm, someArm] => some (scrutinee, noneArm, someArm)
            | _ => none
        | _ => none
  | _ => none

def boolMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Bool.casesOn then
        match args with
        | [_motive, scrutinee, falseArm, trueArm] => some (scrutinee, falseArm, trueArm)
        | _ => none
      else if generatedMatcherScrutineeType? env name == some .bool then
        match args with
        | [_motive, scrutinee, falseArm, trueArm] => some (scrutinee, falseArm, trueArm)
        | _ => none
      else
        none
  | _ => none

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
          | (.const ``Decidable.decide _, [prop, _inst]) =>
              demandCond ctx visiting prop
          | (.const ``Prod.fst _, args) =>
              match args.reverse with
              | product :: _ => demandProductField ctx visiting 0 product
              | _ => .empty
          | (.const ``Prod.snd _, args) =>
              match args.reverse with
              | product :: _ => demandProductField ctx visiting 1 product
              | _ => .empty
          | (.const ``ByteArray.size _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.isEmpty _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.get! _, _) => .trap
          | (.const ``Array.size _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.isEmpty _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.push _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.pop _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``Array.get!Internal _, _) => .trap
          | (.const ``GetElem?.getElem! _, _) => .trap
          | (.const ``Array.back! _, _) => .trap
          | (.const ``Array.getD _, args) =>
              match args.reverse with
              | defaultValue :: index :: array :: _ =>
                  let arrayDemand := demandExpr ctx visiting array
                  let indexDemand := demandExpr ctx visiting index
                  let defaultDemand := demandExpr ctx visiting defaultValue
                  Demand.branch (Demand.always arrayDemand indexDemand) .empty defaultDemand
              | _ => .empty
          | (.const ``Array.set! _, _) => .trap
          | (.const primitive _, args) =>
              match boolMatcherArgs? ctx.env (.const primitive []) args with
              | some (scrutinee, falseArm, trueArm) =>
                  Demand.branch
                    (demandCond ctx visiting scrutinee)
                    (demandUnitExprArm ctx visiting trueArm)
                    (demandUnitExprArm ctx visiting falseArm)
              | none =>
                  match optionMatcherArgs? ctx.env (.const primitive []) args with
                  | some (scrutinee, noneArm, someArm) =>
                      Demand.branch
                        (demandExpr ctx visiting scrutinee)
                        (demandOptionNoneArm ctx visiting noneArm)
                        (demandOptionSomeArm ctx visiting someArm)
                  | none =>
                      match functionIndex? ctx primitive with
                      | some _ =>
                          demandCall ctx visiting primitive args
                      | none =>
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
          match typeAtom? ty with
          | some eqTy =>
              if supportedEqType eqTy then
                Demand.always (demandExpr ctx visiting left) (demandExpr ctx visiting right)
              else
                .empty
          | none => .empty
      | (.const ``Decidable.decide _, [prop, _inst]) => demandCond ctx visiting prop
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
              match functionIndex? ctx name with
              | some _ => demandCall ctx visiting name args
              | none => args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
      | _ => demandExpr ctx visiting expr

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

partial def demandSummary
    (ctx : Context)
    (visiting : List Name)
    (name : Name) : DemandSummary :=
  match ctx.env.find? name with
  | none => { mayDemand := [], mustDemand := [], selfMayTrap := true }
  | some info =>
      match supportedFunction? info with
      | none => { mayDemand := [], mustDemand := [], selfMayTrap := true }
      | some sig =>
          if containsConstant ``Nat.brecOn info || containsConstant name info then
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

def strictRecursiveCallCheck (ctx : Context) (name : Name) (args : List Expr) :
    Except String Unit := do
  let summary := demandSummary ctx [] name
  let indexed := enumerate args
  for item in indexed do
    if mayTrapExpr ctx item.snd && !boolAt summary.mustDemand item.fst then
      .error s!"strict call may evaluate an argument not demanded by callee: {name}"
  .ok ()

mutual
  partial def extractValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr : Expr) :
      Except String (ExtractedValue × Nat) := do
    match expr.consumeMData with
    | .bvar index =>
        match ← lookupBinding locals index with
        | .slot slot => .ok (.scalar (.local slot), nextLocal)
        | .value value => .ok (value, nextLocal)
        | .thunk savedLocals value => extractValueFrom ctx savedLocals nextLocal value
        | .recursor => .error "recursive handle used as a value"
    | .letE _ type value body _ =>
        if !containsBVar 0 body then
          extractValueFrom ctx (.recursor :: locals) nextLocal body
        else
          match typeAtom? type with
          | some ty =>
              if supportedLocalType ty then
                extractValueFrom ctx (.thunk locals value :: locals) nextLocal body
              else
                .error s!"unsupported let-bound type: {type}"
          | none => .error s!"unsupported let-bound type: {type}"
    | .proj ``Prod index body =>
        let valueResult ← extractValueFrom ctx locals nextLocal body
        .ok (← productField index valueResult.fst, valueResult.snd)
    | .proj typeName _ _ => .error s!"unsupported projection: {typeName}"
    | _ =>
        match appFnArgs expr with
        | (.const ``Prod.mk _, args) =>
            match args.reverse with
            | right :: left :: _ =>
                let leftResult ← extractValueFrom ctx locals nextLocal left
                let rightResult ← extractValueFrom ctx locals leftResult.snd right
                .ok (.product leftResult.fst rightResult.fst, rightResult.snd)
            | _ => .error "unsupported product constructor"
        | (.const ``Prod.fst _, args) =>
            match args.reverse with
            | product :: _ =>
                let valueResult ← extractValueFrom ctx locals nextLocal product
                .ok (← productField 0 valueResult.fst, valueResult.snd)
            | _ => .error "unsupported Prod.fst application"
        | (.const ``Prod.snd _, args) =>
            match args.reverse with
            | product :: _ =>
                let valueResult ← extractValueFrom ctx locals nextLocal product
                .ok (← productField 1 valueResult.fst, valueResult.snd)
            | _ => .error "unsupported Prod.snd application"
        | (.const ``Option.none _, args) =>
            match optionConstructorType? args with
            | some payloadTy =>
                .ok (.option (.u64 0) (← defaultValue payloadTy), nextLocal)
            | none => .error "unsupported Option.none application"
        | (.const ``Option.some _, args) =>
            match args.reverse, optionConstructorType? args with
            | value :: _, some _ =>
                let valueResult ← extractValueFrom ctx locals nextLocal value
                .ok (.option (.u64 1) valueResult.fst, valueResult.snd)
            | _, _ => .error "unsupported Option.some application"
        | (.const ``Bool.casesOn _, args) =>
            match boolMatcherArgs? ctx.env (.const ``Bool.casesOn []) args with
            | some (scrutinee, falseArm, trueArm) =>
                let condResult ← extractCondFrom ctx locals nextLocal scrutinee
                let falseResult ← extractUnitArmValueFrom ctx locals condResult.snd falseArm
                let trueResult ← extractUnitArmValueFrom ctx locals falseResult.snd trueArm
                .ok (← valueIte condResult.fst trueResult.fst falseResult.fst, trueResult.snd)
            | none => .error "unsupported Bool.casesOn application"
        | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
            match typeAtom? ty with
            | some .byteArray =>
                let condResult ← extractCondFrom ctx locals nextLocal condExpr
                let thenResult ← extractValueFrom ctx locals condResult.snd thenExpr
                let elseResult ← extractValueFrom ctx locals thenResult.snd elseExpr
                .ok (← valueIte condResult.fst thenResult.fst elseResult.fst, elseResult.snd)
            | some (.product _ _) =>
                let condResult ← extractCondFrom ctx locals nextLocal condExpr
                let thenResult ← extractValueFrom ctx locals condResult.snd thenExpr
                let elseResult ← extractValueFrom ctx locals thenResult.snd elseExpr
                .ok (← valueIte condResult.fst thenResult.fst elseResult.fst, elseResult.snd)
            | some (.sum .unit _) =>
                let condResult ← extractCondFrom ctx locals nextLocal condExpr
                let thenResult ← extractValueFrom ctx locals condResult.snd thenExpr
                let elseResult ← extractValueFrom ctx locals thenResult.snd elseExpr
                .ok (← valueIte condResult.fst thenResult.fst elseResult.fst, elseResult.snd)
            | _ =>
                let exprResult ← extractExprFrom ctx locals nextLocal expr
                .ok (.scalar exprResult.fst, exprResult.snd)
        | (fn, args) =>
            match boolMatcherArgs? ctx.env fn args with
            | some (scrutinee, falseArm, trueArm) =>
                let condResult ← extractCondFrom ctx locals nextLocal scrutinee
                let falseResult ← extractUnitArmValueFrom ctx locals condResult.snd falseArm
                let trueResult ← extractUnitArmValueFrom ctx locals falseResult.snd trueArm
                .ok (← valueIte condResult.fst trueResult.fst falseResult.fst, trueResult.snd)
            | none =>
                match optionMatcherArgs? ctx.env fn args with
                | some (scrutinee, noneArm, someArm) =>
                    extractOptionMatchValueFrom ctx locals nextLocal scrutinee noneArm someArm
                | none =>
                    let exprResult ← extractExprFrom ctx locals nextLocal expr
                    .ok (.scalar exprResult.fst, exprResult.snd)

  partial def extractUnitArmValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (arm : Expr) :
      Except String (ExtractedValue × Nat) := do
    match collectLambdas arm 1 with
    | some body => extractValueFrom ctx (.value (.scalar (.u64 0)) :: locals) nextLocal body
    | none => extractValueFrom ctx locals nextLocal arm

  partial def extractOptionMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (scrutinee noneArm someArm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
    let parts ← optionParts scrutineeResult.fst
    let noneArmResult ←
      match collectLambdas noneArm 1 with
      | some body => .ok (body, .value (.scalar (.u64 0)) :: locals)
      | none => .ok (noneArm, locals)
    let noneResult ←
      extractValueFrom ctx noneArmResult.snd scrutineeResult.snd noneArmResult.fst
    let someBody ←
      match collectLambdas someArm 1 with
      | some body => .ok body
      | none => .error "unsupported Option.some matcher arm"
    let someResult ←
      extractValueFrom ctx (.value parts.snd :: locals) noneResult.snd someBody
    .ok (← valueIte (.eqU64 parts.fst (.u64 0)) noneResult.fst someResult.fst, someResult.snd)

  partial def extractInlineCallValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (name : Name)
      (args : List Expr) :
      Except String (Option (ExtractedValue × Nat)) := do
    if (functionIndex? ctx name).isNone then
      return none
    let info ←
      match ctx.env.find? name with
      | some info => .ok info
      | none => .error s!"declaration disappeared during extraction: {name}"
    if containsConstant ``Nat.brecOn info || containsConstant name info then
      return none
    let sig ←
      match supportedFunction? info with
      | some sig => .ok sig
      | none => .error s!"unsupported function type or declaration: {name}"
    if args.length != sig.params.length then
      .error s!"inline call arity mismatch: {name}"
    else
      let value ←
        match info.value? with
        | some value => .ok value
        | none => .error s!"declaration has no executable value: {name}"
      let body ←
        match collectLambdas value sig.params.length with
        | some body => .ok body
        | none => .error s!"definition body does not match function arity: {name}"
      let argBindings := args.reverse.map (fun arg => Binding.thunk locals arg)
      let result ← extractValueFrom ctx argBindings nextLocal body
      .ok (some result)

  partial def extractExprFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr : Expr) :
      Except String (IRExpr × Nat) := do
    match expr.consumeMData with
    | .bvar index =>
        match ← lookupBinding locals index with
        | .slot slot => .ok (.local slot, nextLocal)
        | .value value => .ok (← scalarValue value, nextLocal)
        | .thunk savedLocals value =>
            let valueResult ← extractValueFrom ctx savedLocals nextLocal value
            .ok (← scalarValue valueResult.fst, valueResult.snd)
        | .recursor => .error "recursive handle used as a value"
    | .letE _ type value body _ =>
        if !containsBVar 0 body then
          extractExprFrom ctx (.recursor :: locals) nextLocal body
        else
          match typeAtom? type with
          | some ty =>
              if supportedLocalType ty then
                extractExprFrom ctx (.thunk locals value :: locals) nextLocal body
              else
                .error s!"unsupported let-bound type: {type}"
          | none => .error s!"unsupported let-bound type: {type}"
    | .proj ``Prod index body =>
        let valueResult ← extractValueFrom ctx locals nextLocal body
        .ok (← scalarValue (← productField index valueResult.fst), valueResult.snd)
    | .proj typeName _ _ => .error s!"unsupported projection: {typeName}"
    | .const ``Bool.true _ => .ok (.u64 1, nextLocal)
    | .const ``Bool.false _ => .ok (.u64 0, nextLocal)
    | .const name _ =>
        match constNatValue? ctx.env name with
        | some value => .ok (← boundedNatExpr value, nextLocal)
        | none =>
            match functionIndex? ctx name with
            | some index => .ok (.call index [], nextLocal)
            | none => .error s!"unsupported constant in expression: {name}"
    | _ =>
        match scalarLiteralExpr? expr with
        | some result => .ok (← result, nextLocal)
        | none =>
          match appFnArgs expr with
            | (.const ``Bool.casesOn _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Decidable.decide _, [prop, _inst]) =>
                let condResult ← extractCondFrom ctx locals nextLocal prop
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
                if typeAtom? ty |>.isSome then
                  let condResult ← extractCondFrom ctx locals nextLocal condExpr
                  let thenResult ← extractExprFrom ctx locals condResult.snd thenExpr
                  let elseResult ← extractExprFrom ctx locals thenResult.snd elseExpr
                  .ok (.ite condResult.fst thenResult.fst elseResult.fst, elseResult.snd)
                else
                  .error "unsupported if-result type"
            | (.const ``Bool.or _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Bool.and _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Bool.not _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Array.replicate _, args) =>
                match args.reverse with
                | value :: cells :: _ =>
                    let valueResult ← extractExprFrom ctx locals nextLocal value
                    let cellsResult ← extractExprFrom ctx locals valueResult.snd cells
                    match valueResult.fst with
                    | .u64 0 => .ok (.arrayAlloc cellsResult.fst, cellsResult.snd)
                    | _ => .ok (.arrayReplicate cellsResult.fst valueResult.fst, cellsResult.snd)
                | _ => .error "unsupported Array.replicate application"
            | (.const ``Array.size _, args) =>
                match args.reverse with
                | array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    .ok (.arraySize arrayResult.fst, arrayResult.snd)
                | _ => .error "unsupported Array.size application"
            | (.const ``Array.isEmpty _, args) =>
                match args.reverse with
                | array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    .ok (boolExpr (.eqU64 (.arraySize arrayResult.fst) (.u64 0)), arrayResult.snd)
                | _ => .error "unsupported Array.isEmpty application"
            | (.const ``Array.push _, args) =>
                match args.reverse with
                | value :: array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let valueResult ← extractExprFrom ctx locals arrayResult.snd value
                    .ok (.arrayPush arrayResult.fst valueResult.fst, valueResult.snd)
                | _ => .error "unsupported Array.push application"
            | (.const ``Array.pop _, args) =>
                match args.reverse with
                | array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    .ok (.arrayPop arrayResult.fst, arrayResult.snd)
                | _ => .error "unsupported Array.pop application"
            | (.const ``Array.get!Internal _, args) =>
                match args.reverse with
                | index :: array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    .ok (.arrayGet arrayResult.fst indexResult.fst, indexResult.snd)
                | _ => .error "unsupported Array.get!Internal application"
            | (.const ``GetElem?.getElem! _, args) =>
                match args.reverse with
                | index :: array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    .ok (.arrayGet arrayResult.fst indexResult.fst, indexResult.snd)
                | _ => .error "unsupported GetElem?.getElem! application"
            | (.const ``Array.back! _, args) =>
                match args.reverse with
                | array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let slot := arrayResult.snd
                    let value :=
                      .arrayGet (.local slot) (.u64Bin .sub (.arraySize (.local slot)) (.u64 1))
                    .ok (.letE slot arrayResult.fst value, slot + 1)
                | _ => .error "unsupported Array.back! application"
            | (.const ``Array.getD _, args) =>
                match args.reverse with
                | defaultValue :: index :: array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let arraySlot := indexResult.snd
                    let indexSlot := arraySlot + 1
                    let defaultResult ← extractExprFrom ctx locals (indexSlot + 1) defaultValue
                    let value :=
                      .ite
                        (.ltU64 (.local indexSlot) (.arraySize (.local arraySlot)))
                        (.arrayGet (.local arraySlot) (.local indexSlot))
                        defaultResult.fst
                    .ok (.letE arraySlot arrayResult.fst (.letE indexSlot indexResult.fst value),
                      defaultResult.snd)
                | _ => .error "unsupported Array.getD application"
            | (.const ``Array.set! _, args) =>
                match args.reverse with
                | value :: index :: array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let valueResult ← extractExprFrom ctx locals indexResult.snd value
                    .ok (.arraySet arrayResult.fst indexResult.fst valueResult.fst, valueResult.snd)
                | _ => .error "unsupported Array.set! application"
            | (.const ``ByteArray.size _, args) =>
                match args with
                | [array] =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayParts arrayResult.fst
                    .ok (parts.snd, arrayResult.snd)
                | _ => .error "unsupported ByteArray.size application"
            | (.const ``ByteArray.isEmpty _, args) =>
                match args with
                | [array] =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayParts arrayResult.fst
                    .ok (boolExpr (.eqU64 parts.snd (.u64 0)), arrayResult.snd)
                | _ => .error "unsupported ByteArray.isEmpty application"
            | (.const ``ByteArray.get! _, args) =>
                match args.reverse with
                | index :: array :: _ =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayParts arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    .ok (.byteArrayGet parts.fst parts.snd indexResult.fst, indexResult.snd)
                | _ => .error "unsupported ByteArray.get! application"
            | (.const ``UInt64.ofNat _, [arg]) =>
                match ofNat? ``Nat arg with
                | some value => .ok (.u64 value, nextLocal)
                | none => extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt64.toNat _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt8.ofNat _, [arg]) =>
                match ofNat? ``Nat arg with
                | some value => .ok (.u64 (value % 256), nextLocal)
                | none =>
                    let argResult ← extractExprFrom ctx locals nextLocal arg
                    .ok (.u64Bin .bitAnd argResult.fst (.u64 255), argResult.snd)
            | (.const ``UInt8.toNat _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``Prod.fst _, args) =>
                match args.reverse with
                | product :: _ =>
                    let valueResult ← extractValueFrom ctx locals nextLocal product
                    .ok (← scalarValue (← productField 0 valueResult.fst), valueResult.snd)
                | _ => .error "unsupported Prod.fst application"
            | (.const ``Prod.snd _, args) =>
                match args.reverse with
                | product :: _ =>
                    let valueResult ← extractValueFrom ctx locals nextLocal product
                    .ok (← scalarValue (← productField 1 valueResult.fst), valueResult.snd)
                | _ => .error "unsupported Prod.snd application"
            | (.const ``Option.none _, _) =>
                .error "option value used where scalar value is required"
            | (.const ``Option.some _, _) =>
                .error "option value used where scalar value is required"
            | (.const ``Prod.mk _, _) =>
                .error "product value used where scalar value is required"
            | (.const primitive _, args) =>
                match boolMatcherArgs? ctx.env (.const primitive []) args with
                | some (scrutinee, falseArm, trueArm) =>
                    let condResult ← extractCondFrom ctx locals nextLocal scrutinee
                    let falseResult ← extractUnitArmValueFrom ctx locals condResult.snd falseArm
                    let trueResult ← extractUnitArmValueFrom ctx locals falseResult.snd trueArm
                    .ok (← scalarValue (← valueIte condResult.fst trueResult.fst falseResult.fst), trueResult.snd)
                | none =>
                    match optionMatcherArgs? ctx.env (.const primitive []) args with
                    | some (scrutinee, noneArm, someArm) =>
                        let valueResult ←
                          extractOptionMatchValueFrom ctx locals nextLocal scrutinee noneArm someArm
                        .ok (← scalarValue valueResult.fst, valueResult.snd)
                    | none =>
                        extractPrimitiveApplicationFrom ctx locals nextLocal primitive args
            | (fn, _) => .error s!"unsupported expression: {fn}"

  partial def extractPrimitiveApplicationFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (primitive : Name)
      (args : List Expr) :
      Except String (IRExpr × Nat) := do
    match ← extractInlineCallValueFrom ctx locals nextLocal primitive args with
    | some valueResult => .ok (← scalarValue valueResult.fst, valueResult.snd)
    | none =>
        match functionIndex? ctx primitive with
        | some index =>
            strictRecursiveCallCheck ctx primitive args
            let sig ←
              match ctx.env.find? primitive with
              | some info =>
                  match supportedFunction? info with
                  | some sig => .ok sig
                  | none => .error s!"unsupported function type or declaration: {primitive}"
              | none => .error s!"declaration disappeared during extraction: {primitive}"
            let argsResult ← extractCallArgsFrom ctx locals nextLocal sig.params args
            .ok (.call index argsResult.fst, argsResult.snd)
        | none =>
            if primitive == ``Complement.complement then
              match args.reverse with
              | value :: _ =>
                  let valueResult ← extractExprFrom ctx locals nextLocal value
                  match primitiveReceiverType? args with
                  | some .u8 =>
                      .ok (.u64Bin .bitXor valueResult.fst (.u64 255), valueResult.snd)
                  | some .u64 =>
                      .ok (.u64Bin .bitXor valueResult.fst (.u64 (runtimeNatLimit - 1)),
                        valueResult.snd)
                  | _ => .error s!"unsupported complement expression: {primitive}"
              | _ => .error s!"unsupported complement expression: {primitive}"
            else
              match primitiveArgPair? args with
              | some (left, right) =>
                  extractPrimitivePairFrom ctx locals nextLocal primitive args left right
              | none => .error s!"unsupported application: {primitive}"

  partial def extractPrimitivePairFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (primitive : Name)
      (args : List Expr)
      (left right : Expr) :
      Except String (IRExpr × Nat) := do
    let leftResult ← extractExprFrom ctx locals nextLocal left
    let rightResult ← extractExprFrom ctx locals leftResult.snd right
    let leftIR := leftResult.fst
    let rightIR := rightResult.fst
    if primitive == ``HAdd.hAdd then
      match primitiveResultType? args with
      | some .nat =>
          .ok (.u64Bin .natAdd leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .add leftIR rightIR), rightResult.snd)
      | _ => .ok (.u64Bin .add leftIR rightIR, rightResult.snd)
    else if primitive == ``HSub.hSub then
      match primitiveResultType? args with
      | some .nat =>
          .ok (.u64Bin .natSub leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .sub leftIR rightIR), rightResult.snd)
      | _ => .ok (.u64Bin .sub leftIR rightIR, rightResult.snd)
    else if primitive == ``HMul.hMul then
      match primitiveResultType? args with
      | some .nat =>
          .ok (.u64Bin .natMul leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .mul leftIR rightIR), rightResult.snd)
      | _ => .ok (.u64Bin .mul leftIR rightIR, rightResult.snd)
    else if primitive == ``HDiv.hDiv then
      .ok (.u64Bin .divU leftIR rightIR, rightResult.snd)
    else if primitive == ``HMod.hMod then
      .ok (.u64Bin .modU leftIR rightIR, rightResult.snd)
    else if primitive == ``HAnd.hAnd then
      match primitiveResultType? args with
      | some .u8 | some .u64 =>
          .ok (.u64Bin .bitAnd leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported bitwise and expression: {primitive}"
    else if primitive == ``HOr.hOr then
      match primitiveResultType? args with
      | some .u8 | some .u64 =>
          .ok (.u64Bin .bitOr leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported bitwise or expression: {primitive}"
    else if primitive == ``HXor.hXor then
      match primitiveResultType? args with
      | some .u8 | some .u64 =>
          .ok (.u64Bin .bitXor leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported bitwise xor expression: {primitive}"
    else if primitive == ``HShiftLeft.hShiftLeft then
      match primitiveResultType? args with
      | some .u64 =>
          .ok (.u64Bin .shiftLeft leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported shift-left expression: {primitive}"
    else if primitive == ``HShiftRight.hShiftRight then
      match primitiveResultType? args with
      | some .u64 =>
          .ok (.u64Bin .shiftRight leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported shift-right expression: {primitive}"
    else if primitive == ``UInt64.land then
      .ok (.u64Bin .bitAnd leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt64.lor then
      .ok (.u64Bin .bitOr leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt64.xor then
      .ok (.u64Bin .bitXor leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt64.shiftLeft then
      .ok (.u64Bin .shiftLeft leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt64.shiftRight then
      .ok (.u64Bin .shiftRight leftIR rightIR, rightResult.snd)
    else if primitive == ``BEq.beq then
      .ok (boolExpr (.eqU64 leftIR rightIR), rightResult.snd)
    else if primitive == ``LT.lt then
      .ok (boolExpr (.ltU64 leftIR rightIR), rightResult.snd)
    else if primitive == ``LE.le then
      .ok (boolExpr (.leU64 leftIR rightIR), rightResult.snd)
    else if primitive == ``GT.gt then
      .ok (boolExpr (.ltU64 rightIR leftIR), rightResult.snd)
    else if primitive == ``GE.ge then
      .ok (boolExpr (.leU64 rightIR leftIR), rightResult.snd)
    else if primitive == ``Min.min then
      match primitiveReceiverType? args with
      | some .nat | some .u8 | some .u64 =>
          .ok (.ite (.leU64 leftIR rightIR) leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported min expression: {primitive}"
    else if primitive == ``Max.max then
      match primitiveReceiverType? args with
      | some .nat | some .u8 | some .u64 =>
          .ok (.ite (.leU64 leftIR rightIR) rightIR leftIR, rightResult.snd)
      | _ => .error s!"unsupported max expression: {primitive}"
    else
      .error s!"unsupported primitive expression: {primitive}"

  partial def extractCondFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr : Expr) :
      Except String (IRCond × Nat) := do
    match expr.consumeMData with
    | .bvar index =>
        match ← lookupBinding locals index with
        | .slot slot => .ok (boolCond (.local slot), nextLocal)
        | .value value => .ok (boolCond (← scalarValue value), nextLocal)
        | .thunk savedLocals value =>
            let valueResult ← extractValueFrom ctx savedLocals nextLocal value
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | .recursor => .error "recursive handle used as a condition"
    | .letE _ _ _ _ _ =>
        let exprResult ← extractExprFrom ctx locals nextLocal expr
        .ok (boolCond exprResult.fst, exprResult.snd)
    | .const ``Bool.true _ => .ok (.true, nextLocal)
    | .const ``Bool.false _ => .ok (.false, nextLocal)
    | .const ``True _ => .ok (.true, nextLocal)
    | .const ``False _ => .ok (.false, nextLocal)
    | _ =>
        match appFnArgs expr with
        | (.const ``Eq _, [ty, left, right]) =>
            match typeAtom? ty with
            | some eqTy =>
                if supportedEqType eqTy then
                  let leftResult ← extractExprFrom ctx locals nextLocal left
                  let rightResult ← extractExprFrom ctx locals leftResult.snd right
                  .ok (.eqU64 leftResult.fst rightResult.fst, rightResult.snd)
                else
                  .error "unsupported equality proposition in condition"
            | none => .error "unsupported equality proposition in condition"
        | (.const ``Decidable.decide _, [prop, _inst]) =>
            extractCondFrom ctx locals nextLocal prop
        | (.const ``And _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.and leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Or _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.or leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Not _, [arg]) =>
            let result ← extractCondFrom ctx locals nextLocal arg
            .ok (.not result.fst, result.snd)
        | (.const ``Bool.casesOn _, _) =>
            let exprResult ← extractExprFrom ctx locals nextLocal expr
            .ok (boolCond exprResult.fst, exprResult.snd)
        | (.const ``BEq.beq _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.eqU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported BEq application"
        | (.const ``LT.lt _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.ltU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported LT.lt application"
        | (.const ``LE.le _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.leU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported LE.le application"
        | (.const ``GT.gt _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.ltU64 rightResult.fst leftResult.fst, rightResult.snd)
            | none => .error "unsupported GT.gt application"
        | (.const ``GE.ge _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.leU64 rightResult.fst leftResult.fst, rightResult.snd)
            | none => .error "unsupported GE.ge application"
        | (.const ``Bool.not _, [arg]) =>
            let result ← extractCondFrom ctx locals nextLocal arg
            .ok (.not result.fst, result.snd)
        | (.const ``Bool.or _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.or leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Bool.and _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.and leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Array.isEmpty _, args) =>
            match args.reverse with
            | array :: _ =>
                let arrayResult ← extractExprFrom ctx locals nextLocal array
                .ok (.eqU64 (.arraySize arrayResult.fst) (.u64 0), arrayResult.snd)
            | _ => .error "unsupported Array.isEmpty condition"
        | (.const ``ByteArray.isEmpty _, args) =>
            match args with
            | [array] =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayParts arrayResult.fst
                .ok (.eqU64 parts.snd (.u64 0), arrayResult.snd)
            | _ => .error "unsupported ByteArray.isEmpty condition"
        | (.const name _, args) =>
            match boolMatcherArgs? ctx.env (.const name []) args with
            | some _ =>
                let exprResult ← extractExprFrom ctx locals nextLocal expr
                .ok (boolCond exprResult.fst, exprResult.snd)
            | none =>
                match ← extractInlineCallValueFrom ctx locals nextLocal name args with
                | some valueResult => .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
                | none =>
                    match functionIndex? ctx name with
                    | some index =>
                        strictRecursiveCallCheck ctx name args
                        let sig ←
                          match ctx.env.find? name with
                          | some info =>
                              match supportedFunction? info with
                              | some sig => .ok sig
                              | none => .error s!"unsupported function type or declaration: {name}"
                          | none => .error s!"declaration disappeared during extraction: {name}"
                        let argsResult ← extractCallArgsFrom ctx locals nextLocal sig.params args
                        .ok (boolCond (.call index argsResult.fst), argsResult.snd)
                    | none => .error s!"unsupported condition: {expr}"
        | _ => .error s!"unsupported condition: {expr}"

  partial def extractExprListFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat) :
      List Expr → Except String (List IRExpr × Nat)
    | [] => .ok ([], nextLocal)
    | expr :: rest => do
        let headResult ← extractExprFrom ctx locals nextLocal expr
        let restResult ← extractExprListFrom ctx locals headResult.snd rest
        .ok (headResult.fst :: restResult.fst, restResult.snd)

  partial def extractCallArgsFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat) :
      List Ty → List Expr → Except String (List IRExpr × Nat)
    | [], [] => .ok ([], nextLocal)
    | ty :: restTys, expr :: restExprs => do
        let valueResult ← extractValueFrom ctx locals nextLocal expr
        let head ← flattenAbiValue ty valueResult.fst
        let rest ← extractCallArgsFrom ctx locals valueResult.snd restTys restExprs
        .ok (head ++ rest.fst, rest.snd)
    | _, _ => .error "function call arity mismatch"
end

def extractExpr (ctx : Context) (locals : List Binding) (nextLocal : Nat) (expr : Expr) :
    Except String (IRExpr × Nat) :=
  extractExprFrom ctx locals nextLocal expr

def extractCond (ctx : Context) (locals : List Binding) (nextLocal : Nat) (expr : Expr) :
    Except String (IRCond × Nat) :=
  extractCondFrom ctx locals nextLocal expr

def localBindingsForParams (params : List Ty) : List Binding :=
  (sourceParamBindings params).reverse

def baseBindingsForParams (params : List Ty) : List Binding :=
  .recursor :: ((sourceParamBindings params).drop 1).reverse

def stepBindingsForParams (params : List Ty) : List Binding :=
  let carried := ((sourceParamBindings params).drop 1).reverse
  (.recursor :: carried) ++ [.value (.scalar (.u64Bin .sub (.local 0) (.u64 1)))]

partial def recCallArgs? (expected : Nat) (expr : Expr) : Option (List Expr) :=
  match appFnArgs expr with
  | (fn, args) =>
      if args.length == expected && containsBVar 0 fn then
        some args
      else
        none

structure RecSpec where
  base : Expr
  exitCond? : Option Expr
  exitValue? : Option Expr
  recArgs : List Expr

def parseStepBody? (paramCount : Nat) (body : Expr) :
    Except String (Option (Expr × Expr) × List Expr) := do
  let expectedArgs := paramCount - 1
  match appFnArgs body with
  | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
      if typeAtom? ty |>.isSome then
        match recCallArgs? expectedArgs elseExpr with
        | some args => .ok (some (condExpr, thenExpr), args)
        | none => .error "recursive branch is not a tail call"
      else
        .error "recursive branch has unsupported if-result type"
  | _ =>
      match recCallArgs? expectedArgs body with
      | some args => .ok (none, args)
      | none => .error "recursive branch is not a supported tail call"

def parseRecMatcher? (name : Name) (paramCount : Nat) (expr : Expr) :
    Except String (Option RecSpec) := do
  match appFnArgs expr with
  | (.const candidate _, args) =>
      if !isMatcherName candidate then
        return none
      let carriedCount := paramCount - 1
      if args.length != paramCount + 4 then
        .error s!"unsupported Nat recursion matcher arity: {name}"
      else
        match args.drop (carriedCount + 2) with
        | baseArm :: succArm :: _below :: [] =>
            let baseBody ←
              match collectLambdas baseArm (carriedCount + 1) with
              | some body => .ok body
              | none => .error s!"unsupported Nat recursion base arm: {name}"
            let stepBody ←
              match collectLambdas succArm (carriedCount + 2) with
              | some body => .ok body
              | none => .error s!"unsupported Nat recursion successor arm: {name}"
            let parsedStep ← parseStepBody? paramCount stepBody
            let exitCond? := parsedStep.fst.map Prod.fst
            let exitValue? := parsedStep.fst.map Prod.snd
            .ok (some {
              base := baseBody,
              exitCond? := exitCond?,
              exitValue? := exitValue?,
              recArgs := parsedStep.snd
            })
        | _ => .error s!"unsupported Nat recursion matcher arguments: {name}"
  | _ => return none

mutual
  partial def findRecSpec? (name : Name) (paramCount : Nat) (expr : Expr) :
      Except String (Option RecSpec) := do
    match ← parseRecMatcher? name paramCount expr with
    | some spec => .ok (some spec)
    | none => findRecSpecInChildren? name paramCount expr

  partial def findRecSpecInChildren? (name : Name) (paramCount : Nat) (expr : Expr) :
      Except String (Option RecSpec) := do
    match expr.consumeMData with
    | .app fn arg =>
        match ← findRecSpec? name paramCount fn with
        | some spec => .ok (some spec)
        | none => findRecSpec? name paramCount arg
    | .lam _ type body _ =>
        match ← findRecSpec? name paramCount type with
        | some spec => .ok (some spec)
        | none => findRecSpec? name paramCount body
    | .forallE _ type body _ =>
        match ← findRecSpec? name paramCount type with
        | some spec => .ok (some spec)
        | none => findRecSpec? name paramCount body
    | .letE _ type value body _ =>
        match ← findRecSpec? name paramCount type with
        | some spec => .ok (some spec)
        | none =>
            match ← findRecSpec? name paramCount value with
            | some spec => .ok (some spec)
            | none => findRecSpec? name paramCount body
    | .mdata _ body => findRecSpec? name paramCount body
    | .proj _ _ body => findRecSpec? name paramCount body
    | _ => .ok none
end

def assignMany (targets : List Nat) (values : List IRExpr) (tempStart : Nat) : IRStmt :=
  let tempAssignments :=
    enumerate values |>.map (fun item => LeanExe.IR.Stmt.assign (tempStart + item.fst) item.snd)
  let targetAssignments :=
    enumerate targets |>.map (fun item => LeanExe.IR.Stmt.assign item.snd (.local (tempStart + item.fst)))
  LeanExe.IR.seqList (tempAssignments ++ targetAssignments)

def extractNatRecFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  let sourceParamCount := params.length
  let wasmParamCount := abiParamCount params
  let spec ←
    match ← findRecSpec? name sourceParamCount value with
    | some spec => .ok spec
    | none => .error s!"unsupported Nat recursion shape: {name}"
  let stepLocals := stepBindingsForParams params
  let baseLocals := baseBindingsForParams params
  let fuelLive : IRCond := .not (.eqU64 (.local 0) (.u64 0))
  let condResult ←
    match spec.exitCond? with
    | some condExpr =>
        let extracted ← extractCond ctx stepLocals wasmParamCount condExpr
        .ok (.and fuelLive (.not extracted.fst), extracted.snd)
    | none => .ok (fuelLive, wasmParamCount)
  let exitResult? ←
    match spec.exitValue? with
    | some exitExpr =>
        let extracted ← extractExpr ctx stepLocals condResult.snd exitExpr
        .ok (some extracted.fst, extracted.snd)
    | none => .ok (none, condResult.snd)
  let carriedParams := params.drop 1
  let recArgsResult ← extractCallArgsFrom ctx stepLocals exitResult?.snd carriedParams spec.recArgs
  let baseResult ← extractExpr ctx baseLocals recArgsResult.snd spec.base
  let loopCond := condResult.fst
  let recIRArgs := recArgsResult.fst
  let targets := (abiTargets params |>.drop 1).flatMap Prod.snd
  let tempStart := baseResult.snd
  let updateArgs := assignMany targets recIRArgs tempStart
  let decFuel : IRStmt := .assign 0 (.u64Bin .sub (.local 0) (.u64 1))
  let loopBody : IRStmt := .seq updateArgs decFuel
  let result :=
    match exitResult?.fst with
    | some exitValue => .ite fuelLive exitValue baseResult.fst
    | none => baseResult.fst
  .ok {
    sourceName := name,
    exportName := exportName,
    params := wasmParamCount,
    locals := tempStart + targets.length,
    body := .while loopCond loopBody,
    result := result
  }

def extractPlainFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  let sourceParamCount := params.length
  let wasmParamCount := abiParamCount params
  let body ←
    match collectLambdas value sourceParamCount with
    | some body => .ok body
    | none => .error s!"definition body does not match function arity: {name}"
  let result ← extractExpr ctx (localBindingsForParams params) wasmParamCount body
  .ok {
    sourceName := name,
    exportName := exportName,
    params := wasmParamCount,
    locals := result.snd,
    body := .skip,
    result := result.fst
  }

def shortExportName (name : Name) : String :=
  match (LeanExe.Extract.Env.displayName name).splitOn "." |>.reverse with
  | part :: _ => part
  | [] => LeanExe.Extract.Env.displayName name

def reservedExportNames : List String :=
  ["memory", "alloc", "reset"]

def extractFunction
    (ctx : Context)
    (entry name : Name)
    (info : ConstantInfo)
    (sig : Signature) : Except String IRFunc := do
  let value ←
    match info.value? with
    | some value => .ok value
    | none => .error s!"declaration has no executable value: {name}"
  let exportName ←
    if name == entry then
      let candidate := shortExportName name
      if reservedExportNames.contains candidate then
        .error s!"entry export name is reserved by the runtime ABI: {candidate}"
      else
        .ok (some candidate)
    else
      .ok none
  match sig.params with
  | .nat :: _ =>
      if containsConstant ``Nat.brecOn info then
        extractNatRecFunc ctx name sig.params value exportName
      else
        extractPlainFunc ctx name sig.params value exportName
  | _ => extractPlainFunc ctx name sig.params value exportName

def compileEnvironment (env : Environment) (moduleName entry : Name) : Except String IRModule := do
  let entryInfo ←
    match env.find? entry with
    | some info => .ok info
    | none => .error s!"entry not found: {entry}"
  let _entrySig ←
    match supportedEntryFunction? entryInfo with
    | some sig => .ok sig
    | none => .error s!"unsupported function type or declaration: {entry}"
  let (_, namesList) ← collectReachable env moduleName.getRoot entry [] []
  let names := namesList.toArray
  let ctx : Context := { env := env, names := names }
  let mut funcs := #[]
  for name in names do
    let info ←
      match env.find? name with
      | some info => .ok info
      | none => .error s!"declaration disappeared during extraction: {name}"
    let sig ←
      if name == entry then
        match supportedEntryFunction? info with
        | some sig => .ok sig
        | none => .error s!"unsupported function type or declaration: {name}"
      else
        match supportedFunction? info with
        | some sig => .ok sig
        | none => .error s!"unsupported function type or declaration: {name}"
    funcs := funcs.push (← extractFunction ctx entry name info sig)
  .ok { funcs := funcs }

def compile (moduleText entryText : String) : IO IRModule := do
  let moduleName := LeanExe.Extract.Env.parseName moduleText
  let entryName := LeanExe.Extract.Env.parseName entryText
  let env ← LeanExe.Extract.Env.loadEnvironment moduleName
  match compileEnvironment env moduleName entryName with
  | .ok module_ => pure module_
  | .error error => throw <| IO.userError error

end LeanExe.Extract.Core
