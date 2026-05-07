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

partial def peelForall (expr : Expr) : List Expr × Expr :=
  match expr.consumeMData with
  | .forallE _ domain body _ =>
      let rest := peelForall body
      (domain :: rest.fst, rest.snd)
  | other => ([], other)

def functionType? (type : Expr) : Option Signature :=
  let parts := peelForall type
  match typeAtom? parts.snd with
  | some result =>
      let params? := parts.fst.mapM typeAtom?
      match params? with
      | some params =>
          if supportedAbiType result && params.all supportedAbiType then
            some { params := params, result := result }
          else
            none
      | none => none
  | none => none

def supportedFunction? (info : ConstantInfo) : Option Signature :=
  if info.isUnsafe || info.isPartial then
    none
  else
    functionType? info.type

def supportedLocalType : Ty → Bool
  | .bool => true
  | .u64 => true
  | .nat => true
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

def boolExpr (cond : IRCond) : IRExpr :=
  .ite cond (.u64 1) (.u64 0)

def boolCond (expr : IRExpr) : IRCond :=
  .not (.eqU64 expr (.u64 0))

def scalarValue (value : ExtractedValue) : Except String IRExpr :=
  match value with
  | .scalar expr => .ok expr
  | .product _ _ => .error "product value used where scalar value is required"
  | .option _ _ => .error "option value used where scalar value is required"

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
  | .option _ _ => .error "option value used where product value is required"

def optionParts (value : ExtractedValue) : Except String (IRExpr × ExtractedValue) :=
  match value with
  | .option tag payload => .ok (tag, payload)
  | .scalar _ => .error "scalar value used where option value is required"
  | .product _ _ => .error "product value used where option value is required"

partial def defaultValue : Ty → Except String ExtractedValue
  | .bool => .ok (.scalar (.u64 0))
  | .u64 => .ok (.scalar (.u64 0))
  | .nat => .ok (.scalar (.u64 0))
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
  | .product thenLeft thenRight, .product elseLeft elseRight => do
      .ok (.product
        (← valueIte cond thenLeft elseLeft)
        (← valueIte cond thenRight elseRight))
  | .option thenTag thenPayload, .option elseTag elsePayload => do
      .ok (.option
        (.ite cond thenTag elseTag)
        (← valueIte cond thenPayload elsePayload))
  | _, _ => .error "if branches have incompatible structured value shapes"

def optionConstructorType? (args : List Expr) : Option Ty :=
  match args with
  | ty :: _ => typeAtom? ty
  | [] => none

def isMatcherName (candidate : Name) : Bool :=
  match candidate with
  | .str _ component => component.startsWith "match_"
  | _ => false

def optionMatcherArgs? (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Option.casesOn || name == ``Option.rec then
        match args.reverse with
        | someArm :: noneArm :: scrutinee :: _ => some (scrutinee, noneArm, someArm)
        | _ => none
      else if isMatcherName name then
        match args with
        | [_motive, scrutinee, noneArm, someArm] => some (scrutinee, noneArm, someArm)
        | _ => none
      else
        none
  | _ => none

def isPartialArrayPrimitive (name : Name) : Bool :=
  name == ``Array.get!Internal ||
    name == ``GetElem?.getElem! ||
    name == ``Array.set!

partial def mayTrapExpr (expr : Expr) : Bool :=
  match expr.consumeMData with
  | .app fn arg =>
      match appFnArgs expr with
      | (.const name _, _) =>
          isPartialArrayPrimitive name || mayTrapExpr fn || mayTrapExpr arg
      | _ => mayTrapExpr fn || mayTrapExpr arg
  | .lam _ type body _ => mayTrapExpr type || mayTrapExpr body
  | .forallE _ type body _ => mayTrapExpr type || mayTrapExpr body
  | .letE _ type value body _ =>
      mayTrapExpr type || mayTrapExpr value || mayTrapExpr body
  | .mdata _ body => mayTrapExpr body
  | .proj _ _ body => mayTrapExpr body
  | _ => false

def strictRecursiveCallCheck (ctx : Context) (name : Name) (args : List Expr) :
    Except String Unit := do
  match ctx.env.find? name with
  | none => .error s!"declaration disappeared during extraction: {name}"
  | some info =>
      if containsConstant ``Nat.brecOn info || containsConstant name info then
        if args.any mayTrapExpr then
          .error s!"strict call to recursive helper may evaluate a trapping argument: {name}"
        else
          .ok ()
      else
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
        | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
            match typeAtom? ty with
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
            match optionMatcherArgs? fn args with
            | some (scrutinee, noneArm, someArm) =>
                extractOptionMatchValueFrom ctx locals nextLocal scrutinee noneArm someArm
            | none =>
                let exprResult ← extractExprFrom ctx locals nextLocal expr
                .ok (.scalar exprResult.fst, exprResult.snd)

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
    | .const name _ =>
        match constNatValue? ctx.env name with
        | some value => .ok (.u64 value, nextLocal)
        | none =>
            match functionIndex? ctx name with
            | some index => .ok (.call index [], nextLocal)
            | none => .error s!"unsupported constant in expression: {name}"
    | _ =>
        match ofNat? ``UInt64 expr <|> ofNat? ``Nat expr with
        | some value => .ok (.u64 value, nextLocal)
        | none =>
            match appFnArgs expr with
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
            | (.const ``Array.replicate _, args) =>
                match args.reverse with
                | value :: cells :: _ =>
                    let valueResult ← extractExprFrom ctx locals nextLocal value
                    match valueResult.fst with
                    | .u64 0 =>
                        let cellsResult ← extractExprFrom ctx locals valueResult.snd cells
                        .ok (.arrayAlloc cellsResult.fst, cellsResult.snd)
                    | _ => .error "Array.replicate currently supports only zero-filled UInt64 arrays"
                | _ => .error "unsupported Array.replicate application"
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
            | (.const ``Array.set! _, args) =>
                match args.reverse with
                | value :: index :: array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let valueResult ← extractExprFrom ctx locals indexResult.snd value
                    .ok (.arraySet arrayResult.fst indexResult.fst valueResult.fst, valueResult.snd)
                | _ => .error "unsupported Array.set! application"
            | (.const ``UInt64.toNat _, [arg]) =>
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
                match optionMatcherArgs? (.const primitive []) args with
                | some (scrutinee, noneArm, someArm) =>
                    let valueResult ←
                      extractOptionMatchValueFrom ctx locals nextLocal scrutinee noneArm someArm
                    .ok (← scalarValue valueResult.fst, valueResult.snd)
                | none =>
                  match ← extractInlineCallValueFrom ctx locals nextLocal primitive args with
                  | some valueResult => .ok (← scalarValue valueResult.fst, valueResult.snd)
                  | none =>
                    match functionIndex? ctx primitive with
                    | some index =>
                        strictRecursiveCallCheck ctx primitive args
                        let argsResult ← extractExprListFrom ctx locals nextLocal args
                        .ok (.call index argsResult.fst, argsResult.snd)
                    | none =>
                        match primitiveArgPair? args with
                        | some (left, right) =>
                            let leftResult ← extractExprFrom ctx locals nextLocal left
                            let rightResult ← extractExprFrom ctx locals leftResult.snd right
                            let leftIR := leftResult.fst
                            let rightIR := rightResult.fst
                            if primitive == ``HAdd.hAdd then
                              .ok (.u64Bin .add leftIR rightIR, rightResult.snd)
                            else if primitive == ``HSub.hSub then
                              .ok (.u64Bin .sub leftIR rightIR, rightResult.snd)
                            else if primitive == ``HMul.hMul then
                              .ok (.u64Bin .mul leftIR rightIR, rightResult.snd)
                            else if primitive == ``HDiv.hDiv then
                              .ok (.u64Bin .divU leftIR rightIR, rightResult.snd)
                            else if primitive == ``HMod.hMod then
                              .ok (.u64Bin .modU leftIR rightIR, rightResult.snd)
                            else if primitive == ``UInt64.land then
                              .ok (.u64Bin .bitAnd leftIR rightIR, rightResult.snd)
                            else if primitive == ``BEq.beq then
                              .ok (boolExpr (.eqU64 leftIR rightIR), rightResult.snd)
                            else
                              .error s!"unsupported primitive expression: {primitive}"
                        | none => .error s!"unsupported application: {primitive}"
            | (fn, _) => .error s!"unsupported expression: {fn}"

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
    | _ =>
        match appFnArgs expr with
        | (.const ``Eq _, [ty, value, truth]) =>
            if isConst ``Bool ty && isConst ``Bool.true truth then
              extractCondFrom ctx locals nextLocal value
            else
              .error "unsupported equality proposition in condition"
        | (.const ``BEq.beq _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.eqU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported BEq application"
        | (.const ``Bool.or _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.or leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Bool.and _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.and leftResult.fst rightResult.fst, rightResult.snd)
        | (.const name _, args) =>
            match ← extractInlineCallValueFrom ctx locals nextLocal name args with
            | some valueResult => .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
            | none =>
                match functionIndex? ctx name with
                | some index =>
                    strictRecursiveCallCheck ctx name args
                    let argsResult ← extractExprListFrom ctx locals nextLocal args
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
end

def extractExpr (ctx : Context) (locals : List Binding) (nextLocal : Nat) (expr : Expr) :
    Except String (IRExpr × Nat) :=
  extractExprFrom ctx locals nextLocal expr

def extractCond (ctx : Context) (locals : List Binding) (nextLocal : Nat) (expr : Expr) :
    Except String (IRCond × Nat) :=
  extractCondFrom ctx locals nextLocal expr

def localBindingsForParams (paramCount : Nat) : List Binding :=
  (List.range paramCount).reverse.map Binding.slot

def baseBindingsForParams (paramCount : Nat) : List Binding :=
  .recursor :: (List.range (paramCount - 1)).reverse.map (fun index => Binding.slot (index + 1))

def stepBindingsForParams (paramCount : Nat) : List Binding :=
  let carried :=
    (List.range (paramCount - 1)).reverse.map (fun index => Binding.slot (index + 1))
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

def enumerateAux {α : Type} : List α → Nat → List (Nat × α)
  | [], _ => []
  | item :: rest, index => (index, item) :: enumerateAux rest (index + 1)

def enumerate {α : Type} (items : List α) : List (Nat × α) :=
  enumerateAux items 0

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
  let paramCount := params.length
  let spec ←
    match ← findRecSpec? name paramCount value with
    | some spec => .ok spec
    | none => .error s!"unsupported Nat recursion shape: {name}"
  let stepLocals := stepBindingsForParams paramCount
  let baseLocals := baseBindingsForParams paramCount
  let fuelLive : IRCond := .not (.eqU64 (.local 0) (.u64 0))
  let condResult ←
    match spec.exitCond? with
    | some condExpr =>
        let extracted ← extractCond ctx stepLocals paramCount condExpr
        .ok (.and fuelLive (.not extracted.fst), extracted.snd)
    | none => .ok (fuelLive, paramCount)
  let exitResult? ←
    match spec.exitValue? with
    | some exitExpr =>
        let extracted ← extractExpr ctx stepLocals condResult.snd exitExpr
        .ok (some extracted.fst, extracted.snd)
    | none => .ok (none, condResult.snd)
  let recArgsResult ← extractExprListFrom ctx stepLocals exitResult?.snd spec.recArgs
  let baseResult ← extractExpr ctx baseLocals recArgsResult.snd spec.base
  let loopCond := condResult.fst
  let recIRArgs := recArgsResult.fst
  let targets := (List.range (paramCount - 1)).map (fun index => index + 1)
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
    params := paramCount,
    locals := tempStart + (paramCount - 1),
    body := .while loopCond loopBody,
    result := result
  }

def extractPlainFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  let paramCount := params.length
  let body ←
    match collectLambdas value paramCount with
    | some body => .ok body
    | none => .error s!"definition body does not match function arity: {name}"
  let result ← extractExpr ctx (localBindingsForParams paramCount) paramCount body
  .ok {
    sourceName := name,
    exportName := exportName,
    params := paramCount,
    locals := result.snd,
    body := .skip,
    result := result.fst
  }

def shortExportName (name : Name) : String :=
  match (LeanExe.Extract.Env.displayName name).splitOn "." |>.reverse with
  | part :: _ => part
  | [] => LeanExe.Extract.Env.displayName name

def extractFunction
    (ctx : Context)
    (entry name : Name)
    (info : ConstantInfo)
    (sig : Signature) : Except String IRFunc := do
  let value ←
    match info.value? with
    | some value => .ok value
    | none => .error s!"declaration has no executable value: {name}"
  let exportName := if name == entry then some (shortExportName name) else none
  match sig.params with
  | .nat :: _ =>
      if containsConstant ``Nat.brecOn info then
        extractNatRecFunc ctx name sig.params value exportName
      else
        extractPlainFunc ctx name sig.params value exportName
  | _ => extractPlainFunc ctx name sig.params value exportName

def compileEnvironment (env : Environment) (moduleName entry : Name) : Except String IRModule := do
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
