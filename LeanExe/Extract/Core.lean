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

inductive Binding where
  | slot (index : Nat)
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
    | _ => none

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
          if params.all (fun ty => ty == .u64 || ty == .nat || ty == .array .u64) then
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

mutual
  partial def extractExpr (ctx : Context) (locals : List Binding) (expr : Expr) :
      Except String IRExpr := do
    match expr.consumeMData with
    | .bvar index =>
        match ← lookupBinding locals index with
        | .slot slot => .ok (.local slot)
        | .recursor => .error "recursive handle used as a value"
    | .const name _ =>
        match constNatValue? ctx.env name with
        | some value => .ok (.u64 value)
        | none =>
            match functionIndex? ctx name with
            | some index => .ok (.call index [])
            | none => .error s!"unsupported constant in expression: {name}"
    | _ =>
        match ofNat? ``UInt64 expr <|> ofNat? ``Nat expr with
        | some value => .ok (.u64 value)
        | none =>
            match appFnArgs expr with
            | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
                if typeAtom? ty |>.isSome then
                  .ok (.ite (← extractCond ctx locals condExpr)
                    (← extractExpr ctx locals thenExpr)
                    (← extractExpr ctx locals elseExpr))
                else
                  .error "unsupported if-result type"
            | (.const ``Bool.or _, _) =>
                .ok (boolExpr (← extractCond ctx locals expr))
            | (.const ``Bool.and _, _) =>
                .ok (boolExpr (← extractCond ctx locals expr))
            | (.const ``Array.replicate _, args) =>
                match args.reverse with
                | value :: cells :: _ =>
                    match ← extractExpr ctx locals value with
                    | .u64 0 => .ok (.arrayAlloc (← extractExpr ctx locals cells))
                    | _ => .error "Array.replicate currently supports only zero-filled UInt64 arrays"
                | _ => .error "unsupported Array.replicate application"
            | (.const ``Array.get!Internal _, args) =>
                match args.reverse with
                | index :: array :: _ =>
                    .ok (.arrayGet
                      (← extractExpr ctx locals array)
                      (← extractExpr ctx locals index))
                | _ => .error "unsupported Array.get!Internal application"
            | (.const ``GetElem?.getElem! _, args) =>
                match args.reverse with
                | index :: array :: _ =>
                    .ok (.arrayGet
                      (← extractExpr ctx locals array)
                      (← extractExpr ctx locals index))
                | _ => .error "unsupported GetElem?.getElem! application"
            | (.const ``Array.set! _, args) =>
                match args.reverse with
                | value :: index :: array :: _ =>
                    .ok (.arraySet
                      (← extractExpr ctx locals array)
                      (← extractExpr ctx locals index)
                      (← extractExpr ctx locals value))
                | _ => .error "unsupported Array.set! application"
            | (.const ``UInt64.toNat _, [arg]) =>
                extractExpr ctx locals arg
            | (.const primitive _, args) =>
                match functionIndex? ctx primitive with
                | some index =>
                    .ok (.call index (← args.mapM (extractExpr ctx locals)))
                | none =>
                    match primitiveArgPair? args with
                    | some (left, right) =>
                        let leftIR ← extractExpr ctx locals left
                        let rightIR ← extractExpr ctx locals right
                        if primitive == ``HAdd.hAdd then
                          .ok (.u64Bin .add leftIR rightIR)
                        else if primitive == ``HSub.hSub then
                          .ok (.u64Bin .sub leftIR rightIR)
                        else if primitive == ``HMul.hMul then
                          .ok (.u64Bin .mul leftIR rightIR)
                        else if primitive == ``HDiv.hDiv then
                          .ok (.u64Bin .divU leftIR rightIR)
                        else if primitive == ``HMod.hMod then
                          .ok (.u64Bin .modU leftIR rightIR)
                        else if primitive == ``UInt64.land then
                          .ok (.u64Bin .bitAnd leftIR rightIR)
                        else if primitive == ``BEq.beq then
                          .ok (boolExpr (.eqU64 leftIR rightIR))
                        else
                          .error s!"unsupported primitive expression: {primitive}"
                    | none => .error s!"unsupported application: {primitive}"
            | (fn, _) => .error s!"unsupported expression: {fn}"

  partial def extractCond (ctx : Context) (locals : List Binding) (expr : Expr) :
      Except String IRCond := do
    match expr.consumeMData with
    | .const ``Bool.true _ => .ok .true
    | .const ``Bool.false _ => .ok .false
    | _ =>
        match appFnArgs expr with
        | (.const ``Eq _, [ty, value, truth]) =>
            if isConst ``Bool ty && isConst ``Bool.true truth then
              extractCond ctx locals value
            else
              .error "unsupported equality proposition in condition"
        | (.const ``BEq.beq _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                .ok (.eqU64 (← extractExpr ctx locals left) (← extractExpr ctx locals right))
            | none => .error "unsupported BEq application"
        | (.const ``Bool.or _, [left, right]) =>
            .ok (.or (← extractCond ctx locals left) (← extractCond ctx locals right))
        | (.const ``Bool.and _, [left, right]) =>
            .ok (.and (← extractCond ctx locals left) (← extractCond ctx locals right))
        | (.const name _, args) =>
            match functionIndex? ctx name with
            | some index =>
                .ok (.not (.eqU64
                  (.call index (← args.mapM (extractExpr ctx locals)))
                  (.u64 0)))
            | none => .error s!"unsupported condition: {expr}"
        | _ => .error s!"unsupported condition: {expr}"
end

partial def collectLambdas (expr : Expr) : Nat → Option Expr
  | 0 => some expr
  | count + 1 =>
      match expr.consumeMData with
      | .lam _ _ body _ => collectLambdas body count
      | _ => none

def localBindingsForParams (paramCount : Nat) : List Binding :=
  (List.range paramCount).reverse.map Binding.slot

partial def recCallArgs? (expected : Nat) (expr : Expr) : Option (List Expr) :=
  match appFnArgs expr with
  | (fn, args) =>
      if args.length == expected && containsBVar 0 fn then
        some args
      else
        none

def parseStepBody? (paramCount : Nat) (body : Expr) :
    Except String (Option Expr × List Expr) := do
  let expectedArgs := paramCount - 1
  match appFnArgs body with
  | (.const ``ite _, [ty, condExpr, _, _thenExpr, elseExpr]) =>
      if isConst ``UInt64 ty then
        match recCallArgs? expectedArgs elseExpr with
        | some args => .ok (some condExpr, args)
        | none => .error "recursive branch is not a tail call"
      else
        .error "recursive branch has unsupported if-result type"
  | _ =>
      match recCallArgs? expectedArgs body with
      | some args => .ok (none, args)
      | none => .error "recursive branch is not a supported tail call"

def stepBodyFromLambda? (paramCount : Nat) (expr : Expr) : Option Expr :=
  match collectLambdas expr (paramCount + 1) with
  | some body =>
      if recCallArgs? (paramCount - 1) body |>.isSome then
        some body
      else
        match appFnArgs body with
        | (.const ``ite _, [ty, _, _, _, elseExpr]) =>
            if isConst ``UInt64 ty && (recCallArgs? (paramCount - 1) elseExpr |>.isSome) then
              some body
            else
              none
        | _ => none
  | none => none

mutual
  partial def findStepBody? (paramCount : Nat) (expr : Expr) : Option Expr :=
    match stepBodyFromLambda? paramCount expr with
    | some body => some body
    | none => findStepBodyInChildren? paramCount expr

  partial def findStepBodyInChildren? (paramCount : Nat) (expr : Expr) : Option Expr :=
    match expr.consumeMData with
    | .app fn arg => findStepBody? paramCount fn <|> findStepBody? paramCount arg
    | .lam _ type body _ => findStepBody? paramCount type <|> findStepBody? paramCount body
    | .forallE _ type body _ => findStepBody? paramCount type <|> findStepBody? paramCount body
    | .letE _ type value body _ =>
        findStepBody? paramCount type <|>
          findStepBody? paramCount value <|>
          findStepBody? paramCount body
    | .mdata _ body => findStepBody? paramCount body
    | .proj _ _ body => findStepBody? paramCount body
    | _ => none
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
  let stepBody ←
    match findStepBody? paramCount value with
    | some body => .ok body
    | none => .error s!"unsupported Nat recursion shape: {name}"
  let stepLocals := .recursor :: localBindingsForParams paramCount
  let parsed ← parseStepBody? paramCount stepBody
  let exitCond? := parsed.fst
  let recArgs := parsed.snd
  let recIRArgs ← recArgs.mapM (extractExpr ctx stepLocals)
  let fuelLive : IRCond := .not (.eqU64 (.local 0) (.u64 0))
  let loopCond ←
    match exitCond? with
    | some condExpr =>
        .ok (.and fuelLive (.not (← extractCond ctx stepLocals condExpr)))
    | none => .ok fuelLive
  let targets := (List.range (paramCount - 1)).map (fun index => index + 1)
  let tempStart := paramCount
  let updateArgs := assignMany targets recIRArgs tempStart
  let decFuel : IRStmt := .assign 0 (.u64Bin .sub (.local 0) (.u64 1))
  let loopBody : IRStmt := .seq updateArgs decFuel
  .ok {
    sourceName := name,
    exportName := exportName,
    params := paramCount,
    locals := paramCount + (paramCount - 1),
    body := .while loopCond loopBody,
    result := .local (paramCount - 1)
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
  .ok {
    sourceName := name,
    exportName := exportName,
    params := paramCount,
    locals := paramCount,
    body := .skip,
    result := ← extractExpr ctx (localBindingsForParams paramCount) body
  }

def containsConstant (name : Name) (info : ConstantInfo) : Bool :=
  info.value? |>.any (fun value => value.getUsedConstants.contains name)

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
