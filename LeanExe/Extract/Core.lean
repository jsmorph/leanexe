import Lean
import Init.Data.ByteArray.Extra
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
  | sum (tag : IRExpr) (left right : ExtractedValue)
  | struct (name : Name) (fields : List ExtractedValue)
  | variant (name : Name) (tag : IRExpr) (ctors : List (List ExtractedValue))
  | recursiveVariant (name : Name) (tag : IRExpr) (ctors : List (List (Ty × ExtractedValue)))
  | heapVariant (name : Name) (ptr : IRExpr)
  | ite (cond : IRCond) (thenValue elseValue : ExtractedValue)
  | letE (slot : Nat) (value : IRExpr) (body : ExtractedValue)
  | letCall (slots : List Nat) (index : Nat) (args : List IRExpr) (body : ExtractedValue)
  deriving BEq, Repr

instance : Inhabited ExtractedValue :=
  ⟨.scalar .trap⟩

inductive ValueLet where
  | expr (slot : Nat) (value : IRExpr)
  | call (slots : List Nat) (index : Nat) (args : List IRExpr)
  deriving BEq, Repr

structure MaterializedSlots where
  lets : List ValueLet
  slots : List IRExpr
  nextLocal : Nat
  deriving BEq, Repr

structure MaterializedArgs where
  lets : List ValueLet
  args : List IRExpr
  nextLocal : Nat
  deriving BEq, Repr

inductive Binding where
  | slot (index : Nat)
  | value (value : ExtractedValue)
  | thunk (locals : List Binding) (expr : Expr)
  | recursor
  deriving BEq, Repr

structure Context where
  env : Environment
  root : Name
  names : Array Name
  inlineStack : List Name

structure VariantCtorLayout where
  name : Name
  fields : List (Option Ty)
  deriving BEq, Repr

structure VariantLayout where
  name : Name
  ctors : List VariantCtorLayout
  deriving BEq, Repr

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

def isIdType (expr : Expr) : Bool :=
  isConst ``Id expr

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

def stringLit? (expr : Expr) : Option String :=
  match expr.consumeMData with
  | .lit (.strVal value) => some value
  | _ => none

def asciiStringBytes? (value : String) : Option (List UInt8) :=
  let bytes := value.toUTF8.data.toList
  if bytes.all (fun byte => byte.toNat < 128) then some bytes else none

def byteArrayLiteralArrayExprAux (index : Nat) (array : IRExpr) : List UInt8 → IRExpr
  | [] => array
  | byte :: rest =>
      byteArrayLiteralArrayExprAux
        (index + 1)
        (.arraySetSlots 1 array (.u64 index) [.u64 byte.toNat])
        rest

def byteArrayLiteralArrayExpr (bytes : List UInt8) : IRExpr :=
  byteArrayLiteralArrayExprAux 0 (.arrayAllocSlots 1 (.u64 bytes.length)) bytes

def byteArrayLiteralValue (slot : Nat) (bytes : List UInt8) : ExtractedValue × Nat :=
  match bytes with
  | [] => (.byteArray (.u64 0) (.u64 0), slot)
  | _ =>
      (.letE slot (byteArrayLiteralArrayExpr bytes)
        (.byteArray (.byteArrayFromArrayPtr (.local slot)) (.arraySize (.local slot))),
        slot + 1)

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
          match ofNat? ``UInt32 expr with
          | some value => some (.ok (.u64 (value % (2 ^ 32))))
          | none =>
              match ofNat? ``Nat expr with
              | some value => some (boundedNatExpr value)
              | none => none

partial def peelForall (expr : Expr) : List Expr × Expr :=
  match expr.consumeMData with
  | .forallE _ domain body _ =>
      let rest := peelForall body
      (domain :: rest.fst, rest.snd)
  | other => ([], other)

def structureInductiveInfo? (env : Environment) (structName : Name) : Option InductiveVal :=
  match env.find? structName with
  | some (.inductInfo info) =>
      if info.numParams == 0 && info.numIndices == 0 && info.ctors.length == 1 && !info.isRec then
        some info
      else
        none
  | _ => none

def structureCtorInfo? (env : Environment) (structName : Name) : Option ConstructorVal :=
  match structureInductiveInfo? env structName with
  | some info =>
      match info.ctors with
      | ctorName :: [] =>
          match env.find? ctorName with
          | some (.ctorInfo ctorInfo) => some ctorInfo
          | _ => none
      | _ => none
  | none => none

def builtinInductiveNames : List Name :=
  [``Bool, ``Nat, ``Unit, ``Option, ``Except, ``Prod]

def userInductiveInfo? (env : Environment) (typeName : Name) : Option InductiveVal :=
  if builtinInductiveNames.contains typeName || isStructureLike env typeName then
    none
  else
    match env.find? typeName with
    | some (.inductInfo info) =>
        if info.numParams == 0 && info.numIndices == 0 && !info.isRec && !info.ctors.isEmpty then
          some info
        else
          none
    | _ => none

def userRecursiveInductiveInfo? (env : Environment) (typeName : Name) : Option InductiveVal :=
  if builtinInductiveNames.contains typeName || isStructureLike env typeName then
    none
  else
    match env.find? typeName with
    | some (.inductInfo info) =>
        if info.numParams == 0 && info.numIndices == 0 && info.isRec && !info.ctors.isEmpty then
          some info
        else
          none
    | _ => none

def runtimeTypesFromKinds (kinds : List (Option Ty)) : List Ty :=
  kinds.filterMap id

def ctorIndex? (ctorName : Name) (ctors : List VariantCtorLayout) : Option Nat :=
  let rec loop : Nat → List VariantCtorLayout → Option Nat
    | _, [] => none
    | index, ctor :: rest =>
        if ctor.name == ctorName then
          some index
        else
          loop (index + 1) rest
  loop 0 ctors

partial def isProofType? (env : Environment) (expr : Expr) : Bool :=
  match expr.consumeMData with
  | .sort .zero => true
  | .forallE _ _ body _ => isProofType? env body
  | .mdata _ body => isProofType? env body
  | _ =>
      match appFnArgs expr with
      | (fn, args) =>
          match fn.consumeMData with
          | .const name _ =>
              match env.find? name with
              | some info =>
                  let parts := peelForall info.type
                  if args.length >= parts.fst.length then
                    parts.snd.consumeMData.isProp
                  else
                    false
              | none => false
          | _ => false

def runtimeFieldIndexFromKinds (sourceIndex : Nat) (kinds : List (Option Ty)) :
    Option (Option Nat) :=
  let rec loop : Nat → Nat → List (Option Ty) → Option (Option Nat)
    | _, _, [] => none
    | currentSource, currentRuntime, kind :: rest =>
        if currentSource == sourceIndex then
          match kind with
          | some _ => some (some currentRuntime)
          | none => some none
        else
          let nextRuntime :=
            match kind with
            | some _ => currentRuntime + 1
            | none => currentRuntime
          loop (currentSource + 1) nextRuntime rest
  loop 0 0 kinds

mutual
  partial def typeAtom? (env : Environment) (expr : Expr) : Option Ty :=
    if isConst ``UInt64 expr then
      some .u64
    else if isConst ``Nat expr then
      some .nat
    else if isConst ``Bool expr then
      some .bool
    else if isConst ``Unit expr then
      some .unit
    else if isConst ``UInt8 expr then
      some .u8
    else if isConst ``UInt32 expr then
      some .u32
    else if isConst ``ByteArray expr then
      some .byteArray
    else
      match appFnArgs expr with
      | (.const ``Array _, [item]) => typeAtom? env item |>.map .array
      | (.const ``Prod _, [left, right]) =>
          match typeAtom? env left, typeAtom? env right with
          | some leftTy, some rightTy => some (.product leftTy rightTy)
          | _, _ => none
      | (.const ``Option _, [item]) =>
          typeAtom? env item |>.map (fun itemTy => .variant ``Option [[], [itemTy]])
      | (.const ``Except _, [error, ok]) =>
          match typeAtom? env error, typeAtom? env ok with
          | some errorTy, some okTy => some (.variant ``Except [[errorTy], [okTy]])
          | _, _ => none
      | (.const name _, []) =>
          if isStructureLike env name then
            structureFieldTypes? env name |>.map (fun fields => .struct name fields)
          else
            match variantLayout? env name with
            | some layout =>
                some (.variant name (layout.ctors.map (fun ctor => runtimeTypesFromKinds ctor.fields)))
            | none =>
                recursiveVariantLayout? env name |>.map fun _layout => .recVariant name
      | _ => none

  partial def structureFieldKinds? (env : Environment) (structName : Name) :
      Option (List (Option Ty)) :=
    if !isStructureLike env structName then
      none
    else
      match structureCtorInfo? env structName with
      | some ctorInfo =>
          let fields := (peelForall ctorInfo.type).fst.drop ctorInfo.numParams
          let flatFieldNames :=
            (getStructureFieldsFlattened env structName (includeSubobjectFields := false)).toList
          if fields.length == ctorInfo.numFields && fields.length == flatFieldNames.length then
            fields.mapM fun field =>
              if isProofType? env field then
                some none
              else
                typeAtom? env field |>.map some
          else
            none
      | none => none

  partial def structureFieldTypes? (env : Environment) (structName : Name) : Option (List Ty) :=
    structureFieldKinds? env structName |>.map (fun fields => fields.filterMap id)

  partial def variantLayout? (env : Environment) (typeName : Name) : Option VariantLayout :=
    match userInductiveInfo? env typeName with
    | some info =>
        let ctorLayouts? := info.ctors.mapM fun ctorName =>
          match env.find? ctorName with
          | some (.ctorInfo ctorInfo) =>
              if ctorInfo.numParams == 0 && ctorInfo.induct == typeName then
                let fields := (peelForall ctorInfo.type).fst.drop ctorInfo.numParams
                if fields.length == ctorInfo.numFields then
                  fields.mapM (fun field =>
                    if isProofType? env field then
                      some none
                    else
                      typeAtom? env field |>.map some) |>.map fun fieldKinds =>
                        ({ name := ctorName, fields := fieldKinds } : VariantCtorLayout)
                else
                  none
              else
                none
          | _ => none
        ctorLayouts? |>.map fun ctors => ({ name := typeName, ctors := ctors } : VariantLayout)
    | none => none

  partial def typeAtomRecursiveField? (env : Environment) (selfName : Name) (expr : Expr) :
      Option Ty :=
    match appFnArgs expr with
    | (.const name _, []) =>
        if name == selfName then
          some (.recVariant selfName)
        else
          match typeAtom? env expr with
          | some (.recVariant _) => none
          | other => other
    | (.const ``Array _, [item]) =>
        typeAtomRecursiveField? env selfName item |>.map .array
    | (.const ``Prod _, [left, right]) =>
        match typeAtomRecursiveField? env selfName left,
            typeAtomRecursiveField? env selfName right with
        | some leftTy, some rightTy => some (.product leftTy rightTy)
        | _, _ => none
    | (.const ``Option _, [item]) =>
        typeAtomRecursiveField? env selfName item |>.map
          (fun itemTy => .variant ``Option [[], [itemTy]])
    | (.const ``Except _, [error, ok]) =>
        match typeAtomRecursiveField? env selfName error,
            typeAtomRecursiveField? env selfName ok with
        | some errorTy, some okTy => some (.variant ``Except [[errorTy], [okTy]])
        | _, _ => none
    | _ =>
        match typeAtom? env expr with
        | some (.recVariant _) => none
        | other => other

  partial def recursiveVariantLayout? (env : Environment) (typeName : Name) :
      Option VariantLayout :=
    match userRecursiveInductiveInfo? env typeName with
    | some info =>
        let ctorLayouts? := info.ctors.mapM fun ctorName =>
          match env.find? ctorName with
          | some (.ctorInfo ctorInfo) =>
              if ctorInfo.numParams == 0 && ctorInfo.induct == typeName then
                let fields := (peelForall ctorInfo.type).fst.drop ctorInfo.numParams
                if fields.length == ctorInfo.numFields then
                  fields.mapM (fun field =>
                    if isProofType? env field then
                      some none
                    else
                      typeAtomRecursiveField? env typeName field |>.map some) |>.map fun fieldKinds =>
                        ({ name := ctorName, fields := fieldKinds } : VariantCtorLayout)
                else
                  none
              else
                none
          | _ => none
        ctorLayouts? |>.map fun ctors => ({ name := typeName, ctors := ctors } : VariantLayout)
    | none => none
end

def anyVariantLayout? (env : Environment) (typeName : Name) : Option VariantLayout :=
  match variantLayout? env typeName with
  | some layout => some layout
  | none => recursiveVariantLayout? env typeName

def structureConstructor? (env : Environment) (ctorName : Name) :
    Option (Name × List (Option Ty)) :=
  match env.find? ctorName with
  | some (.ctorInfo ctorInfo) =>
      if ctorInfo.numParams == 0 && ctorInfo.cidx == 0 && isStructureLike env ctorInfo.induct then
        structureFieldKinds? env ctorInfo.induct |>.map (fun fields => (ctorInfo.induct, fields))
      else
        none
  | _ => none

def variantConstructor? (env : Environment) (ctorName : Name) :
    Option (VariantLayout × Nat × VariantCtorLayout) :=
  match env.find? ctorName with
  | some (.ctorInfo ctorInfo) =>
      match variantLayout? env ctorInfo.induct with
      | some layout =>
          match ctorIndex? ctorName layout.ctors with
          | some index =>
              match layout.ctors[index]? with
              | some ctor => some (layout, index, ctor)
              | none => none
          | none => none
      | none => none
  | _ => none

def recursiveVariantConstructor? (env : Environment) (ctorName : Name) :
    Option (VariantLayout × Nat × VariantCtorLayout) :=
  match env.find? ctorName with
  | some (.ctorInfo ctorInfo) =>
      match recursiveVariantLayout? env ctorInfo.induct with
      | some layout =>
          match ctorIndex? ctorName layout.ctors with
          | some index =>
              match layout.ctors[index]? with
              | some ctor => some (layout, index, ctor)
              | none => none
          | none => none
      | none => none
  | _ => none

def anyVariantConstructor? (env : Environment) (ctorName : Name) :
    Option (VariantLayout × Nat × VariantCtorLayout) :=
  match variantConstructor? env ctorName with
  | some result => some result
  | none => recursiveVariantConstructor? env ctorName

def structureProjection? (env : Environment) (projName : Name) :
    Option (Name × Option Nat) :=
  match env.getProjectionFnInfo? projName with
  | some projInfo =>
      if projInfo.numParams == 0 then
        match env.find? projInfo.ctorName with
        | some (.ctorInfo ctorInfo) =>
            if ctorInfo.numParams == 0 && isStructureLike env ctorInfo.induct then
              match structureFieldKinds? env ctorInfo.induct with
              | some kinds =>
                  runtimeFieldIndexFromKinds projInfo.i kinds |>.map (fun index? =>
                    (ctorInfo.induct, index?))
              | none => none
            else
              none
        | _ => none
      else
        none
  | none => none

def supportedArrayCellType : Ty → Bool
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | _ => false

mutual
  partial def arrayElementSlots? : Ty → Option Nat
    | .bool => some 1
    | .u8 => some 1
    | .u32 => some 1
    | .u64 => some 1
    | .nat => some 1
    | .recVariant _ => some 1
    | .struct _ fields => arrayFieldSlots? fields
    | .variant _ ctors => do
        let payloadSlots ← arrayCtorSlots? ctors
        some (payloadSlots + 1)
    | _ => none

  partial def arrayFieldSlots? : List Ty → Option Nat
    | [] => some 0
    | field :: rest => do
        let head ← arrayElementSlots? field
        let tail ← arrayFieldSlots? rest
        some (head + tail)

  partial def arrayCtorSlots? : List (List Ty) → Option Nat
    | [] => some 0
    | fields :: rest => do
        let head ← arrayFieldSlots? fields
        let tail ← arrayCtorSlots? rest
        some (head + tail)
end

def supportedArrayElementType (ty : Ty) : Bool :=
  arrayElementSlots? ty |>.isSome

partial def containsRecVariant : Ty → Bool
  | .array item => containsRecVariant item
  | .product left right => containsRecVariant left || containsRecVariant right
  | .sum left right => containsRecVariant left || containsRecVariant right
  | .struct _ fields => fields.any containsRecVariant
  | .variant _ ctors => ctors.any (fun fields => fields.any containsRecVariant)
  | .recVariant _ => true
  | _ => false

def supportedAbiArrayElementType (ty : Ty) : Bool :=
  supportedArrayElementType ty && !containsRecVariant ty

def supportedAbiType : Ty → Bool
  | .bool => true
  | .u64 => true
  | .nat => true
  | .array item => supportedAbiArrayElementType item
  | _ => false

partial def supportedParamAbiType : Ty → Bool
  | .byteArray => true
  | .struct _ fields => fields.all supportedParamAbiType
  | .variant _ ctors => ctors.all (fun fields => fields.all supportedParamAbiType)
  | ty => supportedAbiType ty

partial def supportedResultAbiType : Ty → Bool
  | .byteArray => true
  | .struct _ fields => fields.all supportedResultAbiType
  | .variant _ ctors => ctors.all (fun fields => fields.all supportedResultAbiType)
  | ty => supportedAbiType ty

partial def supportedInternalValueType : Ty → Bool
  | .unit => true
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | .byteArray => true
  | .array item => supportedArrayElementType item
  | .struct _ fields => fields.all supportedInternalValueType
  | .variant _ ctors => ctors.all (fun fields => fields.all supportedInternalValueType)
  | .recVariant _ => true
  | _ => false

def supportedInternalParamType : Ty → Bool
  | .byteArray => true
  | ty => supportedInternalValueType ty

def supportedInternalResultType : Ty → Bool :=
  supportedInternalValueType

partial def abiSlots : Ty → Nat
  | .byteArray => 2
  | .struct _ fields => fields.foldl (fun total field => total + abiSlots field) 0
  | .variant _ ctors =>
      1 + ctors.foldl
        (fun total fields => total + fields.foldl (fun acc field => acc + abiSlots field) 0)
        0
  | .recVariant _ => 1
  | _ => 1

partial def internalSlots : Ty → Nat
  | .byteArray => 2
  | .product left right => internalSlots left + internalSlots right
  | .sum left right => 1 + internalSlots left + internalSlots right
  | .struct _ fields => fields.foldl (fun total field => total + internalSlots field) 0
  | .variant _ ctors =>
      1 + ctors.foldl
        (fun total fields => total + fields.foldl (fun acc field => acc + internalSlots field) 0)
        0
  | .recVariant _ => 1
  | _ => 1

def abiParamCount (params : List Ty) : Nat :=
  params.foldl (fun total ty => total + abiSlots ty) 0

def functionTypeWith?
    (env : Environment)
    (paramSupported resultSupported : Ty → Bool)
    (type : Expr) : Option Signature :=
  let parts := peelForall type
  match typeAtom? env parts.snd with
  | some result =>
      let params? := parts.fst.mapM (typeAtom? env)
      match params? with
      | some params =>
          if resultSupported result && params.all paramSupported then
            some { params := params, result := result }
          else
            none
      | none => none
  | none => none

def entryFunctionType? (env : Environment) (type : Expr) : Option Signature :=
  functionTypeWith? env supportedParamAbiType supportedResultAbiType type

def functionType? (env : Environment) (type : Expr) : Option Signature :=
  functionTypeWith? env supportedInternalParamType supportedInternalResultType type

def supportedEntryFunction? (env : Environment) (info : ConstantInfo) : Option Signature :=
  if info.isUnsafe || info.isPartial || info.value?.isNone then
    none
  else
    entryFunctionType? env info.type

def supportedFunction? (env : Environment) (info : ConstantInfo) : Option Signature :=
  if info.isUnsafe || info.isPartial || info.value?.isNone then
    none
  else
    functionType? env info.type

partial def supportedLocalType : Ty → Bool
  | .unit => true
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | .byteArray => true
  | .array item => supportedArrayElementType item
  | .product left right => supportedLocalType left && supportedLocalType right
  | .sum left right => supportedLocalType left && supportedLocalType right
  | .struct _ fields => fields.all supportedLocalType
  | .variant _ ctors => ctors.all (fun fields => fields.all supportedLocalType)
  | .recVariant _ => true

def supportedOneSlotExprType : Ty → Bool
  | .unit => true
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | .array item => supportedArrayElementType item
  | _ => false

def supportedInlineFunction? (env : Environment) (info : ConstantInfo) : Option Signature :=
  if info.isUnsafe || info.isPartial || info.value?.isNone then
    none
  else
    functionTypeWith? env supportedLocalType supportedLocalType info.type

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
    match supportedFunction? env info with
    | some sig => .ok sig
    | none => .error s!"unsupported function type or declaration: {entry}"
  let mut nextSeen := pushName seen entry
  let mut nextNames := names
  for dep in usedConstantsOf info do
    if dep.getRoot == root then
      match env.find? dep with
      | some depInfo =>
          if dep != entry && (supportedFunction? env depInfo |>.isSome) then
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

def localInlineFunction? (ctx : Context) (name : Name) : Bool :=
  name.getRoot == ctx.root &&
    match ctx.env.find? name with
    | some info => (supportedInlineFunction? ctx.env info).isSome
    | none => false

def lookupBinding (locals : List Binding) (index : Nat) : Except String Binding :=
  match locals[index]? with
  | some binding => .ok binding
  | none => .error s!"unbound de Bruijn variable: {index}"

def primitiveArgPair? (args : List Expr) : Option (Expr × Expr) :=
  match args.reverse with
  | right :: left :: _ => some (left, right)
  | _ => none

def primitiveResultType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | _leftType :: _rightType :: resultType :: _ => typeAtom? env resultType
  | _ => none

def primitiveReceiverType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | ty :: _ => typeAtom? env ty
  | _ => none

def boolExpr (cond : IRCond) : IRExpr :=
  .ite cond (.u64 1) (.u64 0)

def boolCond (expr : IRExpr) : IRCond :=
  .not (.eqU64 expr (.u64 0))

def irConstNat? : IRExpr → Option Nat
  | .u64 value => some value
  | _ => none

def u8WrapExpr (expr : IRExpr) : IRExpr :=
  .u64Bin .bitAnd expr (.u64 255)

def u8ShiftAmountExpr (expr : IRExpr) : IRExpr :=
  .u64Bin .bitAnd expr (.u64 7)

def u32WrapExpr (expr : IRExpr) : IRExpr :=
  .u64Bin .bitAnd expr (.u64 (2 ^ 32 - 1))

def u32ShiftAmountExpr (expr : IRExpr) : IRExpr :=
  .u64Bin .bitAnd expr (.u64 31)

def supportedEqType : Ty → Bool
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | _ => false

def scalarValue (value : ExtractedValue) : Except String IRExpr :=
  match value with
  | .scalar expr => .ok expr
  | .byteArray _ _ => .error "ByteArray value used where scalar value is required"
  | .product _ _ => .error "product value used where scalar value is required"
  | .sum _ _ _ => .error "sum value used where scalar value is required"
  | .struct name _ => .error s!"structure value used where scalar value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where scalar value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where scalar value is required: {name}"
  | .heapVariant name _ => .error s!"recursive inductive value used where scalar value is required: {name}"
  | .ite cond thenValue elseValue => do
      .ok (.ite cond (← scalarValue thenValue) (← scalarValue elseValue))
  | .letE slot value body => do
      .ok (.letE slot value (← scalarValue body))
  | .letCall slots index args body => do
      .ok (.letCall slots index args (← scalarValue body))

def byteArrayParts (value : ExtractedValue) : Except String (IRExpr × IRExpr) :=
  match value with
  | .byteArray ptr len => .ok (ptr, len)
  | .scalar _ => .error "scalar value used where ByteArray value is required"
  | .product _ _ => .error "product value used where ByteArray value is required"
  | .sum _ _ _ => .error "sum value used where ByteArray value is required"
  | .struct name _ => .error s!"structure value used where ByteArray value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where ByteArray value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where ByteArray value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where ByteArray value is required: {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← byteArrayParts thenValue
      let elseParts ← byteArrayParts elseValue
      .ok (.ite cond thenParts.fst elseParts.fst, .ite cond thenParts.snd elseParts.snd)
  | .letE slot value body => do
      let parts ← byteArrayParts body
      .ok (.letE slot value parts.fst, .letE slot value parts.snd)
  | .letCall slots index args body => do
      let parts ← byteArrayParts body
      .ok (.letCall slots index args parts.fst, .letCall slots index args parts.snd)

partial def byteArrayPartsWithLets (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × IRExpr) :=
  match value with
  | .byteArray ptr len => .ok ([], ptr, len)
  | .scalar _ => .error "scalar value used where ByteArray value is required"
  | .product _ _ => .error "product value used where ByteArray value is required"
  | .sum _ _ _ => .error "sum value used where ByteArray value is required"
  | .struct name _ => .error s!"structure value used where ByteArray value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where ByteArray value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where ByteArray value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where ByteArray value is required: {name}"
  | .ite cond thenValue elseValue => do
      let parts ← byteArrayParts (.ite cond thenValue elseValue)
      .ok ([], parts.fst, parts.snd)
  | .letE slot value body => do
      let parts ← byteArrayPartsWithLets body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd)
  | .letCall slots index args body => do
      let parts ← byteArrayPartsWithLets body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd)

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
  | .sum _ _ _ => .error "sum value used where product value is required"
  | .struct name _ => .error s!"structure value used where product value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where product value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where product value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where product value is required: {name}"
  | .ite cond thenValue elseValue => do
      .ok (.ite cond (← productField index thenValue) (← productField index elseValue))
  | .letE slot value body => do
      .ok (.letE slot value (← productField index body))
  | .letCall slots callIndex args body => do
      .ok (.letCall slots callIndex args (← productField index body))

def structField (name : Name) (index : Nat) (value : ExtractedValue) : Except String ExtractedValue :=
  match value with
  | .struct actual fields =>
      if actual == name then
        match fields[index]? with
        | some field => .ok field
        | none => .error s!"unsupported structure projection index: {name}.{index}"
      else
        .error s!"structure projection type mismatch: expected {name}, got {actual}"
  | .scalar _ => .error s!"scalar value used where structure value is required: {name}"
  | .byteArray _ _ => .error s!"ByteArray value used where structure value is required: {name}"
  | .product _ _ => .error s!"product value used where structure value is required: {name}"
  | .sum _ _ _ => .error s!"sum value used where structure value is required: {name}"
  | .variant actual _ _ =>
      .error s!"inductive value used where structure value is required: {name}; got {actual}"
  | .recursiveVariant actual _ _ =>
      .error s!"recursive inductive value used where structure value is required: {name}; got {actual}"
  | .heapVariant actual _ =>
      .error s!"recursive inductive value used where structure value is required: {name}; got {actual}"
  | .ite cond thenValue elseValue => do
      .ok (.ite cond (← structField name index thenValue) (← structField name index elseValue))
  | .letE slot value body => do
      .ok (.letE slot value (← structField name index body))
  | .letCall slots callIndex args body => do
      .ok (.letCall slots callIndex args (← structField name index body))

def mkOptionValue (tag : IRExpr) (payload : ExtractedValue) : ExtractedValue :=
  .variant ``Option tag [[], [payload]]

def optionPayloadType? : Ty → Option Ty
  | .variant name [[], [payloadTy]] => if name == ``Option then some payloadTy else none
  | _ => none

partial def wrapValueLets (lets : List ValueLet) (value : ExtractedValue) :
    ExtractedValue :=
  lets.foldr
    (fun item acc =>
      match item with
      | .expr slot expr => .letE slot expr acc
      | .call slots index args => .letCall slots index args acc)
    value

def wrapExprLets (lets : List ValueLet) (expr : IRExpr) : IRExpr :=
  lets.foldr
    (fun item acc =>
      match item with
      | .expr slot value => .letE slot value acc
      | .call slots index args => .letCall slots index args acc)
    expr

def valueLetStmt : ValueLet → IRStmt
  | .expr slot expr => .assign slot expr
  | .call slots index args => .call slots index args

partial def optionPartsWithLets (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × ExtractedValue) :=
  match value with
  | .variant name tag [[], [payload]] =>
      if name == ``Option then
        .ok ([], tag, payload)
      else
        .error s!"inductive value used where Option value is required: {name}"
  | .scalar _ => .error "scalar value used where option value is required"
  | .byteArray _ _ => .error "ByteArray value used where option value is required"
  | .product _ _ => .error "product value used where option value is required"
  | .sum _ _ _ => .error "sum value used where option value is required"
  | .struct name _ => .error s!"structure value used where option value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where Option value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where Option value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where Option value is required: {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← optionPartsWithLets thenValue
      let elseParts ← optionPartsWithLets elseValue
      let thenTag := wrapExprLets thenParts.fst thenParts.snd.fst
      let elseTag := wrapExprLets elseParts.fst elseParts.snd.fst
      let payload :=
        .ite cond
          (wrapValueLets thenParts.fst thenParts.snd.snd)
          (wrapValueLets elseParts.fst elseParts.snd.snd)
      .ok ([], .ite cond thenTag elseTag, payload)
  | .letE slot value body => do
      let parts ← optionPartsWithLets body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd)
  | .letCall slots index args body => do
      let parts ← optionPartsWithLets body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd)

partial def sumPartsWithLets (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × ExtractedValue × ExtractedValue) :=
  match value with
  | .sum tag left right => .ok ([], tag, left, right)
  | .scalar _ => .error "scalar value used where sum value is required"
  | .byteArray _ _ => .error "ByteArray value used where sum value is required"
  | .product _ _ => .error "product value used where sum value is required"
  | .struct name _ => .error s!"structure value used where sum value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where sum value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where sum value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where sum value is required: {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← sumPartsWithLets thenValue
      let elseParts ← sumPartsWithLets elseValue
      let thenTag := wrapExprLets thenParts.fst thenParts.snd.fst
      let elseTag := wrapExprLets elseParts.fst elseParts.snd.fst
      let left :=
        .ite cond
          (wrapValueLets thenParts.fst thenParts.snd.snd.fst)
          (wrapValueLets elseParts.fst elseParts.snd.snd.fst)
      let right :=
        .ite cond
          (wrapValueLets thenParts.fst thenParts.snd.snd.snd)
          (wrapValueLets elseParts.fst elseParts.snd.snd.snd)
      .ok ([], .ite cond thenTag elseTag, left, right)
  | .letE slot value body => do
      let parts ← sumPartsWithLets body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd.fst, parts.snd.snd.snd)
  | .letCall slots index args body => do
      let parts ← sumPartsWithLets body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd.fst, parts.snd.snd.snd)

partial def variantPartsWithLets (expectedName : Name) (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × List (List ExtractedValue)) :=
  match value with
  | .variant name tag ctors =>
      if name == expectedName then
        .ok ([], tag, ctors)
      else
        .error s!"inductive value type mismatch: expected {expectedName}, got {name}"
  | .scalar _ => .error s!"scalar value used where inductive value is required: {expectedName}"
  | .byteArray _ _ =>
      .error s!"ByteArray value used where inductive value is required: {expectedName}"
  | .product _ _ => .error s!"product value used where inductive value is required: {expectedName}"
  | .sum _ _ _ => .error s!"sum value used where inductive value is required: {expectedName}"
  | .struct name _ =>
      .error s!"structure value used where inductive value is required: {expectedName}; got {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where nonrecursive inductive value is required: {expectedName}; got {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where nonrecursive inductive value is required: {expectedName}; got {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← variantPartsWithLets expectedName thenValue
      let elseParts ← variantPartsWithLets expectedName elseValue
      if thenParts.snd.snd.length == elseParts.snd.snd.length then do
        let thenTag := wrapExprLets thenParts.fst thenParts.snd.fst
        let elseTag := wrapExprLets elseParts.fst elseParts.snd.fst
        let ctors ← (thenParts.snd.snd.zip elseParts.snd.snd).mapM fun ctorPair =>
          if ctorPair.fst.length == ctorPair.snd.length then
            .ok <| ctorPair.fst.zip ctorPair.snd |>.map fun fieldPair =>
              .ite cond
                (wrapValueLets thenParts.fst fieldPair.fst)
                (wrapValueLets elseParts.fst fieldPair.snd)
          else
            .error s!"conditional inductive constructor payload shape mismatch: {expectedName}"
        .ok ([], .ite cond thenTag elseTag, ctors)
      else
        .error s!"conditional inductive value shape mismatch: {expectedName}"
  | .letE slot value body => do
      let parts ← variantPartsWithLets expectedName body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd)
  | .letCall slots index args body => do
      let parts ← variantPartsWithLets expectedName body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd)

partial def heapVariantPtrWithLets (expectedName : Name) (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr) :=
  match value with
  | .heapVariant name ptr =>
      if name == expectedName then
        .ok ([], ptr)
      else
        .error s!"recursive inductive value type mismatch: expected {expectedName}, got {name}"
  | .scalar _ =>
      .error s!"scalar value used where recursive inductive value is required: {expectedName}"
  | .byteArray _ _ =>
      .error s!"ByteArray value used where recursive inductive value is required: {expectedName}"
  | .product _ _ =>
      .error s!"product value used where recursive inductive value is required: {expectedName}"
  | .sum _ _ _ =>
      .error s!"sum value used where recursive inductive value is required: {expectedName}"
  | .struct name _ =>
      .error s!"structure value used where recursive inductive value is required: {expectedName}; got {name}"
  | .variant name _ _ =>
      .error s!"nonrecursive inductive value used where recursive inductive value is required: {expectedName}; got {name}"
  | .recursiveVariant name _ _ =>
      .error s!"lazy recursive inductive value used where heap recursive value is required: {expectedName}; got {name}"
  | .ite _ _ _ =>
      .error s!"conditional recursive heap value is unsupported: {expectedName}"
  | .letE slot value body => do
      let parts ← heapVariantPtrWithLets expectedName body
      .ok (.expr slot value :: parts.fst, parts.snd)
  | .letCall slots index args body => do
      let parts ← heapVariantPtrWithLets expectedName body
      .ok (.call slots index args :: parts.fst, parts.snd)

partial def heapVariantPtrWithLets? (expectedName : Name) (value : ExtractedValue) :
    Option (List ValueLet × IRExpr) :=
  match value with
  | .heapVariant name ptr =>
      if name == expectedName then some ([], ptr) else none
  | .letE slot value body =>
      heapVariantPtrWithLets? expectedName body |>.map fun parts =>
        (.expr slot value :: parts.fst, parts.snd)
  | .letCall slots index args body =>
      heapVariantPtrWithLets? expectedName body |>.map fun parts =>
        (.call slots index args :: parts.fst, parts.snd)
  | _ => none

partial def recursiveVariantPartsWithLets (expectedName : Name) (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × List (List ExtractedValue)) :=
  match value with
  | .recursiveVariant name tag ctors =>
      if name == expectedName then
        .ok ([], tag, ctors.map (fun fields => fields.map Prod.snd))
      else
        .error s!"recursive inductive value type mismatch: expected {expectedName}, got {name}"
  | .scalar _ =>
      .error s!"scalar value used where recursive inductive value is required: {expectedName}"
  | .byteArray _ _ =>
      .error s!"ByteArray value used where recursive inductive value is required: {expectedName}"
  | .product _ _ =>
      .error s!"product value used where recursive inductive value is required: {expectedName}"
  | .sum _ _ _ =>
      .error s!"sum value used where recursive inductive value is required: {expectedName}"
  | .struct name _ =>
      .error s!"structure value used where recursive inductive value is required: {expectedName}; got {name}"
  | .variant name _ _ =>
      .error s!"nonrecursive inductive value used where recursive inductive value is required: {expectedName}; got {name}"
  | .heapVariant name _ =>
      .error s!"heap recursive inductive value used where lazy recursive value is required: {expectedName}; got {name}"
  | .ite _ _ _ =>
      .error s!"conditional recursive inductive value is unsupported: {expectedName}"
  | .letE slot value body => do
      let parts ← recursiveVariantPartsWithLets expectedName body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd)
  | .letCall slots index args body => do
      let parts ← recursiveVariantPartsWithLets expectedName body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd)

def mkExceptValue (tag : IRExpr) (errorPayload okPayload : ExtractedValue) : ExtractedValue :=
  .variant ``Except tag [[errorPayload], [okPayload]]

partial def exceptPartsWithLets (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × ExtractedValue × ExtractedValue) :=
  match value with
  | .variant name tag [[errorPayload], [okPayload]] =>
      if name == ``Except then
        .ok ([], tag, errorPayload, okPayload)
      else
        .error s!"inductive value used where Except value is required: {name}"
  | .scalar _ => .error "scalar value used where Except value is required"
  | .byteArray _ _ => .error "ByteArray value used where Except value is required"
  | .product _ _ => .error "product value used where Except value is required"
  | .sum _ _ _ => .error "sum value used where Except value is required"
  | .struct name _ => .error s!"structure value used where Except value is required: {name}"
  | .variant name _ _ =>
      .error s!"inductive value used where Except value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where Except value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where Except value is required: {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← exceptPartsWithLets thenValue
      let elseParts ← exceptPartsWithLets elseValue
      let thenTag := wrapExprLets thenParts.fst thenParts.snd.fst
      let elseTag := wrapExprLets elseParts.fst elseParts.snd.fst
      let errorPayload :=
        .ite cond
          (wrapValueLets thenParts.fst thenParts.snd.snd.fst)
          (wrapValueLets elseParts.fst elseParts.snd.snd.fst)
      let okPayload :=
        .ite cond
          (wrapValueLets thenParts.fst thenParts.snd.snd.snd)
          (wrapValueLets elseParts.fst elseParts.snd.snd.snd)
      .ok ([], .ite cond thenTag elseTag, errorPayload, okPayload)
  | .letE slot value body => do
      let parts ← exceptPartsWithLets body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd.fst, parts.snd.snd.snd)
  | .letCall slots index args body => do
      let parts ← exceptPartsWithLets body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd.fst, parts.snd.snd.snd)

partial def defaultValue : Ty → Except String ExtractedValue
  | .unit => .ok (.scalar (.u64 0))
  | .bool => .ok (.scalar (.u64 0))
  | .u8 => .ok (.scalar (.u64 0))
  | .u32 => .ok (.scalar (.u64 0))
  | .u64 => .ok (.scalar (.u64 0))
  | .nat => .ok (.scalar (.u64 0))
  | .byteArray => .ok (.byteArray (.u64 0) (.u64 0))
  | .array item =>
      if supportedArrayElementType item then
        .ok (.scalar (.u64 0))
      else
        .error s!"unsupported default value type: {reprStr ((.array item : Ty))}"
  | .product left right => do
      .ok (.product (← defaultValue left) (← defaultValue right))
  | .struct name fields => do
      .ok (.struct name (← fields.mapM defaultValue))
  | .variant name ctors => do
      .ok (.variant name (.u64 0) (← ctors.mapM (fun fields => fields.mapM defaultValue)))
  | .recVariant name => .ok (.heapVariant name (.u64 0))
  | .sum left right => do
      .ok (.sum (.u64 0) (← defaultValue left) (← defaultValue right))

partial def trapValue : Ty → Except String ExtractedValue
  | .unit => .ok (.scalar .trap)
  | .bool => .ok (.scalar .trap)
  | .u8 => .ok (.scalar .trap)
  | .u32 => .ok (.scalar .trap)
  | .u64 => .ok (.scalar .trap)
  | .nat => .ok (.scalar .trap)
  | .byteArray => .ok (.byteArray .trap .trap)
  | .array item =>
      if supportedArrayElementType item then
        .ok (.scalar .trap)
      else
        .error s!"unsupported trap value type: {reprStr ((.array item : Ty))}"
  | .product left right => do
      .ok (.product (← trapValue left) (← trapValue right))
  | .struct name fields => do
      .ok (.struct name (← fields.mapM trapValue))
  | .variant name ctors => do
      .ok (.variant name .trap (← ctors.mapM (fun fields => fields.mapM trapValue)))
  | .recVariant name => .ok (.heapVariant name .trap)
  | .sum left right => do
      .ok (.sum .trap (← trapValue left) (← trapValue right))

def byteArrayCopySliceCopiedLen
    (srcLen srcOff copyLen : IRExpr) : IRExpr :=
  let available :=
    .ite
      (.ltU64 srcOff srcLen)
      (.u64Bin .sub srcLen srcOff)
      (.u64 0)
  .ite (.ltU64 copyLen available) copyLen available

def byteArrayCopySliceResultLen
    (srcLen srcOff destLen destOff copyLen : IRExpr) : IRExpr :=
  let copiedLen := byteArrayCopySliceCopiedLen srcLen srcOff copyLen
  let prefixLen := .ite (.ltU64 destOff destLen) destOff destLen
  let suffixStart := .u64Bin .add destOff copiedLen
  let suffixLen :=
    .ite
      (.ltU64 suffixStart destLen)
      (.u64Bin .sub destLen suffixStart)
      (.u64 0)
  .u64Bin .add (.u64Bin .add prefixLen copiedLen) suffixLen

def byteArrayLoadUInt64 (ptr len : IRExpr) (items : List (Nat × Nat)) : IRExpr :=
  items.foldl
    (fun acc item =>
      .u64Bin .bitOr acc
        (.u64Bin .shiftLeft (.byteArrayGet ptr len (.u64 item.fst)) (.u64 item.snd)))
    (.u64 0)

def byteArrayLoadUInt64Checked (ptr len : IRExpr) (items : List (Nat × Nat)) : IRExpr :=
  .ite
    (.eqU64 len (.u64 8))
    (byteArrayLoadUInt64 ptr len items)
    .trap

partial def valueIte
    (cond : IRCond)
    (thenValue elseValue : ExtractedValue) :
    Except String ExtractedValue :=
  match thenValue, elseValue with
  | .letE _ _ _, _ => .ok (.ite cond thenValue elseValue)
  | _, .letE _ _ _ => .ok (.ite cond thenValue elseValue)
  | .letCall _ _ _ _, _ => .ok (.ite cond thenValue elseValue)
  | _, .letCall _ _ _ _ => .ok (.ite cond thenValue elseValue)
  | .ite _ _ _, _ => .ok (.ite cond thenValue elseValue)
  | _, .ite _ _ _ => .ok (.ite cond thenValue elseValue)
  | .scalar thenExpr, .scalar elseExpr => .ok (.scalar (.ite cond thenExpr elseExpr))
  | .byteArray thenPtr thenLen, .byteArray elsePtr elseLen =>
      .ok (.byteArray (.ite cond thenPtr elsePtr) (.ite cond thenLen elseLen))
  | .product thenLeft thenRight, .product elseLeft elseRight => do
      .ok (.product
        (← valueIte cond thenLeft elseLeft)
        (← valueIte cond thenRight elseRight))
  | .sum thenTag thenLeft thenRight, .sum elseTag elseLeft elseRight => do
      .ok (.sum
        (.ite cond thenTag elseTag)
        (← valueIte cond thenLeft elseLeft)
        (← valueIte cond thenRight elseRight))
  | .struct thenName thenFields, .struct elseName elseFields =>
      if thenName == elseName && thenFields.length == elseFields.length then do
        let fields ← (thenFields.zip elseFields).mapM fun item =>
          valueIte cond item.fst item.snd
        .ok (.struct thenName fields)
      else
        .error "if branches have incompatible structure value shapes"
  | .variant thenName thenTag thenCtors, .variant elseName elseTag elseCtors =>
      if thenName == elseName && thenCtors.length == elseCtors.length then do
        let ctors ← (thenCtors.zip elseCtors).mapM fun ctorPair =>
          if ctorPair.fst.length == ctorPair.snd.length then
            ctorPair.fst.zip ctorPair.snd |>.mapM fun fieldPair =>
              valueIte cond fieldPair.fst fieldPair.snd
          else
            .error "if branches have incompatible inductive constructor payload shapes"
        .ok (.variant thenName (.ite cond thenTag elseTag) ctors)
      else
        .error "if branches have incompatible inductive value shapes"
  | .heapVariant thenName thenPtr, .heapVariant elseName elsePtr =>
      if thenName == elseName then
        .ok (.heapVariant thenName (.ite cond thenPtr elsePtr))
      else
        .error "if branches have incompatible recursive inductive value shapes"
  | .recursiveVariant thenName thenTag thenCtors,
      .recursiveVariant elseName elseTag elseCtors =>
      if thenName == elseName && thenCtors.length == elseCtors.length then do
        let combineFields (fields : List (Ty × ExtractedValue) × List (Ty × ExtractedValue)) :
            Except String (List (Ty × ExtractedValue)) :=
          if fields.fst.length == fields.snd.length then
            fields.fst.zip fields.snd |>.mapM fun fieldPair =>
              if fieldPair.fst.fst == fieldPair.snd.fst then do
                let value ← valueIte cond fieldPair.fst.snd fieldPair.snd.snd
                .ok (fieldPair.fst.fst, value)
              else
                .error "if branches have incompatible recursive inductive payload types"
          else
            .error "if branches have incompatible recursive inductive payload shapes"
        let rec combineCtors :
            Nat → List (List (Ty × ExtractedValue) × List (Ty × ExtractedValue)) →
              Except String (List (List (Ty × ExtractedValue)))
          | _, [] => .ok []
          | index, fields :: rest => do
              let head ←
                match irConstNat? thenTag, irConstNat? elseTag with
                | some thenIndex, some elseIndex =>
                    if thenIndex != index then
                      .ok fields.snd
                    else if elseIndex != index then
                      .ok fields.fst
                    else
                      combineFields fields
                | some thenIndex, none =>
                    if thenIndex == index then combineFields fields else .ok fields.snd
                | none, some elseIndex =>
                    if elseIndex == index then combineFields fields else .ok fields.fst
                | _, _ => combineFields fields
              let tail ← combineCtors (index + 1) rest
              .ok (head :: tail)
        let ctors ← combineCtors 0 (thenCtors.zip elseCtors)
        .ok (.recursiveVariant thenName (.ite cond thenTag elseTag) ctors)
      else
        .error "if branches have incompatible recursive inductive value shapes"
  | _, _ => .error "if branches have incompatible structured value shapes"

def combineIteSlots (cond : IRCond) (thenSlots elseSlots : List IRExpr) :
    Except String (List IRExpr) :=
  if thenSlots.length == elseSlots.length then
    .ok <| thenSlots.zip elseSlots |>.map fun item => .ite cond item.fst item.snd
  else
    .error "conditional flattened value shape mismatch"

partial def flattenInternalValue (ty : Ty) (value : ExtractedValue) :
    Except String (List IRExpr) :=
  match ty with
  | .unit => scalarValue value |>.map (fun expr => [expr])
  | .bool => scalarValue value |>.map (fun expr => [expr])
  | .u8 => scalarValue value |>.map (fun expr => [expr])
  | .u32 => scalarValue value |>.map (fun expr => [expr])
  | .u64 => scalarValue value |>.map (fun expr => [expr])
  | .nat => scalarValue value |>.map (fun expr => [expr])
  | .array item =>
      if supportedArrayElementType item then
        scalarValue value |>.map (fun expr => [expr])
      else
        .error s!"unsupported internal value type: {reprStr ((.array item : Ty))}"
  | .byteArray => do
      let parts ← byteArrayParts value
      .ok [parts.fst, parts.snd]
  | .product left right =>
      match value with
      | .product leftValue rightValue => do
          let leftSlots ← flattenInternalValue left leftValue
          let rightSlots ← flattenInternalValue right rightValue
          .ok (leftSlots ++ rightSlots)
      | .letE slot value body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenInternalValue ty thenValue) (← flattenInternalValue ty elseValue)
      | _ => .error "non-product value used where product internal value is required"
  | .sum left right =>
      match value with
      | .sum tag leftValue rightValue => do
          let leftSlots ← flattenInternalValue left leftValue
          let rightSlots ← flattenInternalValue right rightValue
          .ok (tag :: leftSlots ++ rightSlots)
      | .letE slot value body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenInternalValue ty thenValue) (← flattenInternalValue ty elseValue)
      | _ => .error "non-sum value used where sum internal value is required"
  | .struct name fields =>
      match value with
      | .struct actual values =>
          if actual == name && values.length == fields.length then do
            let flattened ← (fields.zip values).mapM fun item =>
              flattenInternalValue item.fst item.snd
            .ok flattened.flatten
          else
            .error s!"structure internal value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenInternalValue ty thenValue) (← flattenInternalValue ty elseValue)
      | _ => .error s!"non-structure value used where structure internal value is required: {name}"
  | .variant name ctors =>
      match value with
      | .variant actual tag values =>
          if actual == name && values.length == ctors.length then do
            let flattened ← (ctors.zip values).mapM fun ctorPair =>
              if ctorPair.fst.length == ctorPair.snd.length then do
                let fields ← ctorPair.fst.zip ctorPair.snd |>.mapM fun fieldPair =>
                  flattenInternalValue fieldPair.fst fieldPair.snd
                .ok fields.flatten
              else
                .error s!"inductive internal constructor payload shape mismatch: {name}"
            .ok (tag :: flattened.flatten)
          else
            .error s!"inductive internal value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenInternalValue ty thenValue) (← flattenInternalValue ty elseValue)
      | _ => .error s!"non-inductive value used where inductive internal value is required: {name}"
  | .recVariant name =>
      match value with
      | .heapVariant actual ptr =>
          if actual == name then
            .ok [ptr]
          else
            .error s!"recursive inductive internal value shape mismatch: {name}"
      | .recursiveVariant actual tag ctors =>
          if actual == name then do
            let flattened ← ctors.mapM fun fields =>
              fields.mapM (fun field => flattenInternalValue field.fst field.snd)
            .ok [(.heapAllocSlots (tag :: flattened.flatten.flatten))]
          else
            .error s!"recursive inductive internal value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenInternalValue ty thenValue) (← flattenInternalValue ty elseValue)
      | _ =>
          .error s!"non-recursive value used where recursive inductive internal value is required: {name}"

partial def flattenAbiValue (ty : Ty) (value : ExtractedValue) : Except String (List IRExpr) :=
  match ty with
  | .unit => scalarValue value |>.map (fun expr => [expr])
  | .bool => scalarValue value |>.map (fun expr => [expr])
  | .u8 => scalarValue value |>.map (fun expr => [expr])
  | .u32 => scalarValue value |>.map (fun expr => [expr])
  | .u64 => scalarValue value |>.map (fun expr => [expr])
  | .nat => scalarValue value |>.map (fun expr => [expr])
  | .array item =>
      if supportedAbiArrayElementType item then
        scalarValue value |>.map (fun expr => [expr])
      else
        .error s!"unsupported ABI value type: {reprStr ((.array item : Ty))}"
  | .byteArray => do
      let parts ← byteArrayParts value
      .ok [parts.fst, parts.snd]
  | .struct name fields => do
      match value with
      | .struct actual values =>
          if actual == name && values.length == fields.length then
            let flattened ← (fields.zip values).mapM fun item =>
              flattenAbiValue item.fst item.snd
            .ok flattened.flatten
          else
            .error s!"structure ABI value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenAbiValue ty thenValue) (← flattenAbiValue ty elseValue)
      | _ => .error s!"non-structure value used where structure ABI value is required: {name}"
  | .variant name ctors => do
      match value with
      | .variant actual tag values =>
          if actual == name && values.length == ctors.length then do
            let flattened ← (ctors.zip values).mapM fun ctorPair =>
              if ctorPair.fst.length == ctorPair.snd.length then do
                let fields ← ctorPair.fst.zip ctorPair.snd |>.mapM fun fieldPair =>
                  flattenAbiValue fieldPair.fst fieldPair.snd
                .ok fields.flatten
              else
                .error s!"inductive ABI constructor payload shape mismatch: {name}"
            .ok (tag :: flattened.flatten)
          else
            .error s!"inductive ABI value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenAbiValue ty thenValue) (← flattenAbiValue ty elseValue)
      | _ => .error s!"non-inductive value used where inductive ABI value is required: {name}"
  | .recVariant name =>
      match value with
      | .heapVariant actual ptr =>
          if actual == name then
            .ok [ptr]
          else
            .error s!"recursive inductive ABI value shape mismatch: {name}"
      | .recursiveVariant actual tag ctors =>
          if actual == name then do
            let flattened ← ctors.mapM fun fields =>
              fields.mapM (fun field => flattenInternalValue field.fst field.snd)
            .ok [(.heapAllocSlots (tag :: flattened.flatten.flatten))]
          else
            .error s!"recursive inductive ABI value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenAbiValue ty thenValue) (← flattenAbiValue ty elseValue)
      | _ => .error s!"non-recursive value used where recursive inductive ABI value is required: {name}"
  | other => .error s!"unsupported ABI value type: {reprStr other}"

def resultSlotCount (useAbi : Bool) (ty : Ty) : Nat :=
  if useAbi then abiSlots ty else internalSlots ty

def flattenResultValue (useAbi : Bool) (ty : Ty) (value : ExtractedValue) :
    Except String (List IRExpr) :=
  if useAbi then flattenAbiValue ty value else flattenInternalValue ty value

def assignResultSlots (targets : List Nat) (values : List IRExpr) : IRStmt :=
  LeanExe.IR.seqList <|
    (targets.zip values).map fun item =>
      LeanExe.IR.Stmt.assign item.fst item.snd

partial def materializeResultValue
    (useAbi : Bool)
    (ty : Ty)
    (targets : List Nat)
    (value : ExtractedValue) :
    Except String IRStmt := do
  match value with
  | .letE slot expr body => do
      .ok (.seq (.assign slot expr) (← materializeResultValue useAbi ty targets body))
  | .letCall slots index args body => do
      .ok (.seq (.call slots index args) (← materializeResultValue useAbi ty targets body))
  | .ite cond thenValue elseValue => do
      let thenStmt ← materializeResultValue useAbi ty targets thenValue
      let elseStmt ← materializeResultValue useAbi ty targets elseValue
      .ok (.ite cond thenStmt elseStmt)
  | _ =>
      let values ← flattenResultValue useAbi ty value
      if targets.length == values.length then
        .ok (assignResultSlots targets values)
      else
        .error "result slot count mismatch"

mutual
  partial def heapLoadValueAt (ptr : IRExpr) : Ty → Nat → Except String (ExtractedValue × Nat)
    | .unit, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .bool, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .u8, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .u32, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .u64, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .nat, slot => .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
    | .array item, slot =>
        if supportedArrayElementType item then
          .ok (.scalar (.heapLoadSlot ptr slot), slot + 1)
        else
          .error s!"unsupported heap field array type: {reprStr ((.array item : Ty))}"
    | .byteArray, slot =>
        .ok (.byteArray (.heapLoadSlot ptr slot) (.heapLoadSlot ptr (slot + 1)), slot + 2)
    | .product left right, slot => do
        let leftLoaded ← heapLoadValueAt ptr left slot
        let rightLoaded ← heapLoadValueAt ptr right leftLoaded.snd
        .ok (.product leftLoaded.fst rightLoaded.fst, rightLoaded.snd)
    | .sum left right, slot => do
        let leftLoaded ← heapLoadValueAt ptr left (slot + 1)
        let rightLoaded ← heapLoadValueAt ptr right leftLoaded.snd
        .ok (.sum (.heapLoadSlot ptr slot) leftLoaded.fst rightLoaded.fst, rightLoaded.snd)
    | .struct name fields, slot => do
        let loaded ← heapLoadFieldsAt ptr fields slot
        .ok (.struct name loaded.fst, loaded.snd)
    | .variant name ctors, slot => do
        let loaded ← heapLoadCtorsAt ptr ctors (slot + 1)
        .ok (.variant name (.heapLoadSlot ptr slot) loaded.fst, loaded.snd)
    | .recVariant name, slot => .ok (.heapVariant name (.heapLoadSlot ptr slot), slot + 1)

  partial def heapLoadFieldsAt (ptr : IRExpr) :
      List Ty → Nat → Except String (List ExtractedValue × Nat)
    | [], slot => .ok ([], slot)
    | field :: rest, slot => do
        let head ← heapLoadValueAt ptr field slot
        let tail ← heapLoadFieldsAt ptr rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)

  partial def heapLoadCtorsAt (ptr : IRExpr) :
      List (List Ty) → Nat → Except String (List (List ExtractedValue) × Nat)
    | [], slot => .ok ([], slot)
    | fields :: rest, slot => do
        let head ← heapLoadFieldsAt ptr fields slot
        let tail ← heapLoadCtorsAt ptr rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)
end

partial def flattenFieldsFromKinds
    (typeName : Name)
    (fieldKinds : List (Option Ty))
    (runtimeFields : List ExtractedValue) :
    Except String (List IRExpr) := do
  let rec loop :
      List (Option Ty) → List ExtractedValue → List (List IRExpr) →
        Except String (List IRExpr)
    | [], [], acc => .ok acc.reverse.flatten
    | [], _ :: _, _ => .error s!"too many runtime fields for {typeName}"
    | some ty :: restKinds, field :: restFields, acc => do
        let flattened ← flattenInternalValue ty field
        loop restKinds restFields (flattened :: acc)
    | some _ :: _, [], _ => .error s!"too few runtime fields for {typeName}"
    | none :: restKinds, fields, acc =>
        loop restKinds fields acc
  loop fieldKinds runtimeFields []

partial def defaultCtorSlotValues (ctors : List VariantCtorLayout) :
    Except String (List (List IRExpr)) :=
  ctors.mapM fun ctor => do
    let defaults ← runtimeTypesFromKinds ctor.fields |>.mapM defaultValue
    flattenFieldsFromKinds ctor.name ctor.fields defaults

partial def heapRuntimeFieldsFromKinds
    (ptr : IRExpr)
    (fieldKinds : List (Option Ty))
    (slot : Nat) :
    Except String (List ExtractedValue × Nat) :=
  let rec loop :
      List (Option Ty) → Nat → List ExtractedValue →
        Except String (List ExtractedValue × Nat)
    | [], next, acc => .ok (acc.reverse, next)
    | some ty :: rest, next, acc => do
        let loaded ← heapLoadValueAt ptr ty next
        loop rest loaded.snd (loaded.fst :: acc)
    | none :: rest, next, acc =>
        loop rest next acc
  loop fieldKinds slot []

partial def flattenArrayElementValue
    (ty : Ty)
    (value : ExtractedValue) :
    Except String (List IRExpr) :=
  match ty with
  | .bool => scalarValue value |>.map (fun expr => [expr])
  | .u8 => scalarValue value |>.map (fun expr => [expr])
  | .u32 => scalarValue value |>.map (fun expr => [expr])
  | .u64 => scalarValue value |>.map (fun expr => [expr])
  | .nat => scalarValue value |>.map (fun expr => [expr])
  | .recVariant name =>
      match value with
      | .heapVariant actual ptr =>
          if actual == name then
            .ok [ptr]
          else
            .error s!"recursive inductive array element shape mismatch: {name}"
      | .recursiveVariant actual tag ctors =>
          if actual == name then do
            let flattened ← ctors.mapM fun fields =>
              fields.mapM (fun field => flattenInternalValue field.fst field.snd)
            .ok [(.heapAllocSlots (tag :: flattened.flatten.flatten))]
          else
            .error s!"recursive inductive array element shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond
            (← flattenArrayElementValue ty thenValue)
            (← flattenArrayElementValue ty elseValue)
      | _ =>
          .error s!"non-recursive value used where recursive inductive array element is required: {name}"
  | .struct name fields =>
      match value with
      | .struct actual values =>
          if actual == name && values.length == fields.length then do
            let flattened ← (fields.zip values).mapM fun item =>
              flattenArrayElementValue item.fst item.snd
            .ok flattened.flatten
          else
            .error s!"structure array element shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond
            (← flattenArrayElementValue ty thenValue)
            (← flattenArrayElementValue ty elseValue)
      | _ =>
          .error s!"non-structure value used where structure array element is required: {name}"
  | .variant name ctors =>
      match value with
      | .variant actual tag values =>
          if actual == name && values.length == ctors.length then do
            let flattened ← (ctors.zip values).mapM fun ctorPair =>
              if ctorPair.fst.length == ctorPair.snd.length then do
                let fields ← (ctorPair.fst.zip ctorPair.snd).mapM (fun item =>
                  flattenArrayElementValue item.fst item.snd)
                .ok fields.flatten
              else
                .error s!"inductive array element payload shape mismatch: {name}"
            .ok (tag :: flattened.flatten)
          else
            .error s!"inductive array element shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenArrayElementValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond
            (← flattenArrayElementValue ty thenValue)
            (← flattenArrayElementValue ty elseValue)
      | _ => .error s!"non-inductive value used where inductive array element is required: {name}"
  | other => .error s!"unsupported array element value type: {reprStr other}"

partial def materializeSlotsWith
    (flatten : ExtractedValue → Except String (List IRExpr))
    (value : ExtractedValue)
    (nextLocal : Nat) :
    Except String MaterializedSlots := do
  match value with
  | .letE slot expr body => do
      let result ← materializeSlotsWith flatten body nextLocal
      .ok { result with lets := .expr slot expr :: result.lets }
  | .letCall slots index args body => do
      let result ← materializeSlotsWith flatten body nextLocal
      .ok { result with lets := .call slots index args :: result.lets }
  | _ =>
      .ok { lets := [], slots := ← flatten value, nextLocal := nextLocal }

def materializeInternalSlots
    (ty : Ty)
    (value : ExtractedValue)
    (nextLocal : Nat) :
    Except String MaterializedSlots :=
  materializeSlotsWith (flattenInternalValue ty) value nextLocal

def materializeArrayElementSlots
    (ty : Ty)
    (value : ExtractedValue)
    (nextLocal : Nat) :
    Except String MaterializedSlots :=
  materializeSlotsWith (flattenArrayElementValue ty) value nextLocal

mutual
  partial def arrayLoadValueAt
      (width : Nat)
      (array index : IRExpr) :
      Ty → Nat → Except String (ExtractedValue × Nat)
    | .bool, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .u8, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .u32, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .u64, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .nat, slot => .ok (.scalar (.arrayGetSlot width slot array index), slot + 1)
    | .recVariant name, slot =>
        .ok (.heapVariant name (.arrayGetSlot width slot array index), slot + 1)
    | .struct name fields, slot => do
        let result ← arrayLoadFieldsAt width array index fields slot
        .ok (.struct name result.fst, result.snd)
    | .variant name ctors, slot => do
        let tag := .arrayGetSlot width slot array index
        let result ← arrayLoadCtorsAt width array index ctors (slot + 1)
        .ok (.variant name tag result.fst, result.snd)
    | other, _ => .error s!"unsupported array element load type: {reprStr other}"

  partial def arrayLoadFieldsAt
      (width : Nat)
      (array index : IRExpr) :
      List Ty → Nat → Except String (List ExtractedValue × Nat)
    | [], slot => .ok ([], slot)
    | field :: rest, slot => do
        let head ← arrayLoadValueAt width array index field slot
        let tail ← arrayLoadFieldsAt width array index rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)

  partial def arrayLoadCtorsAt
      (width : Nat)
      (array index : IRExpr) :
      List (List Ty) → Nat → Except String (List (List ExtractedValue) × Nat)
    | [], slot => .ok ([], slot)
    | fields :: rest, slot => do
        let head ← arrayLoadFieldsAt width array index fields slot
        let tail ← arrayLoadCtorsAt width array index rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)
end

def arrayLoadValue
    (itemTy : Ty)
    (array index : IRExpr) :
    Except String ExtractedValue := do
  let width ←
    match arrayElementSlots? itemTy with
    | some width => .ok width
    | none => .error s!"unsupported array element type: {reprStr itemTy}"
  let loaded ← arrayLoadValueAt width array index itemTy 0
  .ok loaded.fst

mutual
  partial def arrayFindValueAt
      (width : Nat)
      (array : IRExpr)
      (itemStart : Nat)
      (predicate : IRExpr) :
      Ty → Nat → Except String (ExtractedValue × Nat)
    | .bool, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .u8, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .u32, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .u64, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .nat, slot => .ok (.scalar (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .recVariant name, slot =>
        .ok (.heapVariant name (.arrayFindSlot width array itemStart predicate slot), slot + 1)
    | .struct name fields, slot => do
        let result ← arrayFindFieldsAt width array itemStart predicate fields slot
        .ok (.struct name result.fst, result.snd)
    | .variant name ctors, slot => do
        let tag := .arrayFindSlot width array itemStart predicate slot
        let result ← arrayFindCtorsAt width array itemStart predicate ctors (slot + 1)
        .ok (.variant name tag result.fst, result.snd)
    | other, _ => .error s!"unsupported array find element type: {reprStr other}"

  partial def arrayFindFieldsAt
      (width : Nat)
      (array : IRExpr)
      (itemStart : Nat)
      (predicate : IRExpr) :
      List Ty → Nat → Except String (List ExtractedValue × Nat)
    | [], slot => .ok ([], slot)
    | field :: rest, slot => do
        let head ← arrayFindValueAt width array itemStart predicate field slot
        let tail ← arrayFindFieldsAt width array itemStart predicate rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)

  partial def arrayFindCtorsAt
      (width : Nat)
      (array : IRExpr)
      (itemStart : Nat)
      (predicate : IRExpr) :
      List (List Ty) → Nat → Except String (List (List ExtractedValue) × Nat)
    | [], slot => .ok ([], slot)
    | fields :: rest, slot => do
        let head ← arrayFindFieldsAt width array itemStart predicate fields slot
        let tail ← arrayFindCtorsAt width array itemStart predicate rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)
end

def arrayFindValue
    (itemTy : Ty)
    (width : Nat)
    (array : IRExpr)
    (itemStart : Nat)
    (predicate : IRExpr) :
    Except String ExtractedValue := do
  let loaded ← arrayFindValueAt width array itemStart predicate itemTy 0
  .ok loaded.fst

mutual
  partial def arrayLocalValueAt (start : Nat) :
      Ty → Nat → Except String (ExtractedValue × Nat)
    | .bool, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .u8, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .u32, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .u64, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .nat, slot => .ok (.scalar (.local (start + slot)), slot + 1)
    | .recVariant name, slot => .ok (.heapVariant name (.local (start + slot)), slot + 1)
    | .struct name fields, slot => do
        let result ← arrayLocalFieldsAt start fields slot
        .ok (.struct name result.fst, result.snd)
    | .variant name ctors, slot => do
        let tag := .local (start + slot)
        let result ← arrayLocalCtorsAt start ctors (slot + 1)
        .ok (.variant name tag result.fst, result.snd)
    | other, _ => .error s!"unsupported array local element type: {reprStr other}"

  partial def arrayLocalFieldsAt (start : Nat) :
      List Ty → Nat → Except String (List ExtractedValue × Nat)
    | [], slot => .ok ([], slot)
    | field :: rest, slot => do
        let head ← arrayLocalValueAt start field slot
        let tail ← arrayLocalFieldsAt start rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)

  partial def arrayLocalCtorsAt (start : Nat) :
      List (List Ty) → Nat → Except String (List (List ExtractedValue) × Nat)
    | [], slot => .ok ([], slot)
    | fields :: rest, slot => do
        let head ← arrayLocalFieldsAt start fields slot
        let tail ← arrayLocalCtorsAt start rest head.snd
        .ok (head.fst :: tail.fst, tail.snd)
end

def arrayLocalValue (itemTy : Ty) (start : Nat) : Except String ExtractedValue := do
  let loaded ← arrayLocalValueAt start itemTy 0
  .ok loaded.fst

def arrayElementWidth (context : String) (itemTy : Ty) : Except String Nat :=
  match arrayElementSlots? itemTy with
  | some width => .ok width
  | none => .error s!"unsupported {context} item type: {reprStr itemTy}"

mutual
  partial def extractedValueForParam (slot : Nat) : Ty → ExtractedValue
    | .byteArray => .byteArray (.local slot) (.local (slot + 1))
    | .struct name fields => .struct name (extractedStructFieldsForParam slot fields)
    | .variant name ctors =>
        .variant name (.local slot) (extractedVariantCtorsForParam (slot + 1) ctors)
    | .recVariant name => .heapVariant name (.local slot)
    | _ => .scalar (.local slot)

  partial def extractedStructFieldsForParam (slot : Nat) : List Ty → List ExtractedValue
    | [] => []
    | ty :: rest =>
        extractedValueForParam slot ty :: extractedStructFieldsForParam (slot + abiSlots ty) rest

  partial def extractedVariantCtorsForParam (slot : Nat) :
      List (List Ty) → List (List ExtractedValue)
    | [] => []
    | fields :: rest =>
        extractedStructFieldsForParam slot fields ::
          extractedVariantCtorsForParam
            (slot + fields.foldl (fun total field => total + abiSlots field) 0)
            rest
end

def bindingForParam (slot : Nat) : Ty → Binding
  | .byteArray => .value (.byteArray (.local slot) (.local (slot + 1)))
  | .struct name fields => .value (.struct name (extractedStructFieldsForParam slot fields))
  | .variant name ctors =>
      .value (.variant name (.local slot) (extractedVariantCtorsForParam (slot + 1) ctors))
  | .recVariant name => .value (.heapVariant name (.local slot))
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

def sourceFieldBindingsFromKinds
    (typeName : Name)
    (fieldKinds : List (Option Ty))
    (runtimeFields : List ExtractedValue) :
    Except String (List Binding) := do
  let rec loop :
      List (Option Ty) → List ExtractedValue → List Binding →
        Except String (List Binding)
    | [], [], acc => .ok acc.reverse
    | [], _ :: _, _ => .error s!"too many runtime fields for {typeName}"
    | some _ :: restKinds, field :: restFields, acc =>
        loop restKinds restFields (.value field :: acc)
    | some _ :: _, [], _ => .error s!"too few runtime fields for {typeName}"
    | none :: restKinds, fields, acc =>
        loop restKinds fields (.value (.scalar (.u64 0)) :: acc)
  loop fieldKinds runtimeFields []

partial def defaultCtorValues (ctors : List VariantCtorLayout) :
    Except String (List (List ExtractedValue)) :=
  ctors.mapM fun ctor => runtimeTypesFromKinds ctor.fields |>.mapM defaultValue

def typedFieldsFromKinds
    (typeName : Name)
    (fieldKinds : List (Option Ty))
    (runtimeFields : List ExtractedValue) :
    Except String (List (Ty × ExtractedValue)) := do
  let rec loop :
      List (Option Ty) → List ExtractedValue → List (Ty × ExtractedValue) →
        Except String (List (Ty × ExtractedValue))
    | [], [], acc => .ok acc.reverse
    | [], _ :: _, _ => .error s!"too many runtime fields for {typeName}"
    | some ty :: restKinds, field :: restFields, acc =>
        loop restKinds restFields ((ty, field) :: acc)
    | some _ :: _, [], _ => .error s!"too few runtime fields for {typeName}"
    | none :: restKinds, fields, acc =>
        loop restKinds fields acc
  loop fieldKinds runtimeFields []

partial def defaultCtorTypedValues (ctors : List VariantCtorLayout) :
    Except String (List (List (Ty × ExtractedValue))) :=
  ctors.mapM fun ctor => do
    let values ← runtimeTypesFromKinds ctor.fields |>.mapM fun ty => do
      let value ← defaultValue ty
      .ok (ty, value)
    .ok values

def replaceAt? {α : Type} (index : Nat) (value : α) : List α → Option (List α)
  | [] => none
  | head :: rest =>
      if index == 0 then
        some (value :: rest)
      else
        replaceAt? (index - 1) value rest |>.map fun updated => head :: updated

def optionConstructorType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | ty :: _ => typeAtom? env ty
  | [] => none

def exceptConstructorTypes? (env : Environment) (args : List Expr) : Option (Ty × Ty) :=
  match args with
  | errorTy :: okTy :: _ =>
      match typeAtom? env errorTy, typeAtom? env okTy with
      | some errorTy, some okTy => some (errorTy, okTy)
      | _, _ => none
  | _ => none

def exceptMapTypes? (env : Environment) (args : List Expr) : Option (Ty × Ty) :=
  match args with
  | errorTy :: _sourceTy :: resultTy :: _ =>
      match typeAtom? env errorTy, typeAtom? env resultTy with
      | some errorTy, some resultTy => some (errorTy, resultTy)
      | _, _ => none
  | _ => none

def exceptMapErrorTypes? (env : Environment) (args : List Expr) : Option (Ty × Ty) :=
  match args with
  | sourceErrorTy :: resultErrorTy :: _okTy :: _ =>
      match typeAtom? env sourceErrorTy, typeAtom? env resultErrorTy with
      | some sourceErrorTy, some resultErrorTy => some (sourceErrorTy, resultErrorTy)
      | _, _ => none
  | _ => none

def exceptPayloadType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | errorTy :: okTy :: _ =>
      match typeAtom? env errorTy, typeAtom? env okTy with
      | some _, some okTy => some okTy
      | _, _ => none
  | _ => none

def optionMapResultType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | _sourceTy :: resultTy :: _ => typeAtom? env resultTy
  | _ => none

def optionOrElseArgs? (env : Environment) (fn : Expr) (args : List Expr) : Option (Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Option.orElse then
        match args.reverse with
        | fallback :: optionValue :: _ => some (optionValue, fallback)
        | _ => none
      else if name == ``HOrElse.hOrElse then
        match primitiveResultType? env args, args.reverse with
        | some resultTy, fallback :: optionValue :: _ =>
            optionPayloadType? resultTy |>.map (fun _ => (optionValue, fallback))
        | _, _ => none
      else
        none
  | _ => none

def exceptOrElseArgs? (env : Environment) (fn : Expr) (args : List Expr) : Option (Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``HOrElse.hOrElse then
        match primitiveResultType? env args, args.reverse with
        | some (.variant typeName _), fallback :: exceptValue :: _ =>
            if typeName == ``Except then some (exceptValue, fallback) else none
        | _, _ => none
      else
        none
  | _ => none

def idBindArgs? (fn : Expr) (args : List Expr) : Option (Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Bind.bind then
        match args, args.reverse with
        | monadTy :: _, bindFn :: value :: _ =>
            if isIdType monadTy then some (value, bindFn) else none
        | _, _ => none
      else
        none
  | _ => none

partial def listLiteralItems? (env : Environment) (expr : Expr) : Option (Ty × List Expr) :=
  match appFnArgs expr with
  | (.const ``List.nil _, [itemTy]) =>
      typeAtom? env itemTy |>.map (fun ty => (ty, []))
  | (.const ``List.cons _, [itemTy, head, tail]) =>
      match typeAtom? env itemTy, listLiteralItems? env tail with
      | some ty, some (tailTy, items) =>
          if ty == tailTy then
            some (ty, head :: items)
          else
            none
      | _, _ => none
  | _ => none

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
        | _motive :: scrutineeType :: _ => typeAtom? env scrutineeType
        | _ => none
    | none => none

def optionMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  let optionArmKind? (payloadTy : Ty) (arm : Expr) : Option Bool :=
    match arm.consumeMData with
    | .lam _ domain _ _ =>
        match typeAtom? env domain with
        | some .unit => some false
        | some ty => if ty == payloadTy then some true else none
        | none => none
    | _ => none
  let generatedOptionArgs? (payloadTy : Ty) : Option (Expr × Expr × Expr) :=
    match args with
    | [_motive, scrutinee, firstArm, secondArm] =>
        match optionArmKind? payloadTy firstArm, optionArmKind? payloadTy secondArm with
        | some false, some true => some (scrutinee, firstArm, secondArm)
        | some true, some false => some (scrutinee, secondArm, firstArm)
        | _, _ => none
    | _ => none
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Option.casesOn || name == ``Option.rec then
        match args.reverse with
        | someArm :: noneArm :: scrutinee :: _ => some (scrutinee, noneArm, someArm)
        | _ => none
      else
        match generatedMatcherScrutineeType? env name with
        | some resultTy =>
            match optionPayloadType? resultTy with
            | some payloadTy => generatedOptionArgs? payloadTy
            | none => none
        | _ => none
  | _ => none

partial def exceptArmTarget? (expr : Expr) : Option Bool :=
  match expr.consumeMData with
  | .forallE _ _ body _ => exceptArmTarget? body
  | .app _ value =>
      match appFnArgs value with
      | (.const ``Except.error _, _) => some false
      | (.const ``Except.ok _, _) => some true
      | _ => none
  | _ => none

def exceptMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  let generatedExceptArgs? (name : Name) : Option (Expr × Expr × Expr) :=
    match env.find? name, args with
    | some info, [_motive, scrutinee, firstArm, secondArm] =>
        match (peelForall info.type).fst with
        | _motiveTy :: _scrutineeTy :: firstArmTy :: secondArmTy :: _ =>
            match exceptArmTarget? firstArmTy, exceptArmTarget? secondArmTy with
            | some false, some true => some (scrutinee, firstArm, secondArm)
            | some true, some false => some (scrutinee, secondArm, firstArm)
            | _, _ => none
        | _ => none
    | _, _ => none
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Except.casesOn then
        match args.reverse with
        | okArm :: errorArm :: scrutinee :: _ => some (scrutinee, errorArm, okArm)
        | _ => none
      else if name == ``Except.rec then
        match args.reverse with
        | scrutinee :: okArm :: errorArm :: _ => some (scrutinee, errorArm, okArm)
        | _ => none
      else
        generatedExceptArgs? name
  | _ => none

partial def boolArmTarget? (expr : Expr) : Option Bool :=
  match expr.consumeMData with
  | .forallE _ _ body _ => boolArmTarget? body
  | .app _ value =>
      if isConst ``Bool.false value then
        some false
      else if isConst ``Bool.true value then
        some true
      else
        none
  | _ => none

def boolMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  let generatedBoolArgs? (name : Name) : Option (Expr × Expr × Expr) :=
    match env.find? name, args with
    | some info, [_motive, scrutinee, firstArm, secondArm] =>
        match (peelForall info.type).fst with
        | _motiveTy :: _scrutineeTy :: firstArmTy :: secondArmTy :: _ =>
            match boolArmTarget? firstArmTy, boolArmTarget? secondArmTy with
            | some false, some true => some (scrutinee, firstArm, secondArm)
            | some true, some false => some (scrutinee, secondArm, firstArm)
            | _, _ => none
        | _ => none
    | _, _ => none
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Bool.casesOn then
        match args with
        | [_motive, scrutinee, falseArm, trueArm] => some (scrutinee, falseArm, trueArm)
        | _ => none
      else if generatedMatcherScrutineeType? env name == some .bool then
        generatedBoolArgs? name
      else
        none
  | _ => none

def natMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  let natArmKind? (arm : Expr) : Option Bool :=
    match arm.consumeMData with
    | .lam _ domain _ _ =>
        match typeAtom? env domain with
        | some .unit => some false
        | some .nat => some true
        | _ => none
    | _ => none
  let generatedNatArgs? : Option (Expr × Expr × Expr) :=
    match args with
    | [_motive, scrutinee, firstArm, secondArm] =>
        match natArmKind? firstArm, natArmKind? secondArm with
        | some false, some true => some (scrutinee, firstArm, secondArm)
        | some true, some false => some (scrutinee, secondArm, firstArm)
        | _, _ => none
    | _ => none
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Nat.casesOn then
        match args with
        | [_motive, scrutinee, zeroArm, succArm] => some (scrutinee, zeroArm, succArm)
        | _ => none
      else if generatedMatcherScrutineeType? env name == some .nat then
        generatedNatArgs?
      else
        none
  | _ => none

def productMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Prod.casesOn then
        match args.reverse with
        | arm :: scrutinee :: _ => some (scrutinee, arm)
        | _ => none
      else if name == ``Prod.rec then
        match args.reverse with
        | scrutinee :: arm :: _ => some (scrutinee, arm)
        | _ => none
      else
        match generatedMatcherScrutineeType? env name, args with
        | some (.product _ _), [_motive, scrutinee, arm] => some (scrutinee, arm)
        | _, _ => none
  | _ => none

def structureMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Name × Expr × Expr) :=
  let directMatcher? (name : Name) : Option (Name × Expr × Expr) :=
    match env.find? name with
    | some (.recInfo recInfo) =>
        match recInfo.all with
        | structName :: [] =>
            if (structureFieldKinds? env structName).isSome then
              if name == .str structName "casesOn" || name == .str structName "recOn" then
                match args.reverse with
                | arm :: scrutinee :: _ => some (structName, scrutinee, arm)
                | _ => none
              else if name == .str structName "rec" then
                match args.reverse with
                | scrutinee :: arm :: _ => some (structName, scrutinee, arm)
                | _ => none
              else
                none
            else
              none
        | _ => none
    | _ => none
  let generatedMatcher? (name : Name) : Option (Name × Expr × Expr) :=
    match generatedMatcherScrutineeType? env name, args with
    | some (.struct structName _), [_motive, scrutinee, arm] =>
        some (structName, scrutinee, arm)
    | _, _ => none
  match fn.consumeMData with
  | .const name _ =>
      match directMatcher? name with
      | some result => some result
      | none => generatedMatcher? name
  | _ => none

partial def variantArmCtorName? (env : Environment) (expr : Expr) : Option Name :=
  match expr.consumeMData with
  | .forallE _ _ body _ => variantArmCtorName? env body
  | .mdata _ body => variantArmCtorName? env body
  | .app _ value =>
      match appFnArgs value with
      | (.const ctorName _, _) =>
          match anyVariantConstructor? env ctorName with
          | some _ => some ctorName
          | none => none
      | _ => none
  | _ => none

def reorderVariantArms?
    (ctorNames : List Name)
    (typedArms : List (Name × Expr)) :
    Option (List Expr) :=
  ctorNames.mapM fun ctorName =>
    typedArms.find? (fun item => item.fst == ctorName) |>.map Prod.snd

def variantMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (VariantLayout × Expr × List Expr) :=
  let directMatcher? (name : Name) : Option (VariantLayout × Expr × List Expr) :=
    match env.find? name with
    | some (.recInfo recInfo) =>
        match recInfo.all with
        | typeName :: [] =>
            match anyVariantLayout? env typeName with
            | some layout =>
                let ctorCount := layout.ctors.length
                if name == .str typeName "casesOn" || name == .str typeName "recOn" then
                  match args with
                  | _motive :: scrutinee :: rest =>
                      if rest.length == ctorCount then
                        some (layout, scrutinee, rest)
                      else
                        none
                  | _ => none
                else if name == .str typeName "rec" then
                  match args with
                  | _motive :: rest =>
                      let arms := rest.take ctorCount
                      match rest.drop ctorCount with
                      | scrutinee :: [] =>
                          if arms.length == ctorCount then
                            some (layout, scrutinee, arms)
                          else
                            none
                      | _ => none
                  | _ => none
                else
                  none
            | none => none
        | _ => none
    | _ => none
  let generatedMatcher? (name : Name) : Option (VariantLayout × Expr × List Expr) :=
    match generatedMatcherScrutineeType? env name, env.find? name, args with
    | some (.variant typeName _), some info, _motive :: scrutinee :: arms =>
        match anyVariantLayout? env typeName with
        | some layout =>
            let ctorCount := layout.ctors.length
            if arms.length == ctorCount then
              match (peelForall info.type).fst.drop 2 with
              | armTypes =>
                  let armTypes := armTypes.take ctorCount
                  if armTypes.length == ctorCount then
                    let typedArms? :=
                      (armTypes.zip arms).mapM fun item =>
                        variantArmCtorName? env item.fst |>.map fun ctorName =>
                          (ctorName, item.snd)
                    match typedArms? with
                    | some typedArms =>
                        reorderVariantArms? (layout.ctors.map (fun ctor => ctor.name)) typedArms
                          |>.map fun orderedArms => (layout, scrutinee, orderedArms)
                    | none => none
                  else
                    none
            else
              none
        | none => none
    | some (.recVariant typeName), some info, _motive :: scrutinee :: arms =>
        match recursiveVariantLayout? env typeName with
        | some layout =>
            let ctorCount := layout.ctors.length
            if arms.length == ctorCount then
              match (peelForall info.type).fst.drop 2 with
              | armTypes =>
                  let armTypes := armTypes.take ctorCount
                  if armTypes.length == ctorCount then
                    let typedArms? :=
                      (armTypes.zip arms).mapM fun item =>
                        variantArmCtorName? env item.fst |>.map fun ctorName =>
                          (ctorName, item.snd)
                    match typedArms? with
                    | some typedArms =>
                        reorderVariantArms? (layout.ctors.map (fun ctor => ctor.name)) typedArms
                          |>.map fun orderedArms => (layout, scrutinee, orderedArms)
                    | none => none
                  else
                    none
            else
              none
        | none => none
    | _, _, _ => none
  match fn.consumeMData with
  | .const name _ =>
      match directMatcher? name with
      | some result => some result
      | none => generatedMatcher? name
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

def bindSlotExprs (slots : List IRExpr) (nextLocal : Nat) : MaterializedSlots :=
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
                  if isIdType monadTy then demandExpr ctx visiting value else .empty
              | _, _ => .empty
          | (.const ``Bind.bind _, args) =>
              match idBindArgs? (.const ``Bind.bind []) args with
              | some (value, bindFn) =>
                  match collectLambdas bindFn 1 with
                  | some body => Demand.letE (demandExpr ctx visiting value) (demandExpr ctx visiting body)
                  | none => .empty
              | none => .empty
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
          | (.const ``ByteArray.toUInt64LE! _, args) =>
              args.foldl (fun acc arg => Demand.always acc (demandExpr ctx visiting arg)) .empty
          | (.const ``ByteArray.toUInt64BE! _, args) =>
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

def strictCallSafe (ctx : Context) (name : Name) (args : List Expr) : Bool :=
  let summary := demandSummary ctx [] name
  let indexed := enumerate args
  indexed.all fun item =>
    !mayTrapExpr ctx item.snd || boolAt summary.mustDemand item.fst

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
          match typeAtom? ctx.env type with
          | some ty =>
              if supportedLocalType ty then
                extractValueFrom ctx (.thunk locals value :: locals) nextLocal body
              else
                .error s!"unsupported let-bound type: {type}"
          | none => .error s!"unsupported let-bound type: {type}"
    | .proj ``Prod index body =>
        let valueResult ← extractValueFrom ctx locals nextLocal body
        .ok (← productField index valueResult.fst, valueResult.snd)
    | .proj typeName index body =>
        match structureFieldKinds? ctx.env typeName with
        | some kinds =>
            match runtimeFieldIndexFromKinds index kinds with
            | some (some runtimeIndex) =>
                let valueResult ← extractValueFrom ctx locals nextLocal body
                .ok (← structField typeName runtimeIndex valueResult.fst, valueResult.snd)
            | some none => .ok (.scalar (.u64 0), nextLocal)
            | none => .error s!"unsupported structure projection index: {typeName}.{index}"
        | none => .error s!"unsupported projection: {typeName}"
    | .const ``Unit.unit _ => .ok (.scalar (.u64 0), nextLocal)
    | .const ``ByteArray.empty _ => .ok (.byteArray (.u64 0) (.u64 0), nextLocal)
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
        | (.const ``Array.swapAt _, args) =>
            match args, args.reverse with
            | itemTy :: _, _proof :: value :: index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                  match arrayElementSlots? itemTy with
                  | some width =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let arraySlot := indexResult.snd
                    let indexSlot := arraySlot + 1
                    let valueResult ← extractValueFrom ctx locals (indexSlot + 1) value
                    let valueSlots ← flattenArrayElementValue itemTy valueResult.fst
                    let oldValue ← arrayLoadValue itemTy (.local arraySlot) (.local indexSlot)
                    let updatedArray :=
                      .scalar (.arraySetSlots width (.local arraySlot) (.local indexSlot) valueSlots)
                    .ok
                      (.letE arraySlot arrayResult.fst
                        (.letE indexSlot indexResult.fst
                          (.product oldValue updatedArray)),
                        valueResult.snd)
                  | none => .error s!"unsupported Array.swapAt item type: {reprStr itemTy}"
                | none => .error "unsupported Array.swapAt item type"
            | _, _ => .error "unsupported Array.swapAt application"
        | (.const ``id _, args) =>
            match args.reverse with
            | value :: _ => extractValueFrom ctx locals nextLocal value
            | _ => .error "unsupported id application"
        | (.const ``Id.run _, args) =>
            match args.reverse with
            | value :: _ => extractValueFrom ctx locals nextLocal value
            | _ => .error "unsupported Id.run application"
        | (.const ``Pure.pure _, args) =>
            match args, args.reverse with
            | monadTy :: _, value :: _ =>
                if isIdType monadTy then
                  extractValueFrom ctx locals nextLocal value
                else
                  .error "unsupported Pure.pure application"
            | _, _ => .error "unsupported Pure.pure application"
        | (.const ``Bind.bind _, args) =>
            match idBindArgs? (.const ``Bind.bind []) args with
            | some (value, bindFn) =>
                let valueResult ← extractValueFrom ctx locals nextLocal value
                let body ←
                  match collectLambdas bindFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Id bind function"
                extractValueFrom ctx (.value valueResult.fst :: locals) valueResult.snd body
            | none => .error "unsupported Bind.bind application"
        | (.const ``Option.none _, args) =>
            match optionConstructorType? ctx.env args with
            | some payloadTy =>
                .ok (mkOptionValue (.u64 0) (← defaultValue payloadTy), nextLocal)
            | none => .error "unsupported Option.none application"
        | (.const ``Option.some _, args) =>
            match args.reverse, optionConstructorType? ctx.env args with
            | value :: _, some _ =>
                let valueResult ← extractValueFrom ctx locals nextLocal value
                .ok (mkOptionValue (.u64 1) valueResult.fst, valueResult.snd)
            | _, _ => .error "unsupported Option.some application"
        | (.const ``Except.error _, args) =>
            match args.reverse, exceptConstructorTypes? ctx.env args with
            | value :: _, some (_errorTy, okTy) =>
                let valueResult ← extractValueFrom ctx locals nextLocal value
                .ok (mkExceptValue (.u64 0) valueResult.fst (← defaultValue okTy),
                  valueResult.snd)
            | _, _ => .error "unsupported Except.error application"
        | (.const ``Except.ok _, args) =>
            match args.reverse, exceptConstructorTypes? ctx.env args with
            | value :: _, some (errorTy, _okTy) =>
                let valueResult ← extractValueFrom ctx locals nextLocal value
                .ok (mkExceptValue (.u64 1) (← defaultValue errorTy) valueResult.fst,
                  valueResult.snd)
            | _, _ => .error "unsupported Except.ok application"
        | (.const ``Except.map _, args) =>
            match args.reverse, exceptMapTypes? ctx.env args with
            | exceptValue :: mapFn :: _, some (_errorTy, resultTy) =>
                let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
                let parts ← exceptPartsWithLets exceptResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let errorPayload := parts.snd.snd.fst
                let okPayload := parts.snd.snd.snd
                let mapBody ←
                  match collectLambdas mapFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Except.map function"
                let mapResult ←
                  extractValueFrom ctx (.value okPayload :: locals) exceptResult.snd mapBody
                let defaultOk ← defaultValue resultTy
                .ok
                  (wrapValueLets lets
                    (mkExceptValue tag errorPayload
                      (← valueIte (.eqU64 tag (.u64 0)) defaultOk mapResult.fst)),
                    mapResult.snd)
            | _, _ => .error "unsupported Except.map application"
        | (.const ``Except.mapError _, args) =>
            match args.reverse, exceptMapErrorTypes? ctx.env args with
            | exceptValue :: mapFn :: _, some (_sourceErrorTy, resultErrorTy) =>
                let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
                let parts ← exceptPartsWithLets exceptResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let errorPayload := parts.snd.snd.fst
                let okPayload := parts.snd.snd.snd
                let mapBody ←
                  match collectLambdas mapFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Except.mapError function"
                let mapResult ←
                  extractValueFrom ctx (.value errorPayload :: locals) exceptResult.snd mapBody
                let defaultError ← defaultValue resultErrorTy
                .ok
                  (wrapValueLets lets
                    (mkExceptValue tag
                      (← valueIte (.eqU64 tag (.u64 0)) mapResult.fst defaultError)
                      okPayload),
                    mapResult.snd)
            | _, _ => .error "unsupported Except.mapError application"
        | (.const ``Except.bind _, args) =>
            match args.reverse, exceptMapTypes? ctx.env args with
            | bindFn :: exceptValue :: _, some (_errorTy, resultTy) =>
                let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
                let parts ← exceptPartsWithLets exceptResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let errorPayload := parts.snd.snd.fst
                let okPayload := parts.snd.snd.snd
                let bindBody ←
                  match collectLambdas bindFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Except.bind function"
                let bindResult ←
                  extractValueFrom ctx (.value okPayload :: locals) exceptResult.snd bindBody
                let bindParts ← exceptPartsWithLets bindResult.fst
                let bindLets := bindParts.fst
                let bindTag := wrapExprLets bindLets bindParts.snd.fst
                let bindError := wrapValueLets bindLets bindParts.snd.snd.fst
                let bindOk := wrapValueLets bindLets bindParts.snd.snd.snd
                let defaultOk ← defaultValue resultTy
                let isError := .eqU64 tag (.u64 0)
                .ok
                  (wrapValueLets lets
                    (mkExceptValue
                      (.ite isError (.u64 0) bindTag)
                      (← valueIte isError errorPayload bindError)
                      (← valueIte isError defaultOk bindOk)),
                    bindResult.snd)
            | _, _ => .error "unsupported Except.bind application"
        | (.const ``Except.toOption _, args) =>
            match args.reverse, exceptPayloadType? ctx.env args with
            | exceptValue :: _, some _payloadTy =>
                let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
                let parts ← exceptPartsWithLets exceptResult.fst
                .ok
                  (wrapValueLets parts.fst
                    (mkOptionValue parts.snd.fst parts.snd.snd.snd),
                    exceptResult.snd)
            | _, _ => .error "unsupported Except.toOption application"
        | (.const ``Except.isOk _, args) =>
            match args.reverse, exceptPayloadType? ctx.env args with
            | exceptValue :: _, some _payloadTy =>
                let tagResult ← extractExceptTagExprFrom ctx locals nextLocal exceptValue
                .ok (.scalar (boolExpr (.not (.eqU64 tagResult.fst (.u64 0)))), tagResult.snd)
            | _, _ => .error "unsupported Except.isOk application"
        | (.const ``Option.getD _, args) =>
            match args.reverse with
            | defaultValue :: optionValue :: _ =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                let defaultResult ← extractValueFrom ctx locals optionResult.snd defaultValue
                .ok
                  (wrapValueLets lets
                    (← valueIte (.eqU64 tag (.u64 0)) defaultResult.fst payload),
                    defaultResult.snd)
            | _ => .error "unsupported Option.getD application"
        | (.const ``Option.get! _, args) =>
            match args.reverse, optionConstructorType? ctx.env args with
            | optionValue :: _, some payloadTy =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                .ok
                  (wrapValueLets lets
                    (← valueIte (.eqU64 tag (.u64 0)) (← trapValue payloadTy) payload),
                    optionResult.snd)
            | _, _ => .error "unsupported Option.get! application"
        | (.const ``Option.orElse _, args) =>
            match optionOrElseArgs? ctx.env (.const ``Option.orElse []) args with
            | some (optionValue, fallback) =>
                extractOptionOrElseValueFrom ctx locals nextLocal optionValue fallback
            | none => .error "unsupported Option.orElse application"
        | (.const ``HOrElse.hOrElse _, args) =>
            match optionOrElseArgs? ctx.env (.const ``HOrElse.hOrElse []) args with
            | some (optionValue, fallback) =>
                extractOptionOrElseValueFrom ctx locals nextLocal optionValue fallback
            | none =>
                match exceptOrElseArgs? ctx.env (.const ``HOrElse.hOrElse []) args with
                | some (exceptValue, fallback) =>
                    extractExceptOrElseValueFrom ctx locals nextLocal exceptValue fallback
                | none => .error "unsupported HOrElse.hOrElse application"
        | (.const ``Option.elim _, args) =>
            match args.reverse with
            | someArm :: defaultValue :: optionValue :: _ =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                let defaultResult ← extractValueFrom ctx locals optionResult.snd defaultValue
                let someBody ←
                  match collectLambdas someArm 1 with
                  | some body => .ok body
                  | none => .error "unsupported Option.elim some arm"
                let someResult ←
                  extractValueFrom ctx (.value payload :: locals) defaultResult.snd someBody
                .ok
                  (wrapValueLets lets
                    (← valueIte (.eqU64 tag (.u64 0)) defaultResult.fst someResult.fst),
                    someResult.snd)
            | _ => .error "unsupported Option.elim application"
        | (.const ``Option.map _, args) =>
            match args.reverse, optionMapResultType? ctx.env args with
            | optionValue :: mapFn :: _, some resultTy =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                let mapBody ←
                  match collectLambdas mapFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Option.map function"
                let mapResult ←
                  extractValueFrom ctx (.value payload :: locals) optionResult.snd mapBody
                let nonePayload ← defaultValue resultTy
                .ok
                  (wrapValueLets lets
                    (mkOptionValue tag
                      (← valueIte (.eqU64 tag (.u64 0)) nonePayload mapResult.fst)),
                    mapResult.snd)
            | _, _ => .error "unsupported Option.map application"
        | (.const ``Option.filter _, args) =>
            match args.reverse, optionConstructorType? ctx.env args with
            | optionValue :: predicate :: _, some payloadTy =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                let predicateBody ←
                  match collectLambdas predicate 1 with
                  | some body => .ok body
                  | none => .error "unsupported Option.filter predicate"
                let predicateResult ←
                  extractCondFrom ctx (.value payload :: locals) optionResult.snd predicateBody
                let nonePayload ← defaultValue payloadTy
                let keep :=
                  .and (.not (.eqU64 tag (.u64 0))) predicateResult.fst
                .ok
                  (wrapValueLets lets
                    (mkOptionValue (.ite keep (.u64 1) (.u64 0))
                      (← valueIte keep payload nonePayload)),
                    predicateResult.snd)
            | _, _ => .error "unsupported Option.filter application"
        | (.const ``Option.bind _, args) =>
            match args.reverse, optionMapResultType? ctx.env args with
            | bindFn :: optionValue :: _, some resultTy =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                let bindBody ←
                  match collectLambdas bindFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Option.bind function"
                let bindResult ←
                  extractValueFrom ctx (.value payload :: locals) optionResult.snd bindBody
                let bindParts ← optionPartsWithLets bindResult.fst
                let bindLets := bindParts.fst
                let bindTag := wrapExprLets bindLets bindParts.snd.fst
                let bindPayload := wrapValueLets bindLets bindParts.snd.snd
                let nonePayload ← defaultValue resultTy
                .ok
                  (wrapValueLets lets
                    (mkOptionValue
                      (.ite (.eqU64 tag (.u64 0)) (.u64 0) bindTag)
                      (← valueIte (.eqU64 tag (.u64 0)) nonePayload bindPayload)),
                    bindResult.snd)
            | _, _ => .error "unsupported Option.bind application"
        | (.const ``GetElem?.getElem? _, args) =>
            match args.reverse with
            | index :: array :: _ =>
                match primitiveReceiverType? ctx.env args with
                | some (.array itemTy) =>
                  match arrayElementSlots? itemTy with
                  | some _width =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let arraySlot := indexResult.snd
                    let indexSlot := arraySlot + 1
                    let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                    let tag := boolExpr inBounds
                    let payload ← arrayLoadValue itemTy (.local arraySlot) (.local indexSlot)
                    let defaultPayload ← defaultValue itemTy
                    .ok
                      (.letE arraySlot arrayResult.fst
                        (.letE indexSlot indexResult.fst
                          (mkOptionValue tag (← valueIte inBounds payload defaultPayload))),
                        indexSlot + 1)
                  | none =>
                    .error s!"unsupported GetElem?.getElem? receiver type: {reprStr ((.array itemTy : Ty))}"
                | some .byteArray =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let ptrSlot := indexResult.snd
                    let lenSlot := ptrSlot + 1
                    let indexSlot := ptrSlot + 2
                    let inBounds := .ltU64 (.local indexSlot) (.local lenSlot)
                    let tag := boolExpr inBounds
                    let payload :=
                      .scalar
                        (.byteArrayGet (.local ptrSlot) (.local lenSlot) (.local indexSlot))
                    let defaultPayload ← defaultValue .u8
                    .ok
                      (wrapValueLets parts.fst
                        (.letE ptrSlot parts.snd.fst
                          (.letE lenSlot parts.snd.snd
                            (.letE indexSlot indexResult.fst
                              (mkOptionValue tag (← valueIte inBounds payload defaultPayload))))),
                        indexSlot + 1)
                | some other =>
                    .error s!"unsupported GetElem?.getElem? receiver type: {reprStr other}"
                | none => .error "unsupported GetElem?.getElem? receiver type"
            | _ => .error "unsupported GetElem?.getElem? application"
        | (.const ``Array.findIdx? _, args) =>
            match args, args.reverse with
            | itemTyExpr :: _, array :: predicate :: _ =>
                match typeAtom? ctx.env itemTyExpr with
                | some itemTy =>
                  match arrayElementSlots? itemTy with
                  | some sourceWidth =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let itemStart := arrayResult.snd
                    let predicateBody ←
                      match collectLambdas predicate 1 with
                      | some body => .ok body
                      | none => .error "unsupported Array.findIdx? predicate"
                    let itemValue ← arrayLocalValue itemTy itemStart
                    let predicateResult ←
                      extractExprFrom ctx
                        (.value itemValue :: locals)
                        (itemStart + sourceWidth)
                        predicateBody
                    let tag :=
                      .arrayFindIdxSlots
                        sourceWidth arrayResult.fst itemStart predicateResult.fst false
                    let payload :=
                      .arrayFindIdxSlots
                        sourceWidth arrayResult.fst itemStart predicateResult.fst true
                    .ok (mkOptionValue tag (.scalar payload), predicateResult.snd)
                  | none => .error s!"unsupported Array.findIdx? item type: {reprStr itemTy}"
                | none => .error "unsupported Array.findIdx? item type"
            | _, _ => .error "unsupported Array.findIdx? application"
        | (.const ``Array.find? _, args) =>
            match args, args.reverse with
            | itemTyExpr :: _, array :: predicate :: _ =>
                match typeAtom? ctx.env itemTyExpr with
                | some itemTy =>
                  match arrayElementSlots? itemTy with
                  | some sourceWidth =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let itemStart := arrayResult.snd
                    let predicateBody ←
                      match collectLambdas predicate 1 with
                      | some body => .ok body
                      | none => .error "unsupported Array.find? predicate"
                    let itemValue ← arrayLocalValue itemTy itemStart
                    let predicateResult ←
                      extractExprFrom ctx
                        (.value itemValue :: locals)
                        (itemStart + sourceWidth)
                        predicateBody
                    let tag :=
                      .arrayFindIdxSlots
                        sourceWidth arrayResult.fst itemStart predicateResult.fst false
                    let payload ←
                      arrayFindValue
                        itemTy
                        sourceWidth
                        arrayResult.fst
                        itemStart
                        predicateResult.fst
                    .ok (mkOptionValue tag payload, predicateResult.snd)
                  | none => .error s!"unsupported Array.find? item type: {reprStr itemTy}"
                | none => .error "unsupported Array.find? item type"
            | _, _ => .error "unsupported Array.find? application"
        | (.const ``Array.get!Internal _, args) =>
            match args, args.reverse with
            | itemTy :: _, index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let value ← arrayLoadValue itemTy arrayResult.fst indexResult.fst
                    .ok (value, indexResult.snd)
                | none => .error "unsupported Array.get!Internal item type"
            | _, _ => .error "unsupported Array.get!Internal application"
        | (.const ``GetElem?.getElem! _, args) =>
            match args.reverse with
            | index :: array :: _ =>
                match primitiveReceiverType? ctx.env args with
                | some (.array itemTy) =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let value ← arrayLoadValue itemTy arrayResult.fst indexResult.fst
                    .ok (value, indexResult.snd)
                | some .byteArray =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    .ok
                      (.scalar
                        (wrapExprLets parts.fst
                          (.byteArrayGet parts.snd.fst parts.snd.snd indexResult.fst)),
                        indexResult.snd)
                | some other =>
                    .error s!"unsupported GetElem?.getElem! receiver type: {reprStr other}"
                | none => .error "unsupported GetElem?.getElem! receiver type"
            | _ => .error "unsupported GetElem?.getElem! application"
        | (.const ``GetElem.getElem _, args) =>
            match args.reverse with
            | _proof :: index :: array :: _ =>
                match primitiveReceiverType? ctx.env args with
                | some (.array itemTy) =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let value ← arrayLoadValue itemTy arrayResult.fst indexResult.fst
                    .ok (value, indexResult.snd)
                | some .byteArray =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    .ok
                      (.scalar
                        (wrapExprLets parts.fst
                          (.byteArrayGet parts.snd.fst parts.snd.snd indexResult.fst)),
                        indexResult.snd)
                | some other =>
                    .error s!"unsupported GetElem.getElem receiver type: {reprStr other}"
                | none => .error "unsupported GetElem.getElem receiver type"
            | _ => .error "unsupported GetElem.getElem application"
        | (.const ``Array.back? _, args) =>
            match args, args.reverse with
            | itemTy :: _, array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    match arrayElementSlots? itemTy with
                    | some _width =>
                      let arrayResult ← extractExprFrom ctx locals nextLocal array
                      let arraySlot := arrayResult.snd
                      let hasItem := .not (.eqU64 (.arraySize (.local arraySlot)) (.u64 0))
                      let tag := boolExpr hasItem
                      let index := .u64Bin .sub (.arraySize (.local arraySlot)) (.u64 1)
                      let payload ← arrayLoadValue itemTy (.local arraySlot) index
                      let defaultPayload ← defaultValue itemTy
                      .ok
                        (.letE arraySlot arrayResult.fst
                          (mkOptionValue tag (← valueIte hasItem payload defaultPayload)),
                          arraySlot + 1)
                    | none => .error s!"unsupported Array.back? item type: {reprStr itemTy}"
                | none => .error "unsupported Array.back? item type"
            | _, _ => .error "unsupported Array.back? application"
        | (.const ``Array.back! _, args) =>
            match args, args.reverse with
            | itemTy :: _, array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let index := .u64Bin .sub (.arraySize arrayResult.fst) (.u64 1)
                    let value ← arrayLoadValue itemTy arrayResult.fst index
                    .ok (value, arrayResult.snd)
                | none => .error "unsupported Array.back! item type"
            | _, _ => .error "unsupported Array.back! application"
        | (.const ``Array.back _, args) =>
            match args, args.reverse with
            | itemTy :: _, _proof :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let index := .u64Bin .sub (.arraySize arrayResult.fst) (.u64 1)
                    let value ← arrayLoadValue itemTy arrayResult.fst index
                    .ok (value, arrayResult.snd)
                | none => .error "unsupported Array.back item type"
            | _, _ => .error "unsupported Array.back application"
        | (.const ``Array.getD _, args) =>
            match args, args.reverse with
            | itemTy :: _, defaultValue :: index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    match arrayElementSlots? itemTy with
                    | some _width =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let arraySlot := indexResult.snd
                        let indexSlot := arraySlot + 1
                        let defaultResult ← extractValueFrom ctx locals (indexSlot + 1) defaultValue
                        let loaded ← arrayLoadValue itemTy (.local arraySlot) (.local indexSlot)
                        let selected ←
                          valueIte
                            (.ltU64 (.local indexSlot) (.arraySize (.local arraySlot)))
                            loaded
                            defaultResult.fst
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst selected),
                            defaultResult.snd)
                    | none => .error s!"unsupported Array.getD item type: {reprStr itemTy}"
                | none => .error "unsupported Array.getD item type"
            | _, _ => .error "unsupported Array.getD application"
        | (.const ``ByteArray.extract _, args) =>
            match args with
            | [array, start, stop] =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let startResult ← extractExprFrom ctx locals arrayResult.snd start
                let stopResult ← extractExprFrom ctx locals startResult.snd stop
                let ptrSlot := stopResult.snd
                let lenSlot := ptrSlot + 1
                let startSlot := ptrSlot + 2
                let stopSlot := ptrSlot + 3
                let effectiveStop :=
                  .ite
                    (.ltU64 (.local stopSlot) (.local lenSlot))
                    (.local stopSlot)
                    (.local lenSlot)
                let nonempty :=
                  .and
                    (.ltU64 (.local startSlot) (.local lenSlot))
                    (.ltU64 (.local startSlot) effectiveStop)
                let slicePtr := .u64Bin .add (.local ptrSlot) (.local startSlot)
                let sliceLen :=
                  .ite nonempty (.u64Bin .sub effectiveStop (.local startSlot)) (.u64 0)
                .ok
                  (wrapValueLets parts.fst
                    (.letE ptrSlot parts.snd.fst
                      (.letE lenSlot parts.snd.snd
                        (.letE startSlot startResult.fst
                          (.letE stopSlot stopResult.fst
                            (.byteArray slicePtr sliceLen))))),
                    stopSlot + 1)
            | _ => .error "unsupported ByteArray.extract application"
        | (.const ``ByteArray.push _, args) =>
            match args.reverse with
            | value :: array :: _ =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let valueResult ← extractExprFrom ctx locals arrayResult.snd value
                let valueSlot := valueResult.snd
                let ptrSlot := valueSlot + 1
                let lenSlot := valueSlot + 2
                let sourcePtr := wrapExprLets parts.fst parts.snd.fst
                let sourceLen := wrapExprLets parts.fst parts.snd.snd
                let pushedPtr :=
                  .letE ptrSlot sourcePtr
                    (.letE lenSlot sourceLen
                      (.byteArrayPushPtr
                        (.local ptrSlot)
                        (.local lenSlot)
                        (.local valueSlot)))
                let pushedLen := .u64Bin .add sourceLen (.u64 1)
                .ok
                  (.letE valueSlot valueResult.fst (.byteArray pushedPtr pushedLen),
                    lenSlot + 1)
            | _ => .error "unsupported ByteArray.push application"
        | (.const ``ByteArray.append _, args) =>
            match args with
            | [left, right] =>
                let leftResult ← extractValueFrom ctx locals nextLocal left
                let leftParts ← byteArrayPartsWithLets leftResult.fst
                let rightResult ← extractValueFrom ctx locals leftResult.snd right
                let rightParts ← byteArrayPartsWithLets rightResult.fst
                let leftPtrSlot := rightResult.snd
                let leftLenSlot := leftPtrSlot + 1
                let rightPtrSlot := leftPtrSlot + 2
                let rightLenSlot := leftPtrSlot + 3
                let leftPtr := wrapExprLets leftParts.fst leftParts.snd.fst
                let leftLen := wrapExprLets leftParts.fst leftParts.snd.snd
                let rightPtr := wrapExprLets rightParts.fst rightParts.snd.fst
                let rightLen := wrapExprLets rightParts.fst rightParts.snd.snd
                let appendedPtr :=
                  .letE leftPtrSlot leftPtr
                    (.letE leftLenSlot leftLen
                      (.letE rightPtrSlot rightPtr
                        (.letE rightLenSlot rightLen
                          (.byteArrayAppendPtr
                            (.local leftPtrSlot)
                            (.local leftLenSlot)
                            (.local rightPtrSlot)
                            (.local rightLenSlot)))))
                let appendedLen := .u64Bin .add leftLen rightLen
                .ok (.byteArray appendedPtr appendedLen, rightLenSlot + 1)
            | _ => .error "unsupported ByteArray.append application"
        | (.const ``HAppend.hAppend _, args) =>
            match args.reverse, primitiveResultType? ctx.env args with
            | right :: left :: _, some .byteArray =>
                let leftResult ← extractValueFrom ctx locals nextLocal left
                let leftParts ← byteArrayPartsWithLets leftResult.fst
                let rightResult ← extractValueFrom ctx locals leftResult.snd right
                let rightParts ← byteArrayPartsWithLets rightResult.fst
                let leftPtrSlot := rightResult.snd
                let leftLenSlot := leftPtrSlot + 1
                let rightPtrSlot := leftPtrSlot + 2
                let rightLenSlot := leftPtrSlot + 3
                let leftPtr := wrapExprLets leftParts.fst leftParts.snd.fst
                let leftLen := wrapExprLets leftParts.fst leftParts.snd.snd
                let rightPtr := wrapExprLets rightParts.fst rightParts.snd.fst
                let rightLen := wrapExprLets rightParts.fst rightParts.snd.snd
                let appendedPtr :=
                  .letE leftPtrSlot leftPtr
                    (.letE leftLenSlot leftLen
                      (.letE rightPtrSlot rightPtr
                        (.letE rightLenSlot rightLen
                          (.byteArrayAppendPtr
                            (.local leftPtrSlot)
                            (.local leftLenSlot)
                            (.local rightPtrSlot)
                            (.local rightLenSlot)))))
                let appendedLen := .u64Bin .add leftLen rightLen
                .ok (.byteArray appendedPtr appendedLen, rightLenSlot + 1)
            | _, _ =>
                let scalarResult ← extractExprFrom ctx locals nextLocal expr
                .ok (.scalar scalarResult.fst, scalarResult.snd)
        | (.const ``ByteArray.set! _, args) =>
            match args.reverse with
            | value :: index :: array :: _ =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                let valueResult ← extractExprFrom ctx locals indexResult.snd value
                let indexSlot := valueResult.snd
                let valueSlot := indexSlot + 1
                let ptrSlot := indexSlot + 2
                let lenSlot := indexSlot + 3
                let sourcePtr := wrapExprLets parts.fst parts.snd.fst
                let sourceLen := wrapExprLets parts.fst parts.snd.snd
                let setPtr :=
                  .letE ptrSlot sourcePtr
                    (.letE lenSlot sourceLen
                      (.byteArraySetPtr
                        (.local ptrSlot)
                        (.local lenSlot)
                        (.local indexSlot)
                        (.local valueSlot)))
                .ok
                  (.letE indexSlot indexResult.fst
                    (.letE valueSlot valueResult.fst
                      (.byteArray setPtr sourceLen)),
                    lenSlot + 1)
            | _ => .error "unsupported ByteArray.set! application"
        | (.const ``ByteArray.set _, args) =>
            match args.reverse with
            | _proof :: value :: index :: array :: _ =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                let valueResult ← extractExprFrom ctx locals indexResult.snd value
                let indexSlot := valueResult.snd
                let valueSlot := indexSlot + 1
                let ptrSlot := indexSlot + 2
                let lenSlot := indexSlot + 3
                let sourcePtr := wrapExprLets parts.fst parts.snd.fst
                let sourceLen := wrapExprLets parts.fst parts.snd.snd
                let setPtr :=
                  .letE ptrSlot sourcePtr
                    (.letE lenSlot sourceLen
                      (.byteArraySetPtr
                        (.local ptrSlot)
                        (.local lenSlot)
                        (.local indexSlot)
                        (.local valueSlot)))
                .ok
                  (.letE indexSlot indexResult.fst
                    (.letE valueSlot valueResult.fst
                      (.byteArray setPtr sourceLen)),
                    lenSlot + 1)
            | _ => .error "unsupported ByteArray.set application"
        | (.const ``ByteArray.copySlice _, args) =>
            let copyArgs? :=
              match args.reverse with
              | _exact :: copyLen :: destOff :: dest :: srcOff :: src :: _ =>
                  some (src, srcOff, dest, destOff, copyLen)
              | copyLen :: destOff :: dest :: srcOff :: src :: [] =>
                  some (src, srcOff, dest, destOff, copyLen)
              | _ => none
            match copyArgs? with
            | some (src, srcOff, dest, destOff, copyLen) =>
                let srcResult ← extractValueFrom ctx locals nextLocal src
                let srcParts ← byteArrayPartsWithLets srcResult.fst
                let srcOffResult ← extractExprFrom ctx locals srcResult.snd srcOff
                let destResult ← extractValueFrom ctx locals srcOffResult.snd dest
                let destParts ← byteArrayPartsWithLets destResult.fst
                let destOffResult ← extractExprFrom ctx locals destResult.snd destOff
                let copyLenResult ← extractExprFrom ctx locals destOffResult.snd copyLen
                let srcPtrSlot := copyLenResult.snd
                let srcLenSlot := srcPtrSlot + 1
                let srcOffSlot := srcPtrSlot + 2
                let destPtrSlot := srcPtrSlot + 3
                let destLenSlot := srcPtrSlot + 4
                let destOffSlot := srcPtrSlot + 5
                let copyLenSlot := srcPtrSlot + 6
                let srcPtr := wrapExprLets srcParts.fst srcParts.snd.fst
                let srcLen := wrapExprLets srcParts.fst srcParts.snd.snd
                let destPtr := wrapExprLets destParts.fst destParts.snd.fst
                let destLen := wrapExprLets destParts.fst destParts.snd.snd
                let resultLen :=
                  .letE srcPtrSlot srcPtr
                    (.letE srcLenSlot srcLen
                      (.letE srcOffSlot srcOffResult.fst
                        (.letE destPtrSlot destPtr
                          (.letE destLenSlot destLen
                            (.letE destOffSlot destOffResult.fst
                              (.letE copyLenSlot copyLenResult.fst
                                (byteArrayCopySliceResultLen
                                  (.local srcLenSlot)
                                  (.local srcOffSlot)
                                  (.local destLenSlot)
                                  (.local destOffSlot)
                                  (.local copyLenSlot))))))))
                let resultPtr :=
                  .letE srcPtrSlot srcPtr
                    (.letE srcLenSlot srcLen
                      (.letE srcOffSlot srcOffResult.fst
                        (.letE destPtrSlot destPtr
                          (.letE destLenSlot destLen
                            (.letE destOffSlot destOffResult.fst
                              (.letE copyLenSlot copyLenResult.fst
                                (.byteArrayCopySlicePtr
                                  (.local srcPtrSlot)
                                  (.local srcLenSlot)
                                  (.local srcOffSlot)
                                  (.local destPtrSlot)
                                  (.local destLenSlot)
                                  (.local destOffSlot)
                                  (.local copyLenSlot))))))))
                .ok (.byteArray resultPtr resultLen, copyLenSlot + 1)
            | none => .error "unsupported ByteArray.copySlice application"
        | (.const ``ByteArray.findIdx? _, args) =>
            let findArgs? :=
              match args.reverse with
              | start :: predicate :: array :: _ => some (array, predicate, some start)
              | predicate :: array :: [] => some (array, predicate, none)
              | _ => none
            match findArgs? with
            | some (array, predicate, start?) =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let startResult ←
                  match start? with
                  | some start => extractExprFrom ctx locals arrayResult.snd start
                  | none => .ok (.u64 0, arrayResult.snd)
                let byteSlot := startResult.snd
                let predicateBody ←
                  match collectLambdas predicate 1 with
                  | some body => .ok body
                  | none => .error "unsupported ByteArray.findIdx? predicate"
                let predicateResult ←
                  extractExprFrom ctx
                    (.value (.scalar (.local byteSlot)) :: locals)
                    (byteSlot + 1)
                    predicateBody
                let ptr := wrapExprLets parts.fst parts.snd.fst
                let len := wrapExprLets parts.fst parts.snd.snd
                let tag :=
                  .byteArrayFindIdx ptr len startResult.fst byteSlot predicateResult.fst false
                let payload :=
                  .byteArrayFindIdx ptr len startResult.fst byteSlot predicateResult.fst true
                .ok (mkOptionValue tag (.scalar payload), predicateResult.snd)
            | none => .error "unsupported ByteArray.findIdx? application"
        | (.const ``ByteArray.mk _, args) =>
            match args with
            | [array] =>
                let arrayResult ← extractExprFrom ctx locals nextLocal array
                let arraySlot := arrayResult.snd
                .ok
                  (.letE arraySlot arrayResult.fst
                    (.byteArray
                      (.byteArrayFromArrayPtr (.local arraySlot))
                      (.arraySize (.local arraySlot))),
                    arraySlot + 1)
            | _ => .error "unsupported ByteArray.mk application"
        | (.const ``String.toUTF8 _, args) =>
            match args with
            | [value] =>
                match stringLit? value with
                | some stringValue =>
                    match asciiStringBytes? stringValue with
                    | some bytes => .ok (byteArrayLiteralValue nextLocal bytes)
                    | none => .error "unsupported String.toUTF8 literal: expected ASCII"
                | none => .error "unsupported String.toUTF8 argument: expected string literal"
            | _ => .error "unsupported String.toUTF8 application"
        | (.const ``Bool.casesOn _, args) =>
            match boolMatcherArgs? ctx.env (.const ``Bool.casesOn []) args with
            | some (scrutinee, falseArm, trueArm) =>
                let condResult ← extractCondFrom ctx locals nextLocal scrutinee
                let falseResult ← extractUnitArmValueFrom ctx locals condResult.snd falseArm
                let trueResult ← extractUnitArmValueFrom ctx locals falseResult.snd trueArm
                .ok (← valueIte condResult.fst trueResult.fst falseResult.fst, trueResult.snd)
            | none => .error "unsupported Bool.casesOn application"
        | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
            match typeAtom? ctx.env ty with
            | some resultTy =>
                if supportedLocalType resultTy then
                  let condResult ← extractCondFrom ctx locals nextLocal condExpr
                  let thenResult ← extractValueFrom ctx locals condResult.snd thenExpr
                  let elseResult ← extractValueFrom ctx locals thenResult.snd elseExpr
                  .ok (← valueIte condResult.fst thenResult.fst elseResult.fst, elseResult.snd)
                else
                  let exprResult ← extractExprFrom ctx locals nextLocal expr
                  .ok (.scalar exprResult.fst, exprResult.snd)
            | none =>
                let exprResult ← extractExprFrom ctx locals nextLocal expr
                .ok (.scalar exprResult.fst, exprResult.snd)
        | (.const ``dite _, [ty, condExpr, _, thenArm, elseArm]) =>
            match typeAtom? ctx.env ty with
            | some resultTy =>
                if supportedLocalType resultTy then
                  let condResult ← extractCondFrom ctx locals nextLocal condExpr
                  let thenResult ← extractUnitArmValueFrom ctx locals condResult.snd thenArm
                  let elseResult ← extractUnitArmValueFrom ctx locals thenResult.snd elseArm
                  .ok (← valueIte condResult.fst thenResult.fst elseResult.fst, elseResult.snd)
                else
                  .error "unsupported dependent-if result type"
            | none => .error "unsupported dependent-if result type"
        | (fn, args) =>
            match fn.consumeMData with
            | .const name _ =>
                match structureConstructor? ctx.env name with
                | some (structName, fieldKinds) =>
                    if args.length == fieldKinds.length then
                      let rec loop :
                          List Expr → List (Option Ty) → Nat →
                            Except String (List ExtractedValue × Nat)
                        | [], [], next => .ok ([], next)
                        | arg :: restArgs, some _ :: restKinds, next => do
                            let fieldResult ← extractValueFrom ctx locals next arg
                            let restResult ← loop restArgs restKinds fieldResult.snd
                            .ok (fieldResult.fst :: restResult.fst, restResult.snd)
                        | _arg :: restArgs, none :: restKinds, next =>
                            loop restArgs restKinds next
                        | _, _, _ => .error s!"structure constructor arity mismatch: {name}"
                      let result ← loop args fieldKinds nextLocal
                      .ok (.struct structName result.fst, result.snd)
                    else
                      .error s!"structure constructor arity mismatch: {name}"
                | none =>
                    match recursiveVariantConstructor? ctx.env name with
                    | some (layout, ctorIndex, ctor) =>
                        if args.length == ctor.fields.length then
                          let rec recursiveVariantCtorLoop :
                              List Expr → List (Option Ty) → Nat →
                                Except String (List ExtractedValue × Nat)
                            | [], [], next => .ok ([], next)
                            | arg :: restArgs, some _ :: restKinds, next => do
                                let fieldResult ← extractValueFrom ctx locals next arg
                                let restResult ←
                                  recursiveVariantCtorLoop restArgs restKinds fieldResult.snd
                                .ok (fieldResult.fst :: restResult.fst, restResult.snd)
                            | _arg :: restArgs, none :: restKinds, next =>
                                recursiveVariantCtorLoop restArgs restKinds next
                            | _, _, _ => .error s!"inductive constructor arity mismatch: {name}"
                          let runtimeFields ← recursiveVariantCtorLoop args ctor.fields nextLocal
                          let defaults ← defaultCtorTypedValues layout.ctors
                          let activeFields ← typedFieldsFromKinds ctor.name ctor.fields runtimeFields.fst
                          let ctors ←
                            match replaceAt? ctorIndex activeFields defaults with
                            | some ctors => .ok ctors
                            | none => .error s!"inductive constructor index mismatch: {name}"
                          .ok
                            (.recursiveVariant layout.name (.u64 ctorIndex) ctors,
                              runtimeFields.snd)
                        else
                          .error s!"inductive constructor arity mismatch: {name}"
                    | none =>
                        match variantConstructor? ctx.env name with
                        | some (layout, ctorIndex, ctor) =>
                            if args.length == ctor.fields.length then
                              let rec variantCtorLoop :
                                  List Expr → List (Option Ty) → Nat →
                                    Except String (List ExtractedValue × Nat)
                                | [], [], next => .ok ([], next)
                                | arg :: restArgs, some _ :: restKinds, next => do
                                    let fieldResult ← extractValueFrom ctx locals next arg
                                    let restResult ← variantCtorLoop restArgs restKinds fieldResult.snd
                                    .ok (fieldResult.fst :: restResult.fst, restResult.snd)
                                | _arg :: restArgs, none :: restKinds, next =>
                                    variantCtorLoop restArgs restKinds next
                                | _, _, _ => .error s!"inductive constructor arity mismatch: {name}"
                              let runtimeFields ← variantCtorLoop args ctor.fields nextLocal
                              let defaults ← defaultCtorValues layout.ctors
                              let ctors ←
                                match replaceAt? ctorIndex runtimeFields.fst defaults with
                                | some ctors => .ok ctors
                                | none => .error s!"inductive constructor index mismatch: {name}"
                              .ok (.variant layout.name (.u64 ctorIndex) ctors, runtimeFields.snd)
                            else
                              .error s!"inductive constructor arity mismatch: {name}"
                        | none =>
                            match structureProjection? ctx.env name, args with
                            | some (structName, some index), target :: [] =>
                                let valueResult ← extractValueFrom ctx locals nextLocal target
                                .ok (← structField structName index valueResult.fst, valueResult.snd)
                            | some (_structName, none), _target :: [] =>
                                .ok (.scalar (.u64 0), nextLocal)
                            | _, _ =>
                                extractNonStructureValueFrom ctx locals nextLocal expr fn args
            | _ => extractNonStructureValueFrom ctx locals nextLocal expr fn args

  partial def extractNonStructureValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr fn : Expr)
      (args : List Expr) :
      Except String (ExtractedValue × Nat) := do
    match boolMatcherArgs? ctx.env fn args with
    | some (scrutinee, falseArm, trueArm) =>
        let condResult ← extractCondFrom ctx locals nextLocal scrutinee
        let falseResult ← extractUnitArmValueFrom ctx locals condResult.snd falseArm
        let trueResult ← extractUnitArmValueFrom ctx locals falseResult.snd trueArm
        .ok (← valueIte condResult.fst trueResult.fst falseResult.fst, trueResult.snd)
    | none =>
        match exceptMatcherArgs? ctx.env fn args with
        | some (scrutinee, errorArm, okArm) =>
            extractExceptMatchValueFrom ctx locals nextLocal scrutinee errorArm okArm
        | none =>
            match optionMatcherArgs? ctx.env fn args with
            | some (scrutinee, noneArm, someArm) =>
                extractOptionMatchValueFrom ctx locals nextLocal scrutinee noneArm someArm
            | none =>
                match natMatcherArgs? ctx.env fn args with
                | some (scrutinee, zeroArm, succArm) =>
                    extractNatMatchValueFrom ctx locals nextLocal scrutinee zeroArm succArm
                | none =>
                            match productMatcherArgs? ctx.env fn args with
                            | some (scrutinee, arm) =>
                                extractProductMatchValueFrom ctx locals nextLocal scrutinee arm
                            | none =>
                                match structureMatcherArgs? ctx.env fn args with
                                | some (structName, scrutinee, arm) =>
                                    extractStructureMatchValueFrom ctx locals nextLocal structName scrutinee arm
                                | none =>
                                    match variantMatcherArgs? ctx.env fn args with
                                    | some (layout, scrutinee, arms) =>
                                        extractVariantMatchValueFrom ctx locals nextLocal layout scrutinee arms
                                    | none =>
                                        match fn.consumeMData with
                                        | .const name _ =>
                                            match ← extractInlineCallValueFrom ctx locals nextLocal name args with
                                            | some valueResult => .ok valueResult
                                            | none =>
                                                match ← extractFunctionCallValueFrom ctx locals nextLocal name args with
                                                | some valueResult => .ok valueResult
                                                | none =>
                                                    let exprResult ← extractExprFrom ctx locals nextLocal expr
                                                    .ok (.scalar exprResult.fst, exprResult.snd)
                                        | _ =>
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
    let parts ← optionPartsWithLets scrutineeResult.fst
    let lets := parts.fst
    let tag := parts.snd.fst
    let payload := parts.snd.snd
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
      extractValueFrom ctx (.value payload :: locals) noneResult.snd someBody
    .ok
      (wrapValueLets lets
        (← valueIte (.eqU64 tag (.u64 0)) noneResult.fst someResult.fst),
        someResult.snd)

  partial def extractExceptMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (scrutinee errorArm okArm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
    let parts ← exceptPartsWithLets scrutineeResult.fst
    let lets := parts.fst
    let tag := parts.snd.fst
    let errorPayload := parts.snd.snd.fst
    let okPayload := parts.snd.snd.snd
    let errorBody ←
      match collectLambdas errorArm 1 with
      | some body => .ok body
      | none => .error "unsupported Except.error matcher arm"
    let errorResult ←
      extractValueFrom ctx (.value errorPayload :: locals) scrutineeResult.snd errorBody
    let okBody ←
      match collectLambdas okArm 1 with
      | some body => .ok body
      | none => .error "unsupported Except.ok matcher arm"
    let okResult ←
      extractValueFrom ctx (.value okPayload :: locals) errorResult.snd okBody
    .ok
      (wrapValueLets lets
        (← valueIte (.eqU64 tag (.u64 0)) errorResult.fst okResult.fst),
        okResult.snd)

  partial def extractExceptOrElseValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (exceptValue fallback : Expr) :
      Except String (ExtractedValue × Nat) := do
    let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
    let parts ← exceptPartsWithLets exceptResult.fst
    let lets := parts.fst
    let tag := parts.snd.fst
    let errorPayload := parts.snd.snd.fst
    let okPayload := parts.snd.snd.snd
    let fallbackBody ←
      match collectLambdas fallback 1 with
      | some body => .ok body
      | none => .error "unsupported Except fallback"
    let fallbackResult ←
      extractValueFrom ctx (.value (.scalar (.u64 0)) :: locals) exceptResult.snd fallbackBody
    let fallbackParts ← exceptPartsWithLets fallbackResult.fst
    let fallbackLets := fallbackParts.fst
    let fallbackTag := wrapExprLets fallbackLets fallbackParts.snd.fst
    let fallbackError := wrapValueLets fallbackLets fallbackParts.snd.snd.fst
    let fallbackOk := wrapValueLets fallbackLets fallbackParts.snd.snd.snd
    let isError := .eqU64 tag (.u64 0)
    .ok
      (wrapValueLets lets
        (mkExceptValue
          (.ite isError fallbackTag tag)
          (← valueIte isError fallbackError errorPayload)
          (← valueIte isError fallbackOk okPayload)),
        fallbackResult.snd)

  partial def extractExceptTagExprFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (exceptValue : Expr) :
      Except String (IRExpr × Nat) := do
    let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
    let parts ← exceptPartsWithLets exceptResult.fst
    .ok (wrapExprLets parts.fst parts.snd.fst, exceptResult.snd)

  partial def extractOptionOrElseValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (optionValue fallback : Expr) :
      Except String (ExtractedValue × Nat) := do
    let optionResult ← extractValueFrom ctx locals nextLocal optionValue
    let parts ← optionPartsWithLets optionResult.fst
    let lets := parts.fst
    let tag := parts.snd.fst
    let payload := parts.snd.snd
    let fallbackBody ←
      match collectLambdas fallback 1 with
      | some body => .ok body
      | none => .error "unsupported Option.orElse fallback"
    let fallbackResult ←
      extractValueFrom ctx (.value (.scalar (.u64 0)) :: locals) optionResult.snd fallbackBody
    .ok
      (wrapValueLets lets
        (← valueIte (.eqU64 tag (.u64 0)) fallbackResult.fst (mkOptionValue tag payload)),
        fallbackResult.snd)

  partial def extractOptionPredicateCondFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr : Expr)
      (noneValue : Bool) :
      Except String (IRCond × Nat) := do
    match appFnArgs expr with
    | (.const name _, args) =>
        if name == ``Option.any || name == ``Option.all then
          match args.reverse with
          | optionValue :: predicate :: _ =>
              let optionResult ← extractValueFrom ctx locals nextLocal optionValue
              let parts ← optionPartsWithLets optionResult.fst
              let tag := parts.snd.fst
              let payload := parts.snd.snd
              let predicateBody ←
                match collectLambdas predicate 1 with
                | some body => .ok body
                | none => .error s!"unsupported {name} predicate"
              let predicateResult ←
                extractCondFrom ctx (.value payload :: locals) optionResult.snd predicateBody
              let cond :=
                if noneValue then
                  .or (.eqU64 tag (.u64 0)) predicateResult.fst
                else
                  .and (.not (.eqU64 tag (.u64 0))) predicateResult.fst
              .ok (boolCond (wrapExprLets parts.fst (boolExpr cond)), predicateResult.snd)
          | _ => .error s!"unsupported {name} application"
        else
          .error s!"unsupported option predicate application: {expr}"
    | _ => .error s!"unsupported option predicate application: {expr}"

  partial def extractNatMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (scrutinee zeroArm succArm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let scrutineeResult ← extractExprFrom ctx locals nextLocal scrutinee
    let scrutineeSlot := scrutineeResult.snd
    let predValue :=
      .scalar (.u64Bin .natSub (.local scrutineeSlot) (.u64 1))
    let zeroResult ←
      extractUnitArmValueFrom ctx locals (scrutineeSlot + 1) zeroArm
    let succBody ←
      match collectLambdas succArm 1 with
      | some body => .ok body
      | none => .error "unsupported Nat successor matcher arm"
    let succResult ←
      extractValueFrom ctx (.value predValue :: locals) zeroResult.snd succBody
    .ok
      (.letE scrutineeSlot scrutineeResult.fst
        (← valueIte (.eqU64 (.local scrutineeSlot) (.u64 0)) zeroResult.fst succResult.fst),
        succResult.snd)

  partial def extractProductMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (scrutinee arm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
    let leftValue ← productField 0 scrutineeResult.fst
    let rightValue ← productField 1 scrutineeResult.fst
    let body ←
      match collectLambdas arm 2 with
      | some body => .ok body
      | none => .error "unsupported product matcher arm"
    extractValueFrom ctx (.value rightValue :: .value leftValue :: locals) scrutineeResult.snd body

  partial def extractStructureMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (structName : Name)
      (scrutinee arm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let fieldKinds ←
      match structureFieldKinds? ctx.env structName with
      | some fields => .ok fields
      | none => .error s!"unsupported structure matcher type: {structName}"
    let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
    let rec fieldsFromKinds :
        Nat → List (Option Ty) → Except String (List ExtractedValue)
      | _, [] => .ok []
      | runtimeIndex, some _ :: rest => do
          let field ← structField structName runtimeIndex scrutineeResult.fst
          let restFields ← fieldsFromKinds (runtimeIndex + 1) rest
          .ok (field :: restFields)
      | runtimeIndex, none :: rest => do
          let restFields ← fieldsFromKinds runtimeIndex rest
          .ok (.scalar (.u64 0) :: restFields)
    let fieldValues ← fieldsFromKinds 0 fieldKinds
    let body ←
      match collectLambdas arm fieldKinds.length with
      | some body => .ok body
      | none => .error s!"unsupported structure matcher arm: {structName}"
    let fieldBindings := fieldValues.reverse.map Binding.value
    extractValueFrom ctx (fieldBindings ++ locals) scrutineeResult.snd body

  partial def extractVariantMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (layout : VariantLayout)
      (scrutinee : Expr)
      (arms : List Expr) :
      Except String (ExtractedValue × Nat) := do
    if arms.length != layout.ctors.length then
      .error s!"inductive matcher arity mismatch: {layout.name}"
    else
      let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
      if (recursiveVariantLayout? ctx.env layout.name).isSome then
        match heapVariantPtrWithLets? layout.name scrutineeResult.fst with
        | some parts =>
            let ptrSlot := scrutineeResult.snd
            let ptrExpr := wrapExprLets parts.fst parts.snd
            let ptrLocal : IRExpr := .local ptrSlot
            let tag := .heapLoadSlot ptrLocal 0
            let rec heapExtractArms :
                List VariantCtorLayout → List Expr → Nat → Nat →
                  Except String (List ExtractedValue × Nat)
              | [], [], _, next => .ok ([], next)
              | ctor :: restCtors, arm :: restArms, payloadSlot, next => do
                  let runtimeFields ← heapRuntimeFieldsFromKinds ptrLocal ctor.fields payloadSlot
                  let sourceBindings ←
                    sourceFieldBindingsFromKinds layout.name ctor.fields runtimeFields.fst
                  let armResult ←
                    if ctor.fields.isEmpty then
                      extractUnitArmValueFrom ctx locals next arm
                    else
                      let body ←
                        match collectLambdas arm ctor.fields.length with
                        | some body => .ok body
                        | none => .error s!"unsupported inductive matcher arm: {ctor.name}"
                      extractValueFrom ctx (sourceBindings.reverse ++ locals) next body
                  let restResult ←
                    heapExtractArms restCtors restArms runtimeFields.snd armResult.snd
                  .ok (armResult.fst :: restResult.fst, restResult.snd)
              | _, _, _, _ => .error s!"inductive matcher arity mismatch: {layout.name}"
            let armResults ← heapExtractArms layout.ctors arms 1 (ptrSlot + 1)
            let rec heapCombine : List (Nat × ExtractedValue) → Except String ExtractedValue
              | [] => .error s!"inductive matcher has no arms: {layout.name}"
              | [(_index, value)] => .ok value
              | (index, value) :: rest => do
                  let elseValue ← heapCombine rest
                  valueIte (.eqU64 tag (.u64 index)) value elseValue
            .ok (.letE ptrSlot ptrExpr (← heapCombine (enumerate armResults.fst)),
              armResults.snd)
        | none =>
            let parts ← recursiveVariantPartsWithLets layout.name scrutineeResult.fst
            let lets := parts.fst
            let tag := parts.snd.fst
            let ctorValues := parts.snd.snd
            if ctorValues.length != layout.ctors.length then
              .error s!"inductive matcher value shape mismatch: {layout.name}"
            else
              let rec recursiveExtractArms :
                  List VariantCtorLayout → List (List ExtractedValue) → List Expr → Nat →
                    Except String (List ExtractedValue × Nat)
                | [], [], [], next => .ok ([], next)
                | ctor :: restCtors, fields :: restFields, arm :: restArms, next => do
                    let sourceBindings ← sourceFieldBindingsFromKinds layout.name ctor.fields fields
                    let armResult ←
                      if ctor.fields.isEmpty then
                        extractUnitArmValueFrom ctx locals next arm
                      else
                        let body ←
                          match collectLambdas arm ctor.fields.length with
                          | some body => .ok body
                          | none => .error s!"unsupported inductive matcher arm: {ctor.name}"
                        extractValueFrom ctx (sourceBindings.reverse ++ locals) next body
                    let restResult ←
                      recursiveExtractArms restCtors restFields restArms armResult.snd
                    .ok (armResult.fst :: restResult.fst, restResult.snd)
                | _, _, _, _ => .error s!"inductive matcher arity mismatch: {layout.name}"
              let armResults ←
                recursiveExtractArms layout.ctors ctorValues arms scrutineeResult.snd
              let rec recursiveCombine : List (Nat × ExtractedValue) → Except String ExtractedValue
                | [] => .error s!"inductive matcher has no arms: {layout.name}"
                | [(_index, value)] => .ok value
                | (index, value) :: rest => do
                    let elseValue ← recursiveCombine rest
                    valueIte (.eqU64 tag (.u64 index)) value elseValue
              .ok (wrapValueLets lets (← recursiveCombine (enumerate armResults.fst)),
                armResults.snd)
      else
        let parts ← variantPartsWithLets layout.name scrutineeResult.fst
        let lets := parts.fst
        let tag := parts.snd.fst
        let ctorValues := parts.snd.snd
        if ctorValues.length != layout.ctors.length then
          .error s!"inductive matcher value shape mismatch: {layout.name}"
        else
          let rec variantExtractArms :
              List VariantCtorLayout → List (List ExtractedValue) → List Expr → Nat →
                Except String (List ExtractedValue × Nat)
            | [], [], [], next => .ok ([], next)
            | ctor :: restCtors, fields :: restFields, arm :: restArms, next => do
                let sourceBindings ← sourceFieldBindingsFromKinds layout.name ctor.fields fields
                let armResult ←
                  if ctor.fields.isEmpty then
                    extractUnitArmValueFrom ctx locals next arm
                  else
                    let body ←
                      match collectLambdas arm ctor.fields.length with
                      | some body => .ok body
                      | none => .error s!"unsupported inductive matcher arm: {ctor.name}"
                    extractValueFrom ctx (sourceBindings.reverse ++ locals) next body
                let restResult ← variantExtractArms restCtors restFields restArms armResult.snd
                .ok (armResult.fst :: restResult.fst, restResult.snd)
            | _, _, _, _ => .error s!"inductive matcher arity mismatch: {layout.name}"
          let armResults ← variantExtractArms layout.ctors ctorValues arms scrutineeResult.snd
          let rec variantCombine : List (Nat × ExtractedValue) → Except String ExtractedValue
            | [] => .error s!"inductive matcher has no arms: {layout.name}"
            | [(_index, value)] => .ok value
            | (index, value) :: rest => do
                let elseValue ← variantCombine rest
                valueIte (.eqU64 tag (.u64 index)) value elseValue
          .ok (wrapValueLets lets (← variantCombine (enumerate armResults.fst)), armResults.snd)

  partial def extractInlineCallValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (name : Name)
      (args : List Expr) :
      Except String (Option (ExtractedValue × Nat)) := do
    if name.getRoot != ctx.root then
      return none
    if ctx.inlineStack.contains name then
      return none
    let info ←
      match ctx.env.find? name with
      | some info => .ok info
      | none => .error s!"declaration disappeared during extraction: {name}"
    if containsConstant ``Nat.brecOn info || containsConstant name info then
      return none
    let sig ←
      match supportedInlineFunction? ctx.env info with
      | some sig => .ok sig
      | none => .error s!"unsupported function type or declaration: {name}"
    if args.length != sig.params.length then
      .error s!"inline call arity mismatch: {name}"
    else
      if (functionIndex? ctx name).isSome && strictCallSafe ctx name args then
        return none
      let value ←
        match info.value? with
        | some value => .ok value
        | none => .error s!"declaration has no executable value: {name}"
      let body ←
        match collectLambdas value sig.params.length with
        | some body => .ok body
        | none => .error s!"definition body does not match function arity: {name}"
      let argBindings := args.reverse.map (fun arg => Binding.thunk locals arg)
      let inlineCtx := { ctx with inlineStack := name :: ctx.inlineStack }
      let result ← extractValueFrom inlineCtx argBindings nextLocal body
      .ok (some result)

  partial def extractFunctionCallValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (name : Name)
      (args : List Expr) :
      Except String (Option (ExtractedValue × Nat)) := do
    match functionIndex? ctx name with
    | none => .ok none
    | some index =>
        strictRecursiveCallCheck ctx name args
        let sig ←
          match ctx.env.find? name with
          | some info =>
              match supportedFunction? ctx.env info with
              | some sig => .ok sig
              | none => .error s!"unsupported function type or declaration: {name}"
          | none => .error s!"declaration disappeared during extraction: {name}"
        let argsResult ← extractCallArgsFrom ctx locals nextLocal sig.params args
        let slotCount := abiSlots sig.result
        let slotStart := argsResult.nextLocal
        let slots := (List.range slotCount).map (fun offset => slotStart + offset)
        let value := extractedValueForParam slotStart sig.result
        .ok
          (some
            (wrapValueLets argsResult.lets (.letCall slots index argsResult.args value),
              slotStart + slotCount))

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
          match typeAtom? ctx.env type with
          | some ty =>
              if supportedLocalType ty then
                extractExprFrom ctx (.thunk locals value :: locals) nextLocal body
              else
                .error s!"unsupported let-bound type: {type}"
          | none => .error s!"unsupported let-bound type: {type}"
    | .proj ``Prod index body =>
        let valueResult ← extractValueFrom ctx locals nextLocal body
        .ok (← scalarValue (← productField index valueResult.fst), valueResult.snd)
    | .proj typeName index body =>
        match structureFieldKinds? ctx.env typeName with
        | some kinds =>
            match runtimeFieldIndexFromKinds index kinds with
            | some (some runtimeIndex) =>
                let valueResult ← extractValueFrom ctx locals nextLocal body
                .ok (← scalarValue (← structField typeName runtimeIndex valueResult.fst),
                  valueResult.snd)
            | some none => .ok (.u64 0, nextLocal)
            | none => .error s!"unsupported structure projection index: {typeName}.{index}"
        | none => .error s!"unsupported projection: {typeName}"
    | .const ``Unit.unit _ => .ok (.u64 0, nextLocal)
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
            | (.const ``Option.getD _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Option.get! _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Option.elim _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Option.isSome _, args) =>
                match args.reverse with
                | optionValue :: _ =>
                    let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                    let parts ← optionPartsWithLets optionResult.fst
                    let tag := wrapExprLets parts.fst parts.snd.fst
                    .ok (boolExpr (.not (.eqU64 tag (.u64 0))), optionResult.snd)
                | _ => .error "unsupported Option.isSome application"
            | (.const ``Option.isNone _, args) =>
                match args.reverse with
                | optionValue :: _ =>
                    let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                    let parts ← optionPartsWithLets optionResult.fst
                    let tag := wrapExprLets parts.fst parts.snd.fst
                    .ok (boolExpr (.eqU64 tag (.u64 0)), optionResult.snd)
                | _ => .error "unsupported Option.isNone application"
            | (.const ``Option.any _, _) =>
                let condResult ← extractOptionPredicateCondFrom ctx locals nextLocal expr false
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Option.all _, _) =>
                let condResult ← extractOptionPredicateCondFrom ctx locals nextLocal expr true
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``id _, args) =>
                match args.reverse with
                | value :: _ =>
                    let valueResult ← extractValueFrom ctx locals nextLocal value
                    .ok (← scalarValue valueResult.fst, valueResult.snd)
                | _ => .error "unsupported id application"
            | (.const ``Nat.blt _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Nat.ble _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Nat.beq _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Except.isOk _, args) =>
                match args.reverse, exceptPayloadType? ctx.env args with
                | exceptValue :: _, some _payloadTy =>
                    let tagResult ← extractExceptTagExprFrom ctx locals nextLocal exceptValue
                    .ok (boolExpr (.not (.eqU64 tagResult.fst (.u64 0))), tagResult.snd)
                | _, _ => .error "unsupported Except.isOk application"
            | (.const ``Decidable.decide _, [prop, _inst]) =>
                let condResult ← extractCondFrom ctx locals nextLocal prop
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Id.run _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Pure.pure _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Bind.bind _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
                if typeAtom? ctx.env ty |>.isSome then
                  let condResult ← extractCondFrom ctx locals nextLocal condExpr
                  let thenResult ← extractExprFrom ctx locals condResult.snd thenExpr
                  let elseResult ← extractExprFrom ctx locals thenResult.snd elseExpr
                  .ok (.ite condResult.fst thenResult.fst elseResult.fst, elseResult.snd)
                else
                  .error "unsupported if-result type"
            | (.const ``dite _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Bool.or _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Bool.and _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Bool.not _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Bool.xor _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``List.toArray _, args) =>
                match args with
                | [_itemTy, listExpr] =>
                    match listLiteralItems? ctx.env listExpr with
                    | some (itemTy, items) =>
                      match arrayElementSlots? itemTy with
                      | some width =>
                        let rec build
                            (index next : Nat)
                            (arrayExpr : IRExpr)
                            (remaining : List Expr) :
                            Except String (IRExpr × Nat) := do
                          match remaining with
                          | [] => .ok (arrayExpr, next)
                          | item :: rest =>
                              let itemResult ← extractValueFrom ctx locals next item
                              let itemSlots ←
                                materializeArrayElementSlots itemTy itemResult.fst itemResult.snd
                              let arraySlot := itemSlots.nextLocal
                              build (index + 1) (arraySlot + 1)
                                (.letE arraySlot arrayExpr
                                  (wrapExprLets itemSlots.lets
                                    (.arraySetSlots
                                      width
                                      (.local arraySlot)
                                      (.u64 index)
                                      itemSlots.slots)))
                                rest
                        build 0 nextLocal (.arrayAllocSlots width (.u64 items.length)) items
                      | none => .error s!"unsupported List.toArray item type: {reprStr itemTy}"
                    | none => .error "unsupported List.toArray argument"
                | _ => .error "unsupported List.toArray application"
            | (.const ``Array.replicate _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: cells :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.replicate" itemTy
                        let cellsResult ← extractExprFrom ctx locals nextLocal cells
                        let valueResult ← extractValueFrom ctx locals cellsResult.snd value
                        let slots ← flattenArrayElementValue itemTy valueResult.fst
                        .ok (.arrayReplicateSlots width cellsResult.fst slots, valueResult.snd)
                    | none => .error "unsupported Array.replicate item type"
                | _, _ => .error "unsupported Array.replicate application"
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
                match args, args.reverse with
                | itemTy :: _, value :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.push" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let valueResult ← extractValueFrom ctx locals arrayResult.snd value
                        let slots ←
                          materializeArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let arraySlot := slots.nextLocal
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (wrapExprLets slots.lets
                              (.arrayPushSlots width (.local arraySlot) slots.slots)),
                            arraySlot + 1)
                    | none => .error "unsupported Array.push item type"
                | _, _ => .error "unsupported Array.push application"
            | (.const ``Array.pop _, args) =>
                match args, args.reverse with
                | itemTy :: _, array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.pop" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        .ok (.arrayPopSlots width arrayResult.fst, arrayResult.snd)
                    | none => .error "unsupported Array.pop item type"
                | _, _ => .error "unsupported Array.pop application"
            | (.const ``Array.eraseIdxIfInBounds _, args) =>
                match args, args.reverse with
                | itemTy :: _, index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.eraseIdxIfInBounds" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok (.arrayEraseIfInBoundsSlots width arrayResult.fst indexResult.fst,
                          indexResult.snd)
                    | none => .error "unsupported Array.eraseIdxIfInBounds item type"
                | _, _ => .error "unsupported Array.eraseIdxIfInBounds application"
            | (.const ``Array.eraseIdx _, args) =>
                match args, args.reverse with
                | itemTy :: _, _proof :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.eraseIdx" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok (.arrayEraseIfInBoundsSlots width arrayResult.fst indexResult.fst,
                          indexResult.snd)
                    | none => .error "unsupported Array.eraseIdx item type"
                | _, _ => .error "unsupported Array.eraseIdx application"
            | (.const ``Array.swapIfInBounds _, args) =>
                match args, args.reverse with
                | itemTy :: _, right :: left :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.swapIfInBounds" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let leftResult ← extractExprFrom ctx locals arrayResult.snd left
                        let rightResult ← extractExprFrom ctx locals leftResult.snd right
                        .ok
                          (.arraySwapIfInBoundsSlots
                            width
                            arrayResult.fst
                            leftResult.fst
                            rightResult.fst,
                            rightResult.snd)
                    | none => .error "unsupported Array.swapIfInBounds item type"
                | _, _ => .error "unsupported Array.swapIfInBounds application"
            | (.const ``Array.swap _, args) =>
                match args, args.reverse with
                | itemTy :: _, _rightProof :: _leftProof :: right :: left :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.swap" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let leftResult ← extractExprFrom ctx locals arrayResult.snd left
                        let rightResult ← extractExprFrom ctx locals leftResult.snd right
                        .ok
                          (.arraySwapIfInBoundsSlots
                            width
                            arrayResult.fst
                            leftResult.fst
                            rightResult.fst,
                            rightResult.snd)
                    | none => .error "unsupported Array.swap item type"
                | _, _ => .error "unsupported Array.swap application"
            | (.const ``Array.reverse _, args) =>
                match args, args.reverse with
                | itemTy :: _, array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.reverse" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        .ok (.arrayReverseSlots width arrayResult.fst, arrayResult.snd)
                    | none => .error "unsupported Array.reverse item type"
                | _, _ => .error "unsupported Array.reverse application"
            | (.const ``Array.insertIdx _, args) =>
                match args, args.reverse with
                | itemTy :: _, _proof :: value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.insertIdx" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let valueResult ← extractValueFrom ctx locals indexResult.snd value
                        let slots ←
                          materializeArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let arraySlot := slots.nextLocal
                        let indexSlot := arraySlot + 1
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (wrapExprLets slots.lets
                                (.arrayInsertIfInBoundsSlots
                                  width
                                  (.local arraySlot)
                                  (.local indexSlot)
                                  slots.slots))),
                            indexSlot + 1)
                    | none => .error "unsupported Array.insertIdx item type"
                | _, _ => .error "unsupported Array.insertIdx application"
            | (.const ``Array.insertIdx! _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.insertIdx!" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let arraySlot := indexResult.snd
                        let indexSlot := arraySlot + 1
                        let valueResult ← extractValueFrom ctx locals (indexSlot + 1) value
                        let slots ←
                          materializeArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let inserted :=
                          wrapExprLets slots.lets
                            (.arrayInsertIfInBoundsSlots
                              width
                              (.local arraySlot)
                              (.local indexSlot)
                              slots.slots)
                        let inBounds := .leU64 (.local indexSlot) (.arraySize (.local arraySlot))
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (.ite inBounds inserted .trap)),
                            slots.nextLocal)
                    | none => .error "unsupported Array.insertIdx! item type"
                | _, _ => .error "unsupported Array.insertIdx! application"
            | (.const ``Array.append _, args) =>
                match args, args.reverse with
                | itemTy :: _, right :: left :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.append" itemTy
                        let leftResult ← extractExprFrom ctx locals nextLocal left
                        let rightResult ← extractExprFrom ctx locals leftResult.snd right
                        .ok (.arrayAppendSlots width leftResult.fst rightResult.fst, rightResult.snd)
                    | none => .error "unsupported Array.append item type"
                | _, _ => .error "unsupported Array.append application"
            | (.const ``Array.insertIdxIfInBounds _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.insertIdxIfInBounds" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let valueResult ← extractValueFrom ctx locals indexResult.snd value
                        let slots ← flattenArrayElementValue itemTy valueResult.fst
                        .ok
                          (.arrayInsertIfInBoundsSlots
                            width
                            arrayResult.fst
                            indexResult.fst
                            slots,
                            valueResult.snd)
                    | none => .error "unsupported Array.insertIdxIfInBounds item type"
                | _, _ => .error "unsupported Array.insertIdxIfInBounds application"
            | (.const ``HAppend.hAppend _, args) =>
                match args.reverse, primitiveResultType? ctx.env args with
                | right :: left :: _, some (.array itemTy) =>
                    let width ← arrayElementWidth "HAppend.hAppend" itemTy
                    let leftResult ← extractExprFrom ctx locals nextLocal left
                    let rightResult ← extractExprFrom ctx locals leftResult.snd right
                    .ok (.arrayAppendSlots width leftResult.fst rightResult.fst, rightResult.snd)
                | _, _ => .error "unsupported HAppend.hAppend application"
            | (.const ``Array.modify _, args) =>
                match args, args.reverse with
                | itemTy :: _, modifyFn :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.modify" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let arraySlot := indexResult.snd
                        let indexSlot := arraySlot + 1
                        let oldValue ← arrayLoadValue itemTy (.local arraySlot) (.local indexSlot)
                        let modifyBody ←
                          match collectLambdas modifyFn 1 with
                          | some body => .ok body
                          | none => .error "unsupported Array.modify function"
                        let modifiedResult ←
                          extractValueFrom ctx (.value oldValue :: locals) (indexSlot + 1) modifyBody
                        let slots ← flattenArrayElementValue itemTy modifiedResult.fst
                        let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                        let modifiedArray :=
                          .arraySetSlots width (.local arraySlot) (.local indexSlot) slots
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (.ite inBounds modifiedArray (.local arraySlot))),
                            modifiedResult.snd)
                    | none => .error "unsupported Array.modify item type"
                | _, _ => .error "unsupported Array.modify application"
            | (.const ``Array.extract _, args) =>
                match args, args.reverse with
                | itemTy :: _, stop :: start :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.extract" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let startResult ← extractExprFrom ctx locals arrayResult.snd start
                        let stopResult ← extractExprFrom ctx locals startResult.snd stop
                        .ok (.arrayExtractSlots width arrayResult.fst startResult.fst stopResult.fst,
                          stopResult.snd)
                    | none => .error "unsupported Array.extract item type"
                | _, _ => .error "unsupported Array.extract application"
            | (.const ``Array.map _, args) =>
                match args, args.reverse with
                | sourceTy :: resultTy :: _, array :: mapFn :: _ =>
                    match typeAtom? ctx.env sourceTy, typeAtom? ctx.env resultTy with
                    | some source, some result =>
                      match arrayElementSlots? source, arrayElementSlots? result with
                      | some sourceWidth, some resultWidth =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let itemStart := arrayResult.snd
                        let mapBody ←
                          match collectLambdas mapFn 1 with
                          | some body => .ok body
                          | none => .error "unsupported Array.map function"
                        let itemValue ← arrayLocalValue source itemStart
                        let bodyResult ←
                          extractValueFrom ctx (.value itemValue :: locals)
                            (itemStart + sourceWidth) mapBody
                        let bodySlots ← flattenArrayElementValue result bodyResult.fst
                        .ok
                          (.arrayMapSlots
                            sourceWidth
                            resultWidth
                            arrayResult.fst
                            itemStart
                            bodySlots,
                            bodyResult.snd)
                      | _, _ =>
                        .error s!"unsupported Array.map item types: {reprStr source}, {reprStr result}"
                    | _, _ => .error "unsupported Array.map item types"
                | _, _ => .error "unsupported Array.map application"
            | (.const ``Array.any _, args) =>
                match args with
                | itemTyExpr :: array :: predicate :: rest =>
                    match typeAtom? ctx.env itemTyExpr with
                    | some itemTy =>
                      match arrayElementSlots? itemTy with
                      | some sourceWidth =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let startStop ←
                          match rest with
                          | [] => .ok ((.u64 0, .arraySize arrayResult.fst), arrayResult.snd)
                          | [start] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              .ok ((startResult.fst, .arraySize arrayResult.fst), startResult.snd)
                          | [start, stop] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              let stopResult ← extractExprFrom ctx locals startResult.snd stop
                              .ok ((startResult.fst, stopResult.fst), stopResult.snd)
                          | _ => .error "unsupported Array.any application"
                        let itemStart := startStop.snd
                        let predicateBody ←
                          match collectLambdas predicate 1 with
                          | some body => .ok body
                          | none => .error "unsupported Array.any predicate"
                        let itemValue ← arrayLocalValue itemTy itemStart
                        let predicateResult ←
                          extractExprFrom ctx
                            (.value itemValue :: locals)
                            (itemStart + sourceWidth)
                            predicateBody
                        .ok
                          (.arrayAnySlots
                            sourceWidth
                            arrayResult.fst
                            startStop.fst.fst
                            startStop.fst.snd
                            itemStart
                            predicateResult.fst
                            false,
                            predicateResult.snd)
                      | none => .error s!"unsupported Array.any item type: {reprStr itemTy}"
                    | none => .error "unsupported Array.any item type"
                | _ => .error "unsupported Array.any application"
            | (.const ``Array.all _, args) =>
                match args with
                | itemTyExpr :: array :: predicate :: rest =>
                    match typeAtom? ctx.env itemTyExpr with
                    | some itemTy =>
                      match arrayElementSlots? itemTy with
                      | some sourceWidth =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let startStop ←
                          match rest with
                          | [] => .ok ((.u64 0, .arraySize arrayResult.fst), arrayResult.snd)
                          | [start] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              .ok ((startResult.fst, .arraySize arrayResult.fst), startResult.snd)
                          | [start, stop] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              let stopResult ← extractExprFrom ctx locals startResult.snd stop
                              .ok ((startResult.fst, stopResult.fst), stopResult.snd)
                          | _ => .error "unsupported Array.all application"
                        let itemStart := startStop.snd
                        let predicateBody ←
                          match collectLambdas predicate 1 with
                          | some body => .ok body
                          | none => .error "unsupported Array.all predicate"
                        let itemValue ← arrayLocalValue itemTy itemStart
                        let predicateResult ←
                          extractExprFrom ctx
                            (.value itemValue :: locals)
                            (itemStart + sourceWidth)
                            predicateBody
                        .ok
                          (.arrayAnySlots
                            sourceWidth
                            arrayResult.fst
                            startStop.fst.fst
                            startStop.fst.snd
                            itemStart
                            predicateResult.fst
                            true,
                            predicateResult.snd)
                      | none => .error s!"unsupported Array.all item type: {reprStr itemTy}"
                    | none => .error "unsupported Array.all item type"
                | _ => .error "unsupported Array.all application"
            | (.const ``Array.filter _, args) =>
                match args with
                | itemTyExpr :: predicate :: array :: rest =>
                    match typeAtom? ctx.env itemTyExpr with
                    | some itemTy =>
                      match arrayElementSlots? itemTy with
                      | some sourceWidth =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let startStop ←
                          match rest with
                          | [] => .ok ((.u64 0, .arraySize arrayResult.fst), arrayResult.snd)
                          | [start] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              .ok ((startResult.fst, .arraySize arrayResult.fst), startResult.snd)
                          | [start, stop] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              let stopResult ← extractExprFrom ctx locals startResult.snd stop
                              .ok ((startResult.fst, stopResult.fst), stopResult.snd)
                          | _ => .error "unsupported Array.filter application"
                        let itemStart := startStop.snd
                        let predicateBody ←
                          match collectLambdas predicate 1 with
                          | some body => .ok body
                          | none => .error "unsupported Array.filter predicate"
                        let itemValue ← arrayLocalValue itemTy itemStart
                        let predicateResult ←
                          extractExprFrom ctx
                            (.value itemValue :: locals)
                            (itemStart + sourceWidth)
                            predicateBody
                        .ok
                          (.arrayFilterSlots
                            sourceWidth
                            arrayResult.fst
                            startStop.fst.fst
                            startStop.fst.snd
                            itemStart
                            predicateResult.fst,
                            predicateResult.snd)
                      | none => .error s!"unsupported Array.filter item type: {reprStr itemTy}"
                    | none => .error "unsupported Array.filter item type"
                | _ => .error "unsupported Array.filter application"
            | (.const ``Array.foldl _, args) =>
                match args with
                | sourceTyExpr :: resultTyExpr :: foldFn :: init :: array :: rest =>
                    match typeAtom? ctx.env sourceTyExpr, typeAtom? ctx.env resultTyExpr with
                    | some sourceTy, some resultTy =>
                      match arrayElementSlots? sourceTy with
                      | some sourceWidth =>
                        if supportedOneSlotExprType resultTy then
                          let arrayResult ← extractExprFrom ctx locals nextLocal array
                          let initResult ← extractExprFrom ctx locals arrayResult.snd init
                          let startStop ←
                            match rest with
                            | [] => .ok ((.u64 0, .arraySize arrayResult.fst), initResult.snd)
                            | [start] =>
                                let startResult ← extractExprFrom ctx locals initResult.snd start
                                .ok ((startResult.fst, .arraySize arrayResult.fst), startResult.snd)
                            | [start, stop] =>
                                let startResult ← extractExprFrom ctx locals initResult.snd start
                                let stopResult ← extractExprFrom ctx locals startResult.snd stop
                                .ok ((startResult.fst, stopResult.fst), stopResult.snd)
                            | _ => .error "unsupported Array.foldl application"
                          let accSlot := startStop.snd
                          let itemStart := accSlot + 1
                          let foldBody ←
                            match collectLambdas foldFn 2 with
                            | some body => .ok body
                            | none => .error "unsupported Array.foldl function"
                          let itemValue ← arrayLocalValue sourceTy itemStart
                          let bodyResult ←
                            extractExprFrom ctx
                              (.value itemValue :: .value (.scalar (.local accSlot)) :: locals)
                              (itemStart + sourceWidth)
                              foldBody
                          .ok
                            (.arrayFoldSlots
                              sourceWidth
                              arrayResult.fst
                              startStop.fst.fst
                              startStop.fst.snd
                              initResult.fst
                              accSlot
                              itemStart
                              bodyResult.fst,
                              bodyResult.snd)
                        else
                          .error s!"unsupported Array.foldl result type: {reprStr resultTy}"
                      | none => .error s!"unsupported Array.foldl item type: {reprStr sourceTy}"
                    | _, _ => .error "unsupported Array.foldl item types"
                | _ => .error "unsupported Array.foldl application"
            | (.const ``Array.empty _, args) =>
                match args with
                | [itemTy] =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.empty" itemTy
                        .ok (.arrayAllocSlots width (.u64 0), nextLocal)
                    | none => .error "unsupported Array.empty item type"
                | _ => .error "unsupported Array.empty application"
            | (.const ``Array.mkEmpty _, args) =>
                match args with
                | [itemTy, _capacity] =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.mkEmpty" itemTy
                        .ok (.arrayAllocSlots width (.u64 0), nextLocal)
                    | none => .error "unsupported Array.mkEmpty item type"
                | _ => .error "unsupported Array.mkEmpty application"
            | (.const ``Array.emptyWithCapacity _, args) =>
                match args with
                | [itemTy, _capacity] =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.emptyWithCapacity" itemTy
                        .ok (.arrayAllocSlots width (.u64 0), nextLocal)
                    | none => .error "unsupported Array.emptyWithCapacity item type"
                | _ => .error "unsupported Array.emptyWithCapacity application"
            | (.const ``Array.singleton _, args) =>
                match args with
                | [itemTy, value] =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.singleton" itemTy
                        let valueResult ← extractValueFrom ctx locals nextLocal value
                        let slots ←
                          materializeArrayElementSlots itemTy valueResult.fst valueResult.snd
                        .ok
                          (wrapExprLets slots.lets
                            (.arraySetSlots
                              width
                              (.arrayAllocSlots width (.u64 1))
                              (.u64 0)
                              slots.slots),
                            slots.nextLocal)
                    | none => .error "unsupported Array.singleton item type"
                | _ => .error "unsupported Array.singleton application"
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
                    match primitiveReceiverType? ctx.env args with
                    | some .byteArray =>
                        let arrayResult ← extractValueFrom ctx locals nextLocal array
                        let parts ← byteArrayPartsWithLets arrayResult.fst
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok
                          (wrapExprLets parts.fst
                            (.byteArrayGet parts.snd.fst parts.snd.snd indexResult.fst),
                            indexResult.snd)
                    | _ =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok (.arrayGet arrayResult.fst indexResult.fst, indexResult.snd)
                | _ => .error "unsupported GetElem?.getElem! application"
            | (.const ``GetElem.getElem _, args) =>
                match args.reverse with
                | _proof :: index :: array :: _ =>
                    match primitiveReceiverType? ctx.env args with
                    | some .byteArray =>
                        let arrayResult ← extractValueFrom ctx locals nextLocal array
                        let parts ← byteArrayPartsWithLets arrayResult.fst
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok
                          (wrapExprLets parts.fst
                            (.byteArrayGet parts.snd.fst parts.snd.snd indexResult.fst),
                            indexResult.snd)
                    | _ =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok (.arrayGet arrayResult.fst indexResult.fst, indexResult.snd)
                | _ => .error "unsupported GetElem.getElem application"
            | (.const ``Array.back! _, args) =>
                match args.reverse with
                | array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let slot := arrayResult.snd
                    let value :=
                      .arrayGet (.local slot) (.u64Bin .sub (.arraySize (.local slot)) (.u64 1))
                    .ok (.letE slot arrayResult.fst value, slot + 1)
                | _ => .error "unsupported Array.back! application"
            | (.const ``Array.back _, args) =>
                match args.reverse with
                | _proof :: array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let slot := arrayResult.snd
                    let value :=
                      .arrayGet (.local slot) (.u64Bin .sub (.arraySize (.local slot)) (.u64 1))
                    .ok (.letE slot arrayResult.fst value, slot + 1)
                | _ => .error "unsupported Array.back application"
            | (.const ``Array.getD _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                let scalar ← scalarValue valueResult.fst
                .ok (scalar, valueResult.snd)
            | (.const ``Array.set _, args) =>
                match args, args.reverse with
                | itemTy :: _, _proof :: value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                      match arrayElementSlots? itemTy with
                      | some width =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let valueResult ← extractValueFrom ctx locals indexResult.snd value
                        let slots ←
                          materializeArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let arraySlot := slots.nextLocal
                        let indexSlot := arraySlot + 1
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (wrapExprLets slots.lets
                                (.arraySetSlots
                                  width
                                  (.local arraySlot)
                                  (.local indexSlot)
                                  slots.slots))),
                            indexSlot + 1)
                      | none => .error s!"unsupported Array.set item type: {reprStr itemTy}"
                    | none => .error "unsupported Array.set item type"
                | _, _ => .error "unsupported Array.set application"
            | (.const ``Array.setIfInBounds _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                      match arrayElementSlots? itemTy with
                      | some width =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let arraySlot := indexResult.snd
                        let indexSlot := arraySlot + 1
                        let valueResult ← extractValueFrom ctx locals (indexSlot + 1) value
                        let slots ← flattenArrayElementValue itemTy valueResult.fst
                        let updated :=
                          .arraySetSlots width (.local arraySlot) (.local indexSlot) slots
                        let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (.ite inBounds updated (.local arraySlot))),
                            valueResult.snd)
                      | none => .error s!"unsupported Array.setIfInBounds item type: {reprStr itemTy}"
                    | none => .error "unsupported Array.setIfInBounds item type"
                | _, _ => .error "unsupported Array.setIfInBounds application"
            | (.const ``Array.set! _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.set!" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let valueResult ← extractValueFrom ctx locals indexResult.snd value
                        let slots ←
                          materializeArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let arraySlot := slots.nextLocal
                        let indexSlot := arraySlot + 1
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (wrapExprLets slots.lets
                                (.arraySetSlots
                                  width
                                  (.local arraySlot)
                                  (.local indexSlot)
                                  slots.slots))),
                            indexSlot + 1)
                    | none => .error "unsupported Array.set! item type"
                | _, _ => .error "unsupported Array.set! application"
            | (.const ``Array.eraseIdx! _, args) =>
                match args, args.reverse with
                | itemTy :: _, index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.eraseIdx!" itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let arraySlot := indexResult.snd
                        let indexSlot := arraySlot + 1
                        let erased :=
                          .arrayEraseIfInBoundsSlots width (.local arraySlot) (.local indexSlot)
                        let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (.ite inBounds erased .trap)),
                            indexSlot + 1)
                    | none => .error "unsupported Array.eraseIdx! item type"
                | _, _ => .error "unsupported Array.eraseIdx! application"
            | (.const ``ByteArray.foldl _, args) =>
                match args with
                | resultTyExpr :: foldFn :: init :: array :: rest =>
                    match typeAtom? ctx.env resultTyExpr with
                    | some resultTy =>
                        if supportedOneSlotExprType resultTy then
                          let arrayResult ← extractValueFrom ctx locals nextLocal array
                          let parts ← byteArrayPartsWithLets arrayResult.fst
                          let ptr := wrapExprLets parts.fst parts.snd.fst
                          let len := wrapExprLets parts.fst parts.snd.snd
                          let initResult ← extractExprFrom ctx locals arrayResult.snd init
                          let startStop ←
                            match rest with
                            | [] => .ok ((.u64 0, len), initResult.snd)
                            | [start] =>
                                let startResult ← extractExprFrom ctx locals initResult.snd start
                                .ok ((startResult.fst, len), startResult.snd)
                            | [start, stop] =>
                                let startResult ← extractExprFrom ctx locals initResult.snd start
                                let stopResult ← extractExprFrom ctx locals startResult.snd stop
                                .ok ((startResult.fst, stopResult.fst), stopResult.snd)
                            | _ => .error "unsupported ByteArray.foldl application"
                          let accSlot := startStop.snd
                          let byteSlot := accSlot + 1
                          let body ←
                            match collectLambdas foldFn 2 with
                            | some body => .ok body
                            | none => .error "unsupported ByteArray.foldl function"
                          let bodyResult ←
                            extractExprFrom ctx
                              (.value (.scalar (.local byteSlot)) ::
                                .value (.scalar (.local accSlot)) :: locals)
                              (byteSlot + 1)
                              body
                          .ok
                            (.byteArrayFold
                              ptr
                              len
                              startStop.fst.fst
                              startStop.fst.snd
                              initResult.fst
                              accSlot
                              byteSlot
                              bodyResult.fst,
                              bodyResult.snd)
                        else
                          .error s!"unsupported ByteArray.foldl result type: {reprStr resultTy}"
                    | none => .error "unsupported ByteArray.foldl result type"
                | _ => .error "unsupported ByteArray.foldl application"
            | (.const ``ByteArray.size _, args) =>
                match args with
                | [array] =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    .ok (wrapExprLets parts.fst parts.snd.snd, arrayResult.snd)
                | _ => .error "unsupported ByteArray.size application"
            | (.const ``ByteArray.isEmpty _, args) =>
                match args with
                | [array] =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let len := wrapExprLets parts.fst parts.snd.snd
                    .ok (boolExpr (.eqU64 len (.u64 0)), arrayResult.snd)
                | _ => .error "unsupported ByteArray.isEmpty application"
            | (.const ``ByteArray.toUInt64LE! _, args) =>
                match args with
                | [array] =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let ptrSlot := arrayResult.snd
                    let lenSlot := ptrSlot + 1
                    let ptr := wrapExprLets parts.fst parts.snd.fst
                    let len := wrapExprLets parts.fst parts.snd.snd
                    .ok
                      (.letE ptrSlot ptr
                        (.letE lenSlot len
                          (byteArrayLoadUInt64Checked
                            (.local ptrSlot)
                            (.local lenSlot)
                            [(0, 0), (1, 8), (2, 16), (3, 24),
                              (4, 32), (5, 40), (6, 48), (7, 56)])),
                        lenSlot + 1)
                | _ => .error "unsupported ByteArray.toUInt64LE! application"
            | (.const ``ByteArray.toUInt64BE! _, args) =>
                match args with
                | [array] =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let ptrSlot := arrayResult.snd
                    let lenSlot := ptrSlot + 1
                    let ptr := wrapExprLets parts.fst parts.snd.fst
                    let len := wrapExprLets parts.fst parts.snd.snd
                    .ok
                      (.letE ptrSlot ptr
                        (.letE lenSlot len
                          (byteArrayLoadUInt64Checked
                            (.local ptrSlot)
                            (.local lenSlot)
                            [(7, 0), (6, 8), (5, 16), (4, 24),
                              (3, 32), (2, 40), (1, 48), (0, 56)])),
                        lenSlot + 1)
                | _ => .error "unsupported ByteArray.toUInt64BE! application"
            | (.const ``ByteArray.get! _, args) =>
                match args.reverse with
                | index :: array :: _ =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    .ok
                      (wrapExprLets parts.fst
                        (.byteArrayGet parts.snd.fst parts.snd.snd indexResult.fst),
                        indexResult.snd)
                | _ => .error "unsupported ByteArray.get! application"
            | (.const ``Bool.toNat _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt64.ofNat _, [arg]) =>
                match ofNat? ``Nat arg with
                | some value => .ok (.u64 value, nextLocal)
                | none => extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt64.toNat _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt64.toUInt8 _, [arg]) =>
                let argResult ← extractExprFrom ctx locals nextLocal arg
                .ok (.u64Bin .bitAnd argResult.fst (.u64 255), argResult.snd)
            | (.const ``UInt64.toUInt32 _, [arg]) =>
                let argResult ← extractExprFrom ctx locals nextLocal arg
                .ok (.u64Bin .bitAnd argResult.fst (.u64 (2 ^ 32 - 1)), argResult.snd)
            | (.const ``Nat.toUInt64 _, [arg]) =>
                match ofNat? ``Nat arg with
                | some value => .ok (.u64 value, nextLocal)
                | none => extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt32.ofNat _, [arg]) =>
                match ofNat? ``Nat arg with
                | some value => .ok (.u64 (value % (2 ^ 32)), nextLocal)
                | none =>
                    let argResult ← extractExprFrom ctx locals nextLocal arg
                    .ok (.u64Bin .bitAnd argResult.fst (.u64 (2 ^ 32 - 1)), argResult.snd)
            | (.const ``UInt32.toNat _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt32.toUInt64 _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt32.toUInt8 _, [arg]) =>
                let argResult ← extractExprFrom ctx locals nextLocal arg
                .ok (.u64Bin .bitAnd argResult.fst (.u64 255), argResult.snd)
            | (.const ``UInt8.ofNat _, [arg]) =>
                match ofNat? ``Nat arg with
                | some value => .ok (.u64 (value % 256), nextLocal)
                | none =>
                    let argResult ← extractExprFrom ctx locals nextLocal arg
                    .ok (.u64Bin .bitAnd argResult.fst (.u64 255), argResult.snd)
            | (.const ``UInt8.toNat _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt8.toUInt64 _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt8.toUInt32 _, [arg]) =>
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
                match structureProjection? ctx.env primitive, args with
                | some (structName, some index), target :: [] =>
                    let valueResult ← extractValueFrom ctx locals nextLocal target
                    .ok (← scalarValue (← structField structName index valueResult.fst), valueResult.snd)
                | some (_structName, none), _target :: [] =>
                    .ok (.u64 0, nextLocal)
                | _, _ =>
                    match boolMatcherArgs? ctx.env (.const primitive []) args with
                    | some (scrutinee, falseArm, trueArm) =>
                        let condResult ← extractCondFrom ctx locals nextLocal scrutinee
                        let falseResult ← extractUnitArmValueFrom ctx locals condResult.snd falseArm
                        let trueResult ← extractUnitArmValueFrom ctx locals falseResult.snd trueArm
                        .ok (← scalarValue (← valueIte condResult.fst trueResult.fst falseResult.fst), trueResult.snd)
                    | none =>
                        match exceptMatcherArgs? ctx.env (.const primitive []) args with
                        | some (scrutinee, errorArm, okArm) =>
                            let valueResult ←
                              extractExceptMatchValueFrom ctx locals nextLocal scrutinee errorArm okArm
                            .ok (← scalarValue valueResult.fst, valueResult.snd)
                        | none =>
                            match optionMatcherArgs? ctx.env (.const primitive []) args with
                            | some (scrutinee, noneArm, someArm) =>
                                let valueResult ←
                                  extractOptionMatchValueFrom ctx locals nextLocal scrutinee noneArm someArm
                                .ok (← scalarValue valueResult.fst, valueResult.snd)
                            | none =>
                                match natMatcherArgs? ctx.env (.const primitive []) args with
                                | some (scrutinee, zeroArm, succArm) =>
                                    let valueResult ←
                                      extractNatMatchValueFrom ctx locals nextLocal scrutinee zeroArm succArm
                                    .ok (← scalarValue valueResult.fst, valueResult.snd)
                                | none =>
                                    match productMatcherArgs? ctx.env (.const primitive []) args with
                                    | some (scrutinee, arm) =>
                                        let valueResult ←
                                          extractProductMatchValueFrom ctx locals nextLocal scrutinee arm
                                        .ok (← scalarValue valueResult.fst, valueResult.snd)
                                    | none =>
                                        match structureMatcherArgs? ctx.env (.const primitive []) args with
                                        | some (structName, scrutinee, arm) =>
                                            let valueResult ←
                                              extractStructureMatchValueFrom ctx locals nextLocal
                                                structName scrutinee arm
                                            .ok (← scalarValue valueResult.fst, valueResult.snd)
                                        | none =>
                                            match variantMatcherArgs? ctx.env (.const primitive []) args with
                                            | some (layout, scrutinee, arms) =>
                                                let valueResult ←
                                                  extractVariantMatchValueFrom ctx locals nextLocal
                                                    layout scrutinee arms
                                                .ok (← scalarValue valueResult.fst, valueResult.snd)
                                            | none =>
                                                extractPrimitiveApplicationFrom ctx locals nextLocal
                                                  primitive args
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
                  match supportedFunction? ctx.env info with
                  | some sig => .ok sig
                  | none => .error s!"unsupported function type or declaration: {primitive}"
              | none => .error s!"declaration disappeared during extraction: {primitive}"
            let argsResult ← extractCallArgsFrom ctx locals nextLocal sig.params args
            .ok (wrapExprLets argsResult.lets (.call index argsResult.args), argsResult.nextLocal)
        | none =>
            if primitive == ``Complement.complement then
              match args.reverse with
              | value :: _ =>
                  let valueResult ← extractExprFrom ctx locals nextLocal value
                  match primitiveReceiverType? ctx.env args with
                  | some .u8 =>
                      .ok (.u64Bin .bitXor valueResult.fst (.u64 255), valueResult.snd)
                  | some .u32 =>
                      .ok (.u64Bin .bitXor valueResult.fst (.u64 (2 ^ 32 - 1)),
                        valueResult.snd)
                  | some .u64 =>
                      .ok (.u64Bin .bitXor valueResult.fst (.u64 (runtimeNatLimit - 1)),
                        valueResult.snd)
                  | _ => .error s!"unsupported complement expression: {primitive}"
              | _ => .error s!"unsupported complement expression: {primitive}"
            else if primitive == ``Nat.succ then
              match args.reverse with
              | value :: _ =>
                  let valueResult ← extractExprFrom ctx locals nextLocal value
                  .ok (.u64Bin .natAdd valueResult.fst (.u64 1), valueResult.snd)
              | _ => .error "unsupported Nat.succ application"
            else if primitive == ``Nat.pred then
              match args.reverse with
              | value :: _ =>
                  let valueResult ← extractExprFrom ctx locals nextLocal value
                  .ok (.u64Bin .natSub valueResult.fst (.u64 1), valueResult.snd)
              | _ => .error "unsupported Nat.pred application"
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
      match primitiveResultType? ctx.env args with
      | some .nat =>
          .ok (.u64Bin .natAdd leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .add leftIR rightIR), rightResult.snd)
      | some .u32 =>
          .ok (u32WrapExpr (.u64Bin .add leftIR rightIR), rightResult.snd)
      | _ => .ok (.u64Bin .add leftIR rightIR, rightResult.snd)
    else if primitive == ``HSub.hSub then
      match primitiveResultType? ctx.env args with
      | some .nat =>
          .ok (.u64Bin .natSub leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .sub leftIR rightIR), rightResult.snd)
      | some .u32 =>
          .ok (u32WrapExpr (.u64Bin .sub leftIR rightIR), rightResult.snd)
      | _ => .ok (.u64Bin .sub leftIR rightIR, rightResult.snd)
    else if primitive == ``HMul.hMul then
      match primitiveResultType? ctx.env args with
      | some .nat =>
          .ok (.u64Bin .natMul leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .mul leftIR rightIR), rightResult.snd)
      | some .u32 =>
          .ok (u32WrapExpr (.u64Bin .mul leftIR rightIR), rightResult.snd)
      | _ => .ok (.u64Bin .mul leftIR rightIR, rightResult.snd)
    else if primitive == ``HDiv.hDiv then
      .ok (.u64Bin .divU leftIR rightIR, rightResult.snd)
    else if primitive == ``HMod.hMod then
      .ok (.u64Bin .modU leftIR rightIR, rightResult.snd)
    else if primitive == ``HAnd.hAnd then
      match primitiveResultType? ctx.env args with
      | some .u8 | some .u32 | some .u64 =>
          .ok (.u64Bin .bitAnd leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported bitwise and expression: {primitive}"
    else if primitive == ``HOr.hOr then
      match primitiveResultType? ctx.env args with
      | some .u8 | some .u32 | some .u64 =>
          .ok (.u64Bin .bitOr leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported bitwise or expression: {primitive}"
    else if primitive == ``HXor.hXor then
      match primitiveResultType? ctx.env args with
      | some .u8 | some .u32 | some .u64 =>
          .ok (.u64Bin .bitXor leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported bitwise xor expression: {primitive}"
    else if primitive == ``HShiftLeft.hShiftLeft then
      match primitiveReceiverType? ctx.env args with
      | some .u64 =>
          .ok (.u64Bin .shiftLeft leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .shiftLeft leftIR (u8ShiftAmountExpr rightIR)),
            rightResult.snd)
      | some .u32 =>
          .ok (u32WrapExpr (.u64Bin .shiftLeft leftIR (u32ShiftAmountExpr rightIR)),
            rightResult.snd)
      | _ => .error s!"unsupported shift-left expression: {primitive}"
    else if primitive == ``HShiftRight.hShiftRight then
      match primitiveReceiverType? ctx.env args with
      | some .u64 =>
          .ok (.u64Bin .shiftRight leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (.u64Bin .shiftRight leftIR (u8ShiftAmountExpr rightIR), rightResult.snd)
      | some .u32 =>
          .ok (.u64Bin .shiftRight leftIR (u32ShiftAmountExpr rightIR), rightResult.snd)
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
    else if primitive == ``UInt32.land then
      .ok (.u64Bin .bitAnd leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt32.lor then
      .ok (.u64Bin .bitOr leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt32.xor then
      .ok (.u64Bin .bitXor leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt32.shiftLeft then
      .ok (u32WrapExpr (.u64Bin .shiftLeft leftIR (u32ShiftAmountExpr rightIR)),
        rightResult.snd)
    else if primitive == ``UInt32.shiftRight then
      .ok (.u64Bin .shiftRight leftIR (u32ShiftAmountExpr rightIR), rightResult.snd)
    else if primitive == ``UInt8.shiftLeft then
      .ok (u8WrapExpr (.u64Bin .shiftLeft leftIR (u8ShiftAmountExpr rightIR)),
        rightResult.snd)
    else if primitive == ``UInt8.shiftRight then
      .ok (.u64Bin .shiftRight leftIR (u8ShiftAmountExpr rightIR), rightResult.snd)
    else if primitive == ``BEq.beq then
      .ok (boolExpr (.eqU64 leftIR rightIR), rightResult.snd)
    else if primitive == ``bne then
      .ok (boolExpr (.not (.eqU64 leftIR rightIR)), rightResult.snd)
    else if primitive == ``LT.lt then
      .ok (boolExpr (.ltU64 leftIR rightIR), rightResult.snd)
    else if primitive == ``LE.le then
      .ok (boolExpr (.leU64 leftIR rightIR), rightResult.snd)
    else if primitive == ``GT.gt then
      .ok (boolExpr (.ltU64 rightIR leftIR), rightResult.snd)
    else if primitive == ``GE.ge then
      .ok (boolExpr (.leU64 rightIR leftIR), rightResult.snd)
    else if primitive == ``Min.min then
      match primitiveReceiverType? ctx.env args with
      | some .nat | some .u8 | some .u32 | some .u64 =>
          .ok (.ite (.leU64 leftIR rightIR) leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported min expression: {primitive}"
    else if primitive == ``Max.max then
      match primitiveReceiverType? ctx.env args with
      | some .nat | some .u8 | some .u32 | some .u64 =>
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
            match typeAtom? ctx.env ty with
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
        | (.const ``Id.run _, _) =>
            let valueResult ← extractValueFrom ctx locals nextLocal expr
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | (.const ``Pure.pure _, _) =>
            let valueResult ← extractValueFrom ctx locals nextLocal expr
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | (.const ``Bind.bind _, _) =>
            let valueResult ← extractValueFrom ctx locals nextLocal expr
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | (.const ``dite _, _) =>
            let valueResult ← extractValueFrom ctx locals nextLocal expr
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
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
        | (.const ``bne _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.not (.eqU64 leftResult.fst rightResult.fst), rightResult.snd)
            | none => .error "unsupported bne application"
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
        | (.const ``Option.get! _, _) =>
            let valueResult ← extractValueFrom ctx locals nextLocal expr
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | (.const ``Array.get!Internal _, _) =>
            let exprResult ← extractExprFrom ctx locals nextLocal expr
            .ok (boolCond exprResult.fst, exprResult.snd)
        | (.const ``GetElem?.getElem! _, _) =>
            let exprResult ← extractExprFrom ctx locals nextLocal expr
            .ok (boolCond exprResult.fst, exprResult.snd)
        | (.const ``GetElem.getElem _, _) =>
            let exprResult ← extractExprFrom ctx locals nextLocal expr
            .ok (boolCond exprResult.fst, exprResult.snd)
        | (.const ``Option.isSome _, args) =>
            match args.reverse with
            | optionValue :: _ =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let tag := wrapExprLets parts.fst parts.snd.fst
                .ok (.not (.eqU64 tag (.u64 0)), optionResult.snd)
            | _ => .error "unsupported Option.isSome condition"
        | (.const ``Option.isNone _, args) =>
            match args.reverse with
            | optionValue :: _ =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let tag := wrapExprLets parts.fst parts.snd.fst
                .ok (.eqU64 tag (.u64 0), optionResult.snd)
            | _ => .error "unsupported Option.isNone condition"
        | (.const ``Option.any _, _) =>
            extractOptionPredicateCondFrom ctx locals nextLocal expr false
        | (.const ``Option.all _, _) =>
            extractOptionPredicateCondFrom ctx locals nextLocal expr true
        | (.const ``Except.isOk _, args) =>
            match args.reverse, exceptPayloadType? ctx.env args with
            | exceptValue :: _, some _payloadTy =>
                let tagResult ← extractExceptTagExprFrom ctx locals nextLocal exceptValue
                .ok (.not (.eqU64 tagResult.fst (.u64 0)), tagResult.snd)
            | _, _ => .error "unsupported Except.isOk condition"
        | (.const ``Bool.or _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.or leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Bool.and _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.and leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Bool.xor _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok
              (.or
                (.and leftResult.fst (.not rightResult.fst))
                (.and (.not leftResult.fst) rightResult.fst),
                rightResult.snd)
        | (.const ``Nat.blt _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.ltU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported Nat.blt application"
        | (.const ``Nat.ble _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.leU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported Nat.ble application"
        | (.const ``Nat.beq _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.eqU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported Nat.beq application"
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
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let len := wrapExprLets parts.fst parts.snd.snd
                .ok (.eqU64 len (.u64 0), arrayResult.snd)
            | _ => .error "unsupported ByteArray.isEmpty condition"
        | (.const name _, args) =>
            match boolMatcherArgs? ctx.env (.const name []) args with
            | some _ =>
                let exprResult ← extractExprFrom ctx locals nextLocal expr
                .ok (boolCond exprResult.fst, exprResult.snd)
            | none =>
                match exceptMatcherArgs? ctx.env (.const name []) args with
                | some _ =>
                    let exprResult ← extractExprFrom ctx locals nextLocal expr
                    .ok (boolCond exprResult.fst, exprResult.snd)
                | none =>
                    match natMatcherArgs? ctx.env (.const name []) args with
                    | some _ =>
                        let exprResult ← extractExprFrom ctx locals nextLocal expr
                        .ok (boolCond exprResult.fst, exprResult.snd)
                    | none =>
                        match productMatcherArgs? ctx.env (.const name []) args with
                        | some _ =>
                            let exprResult ← extractExprFrom ctx locals nextLocal expr
                            .ok (boolCond exprResult.fst, exprResult.snd)
                        | none =>
                            match structureMatcherArgs? ctx.env (.const name []) args with
                            | some _ =>
                                let exprResult ← extractExprFrom ctx locals nextLocal expr
                                .ok (boolCond exprResult.fst, exprResult.snd)
                            | none =>
                                match variantMatcherArgs? ctx.env (.const name []) args with
                                | some _ =>
                                    let exprResult ← extractExprFrom ctx locals nextLocal expr
                                    .ok (boolCond exprResult.fst, exprResult.snd)
                                | none =>
                                    match ← extractInlineCallValueFrom ctx locals nextLocal name args with
                                    | some valueResult =>
                                        .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
                                    | none =>
                                        match functionIndex? ctx name with
                                        | some index =>
                                            strictRecursiveCallCheck ctx name args
                                            let sig ←
                                              match ctx.env.find? name with
                                              | some info =>
                                                  match supportedFunction? ctx.env info with
                                                  | some sig => .ok sig
                                                  | none =>
                                                      .error
                                                        s!"unsupported function type or declaration: {name}"
                                              | none =>
                                                  .error s!"declaration disappeared during extraction: {name}"
                                            let argsResult ← extractCallArgsFrom ctx locals nextLocal sig.params args
                                            .ok
                                              (boolCond
                                                (wrapExprLets argsResult.lets
                                                  (.call index argsResult.args)),
                                                argsResult.nextLocal)
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
      List Ty → List Expr → Except String MaterializedArgs
    | [], [] => .ok { lets := [], args := [], nextLocal := nextLocal }
    | ty :: restTys, expr :: restExprs => do
        let valueResult ← extractValueFrom ctx locals nextLocal expr
        let head ← materializeInternalSlots ty valueResult.fst valueResult.snd
        let bound := bindSlotExprs head.slots head.nextLocal
        let rest ← extractCallArgsFrom ctx locals bound.nextLocal restTys restExprs
        .ok {
          lets := head.lets ++ bound.lets ++ rest.lets,
          args := bound.slots ++ rest.args,
          nextLocal := rest.nextLocal
        }
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
  continueCond? : Option Expr
  continueWhenTrue : Bool
  exitValue? : Option Expr
  recArgs : List Expr

def parseStepBody? (env : Environment) (paramCount : Nat) (body : Expr) :
    Except String (Option (Expr × Bool) × Option Expr × List Expr) := do
  let expectedArgs := paramCount - 1
  match appFnArgs body with
  | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
      if typeAtom? env ty |>.isSome then
        match recCallArgs? expectedArgs thenExpr with
        | some args => .ok (some (condExpr, true), some elseExpr, args)
        | none =>
            match recCallArgs? expectedArgs elseExpr with
            | some args => .ok (some (condExpr, false), some thenExpr, args)
            | none => .error "recursive branch is not a tail call"
      else
        .error "recursive branch has unsupported if-result type"
  | _ =>
      match recCallArgs? expectedArgs body with
      | some args => .ok (none, none, args)
      | none => .error "recursive branch is not a supported tail call"

def parseRecMatcher? (env : Environment) (name : Name) (paramCount : Nat) (expr : Expr) :
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
            let parsedStep ← parseStepBody? env paramCount stepBody
            let continueCond? := parsedStep.fst.map Prod.fst
            let continueWhenTrue := parsedStep.fst.map Prod.snd |>.getD true
            .ok (some {
              base := baseBody,
              continueCond? := continueCond?,
              continueWhenTrue := continueWhenTrue,
              exitValue? := parsedStep.snd.fst,
              recArgs := parsedStep.snd.snd
            })
        | _ => .error s!"unsupported Nat recursion matcher arguments: {name}"
  | _ => return none

mutual
  partial def findRecSpec? (env : Environment) (name : Name) (paramCount : Nat) (expr : Expr) :
      Except String (Option RecSpec) := do
    match ← parseRecMatcher? env name paramCount expr with
    | some spec => .ok (some spec)
    | none => findRecSpecInChildren? env name paramCount expr

  partial def findRecSpecInChildren? (env : Environment) (name : Name) (paramCount : Nat) (expr : Expr) :
      Except String (Option RecSpec) := do
    match expr.consumeMData with
    | .app fn arg =>
        match ← findRecSpec? env name paramCount fn with
        | some spec => .ok (some spec)
        | none => findRecSpec? env name paramCount arg
    | .lam _ type body _ =>
        match ← findRecSpec? env name paramCount type with
        | some spec => .ok (some spec)
        | none => findRecSpec? env name paramCount body
    | .forallE _ type body _ =>
        match ← findRecSpec? env name paramCount type with
        | some spec => .ok (some spec)
        | none => findRecSpec? env name paramCount body
    | .letE _ type value body _ =>
        match ← findRecSpec? env name paramCount type with
        | some spec => .ok (some spec)
        | none =>
            match ← findRecSpec? env name paramCount value with
            | some spec => .ok (some spec)
            | none => findRecSpec? env name paramCount body
    | .mdata _ body => findRecSpec? env name paramCount body
    | .proj _ _ body => findRecSpec? env name paramCount body
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
    (resultTy : Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  let sourceParamCount := params.length
  let wasmParamCount := abiParamCount params
  let spec ←
    match ← findRecSpec? ctx.env name sourceParamCount value with
    | some spec => .ok spec
    | none => .error s!"unsupported Nat recursion shape: {name}"
  let stepLocals := stepBindingsForParams params
  let baseLocals := baseBindingsForParams params
  let fuelLive : IRCond := .not (.eqU64 (.local 0) (.u64 0))
  let condResult ←
    match spec.continueCond? with
    | some condExpr =>
        let extracted ← extractCond ctx stepLocals wasmParamCount condExpr
        let continueCond :=
          if spec.continueWhenTrue then
            extracted.fst
          else
            .not extracted.fst
        .ok (.and fuelLive continueCond, extracted.snd)
    | none => .ok (fuelLive, wasmParamCount)
  let exitResult? ←
    match spec.exitValue? with
    | some exitExpr =>
        let extracted ← extractValueFrom ctx stepLocals condResult.snd exitExpr
        .ok (some extracted.fst, extracted.snd)
    | none => .ok (none, condResult.snd)
  let carriedParams := params.drop 1
  let recArgsResult ← extractCallArgsFrom ctx stepLocals exitResult?.snd carriedParams spec.recArgs
  let baseResult ← extractValueFrom ctx baseLocals recArgsResult.nextLocal spec.base
  let loopCond := condResult.fst
  let recIRArgs := recArgsResult.args
  let targets := (abiTargets params |>.drop 1).flatMap Prod.snd
  let tempStart := baseResult.snd
  let updateArgs :=
    LeanExe.IR.seqList <|
      recArgsResult.lets.map valueLetStmt ++ [assignMany targets recIRArgs tempStart]
  let decFuel : IRStmt := .assign 0 (.u64Bin .sub (.local 0) (.u64 1))
  let loopBody : IRStmt := .seq updateArgs decFuel
  let resultValue ←
    match exitResult?.fst with
    | some exitValue => valueIte fuelLive exitValue baseResult.fst
    | none => .ok baseResult.fst
  let useAbi := exportName.isSome
  let resultStart := tempStart + targets.length
  let resultCount := resultSlotCount useAbi resultTy
  let resultTargets := (List.range resultCount).map (fun offset => resultStart + offset)
  let resultBody ← materializeResultValue useAbi resultTy resultTargets resultValue
  .ok {
    sourceName := name,
    exportName := exportName,
    params := wasmParamCount,
    locals := resultStart + resultCount,
    body := LeanExe.IR.seqList [.while loopCond loopBody, resultBody],
    results := resultTargets.map LeanExe.IR.Expr.local
  }

def extractPlainFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (resultTy : Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  let sourceParamCount := params.length
  let wasmParamCount := abiParamCount params
  let body ←
    match collectLambdas value sourceParamCount with
    | some body => .ok body
    | none => .error s!"definition body does not match function arity: {name}"
  let result ← extractValueFrom ctx (localBindingsForParams params) wasmParamCount body
  let useAbi := exportName.isSome
  let resultCount := resultSlotCount useAbi resultTy
  let resultTargets := (List.range resultCount).map (fun offset => result.snd + offset)
  let resultBody ← materializeResultValue useAbi resultTy resultTargets result.fst
  .ok {
    sourceName := name,
    exportName := exportName,
    params := wasmParamCount,
    locals := result.snd + resultCount,
    body := resultBody,
    results := resultTargets.map LeanExe.IR.Expr.local
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
        extractNatRecFunc ctx name sig.params sig.result value exportName
      else
        extractPlainFunc ctx name sig.params sig.result value exportName
  | _ => extractPlainFunc ctx name sig.params sig.result value exportName

def compileEnvironment (env : Environment) (moduleName entry : Name) : Except String IRModule := do
  let entryInfo ←
    match env.find? entry with
    | some info => .ok info
    | none => .error s!"entry not found: {entry}"
  let _entrySig ←
    match supportedEntryFunction? env entryInfo with
    | some sig => .ok sig
    | none => .error s!"unsupported function type or declaration: {entry}"
  let (_, namesList) ← collectReachable env moduleName.getRoot entry [] []
  let names := namesList.toArray
  let ctx : Context := { env := env, root := moduleName.getRoot, names := names, inlineStack := [] }
  let mut funcs := #[]
  for name in names do
    let info ←
      match env.find? name with
      | some info => .ok info
      | none => .error s!"declaration disappeared during extraction: {name}"
    let sig ←
      if name == entry then
        match supportedEntryFunction? ctx.env info with
        | some sig => .ok sig
        | none => .error s!"unsupported function type or declaration: {name}"
      else
        match supportedFunction? ctx.env info with
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
