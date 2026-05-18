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

structure SyntheticFunction where
  name : Name
  sig : Signature
  value : Expr
  typeName : Name
  typeParams : List Ty
  dynamicPostArgTypes : List Ty
  captureIndices : List Nat
  captureTypes : List Ty
  motive : Expr
  step : Expr
  postArgs : List Expr

inductive ExtractedValue where
  | scalar (expr : IRExpr)
  | array (owner ptr : IRExpr)
  | byteArray (owner ptr len : IRExpr)
  | product (left right : ExtractedValue)
  | sum (tag : IRExpr) (left right : ExtractedValue)
  | struct (name : Name) (fields : List ExtractedValue)
  | variant (name : Name) (tag : IRExpr) (ctors : List (List ExtractedValue))
  | recursiveVariant (name : Name) (tag : IRExpr) (ctors : List (List (Ty × ExtractedValue)))
  | heapVariant (name : Name) (ptr : IRExpr)
  | ite (cond : IRCond) (thenValue elseValue : ExtractedValue)
  | letE (slot : Nat) (value : IRExpr) (body : ExtractedValue)
  | letCall (slots : List Nat) (index : Nat) (args : List IRExpr) (body : ExtractedValue)
  | letLocal (lets : List LeanExe.IR.LocalLet) (body : ExtractedValue)
  deriving BEq, Repr

instance : Inhabited ExtractedValue :=
  ⟨.scalar .trap⟩

inductive StructuralBelow where
  | unit
  | call (functionName : Name) (arg : ExtractedValue) (capturedArgs : List ExtractedValue)
  | pair (left right : StructuralBelow)
  deriving BEq, Repr

inductive ValueLet where
  | expr (slot : Nat) (value : IRExpr)
  | call (slots : List Nat) (index : Nat) (args : List IRExpr)
  deriving BEq, Repr

structure StrictSlots where
  lets : List ValueLet
  slots : List IRExpr
  nextLocal : Nat
  deriving BEq, Repr

structure StrictArgs where
  lets : List ValueLet
  args : List IRExpr
  nextLocal : Nat
  deriving BEq, Repr

inductive Binding where
  | slot (index : Nat)
  | value (value : ExtractedValue)
  | thunk (locals : List Binding) (expr : Expr)
  | structuralRec (functionName : Name) (arg : ExtractedValue)
  | structuralBelow (below : StructuralBelow)
  | wfRecursor (functionName : Name)
  | natRecursor (functionName : Name)
  | recursor
  deriving BEq, Repr

structure Context where
  env : Environment
  root : Name
  names : Array Name
  synthetics : Array SyntheticFunction
  freshResultOwnerOffsets : Array (List Nat)
  inlineStack : List Name

structure VariantCtorLayout where
  name : Name
  fields : List (Option Ty)
  deriving BEq, Repr

structure VariantLayout where
  name : Name
  params : List Ty := []
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

partial def collectLambdas (expr : Expr) : Nat → Option Expr
  | 0 => some expr
  | count + 1 =>
      match expr.consumeMData with
      | .lam _ _ body _ => collectLambdas body count
      | _ => none

def isIdType (expr : Expr) : Bool :=
  isConst ``Id expr

def isOptionMonadType (expr : Expr) : Bool :=
  isConst ``Option expr

def isStringType (expr : Expr) : Bool :=
  isConst ``String expr

def isCharType (expr : Expr) : Bool :=
  isConst ``Char expr

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
        (.arraySetSlots 1 0 0 array (.u64 index) [.u64 byte.toNat])
        rest

def byteArrayLiteralArrayExpr (bytes : List UInt8) : IRExpr :=
  byteArrayLiteralArrayExprAux 0 (.arrayAllocSlots 1 0 (.u64 bytes.length)) bytes

def byteArrayLiteralValue (slot : Nat) (bytes : List UInt8) : ExtractedValue × Nat :=
  match bytes with
  | [] => (.byteArray (.u64 0) (.u64 0) (.u64 0), slot)
  | _ =>
      let ptrSlot := slot + 1
      (.letE slot (byteArrayLiteralArrayExpr bytes)
        (.letE ptrSlot (.byteArrayFromArrayPtr (.local slot))
          (.byteArray (.local ptrSlot) (.local ptrSlot) (.arraySize (.local slot)))),
        ptrSlot + 1)

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
  match natLit? expr with
  | some value => some (boundedNatExpr value)
  | none =>
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

def nonRuntimeEvidenceTypeNames : List Name :=
  [``Inhabited, ``Decidable, ``BEq, ``LT, ``LE, ``OfNat, ``HAdd, ``HSub, ``HMul, ``HDiv,
    ``HMod, ``GetElem, ``GetElem?]

def isRuntimeStructure (env : Environment) (name : Name) : Bool :=
  isStructure env name && !isClass env name && !nonRuntimeEvidenceTypeNames.contains name

def structureInductiveInfo? (env : Environment) (structName : Name) : Option InductiveVal :=
  if !isRuntimeStructure env structName then
    none
  else
    match env.find? structName with
    | some (.inductInfo info) =>
        if info.numIndices == 0 && info.ctors.length == 1 && !info.isRec then
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
  [``Bool, ``Nat, ``Unit, ``Option, ``Except, ``Prod, ``PSum, ``String]

def userInductiveInfo? (env : Environment) (typeName : Name) : Option InductiveVal :=
  if builtinInductiveNames.contains typeName || isRuntimeStructure env typeName ||
      isClass env typeName || nonRuntimeEvidenceTypeNames.contains typeName then
    none
  else
    match env.find? typeName with
    | some (.inductInfo info) =>
        if info.numIndices == 0 && !info.isRec && !info.ctors.isEmpty then
          some info
        else
          none
    | _ => none

def userRecursiveInductiveInfo? (env : Environment) (typeName : Name) : Option InductiveVal :=
  if builtinInductiveNames.contains typeName || isRuntimeStructure env typeName ||
      isClass env typeName || nonRuntimeEvidenceTypeNames.contains typeName then
    none
  else
    match env.find? typeName with
    | some (.inductInfo info) =>
        if info.numIndices == 0 && info.isRec && !info.ctors.isEmpty then
          some info
        else
          none
    | _ => none

def recursiveFamilyNames? (env : Environment) (typeName : Name) (params : List Ty) :
    Option (List Name) := do
  let info ← userRecursiveInductiveInfo? env typeName
  if params.length != info.numParams then
    none
  else if info.all.all (fun member =>
      match userRecursiveInductiveInfo? env member with
      | some memberInfo =>
          memberInfo.all == info.all &&
            memberInfo.numParams == info.numParams &&
            memberInfo.numIndices == 0
      | none => false) then
    some info.all
  else
    none

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

partial def tyExpr? : Ty → Option Expr
  | .unit => some (.const ``Unit [])
  | .bool => some (.const ``Bool [])
  | .u8 => some (.const ``UInt8 [])
  | .u32 => some (.const ``UInt32 [])
  | .u64 => some (.const ``UInt64 [])
  | .nat => some (.const ``Nat [])
  | .byteArray => some (.const ``ByteArray [])
  | .array item => tyExpr? item |>.map (fun itemExpr => .app (.const ``Array []) itemExpr)
  | .product left right => do
      let leftExpr ← tyExpr? left
      let rightExpr ← tyExpr? right
      some (.app (.app (.const ``Prod []) leftExpr) rightExpr)
  | .struct name params _ => do
      let paramExprs ← params.mapM tyExpr?
      some (paramExprs.foldl (fun acc param => .app acc param) (.const name []))
  | .variant name params [[], [payload]] =>
      if name == ``Option then
        tyExpr? payload |>.map (fun payloadExpr => .app (.const ``Option []) payloadExpr)
      else do
        let paramExprs ← params.mapM tyExpr?
        some (paramExprs.foldl (fun acc param => .app acc param) (.const name []))
  | .variant name params [[error], [ok]] =>
      if name == ``Except then do
        let errorExpr ← tyExpr? error
        let okExpr ← tyExpr? ok
        some (.app (.app (.const ``Except []) errorExpr) okExpr)
      else do
        let paramExprs ← params.mapM tyExpr?
        some (paramExprs.foldl (fun acc param => .app acc param) (.const name []))
  | .variant name params _ => do
      let paramExprs ← params.mapM tyExpr?
      some (paramExprs.foldl (fun acc param => .app acc param) (.const name []))
  | .recVariant name params => do
      let paramExprs ← params.mapM tyExpr?
      some (paramExprs.foldl (fun acc param => .app acc param) (.const name []))
  | .sum left right => do
      let leftExpr ← tyExpr? left
      let rightExpr ← tyExpr? right
      some (.app (.app (.const ``PSum []) leftExpr) rightExpr)

def ctorFieldDomainsWithParams? (ctorInfo : ConstructorVal) (params : List Ty) :
    Option (List Expr) := do
  if params.length != ctorInfo.numParams then
    none
  else
    let paramExprs ← params.mapM tyExpr?
    let fields := (peelForall ctorInfo.type).fst.drop ctorInfo.numParams
    if fields.length == ctorInfo.numFields then
      let paramArray := paramExprs.toArray
      fields.zipIdx.mapM fun item =>
        let previousFields :=
          (List.range item.snd).toArray.map fun i =>
            .bvar (item.snd - i - 1)
        some (item.fst.instantiateRev (paramArray ++ previousFields))
    else
      none

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
    else if isStringType expr || isCharType expr then
      none
    else
      match appFnArgs expr with
      | (.const ``Array _, [item]) => typeAtom? env item |>.map .array
      | (.const ``Prod _, [left, right]) =>
          match typeAtom? env left, typeAtom? env right with
          | some leftTy, some rightTy => some (.product leftTy rightTy)
          | _, _ => none
      | (.const ``PSum _, [left, right]) =>
          match typeAtom? env left, typeAtom? env right with
          | some leftTy, some rightTy => some (.sum leftTy rightTy)
          | _, _ => none
      | (.const ``PSum.casesOn _, [_left, _right, _motive, _scrutinee, leftArm, rightArm]) =>
          match collectLambdas leftArm 1, collectLambdas rightArm 1 with
          | some leftBody, some rightBody =>
              match typeAtom? env leftBody, typeAtom? env rightBody with
              | some leftTy, some rightTy =>
                  if leftTy == rightTy then some leftTy else none
              | _, _ => none
          | _, _ => none
      | (.const ``Option _, [item]) =>
          typeAtom? env item |>.map (fun itemTy => .variant ``Option [itemTy] [[], [itemTy]])
      | (.const ``Except _, [error, ok]) =>
          match typeAtom? env error, typeAtom? env ok with
          | some errorTy, some okTy =>
              some (.variant ``Except [errorTy, okTy] [[errorTy], [okTy]])
          | _, _ => none
      | (.const name _, args) =>
          if nonRuntimeEvidenceTypeNames.contains name then
            none
          else
            match args.mapM (typeAtom? env) with
            | some params =>
                if isRuntimeStructure env name then
                  structureFieldKindsWithParams? env name params |>.map fun fields =>
                    .struct name params (runtimeTypesFromKinds fields)
                else
                  match variantLayoutWithParams? env name params with
                  | some layout =>
                      some (.variant name params (layout.ctors.map fun ctor =>
                        runtimeTypesFromKinds ctor.fields))
                  | none =>
                      recursiveVariantLayout? env name params |>.map fun _layout =>
                        .recVariant name params
            | none => none
      | _ => none

  partial def structureFieldKindsWithParams? (env : Environment) (structName : Name)
      (params : List Ty) :
      Option (List (Option Ty)) :=
    if !isRuntimeStructure env structName then
      none
    else
      match structureCtorInfo? env structName with
      | some ctorInfo =>
          if params.length != ctorInfo.numParams then
            none
          else
          let fields? := ctorFieldDomainsWithParams? ctorInfo params
          let flatFieldNames :=
            (getStructureFieldsFlattened env structName (includeSubobjectFields := false)).toList
          match fields? with
          | some fields =>
              if fields.length == ctorInfo.numFields && fields.length == flatFieldNames.length then
                fields.mapM fun field =>
                  if isProofType? env field then
                    some none
                  else
                    typeAtom? env field |>.map some
              else
                none
          | none => none
      | none => none

  partial def structureFieldKinds? (env : Environment) (structName : Name) :
      Option (List (Option Ty)) :=
    structureFieldKindsWithParams? env structName []

  partial def structureFieldTypes? (env : Environment) (structName : Name) : Option (List Ty) :=
    structureFieldKinds? env structName |>.map (fun fields => fields.filterMap id)

  partial def structureTypeLayout? (env : Environment) (expr : Expr) :
      Option (Name × List (Option Ty)) :=
    match appFnArgs expr with
    | (.const name _, args) =>
        if isRuntimeStructure env name then
          match args.mapM (typeAtom? env) with
          | some params =>
              structureFieldKindsWithParams? env name params |>.map fun fields => (name, fields)
          | none => none
        else
          none
    | _ => none

  partial def variantLayoutWithParams? (env : Environment) (typeName : Name)
      (params : List Ty) : Option VariantLayout :=
    match userInductiveInfo? env typeName with
    | some info =>
        if params.length != info.numParams then
          none
        else
        let ctorLayouts? := info.ctors.mapM fun ctorName =>
          match env.find? ctorName with
          | some (.ctorInfo ctorInfo) =>
              if ctorInfo.numParams == info.numParams && ctorInfo.induct == typeName then
                match ctorFieldDomainsWithParams? ctorInfo params with
                | some fields =>
                    fields.mapM (fun field =>
                      if isProofType? env field then
                        some none
                      else
                        typeAtom? env field |>.map some) |>.map fun fieldKinds =>
                          ({ name := ctorName, fields := fieldKinds } : VariantCtorLayout)
                | none => none
              else
                none
          | _ => none
        ctorLayouts? |>.map fun ctors =>
          ({ name := typeName, params := params, ctors := ctors } : VariantLayout)
    | none => none

  partial def variantLayout? (env : Environment) (typeName : Name) : Option VariantLayout :=
    variantLayoutWithParams? env typeName []

  partial def variantTypeLayout? (env : Environment) (expr : Expr) :
      Option VariantLayout :=
    match appFnArgs expr with
    | (.const name _, args) =>
        match args.mapM (typeAtom? env) with
        | some params => variantLayoutWithParams? env name params
        | none => none
    | _ => none

  partial def typeAtomRecursiveField?
      (env : Environment)
      (familyNames : List Name)
      (familyParams : List Ty)
      (expr : Expr) :
      Option Ty :=
    match appFnArgs expr with
    | (.const ``Array _, [item]) =>
        typeAtomRecursiveField? env familyNames familyParams item |>.map .array
    | (.const ``Prod _, [left, right]) =>
        match typeAtomRecursiveField? env familyNames familyParams left,
            typeAtomRecursiveField? env familyNames familyParams right with
        | some leftTy, some rightTy => some (.product leftTy rightTy)
        | _, _ => none
    | (.const ``PSum _, [left, right]) =>
        match typeAtomRecursiveField? env familyNames familyParams left,
            typeAtomRecursiveField? env familyNames familyParams right with
        | some leftTy, some rightTy => some (.sum leftTy rightTy)
        | _, _ => none
    | (.const ``Option _, [item]) =>
        typeAtomRecursiveField? env familyNames familyParams item |>.map
          (fun itemTy => .variant ``Option [itemTy] [[], [itemTy]])
    | (.const ``Except _, [error, ok]) =>
        match typeAtomRecursiveField? env familyNames familyParams error,
            typeAtomRecursiveField? env familyNames familyParams ok with
        | some errorTy, some okTy =>
            some (.variant ``Except [errorTy, okTy] [[errorTy], [okTy]])
        | _, _ => none
    | (.const name _, args) =>
        if familyNames.contains name then
          match args.mapM (typeAtom? env) with
          | some params =>
              if params == familyParams then some (.recVariant name familyParams) else none
          | none => none
        else
          match typeAtom? env expr with
          | some (.recVariant _ _) => none
          | other => other
    | _ =>
        match typeAtom? env expr with
        | some (.recVariant _ _) => none
        | other => other

  partial def recursiveVariantLayout? (env : Environment) (typeName : Name) (params : List Ty := []) :
      Option VariantLayout :=
    match userRecursiveInductiveInfo? env typeName with
    | some info =>
        match recursiveFamilyNames? env typeName params with
        | none => none
        | some familyNames =>
          let ctorLayouts? := info.ctors.mapM fun ctorName =>
            match env.find? ctorName with
            | some (.ctorInfo ctorInfo) =>
                if ctorInfo.numParams == info.numParams && ctorInfo.induct == typeName then
                  match ctorFieldDomainsWithParams? ctorInfo params with
                  | some fields =>
                      fields.mapM (fun field =>
                        if isProofType? env field then
                          some none
                        else
                          typeAtomRecursiveField? env familyNames params field |>.map some)
                        |>.map fun fieldKinds =>
                          ({ name := ctorName, fields := fieldKinds } : VariantCtorLayout)
                  | none => none
                else
                  none
            | _ => none
          ctorLayouts? |>.map fun ctors =>
            ({ name := typeName, params := params, ctors := ctors } : VariantLayout)
    | none => none
end

def anyVariantLayout? (env : Environment) (typeName : Name) : Option VariantLayout :=
  match variantLayout? env typeName with
  | some layout => some layout
  | none => recursiveVariantLayout? env typeName

def structureConstructorForArgs? (env : Environment) (ctorName : Name) (args : List Expr) :
    Option (Name × List (Option Ty) × List Expr) :=
  match env.find? ctorName with
  | some (.ctorInfo ctorInfo) =>
      if ctorInfo.cidx == 0 && isRuntimeStructure env ctorInfo.induct then
        let paramArgs := args.take ctorInfo.numParams
        let runtimeArgs := args.drop ctorInfo.numParams
        match paramArgs.mapM (typeAtom? env) with
        | some params =>
            structureFieldKindsWithParams? env ctorInfo.induct params |>.map fun fields =>
              (ctorInfo.induct, fields, runtimeArgs)
        | none => none
      else
        none
  | _ => none

def structureConstructor? (env : Environment) (ctorName : Name) :
    Option (Name × List (Option Ty)) :=
  match env.find? ctorName with
  | some (.ctorInfo ctorInfo) =>
      if ctorInfo.numParams == 0 && ctorInfo.cidx == 0 &&
          isRuntimeStructure env ctorInfo.induct then
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

def variantConstructorForArgs? (env : Environment) (ctorName : Name) (args : List Expr) :
    Option (VariantLayout × Nat × VariantCtorLayout × List Expr) :=
  match env.find? ctorName with
  | some (.ctorInfo ctorInfo) =>
      let paramArgs := args.take ctorInfo.numParams
      let runtimeArgs := args.drop ctorInfo.numParams
      match paramArgs.mapM (typeAtom? env) with
      | some params =>
          match variantLayoutWithParams? env ctorInfo.induct params with
          | some layout =>
              match ctorIndex? ctorName layout.ctors with
              | some index =>
                  match layout.ctors[index]? with
                  | some ctor => some (layout, index, ctor, runtimeArgs)
                  | none => none
              | none => none
          | none => none
      | none => none
  | _ => none

def recursiveVariantConstructor? (env : Environment) (ctorName : Name) :
    Option (VariantLayout × Nat × VariantCtorLayout) :=
  match env.find? ctorName with
  | some (.ctorInfo ctorInfo) =>
      match recursiveVariantLayout? env ctorInfo.induct [] with
      | some layout =>
          match ctorIndex? ctorName layout.ctors with
          | some index =>
              match layout.ctors[index]? with
              | some ctor => some (layout, index, ctor)
              | none => none
          | none => none
      | none => none
  | _ => none

def recursiveVariantConstructorForArgs? (env : Environment) (ctorName : Name) (args : List Expr) :
    Option (VariantLayout × Nat × VariantCtorLayout × List Expr) :=
  match env.find? ctorName with
  | some (.ctorInfo ctorInfo) =>
      let paramArgs := args.take ctorInfo.numParams
      let runtimeArgs := args.drop ctorInfo.numParams
      match paramArgs.mapM (typeAtom? env) with
      | some params =>
          match recursiveVariantLayout? env ctorInfo.induct params with
          | some layout =>
              match ctorIndex? ctorName layout.ctors with
              | some index =>
                  match layout.ctors[index]? with
                  | some ctor => some (layout, index, ctor, runtimeArgs)
                  | none => none
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
            if ctorInfo.numParams == 0 && isRuntimeStructure env ctorInfo.induct then
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

def structureProjectionForArgs? (env : Environment) (projName : Name) (args : List Expr) :
    Option (Name × Option Nat × Expr) :=
  match env.getProjectionFnInfo? projName with
  | some projInfo =>
      match env.find? projInfo.ctorName with
      | some (.ctorInfo ctorInfo) =>
          if isRuntimeStructure env ctorInfo.induct then
            let paramArgs := args.take projInfo.numParams
            let restArgs := args.drop projInfo.numParams
            match paramArgs.mapM (typeAtom? env), restArgs with
            | some params, target :: [] =>
                match structureFieldKindsWithParams? env ctorInfo.induct params with
                | some kinds =>
                    runtimeFieldIndexFromKinds projInfo.i kinds |>.map fun index? =>
                      (ctorInfo.induct, index?, target)
                | none => none
            | _, _ => none
          else
            none
      | _ => none
  | none => none

def supportedArrayCellType : Ty → Bool
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | _ => false

inductive ValueLayout where
  | scalar
  | pointer
  | fixed (slots : Nat)
  deriving BEq, Repr

def ValueLayout.slotCount : ValueLayout → Nat
  | .scalar => 1
  | .pointer => 1
  | .fixed slots => slots

mutual
  partial def valueLayout? : Ty → Option ValueLayout
    | .unit => some .scalar
    | .bool => some .scalar
    | .u8 => some .scalar
    | .u32 => some .scalar
    | .u64 => some .scalar
    | .nat => some .scalar
    | .byteArray => some (.fixed 3)
    | .array item => do
      let _ ← arrayElementLayout? item
      some (.fixed 2)
    | .product left right => do
        let leftSlots ← valueLayoutSlots? left
        let rightSlots ← valueLayoutSlots? right
        some (.fixed (leftSlots + rightSlots))
    | .sum left right => do
        let leftSlots ← valueLayoutSlots? left
        let rightSlots ← valueLayoutSlots? right
        some (.fixed (leftSlots + rightSlots + 1))
    | .struct _ _ fields => do
        let slots ← valueFieldSlots? fields
        some (.fixed slots)
    | .variant _ _ ctors => do
        let payloadSlots ← valueCtorSlots? ctors
        some (.fixed (payloadSlots + 1))
    | .recVariant _ _ => some .pointer

  partial def valueLayoutSlots? (ty : Ty) : Option Nat := do
    let layout ← valueLayout? ty
    some layout.slotCount

  partial def valueFieldSlots? : List Ty → Option Nat
    | [] => some 0
    | field :: rest => do
        let head ← valueLayoutSlots? field
        let tail ← valueFieldSlots? rest
        some (head + tail)

  partial def valueCtorSlots? : List (List Ty) → Option Nat
    | [] => some 0
    | fields :: rest => do
        let head ← valueFieldSlots? fields
        let tail ← valueCtorSlots? rest
        some (head + tail)

  partial def arrayElementLayout? : Ty → Option ValueLayout
    | .unit => some .scalar
    | .bool => some .scalar
    | .u8 => some .scalar
    | .u32 => some .scalar
    | .u64 => some .scalar
    | .nat => some .scalar
    | .array item => do
      let _ ← arrayElementLayout? item
      some (.fixed 2)
    | .product left right => do
        let leftSlots ← arrayElementSlots? left
        let rightSlots ← arrayElementSlots? right
        some (.fixed (leftSlots + rightSlots))
    | .sum left right => do
        let leftSlots ← arrayElementSlots? left
        let rightSlots ← arrayElementSlots? right
        some (.fixed (leftSlots + rightSlots + 1))
    | .struct _ _ fields => do
        let slots ← arrayFieldSlots? fields
        some (.fixed slots)
    | .variant _ _ ctors => do
        let payloadSlots ← arrayCtorSlots? ctors
        some (.fixed (payloadSlots + 1))
    | .recVariant _ _ => some .pointer
    | .byteArray => some (.fixed 3)

  partial def arrayElementSlots? (ty : Ty) : Option Nat := do
    let layout ← arrayElementLayout? ty
    some layout.slotCount

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

partial def supportedAbiArrayElementType : Ty → Bool
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | .struct _ _ fields => fields.all supportedAbiArrayElementType
  | .variant _ _ ctors => ctors.all (fun fields => fields.all supportedAbiArrayElementType)
  | _ => false

def supportedAbiType : Ty → Bool
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | .array item => supportedAbiArrayElementType item
  | _ => false

partial def supportedParamAbiType : Ty → Bool
  | .byteArray => true
  | .struct _ _ fields => fields.all supportedParamAbiType
  | .variant _ _ ctors => ctors.all (fun fields => fields.all supportedParamAbiType)
  | ty => supportedAbiType ty

partial def supportedResultAbiType : Ty → Bool
  | .byteArray => true
  | .struct _ _ fields => fields.all supportedResultAbiType
  | .variant _ _ ctors => ctors.all (fun fields => fields.all supportedResultAbiType)
  | ty => supportedAbiType ty

def supportedInternalValueType (ty : Ty) : Bool :=
  valueLayout? ty |>.isSome

def supportedInternalParamType : Ty → Bool
  | .byteArray => true
  | ty => supportedInternalValueType ty

def supportedInternalResultType : Ty → Bool :=
  supportedInternalValueType

partial def abiSlots : Ty → Nat
  | .byteArray => 2
  | .sum left right => 1 + abiSlots left + abiSlots right
  | .struct _ _ fields => fields.foldl (fun total field => total + abiSlots field) 0
  | .variant _ _ ctors =>
      1 + ctors.foldl
        (fun total fields => total + fields.foldl (fun acc field => acc + abiSlots field) 0)
        0
  | .recVariant _ _ => 1
  | _ => 1

partial def internalSlots : Ty → Nat
  | .byteArray => 3
  | .array _ => 2
  | .product left right => internalSlots left + internalSlots right
  | .sum left right => 1 + internalSlots left + internalSlots right
  | .struct _ _ fields => fields.foldl (fun total field => total + internalSlots field) 0
  | .variant _ _ ctors =>
      1 + ctors.foldl
        (fun total fields => total + fields.foldl (fun acc field => acc + internalSlots field) 0)
        0
  | .recVariant _ _ => 1
  | _ => 1

def abiParamCount (params : List Ty) : Nat :=
  params.foldl (fun total ty => total + abiSlots ty) 0

def functionParamSlots (useAbi : Bool) (ty : Ty) : Nat :=
  if useAbi then abiSlots ty else internalSlots ty

def functionParamCount (useAbi : Bool) (params : List Ty) : Nat :=
  params.foldl (fun total ty => total + functionParamSlots useAbi ty) 0

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

def supportedLocalType (ty : Ty) : Bool :=
  valueLayout? ty |>.isSome

partial def supportedLoopAccumulatorType : Ty → Bool
  | .unit => true
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | .byteArray => true
  | .array item => supportedArrayElementType item
  | .product left right =>
      supportedLoopAccumulatorType left && supportedLoopAccumulatorType right
  | .sum left right =>
      supportedLoopAccumulatorType left && supportedLoopAccumulatorType right
  | .struct _ _ fields => fields.all supportedLoopAccumulatorType
  | .variant _ _ ctors => ctors.all (fun fields => fields.all supportedLoopAccumulatorType)
  | .recVariant _ _ => true

def supportedInlineFunction? (env : Environment) (info : ConstantInfo) : Option Signature :=
  if info.isUnsafe || info.isPartial || info.value?.isNone then
    none
  else
    functionTypeWith? env supportedLocalType supportedLocalType info.type

structure InlineSpecialization where
  sig : Signature
  staticArgs : List Expr
  runtimeArgs : List Expr

def staticInlineDomain (env : Environment) (domain : Expr) : Bool :=
  match domain.consumeMData with
  | .sort _ => true
  | _ => isProofType? env domain

def specializedInlineCall?
    (env : Environment)
    (info : ConstantInfo)
    (args : List Expr) :
    Option InlineSpecialization := do
  if info.isUnsafe || info.isPartial || info.value?.isNone then
    none
  else
    let parts := peelForall info.type
    if parts.fst.length != args.length then
      none
    else
      let rec loop
          (previous staticArgs runtimeArgs : List Expr)
          (runtimeTys : List Ty)
          (seenRuntime : Bool) :
          List Expr → List Expr → Option (List Expr × List Expr × List Ty)
        | [], [] => some (staticArgs, runtimeArgs, runtimeTys)
        | domain :: restDomains, arg :: restArgs =>
            let instantiatedDomain := domain.instantiateRev previous.toArray
            match typeAtom? env instantiatedDomain with
            | some ty =>
                if supportedLocalType ty then
                  loop (previous ++ [arg]) staticArgs (runtimeArgs ++ [arg])
                    (runtimeTys ++ [ty]) true
                    restDomains restArgs
                else
                  none
            | none =>
                if seenRuntime then
                  none
                else if staticInlineDomain env instantiatedDomain then
                  loop (previous ++ [arg]) (staticArgs ++ [arg]) runtimeArgs runtimeTys false
                    restDomains restArgs
                else
                  none
        | _, _ => none
      let (staticArgs, runtimeArgs, runtimeTys) ← loop [] [] [] [] false parts.fst args
      let resultTy ← typeAtom? env (parts.snd.instantiateRev args.toArray)
      if supportedLocalType resultTy then
        some {
          sig := { params := runtimeTys, result := resultTy },
          staticArgs := staticArgs,
          runtimeArgs := runtimeArgs
        }
      else
        none

partial def instantiateLeadingLambdas (value : Expr) : List Expr → Option Expr
  | [] => some value
  | arg :: rest =>
      match value.consumeMData with
      | .lam _ _ body _ => instantiateLeadingLambdas (body.instantiate1 arg) rest
      | _ => none

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

def isDirectLambda (expr : Expr) : Bool :=
  match expr.consumeMData with
  | .lam _ _ _ _ => true
  | _ => false

def hasDirectLambdaArg (args : List Expr) : Bool :=
  args.any isDirectLambda

def keepDynamicArgs (args : List Expr) : List Expr :=
  args.filter fun arg => !isDirectLambda arg

def dynamicStructuralExtraArgs (expected : List Ty) (extraArgs : List Expr) :
    Except String (List Expr) := do
  let dynamicArgs := keepDynamicArgs extraArgs
  if dynamicArgs.length == expected.length then
    .ok dynamicArgs
  else
    .error "unsupported structural recursion carried arguments"

def blocksTransparentSpecialization (name : Name) : Bool :=
  let root := name.getRoot
  name == ``ite || name == ``dite || name == ``WellFounded.fix ||
    name == ``WellFounded.Nat.fix ||
    (match name with
    | .str _ component =>
        component.startsWith "match_" ||
          component == "brecOn" ||
          component == "rec" ||
          component == "recOn" ||
          component == "casesOn"
    | _ => false) ||
    [``Array, ``ByteArray, ``Option, ``Except, ``ForIn, ``Functor, ``Bind, ``Pure, ``Id, ``Nat,
      ``Decidable, ``GetElem, ``GetElem?, ``HOrElse, ``OrElse].contains root

partial def rebuildApp (fn : Expr) : List Expr → Expr
  | [] => fn
  | arg :: rest => rebuildApp (.app fn arg) rest

partial def betaSpecializeExpr
    (env : Environment)
    (root : Name)
    (fuel : Nat)
    (expr : Expr) : Expr :=
  match fuel with
  | 0 => expr
  | fuel + 1 =>
      let normalize := betaSpecializeExpr env root fuel
      match expr.consumeMData with
      | .app _ _ =>
          let (fn, args) := appFnArgs expr
          let normalizedFn := normalize fn
          let normalizedArgs := args.map normalize
          let rec applyNormalized (fn : Expr) : List Expr → Expr
            | [] => fn
            | arg :: rest =>
                match fn.consumeMData with
                | .lam _ _ body _ => applyNormalized (normalize (body.instantiate1 arg)) rest
                | _ => rebuildApp fn (arg :: rest)
          let applied := applyNormalized normalizedFn normalizedArgs
          match appFnArgs applied with
          | (.const name _, appliedArgs) =>
              if name.getRoot != root &&
                  !blocksTransparentSpecialization name &&
                  hasDirectLambdaArg appliedArgs then
                match env.find? name with
                | some info =>
                    match info.value? with
                    | some value => normalize (rebuildApp value appliedArgs)
                    | none => applied
                | none => applied
              else
                applied
          | _ => applied
      | .lam name type body bi => .lam name (normalize type) (normalize body) bi
      | .forallE name type body bi => .forallE name (normalize type) (normalize body) bi
      | .letE name type value body nondep =>
          .letE name (normalize type) (normalize value) (normalize body) nondep
      | .mdata data body => .mdata data (normalize body)
      | .proj typeName index body => .proj typeName index (normalize body)
      | other => other

def containsConstantInExpr (name : Name) (expr : Expr) : Bool :=
  expr.getUsedConstants.contains name

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

def syntheticFunction? (ctx : Context) (name : Name) : Option SyntheticFunction :=
  ctx.synthetics.toList.find? (fun synth => synth.name == name)

def functionSignature? (ctx : Context) (name : Name) : Option Signature :=
  match syntheticFunction? ctx name with
  | some synth => some synth.sig
  | none =>
      match ctx.env.find? name with
      | some info => supportedFunction? ctx.env info
      | none => none

def localInlineFunction? (ctx : Context) (name : Name) : Bool :=
  name.getRoot == ctx.root &&
    match ctx.env.find? name with
    | some info => (supportedInlineFunction? ctx.env info).isSome
    | none => false

end LeanExe.Extract.Core
