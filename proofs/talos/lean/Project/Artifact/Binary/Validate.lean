import Project.Artifact.Binary.Decode

namespace Wasm.Binary

inductive ValidationErrorKind where
  | invalidSectionSequence
  | missingSection (id : SectionId)
  | functionCodeCountMismatch (functions codes : Nat)
  | typeIndexOutOfBounds (index : UInt32)
  | functionIndexOutOfBounds (index : UInt32)
  | localIndexOutOfBounds (index : UInt32)
  | globalIndexOutOfBounds (index : UInt32)
  | immutableGlobal (index : UInt32)
  | memoryCount (count : Nat)
  | memoryIndexOutOfBounds (index : UInt32)
  | invalidMemoryLimits
  | invalidAlignment (found maximum : UInt32)
  | duplicateExportName (name : String)
  | invalidExportIndex (name : String)
  | invalidNameEncoding (name : String)
  | constantOutOfRange (width : Nat) (value : Int)
  | globalInitializerType
  | stackUnderflow (expected : Option ValType)
  | typeMismatch (expected found : ValType)
  | stackHeightMismatch (expected found : Nat)
  | branchDepthOutOfBounds (depth : UInt32)
  | ifBranchMismatch
  deriving Repr, Inhabited, DecidableEq

structure ValidationError where
  functionIndex : Option Nat
  instructionPath : List Nat
  kind : ValidationErrorKind
  deriving Repr, Inhabited, DecidableEq

structure ValidatedModule where
  private mk ::
  raw : RawModule

namespace Validator

structure StackState where
  values : List ValType
  polymorphic : Bool
  deriving DecidableEq

structure Context where
  functionIndex : Nat
  functions : List FuncType
  locals : UInt32 → Option ValType
  globals : List GlobalType
  labels : List (List ValType)
  results : List ValType
  hasMemory : Bool

def validationFailure (context : Context) (path : List Nat)
    (kind : ValidationErrorKind) : Except ValidationError α :=
  .error { functionIndex := some context.functionIndex, instructionPath := path, kind }

def moduleFailure (kind : ValidationErrorKind) : Except ValidationError α :=
  .error { functionIndex := none, instructionPath := [], kind }

def StackState.push (state : StackState) (type : ValType) : StackState :=
  { state with values := type :: state.values }

def StackState.pushMany (state : StackState) (types : List ValType) : StackState :=
  { state with values := types.reverse ++ state.values }

def bottom (count : Nat) (values : List ValType) : List ValType :=
  values.drop (values.length - count)

def popExpected (context : Context) (path : List Nat) (base : Nat)
    (expected : ValType) (state : StackState) : Except ValidationError StackState :=
  match state.values with
  | found :: rest =>
      if state.values.length = base then
        if state.polymorphic then
          pure state
        else
          validationFailure context path (.stackUnderflow (some expected))
      else if found = expected then
        pure { state with values := rest }
      else
        validationFailure context path (.typeMismatch expected found)
  | [] =>
      if state.polymorphic && base = 0 then
        pure state
      else
        validationFailure context path (.stackUnderflow (some expected))

def popAny (context : Context) (path : List Nat) (base : Nat)
    (state : StackState) : Except ValidationError StackState :=
  match state.values with
  | _ :: rest =>
      if state.values.length = base then
        if state.polymorphic then
          pure state
        else
          validationFailure context path (.stackUnderflow none)
      else
        pure { state with values := rest }
  | [] =>
      if state.polymorphic && base = 0 then
        pure state
      else
        validationFailure context path (.stackUnderflow none)

def popExpectedList (context : Context) (path : List Nat) (base : Nat) :
    List ValType → StackState → Except ValidationError StackState
  | [], state => pure state
  | type :: rest, state => do
      let state ← popExpected context path base type state
      popExpectedList context path base rest state

def popMany (context : Context) (path : List Nat) (base : Nat)
    (types : List ValType) (state : StackState) : Except ValidationError StackState :=
  popExpectedList context path base types.reverse state

def markUnreachable (base : Nat) (state : StackState) : StackState :=
  { values := bottom base state.values, polymorphic := true }

def blockResults : BlockType → List ValType
  | .empty => []
  | .value type => [type]

def finishFrame (context : Context) (path : List Nat) (base : Nat)
    (outer body : StackState) (results : List ValType) : Except ValidationError StackState := do
  let consumed ← popMany context path base results body
  if consumed.values.length = base then
    pure (outer.pushMany results)
  else
    validationFailure context path
      (.stackHeightMismatch (base + results.length) body.values.length)

def checkMemory (context : Context) (path : List Nat) : Except ValidationError Unit :=
  if context.hasMemory then
    pure ()
  else
    validationFailure context path (.memoryCount 0)

def checkAlignment (context : Context) (path : List Nat) (arg : MemArg)
    (maximum : UInt32) : Except ValidationError Unit :=
  if arg.align ≤ maximum then
    pure ()
  else
    validationFailure context path (.invalidAlignment arg.align maximum)

def unary (context : Context) (path : List Nat) (base : Nat)
    (input output : ValType) (state : StackState) : Except ValidationError StackState := do
  let state ← popExpected context path base input state
  pure (state.push output)

def binary (context : Context) (path : List Nat) (base : Nat)
    (input output : ValType) (state : StackState) : Except ValidationError StackState := do
  let state ← popExpected context path base input state
  let state ← popExpected context path base input state
  pure (state.push output)

def localDeclType : List LocalDecl → Nat → Option ValType
  | [], _ => none
  | decl :: rest, index =>
      if index < decl.count.toNat then
        some decl.type
      else
        localDeclType rest (index - decl.count.toNat)

def localType (params : List ValType) (locals : List LocalDecl)
    (index : UInt32) : Option ValType :=
  if index.toNat < params.length then
    params[index.toNat]?
  else
    localDeclType locals (index.toNat - params.length)

def inSignedRange (width : Nat) (value : Int) : Bool :=
  -(2 : Int) ^ (width - 1) ≤ value && value < (2 : Int) ^ (width - 1)

mutual
  def validateInstr (context : Context) (path : List Nat) (base : Nat)
      (state : StackState) : Instr → Except ValidationError StackState
    | .unreachable => pure (markUnreachable base state)
    | .drop => popAny context path base state
    | .block type body => do
        let results := blockResults type
        let innerBase := state.values.length
        let innerContext := { context with labels := results :: context.labels }
        let bodyState ← validateInstrs innerContext path innerBase state 0 body
        finishFrame context path innerBase state bodyState results
    | .loop type body => do
        let results := blockResults type
        let innerBase := state.values.length
        let innerContext := { context with labels := [] :: context.labels }
        let bodyState ← validateInstrs innerContext path innerBase state 0 body
        finishFrame context path innerBase state bodyState results
    | .iff type thenBody elseBody => do
        let outer ← popExpected context path base .i32 state
        let results := blockResults type
        let innerContext := { context with labels := results :: context.labels }
        let thenState ←
          validateInstrs innerContext (path ++ [0]) outer.values.length outer 0 thenBody
        let thenResult ← finishFrame context path outer.values.length outer thenState results
        let elseState ←
          match elseBody with
          | none => pure outer
          | some body =>
              validateInstrs innerContext (path ++ [1]) outer.values.length outer 0 body
        let elseResult ← finishFrame context path outer.values.length outer elseState results
        if thenResult = elseResult then
          pure thenResult
        else
          validationFailure context path .ifBranchMismatch
    | .br depth => do
        let some types := context.labels[depth.toNat]?
          | validationFailure context path (.branchDepthOutOfBounds depth)
        let state ← popMany context path base types state
        pure (markUnreachable base state)
    | .brIf depth => do
        let state ← popExpected context path base .i32 state
        let some types := context.labels[depth.toNat]?
          | validationFailure context path (.branchDepthOutOfBounds depth)
        let state ← popMany context path base types state
        pure (state.pushMany types)
    | .ret => do
        let state ← popMany context path base context.results state
        pure (markUnreachable base state)
    | .call index => do
        let some type := context.functions[index.toNat]?
          | validationFailure context path (.functionIndexOutOfBounds index)
        let state ← popMany context path base type.params state
        pure (state.pushMany type.results)
    | .localGet index =>
        match context.locals index with
        | some type => pure (state.push type)
        | none => validationFailure context path (.localIndexOutOfBounds index)
    | .localSet index =>
        match context.locals index with
        | some type => popExpected context path base type state
        | none => validationFailure context path (.localIndexOutOfBounds index)
    | .localTee index =>
        match context.locals index with
        | some type => do
            let state ← popExpected context path base type state
            pure (state.push type)
        | none => validationFailure context path (.localIndexOutOfBounds index)
    | .globalGet index =>
        match context.globals[index.toNat]? with
        | some type => pure (state.push type.type)
        | none => validationFailure context path (.globalIndexOutOfBounds index)
    | .globalSet index =>
        match context.globals[index.toNat]? with
        | none => validationFailure context path (.globalIndexOutOfBounds index)
        | some type =>
            if type.mutability = .mutable then
              popExpected context path base type.type state
            else
              validationFailure context path (.immutableGlobal index)
    | .i32Const value =>
        if inSignedRange 32 value then pure (state.push .i32)
        else validationFailure context path (.constantOutOfRange 32 value)
    | .i64Const value =>
        if inSignedRange 64 value then pure (state.push .i64)
        else validationFailure context path (.constantOutOfRange 64 value)
    | .i32Eqz => unary context path base .i32 .i32 state
    | .i32Eq => binary context path base .i32 .i32 state
    | .i32And => binary context path base .i32 .i32 state
    | .i64Eqz => unary context path base .i64 .i32 state
    | .i64Eq => binary context path base .i64 .i32 state
    | .i64Ne => binary context path base .i64 .i32 state
    | .i64LtU => binary context path base .i64 .i32 state
    | .i64LeU => binary context path base .i64 .i32 state
    | .i64GeU => binary context path base .i64 .i32 state
    | .i64Add => binary context path base .i64 .i64 state
    | .i64Sub => binary context path base .i64 .i64 state
    | .i64Mul => binary context path base .i64 .i64 state
    | .i64DivU => binary context path base .i64 .i64 state
    | .i64RemU => binary context path base .i64 .i64 state
    | .i64And => binary context path base .i64 .i64 state
    | .i64Or => binary context path base .i64 .i64 state
    | .i64Xor => binary context path base .i64 .i64 state
    | .i64Shl => binary context path base .i64 .i64 state
    | .i64ShrU => binary context path base .i64 .i64 state
    | .f64Add => binary context path base .f64 .f64 state
    | .f64Mul => binary context path base .f64 .f64 state
    | .i32WrapI64 => unary context path base .i64 .i32 state
    | .i64ExtendI32U => unary context path base .i32 .i64 state
    | .i64ReinterpretF64 => unary context path base .f64 .i64 state
    | .f64ReinterpretI64 => unary context path base .i64 .f64 state
    | .i64Load arg => do
        checkMemory context path
        checkAlignment context path arg 3
        let state ← popExpected context path base .i32 state
        pure (state.push .i64)
    | .i32Load arg => do
        checkMemory context path
        checkAlignment context path arg 2
        let state ← popExpected context path base .i32 state
        pure (state.push .i32)
    | .i32Load8U arg => do
        checkMemory context path
        checkAlignment context path arg 0
        let state ← popExpected context path base .i32 state
        pure (state.push .i32)
    | .i64Store arg => do
        checkMemory context path
        checkAlignment context path arg 3
        let state ← popExpected context path base .i64 state
        popExpected context path base .i32 state
    | .i32Store arg => do
        checkMemory context path
        checkAlignment context path arg 2
        let state ← popExpected context path base .i32 state
        popExpected context path base .i32 state
    | .i32Store8 arg => do
        checkMemory context path
        checkAlignment context path arg 0
        let state ← popExpected context path base .i32 state
        popExpected context path base .i32 state
    | .memorySize memory => do
        checkMemory context path
        if memory = 0 then
          pure (state.push .i32)
        else
          validationFailure context path (.memoryIndexOutOfBounds memory)
    | .memoryGrow memory => do
        checkMemory context path
        if memory = 0 then
          let state ← popExpected context path base .i32 state
          pure (state.push .i32)
        else
          validationFailure context path (.memoryIndexOutOfBounds memory)

  def validateInstrs (context : Context) (parentPath : List Nat) (base : Nat)
      (state : StackState) : Nat → List Instr → Except ValidationError StackState
    | _, [] => pure state
    | index, instr :: rest => do
        let path := parentPath ++ [index]
        let state ← validateInstr context path base state instr
        validateInstrs context parentPath base state (index + 1) rest
end

def sectionRank : SectionId → Nat
  | .type => 1
  | .function => 2
  | .memory => 3
  | .global => 4
  | .export => 5
  | .code => 6

def orderedSections : List SectionId → Bool
  | [] => true
  | first :: rest =>
      first ∉ rest && rest.all (fun next => sectionRank first < sectionRank next) &&
        orderedSections rest

def requireSection (module_ : RawModule) (id : SectionId) (needed : Bool) :
    Except ValidationError Unit :=
  if needed && id ∉ module_.sections then
    moduleFailure (.missingSection id)
  else
    pure ()

def validateRequiredSections (module_ : RawModule) :
    List (SectionId × Bool) → Except ValidationError Unit
  | [] => pure ()
  | (id, needed) :: rest => do
      requireSection module_ id needed
      validateRequiredSections module_ rest

def validateSections (module_ : RawModule) : Except ValidationError Unit :=
  if orderedSections module_.sections then
    validateRequiredSections module_
      [(.type, !module_.types.isEmpty),
       (.function, !module_.functionTypeIndices.isEmpty),
       (.memory, !module_.memories.isEmpty),
       (.global, !module_.globals.isEmpty),
       (.export, !module_.exports.isEmpty),
       (.code, !module_.codes.isEmpty)]
  else
    moduleFailure .invalidSectionSequence

def validateLimits (limits : Limits) : Except ValidationError Unit :=
  if limits.min.toNat ≤ 65536 &&
      limits.max.all (fun max => limits.min ≤ max && max.toNat ≤ 65536) then
    pure ()
  else
    moduleFailure .invalidMemoryLimits

def constType : ConstExpr → ValType
  | .i32Const _ => .i32
  | .i64Const _ => .i64

def validateGlobal (global : Global) : Except ValidationError Unit :=
  if constType global.init = global.type.type then
    match global.init with
    | .i32Const value =>
        if inSignedRange 32 value then pure ()
        else moduleFailure (.constantOutOfRange 32 value)
    | .i64Const value =>
        if inSignedRange 64 value then pure ()
        else moduleFailure (.constantOutOfRange 64 value)
  else
    moduleFailure .globalInitializerType

def validateGlobals : List Global → Except ValidationError Unit
  | [] => pure ()
  | global :: rest => do
      validateGlobal global
      validateGlobals rest

def duplicateName? : List Export → Option String
  | [] => none
  | entry :: rest =>
      if rest.any (fun other => other.name.bytes == entry.name.bytes) then
        some entry.name.text
      else
        duplicateName? rest

def validateExportEntry (module_ : RawModule) (entry : Export) :
    Except ValidationError Unit :=
  if entry.name.text.toByteArray.data.toList = entry.name.bytes then
    let valid : Bool :=
      match entry.desc with
      | .func index => decide (index.toNat < module_.functionTypeIndices.length)
      | .memory index => decide (index.toNat < module_.memories.length)
      | .global index => decide (index.toNat < module_.globals.length)
    if valid then pure () else moduleFailure (.invalidExportIndex entry.name.text)
  else
    moduleFailure (.invalidNameEncoding entry.name.text)

def validateExportEntries (module_ : RawModule) :
    List Export → Except ValidationError Unit
  | [] => pure ()
  | entry :: rest => do
      validateExportEntry module_ entry
      validateExportEntries module_ rest

def validateExports (module_ : RawModule) : Except ValidationError Unit :=
  match duplicateName? module_.exports with
  | some name => moduleFailure (.duplicateExportName name)
  | none => validateExportEntries module_ module_.exports

def resolveTypes (types : List FuncType) :
    List UInt32 → Except ValidationError (List FuncType)
  | [] => pure []
  | index :: rest => do
    match types[index.toNat]? with
    | some type => pure (type :: (← resolveTypes types rest))
    | none => moduleFailure (.typeIndexOutOfBounds index)

def resolveFunctionTypes (module_ : RawModule) :
    Except ValidationError (List FuncType) :=
  resolveTypes module_.types module_.functionTypeIndices

def validateFunction (module_ : RawModule) (functions : List FuncType)
    (index : Nat) (type : FuncType) (code : Code) : Except ValidationError Unit := do
  let context : Context :=
    { functionIndex := index
      functions
      locals := localType type.params code.locals
      globals := module_.globals.map (·.type)
      labels := [type.results]
      results := type.results
      hasMemory := module_.memories.length = 1 }
  let initial : StackState := { values := [], polymorphic := false }
  let state ← validateInstrs context [] 0 initial 0 code.body
  let _ ← finishFrame context [] 0 initial state type.results
  pure ()

def validateFunctionPairs (module_ : RawModule) (functions : List FuncType) :
    Nat → List FuncType → List Code → Except ValidationError Unit
  | _, [], [] => pure ()
  | index, type :: types, code :: codes => do
      validateFunction module_ functions index type code
      validateFunctionPairs module_ functions (index + 1) types codes
  | _, _, _ =>
      moduleFailure (.functionCodeCountMismatch functions.length module_.codes.length)

def validateFunctions (module_ : RawModule) (functions : List FuncType) :
    Except ValidationError Unit :=
  validateFunctionPairs module_ functions 0 functions module_.codes

def validateRaw (module_ : RawModule) : Except ValidationError Unit := do
  validateSections module_
  if module_.memories.length = 1 then
    validateLimits module_.memories.head!.limits
  else
    moduleFailure (.memoryCount module_.memories.length)
  validateGlobals module_.globals
  validateExports module_
  let functions ← resolveFunctionTypes module_
  validateFunctions module_ functions

end Validator

def validate (module_ : RawModule) : Except ValidationError ValidatedModule := do
  Validator.validateRaw module_
  pure { raw := module_ }

end Wasm.Binary
