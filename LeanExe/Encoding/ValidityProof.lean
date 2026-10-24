import Lean
import LeanExe.Encoding.Completeness.Writes
import LeanExe.Encoding.Spec.Validity

namespace Wasm.Encoding.ValidityProof

open Lean Meta

theorem globalReady_of_spec {bytes : Spec.Bytes} {declaration : Wasm.GlobalDecl}
    (encoding : Spec.Global bytes declaration) : GlobalReady declaration := by
  cases encoding <;> constructor

def checkGlobal (declaration : Wasm.GlobalDecl) : Bool :=
  (Wasm.Encoding.global declaration).isOk

theorem checkGlobal_sound {declaration : Wasm.GlobalDecl} (accepted : checkGlobal declaration = true) :
    GlobalReady declaration := by
  cases result : Wasm.Encoding.global declaration with
  | error message => simp [checkGlobal, result, Except.isOk, Except.toBool] at accepted
  | ok encoding => exact globalReady_of_spec encoding.property

theorem functions_of_indices (wasmModule : Wasm.Module)
    (typed : ∀ index < wasmModule.funcs.length,
      Spec.Validity.Function wasmModule wasmModule.funcs[index]!) :
    ∀ function ∈ wasmModule.funcs, Spec.Validity.Function wasmModule function := by
  intro function member
  obtain ⟨index, bound, rfl⟩ := List.getElem_of_mem member
  simpa only [getElem!_pos wasmModule.funcs index bound] using typed index bound

theorem types_nil : Spec.Validity.Types [] := by
  intro type member
  cases member

theorem types_cons {type : ValueType} {types : List ValueType}
    (head : Numeric type) (tail : Spec.Validity.Types types) : Spec.Validity.Types (type :: types) := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail value member

def checkDataSegment (segment : Wasm.DataSegment) : Bool :=
  segment.memIdx == 0 && segment.offset.isSome && segment.offsetExpr.isEmpty

theorem checkDataSegment_sound {segment : Wasm.DataSegment}
    (accepted : checkDataSegment segment = true) : Spec.Validity.DataSegment segment := by
  simp only [checkDataSegment, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at accepted
  exact ⟨accepted.1.1, accepted.1.2, accepted.2⟩

def checkMemory (memory : Wasm.MemDecl) : Bool :=
  decide (memory.is64 = false) && memory.data.all checkDataSegment &&
    decide (memory.pagesMin.toNat ≤ 65536) &&
    memory.pagesMax.all (fun maximum =>
      decide (memory.pagesMin ≤ maximum ∧ maximum.toNat ≤ 65536))

theorem checkMemory_sound {memory : Wasm.MemDecl} (accepted : checkMemory memory = true) :
    Spec.Validity.Memory memory := by
  simp only [checkMemory, Bool.and_eq_true, decide_eq_true_eq] at accepted
  refine ⟨accepted.1.1.1, ?_, accepted.1.2, ?_⟩
  · intro segment member
    exact checkDataSegment_sound (List.all_eq_true.mp accepted.1.1.2 segment member)
  · intro maximum member
    have bound := (Option.all_eq_true _ _).mp accepted.2 maximum member
    exact of_decide_eq_true bound

theorem checkMemories_sound {memories : Option Wasm.MemDecl}
    (accepted : memories.all checkMemory = true) :
    ∀ memory ∈ memories, Spec.Validity.Memory memory := by
  intro memory member
  exact checkMemory_sound ((Option.all_eq_true _ _).mp accepted memory member)

def checkImports (types : List Wasm.FuncType) (imports : List Wasm.ImportDecl) : Bool :=
  imports.all fun declaration =>
    (signatureIndex { params := declaration.params, results := declaration.results } types).isOk

theorem checkImports_sound {types : List Wasm.FuncType} {imports : List Wasm.ImportDecl}
    (accepted : checkImports types imports = true) :
    ∀ declaration ∈ imports,
      ({ params := declaration.params, results := declaration.results } : Wasm.FuncType) ∈ types := by
  intro declaration member
  have present := List.all_eq_true.mp accepted declaration member
  cases result : signatureIndex
      { params := declaration.params, results := declaration.results } types with
  | error message => simp [result, Except.isOk, Except.toBool] at present
  | ok index => exact List.mem_of_getElem? index.property

private inductive AtomicRule where
  | fixed (constructor : Name)
  | immediate (constructor : Name)
  | unary (constructor : Name)
  | binary (constructor : Name)
  | localOp (constructor : Name) (index : Nat) (type : ValueType)
  | globalOp (constructor : Name) (index : Nat) (type : ValueType) (mutable : Bool)
  | call (index : Nat) (type : FuncType)
  | memory (constructor : Name)
  | load (constructor : Name)
  | store (constructor : Name)
  | branchIf (index : Nat) (results : List ValueType)
  | control

private structure Atomic where
  inputs : List ValueType
  outputs : List ValueType
  rule : AtomicRule

private def unary? : Wasm.Instruction → Option (Name × ValueType × ValueType)
  | .eqz => some (``Spec.Validity.Unary.eqz, .i32, .i32)
  | .eqzI64 => some (``Spec.Validity.Unary.eqzI64, .i64, .i32)
  | .wrapI64 => some (``Spec.Validity.Unary.wrapI64, .i64, .i32)
  | .extendUI32 => some (``Spec.Validity.Unary.extendUI32, .i32, .i64)
  | .f32Nearest => some (``Spec.Validity.Unary.f32Nearest, .f32, .f32)
  | .f32Sqrt => some (``Spec.Validity.Unary.f32Sqrt, .f32, .f32)
  | .f64Sqrt => some (``Spec.Validity.Unary.f64Sqrt, .f64, .f64)
  | .f64Abs => some (``Spec.Validity.Unary.f64Abs, .f64, .f64)
  | .f32Abs => some (``Spec.Validity.Unary.f32Abs, .f32, .f32)
  | .f64ConvertI64U => some (``Spec.Validity.Unary.f64ConvertI64U, .i64, .f64)
  | .f32ConvertI32S => some (``Spec.Validity.Unary.f32ConvertI32S, .i32, .f32)
  | .f32ConvertI64U => some (``Spec.Validity.Unary.f32ConvertI64U, .i64, .f32)
  | .i32TruncSatF32S => some (``Spec.Validity.Unary.i32TruncSatF32S, .f32, .i32)
  | .i64TruncSatF32U => some (``Spec.Validity.Unary.i64TruncSatF32U, .f32, .i64)
  | .i64TruncSatF64U => some (``Spec.Validity.Unary.i64TruncSatF64U, .f64, .i64)
  | .extend8S => some (``Spec.Validity.Unary.extend8S, .i32, .i32)
  | .f32DemoteF64 => some (``Spec.Validity.Unary.f32DemoteF64, .f64, .f32)
  | .f64PromoteF32 => some (``Spec.Validity.Unary.f64PromoteF32, .f32, .f64)
  | .i32ReinterpretF32 => some (``Spec.Validity.Unary.i32ReinterpretF32, .f32, .i32)
  | .i64ReinterpretF64 => some (``Spec.Validity.Unary.i64ReinterpretF64, .f64, .i64)
  | .f32ReinterpretI32 => some (``Spec.Validity.Unary.f32ReinterpretI32, .i32, .f32)
  | .f64ReinterpretI64 => some (``Spec.Validity.Unary.f64ReinterpretI64, .i64, .f64)
  | _ => none

private def binary? : Wasm.Instruction → Option (Name × ValueType × ValueType)
  | .eq => some (``Spec.Validity.Binary.eq, .i32, .i32)
  | .ltU => some (``Spec.Validity.Binary.ltU, .i32, .i32)
  | .gtU => some (``Spec.Validity.Binary.gtU, .i32, .i32)
  | .leU => some (``Spec.Validity.Binary.leU, .i32, .i32)
  | .geU => some (``Spec.Validity.Binary.geU, .i32, .i32)
  | .add => some (``Spec.Validity.Binary.add, .i32, .i32)
  | .and => some (``Spec.Validity.Binary.and, .i32, .i32)
  | .eqI64 => some (``Spec.Validity.Binary.eqI64, .i64, .i32)
  | .neI64 => some (``Spec.Validity.Binary.neI64, .i64, .i32)
  | .ltUI64 => some (``Spec.Validity.Binary.ltUI64, .i64, .i32)
  | .leUI64 => some (``Spec.Validity.Binary.leUI64, .i64, .i32)
  | .geUI64 => some (``Spec.Validity.Binary.geUI64, .i64, .i32)
  | .f64Eq => some (``Spec.Validity.Binary.f64Eq, .f64, .i32)
  | .f64Lt => some (``Spec.Validity.Binary.f64Lt, .f64, .i32)
  | .f64Le => some (``Spec.Validity.Binary.f64Le, .f64, .i32)
  | .f32Eq => some (``Spec.Validity.Binary.f32Eq, .f32, .i32)
  | .f32Lt => some (``Spec.Validity.Binary.f32Lt, .f32, .i32)
  | .f32Le => some (``Spec.Validity.Binary.f32Le, .f32, .i32)
  | .addI64 => some (``Spec.Validity.Binary.addI64, .i64, .i64)
  | .subI64 => some (``Spec.Validity.Binary.subI64, .i64, .i64)
  | .mulI64 => some (``Spec.Validity.Binary.mulI64, .i64, .i64)
  | .divUI64 => some (``Spec.Validity.Binary.divUI64, .i64, .i64)
  | .remUI64 => some (``Spec.Validity.Binary.remUI64, .i64, .i64)
  | .andI64 => some (``Spec.Validity.Binary.andI64, .i64, .i64)
  | .orI64 => some (``Spec.Validity.Binary.orI64, .i64, .i64)
  | .xorI64 => some (``Spec.Validity.Binary.xorI64, .i64, .i64)
  | .shlI64 => some (``Spec.Validity.Binary.shlI64, .i64, .i64)
  | .shrUI64 => some (``Spec.Validity.Binary.shrUI64, .i64, .i64)
  | .f32Add => some (``Spec.Validity.Binary.f32Add, .f32, .f32)
  | .f32Sub => some (``Spec.Validity.Binary.f32Sub, .f32, .f32)
  | .f32Mul => some (``Spec.Validity.Binary.f32Mul, .f32, .f32)
  | .f32Div => some (``Spec.Validity.Binary.f32Div, .f32, .f32)
  | .f64Add => some (``Spec.Validity.Binary.f64Add, .f64, .f64)
  | .f64Sub => some (``Spec.Validity.Binary.f64Sub, .f64, .f64)
  | .f64Mul => some (``Spec.Validity.Binary.f64Mul, .f64, .f64)
  | .f64Div => some (``Spec.Validity.Binary.f64Div, .f64, .f64)
  | _ => none

private def lookup (label : String) (values : List α) (index : Nat) : Except String α :=
  match values[index]? with
  | some value => .ok value
  | none => .error s!"{label} index {index} is out of bounds"

private def controlResults (parameters results : Nat) (parameterTypes resultTypes : List ValueType) :
    Except String (List ValueType) :=
  if parameters != 0 || parameterTypes != [] || results != resultTypes.length || resultTypes.length > 1 then
    .error "structured control is outside the zero-parameter, at-most-one-result encoding profile"
  else .ok resultTypes

private def atomic (context : Spec.Validity.Context) (instruction : Wasm.Instruction) :
    Except String Atomic := do
  if let some (constructor, input, output) := unary? instruction then
    return ⟨[input], [output], .unary constructor⟩
  if let some (constructor, input, output) := binary? instruction then
    return ⟨[input, input], [output], .binary constructor⟩
  match instruction with
  | .nop => return ⟨[], [], .fixed ``Spec.Validity.Instruction.nop⟩
  | .const _ => return ⟨[], [.i32], .immediate ``Spec.Validity.Instruction.const32⟩
  | .constI64 _ => return ⟨[], [.i64], .immediate ``Spec.Validity.Instruction.const64⟩
  | .f32Const _ => return ⟨[], [.f32], .immediate ``Spec.Validity.Instruction.constF32⟩
  | .f64Const _ => return ⟨[], [.f64], .immediate ``Spec.Validity.Instruction.constF64⟩
  | .localGet index =>
    let type ← lookup "local" context.locals index
    return ⟨[], [type], .localOp ``Spec.Validity.Instruction.localGet index type⟩
  | .localSet index =>
    let type ← lookup "local" context.locals index
    return ⟨[type], [], .localOp ``Spec.Validity.Instruction.localSet index type⟩
  | .localTee index =>
    let type ← lookup "local" context.locals index
    return ⟨[type], [type], .localOp ``Spec.Validity.Instruction.localTee index type⟩
  | .globalGet index =>
    let (type, mutable) ← lookup "global" context.globals index
    return ⟨[], [type], .globalOp ``Spec.Validity.Instruction.globalGet index type mutable⟩
  | .globalSet index =>
    let (type, mutable) ← lookup "global" context.globals index
    unless mutable do throw s!"global {index} is immutable"
    return ⟨[type], [], .globalOp ``Spec.Validity.Instruction.globalSet index type true⟩
  | .call index =>
    let type ← lookup "function" context.functions index
    return ⟨type.params, type.results, .call index type⟩
  | .memorySize => return ⟨[], [.i32], .memory ``Spec.Validity.Instruction.memorySize⟩
  | .memoryGrow => return ⟨[.i32], [.i32], .memory ``Spec.Validity.Instruction.memoryGrow⟩
  | .load32 _ => return ⟨[.i32], [.i32], .load ``Spec.Validity.Load.i32⟩
  | .load64 _ => return ⟨[.i32], [.i64], .load ``Spec.Validity.Load.i64⟩
  | .load8U _ => return ⟨[.i32], [.i32], .load ``Spec.Validity.Load.i32_8⟩
  | .store32 _ => return ⟨[.i32, .i32], [], .store ``Spec.Validity.Store.i32⟩
  | .store64 _ => return ⟨[.i32, .i64], [], .store ``Spec.Validity.Store.i64⟩
  | .store8 _ => return ⟨[.i32, .i32], [], .store ``Spec.Validity.Store.i32_8⟩
  | .br_if index =>
    let results ← lookup "label" context.labels index
    return ⟨results ++ [.i32], results, .branchIf index results⟩
  | .block parameters results _ parameterTypes resultTypes
  | .loop parameters results _ parameterTypes resultTypes =>
    return ⟨[], ← controlResults parameters results parameterTypes resultTypes, .control⟩
  | .iff parameters results _ _ parameterTypes resultTypes =>
    return ⟨[.i32], ← controlResults parameters results parameterTypes resultTypes, .control⟩
  | _ => throw s!"unsupported instruction: {repr instruction}"

private def consume (stack required : List ValueType) : Except String (List ValueType) :=
  if required.length > stack.length then .error "operand stack underflow"
  else if stack.drop (stack.length - required.length) != required then
    .error s!"operand types disagree: stack {repr stack}, required suffix {repr required}"
  else .ok (stack.take (stack.length - required.length))

private def inferConsume (stack needed : List ValueType) :
    List ValueType → Except String (List ValueType × List ValueType)
  | [] => .ok (stack, needed)
  | type :: rest =>
    match stack with
    | [] => inferConsume [] (type :: needed) rest
    | top :: stack =>
      if top == type then inferConsume stack needed rest
      else .error s!"operand types disagree: found {repr top}, required {repr type}"

/-- Infer the smallest incoming stack for a suffix after a polymorphic instruction. -/
def requiredInputs (context : Spec.Validity.Context) (code : Wasm.Program)
    (outputs : List ValueType) : Except String (List ValueType) := do
  let rec visit (code : Wasm.Program) (stack needed : List ValueType) : Except String (List ValueType) := do
    match code with
    | [] =>
      if stack.length > outputs.length || outputs.reverse.take stack.length != stack then
        throw s!"result types disagree: inferred {repr stack.reverse}, declared {repr outputs}"
      return outputs.take (outputs.length - stack.length) ++ needed
    | .unreachable :: _ => return needed
    | .br index :: _ =>
      let results ← lookup "label" context.labels index
      let (_, needed) ← inferConsume stack needed results.reverse
      return needed
    | .ret :: _ =>
      let (_, needed) ← inferConsume stack needed context.results.reverse
      return needed
    | .drop :: rest =>
      match stack with
      | [] => visit rest [] (.i32 :: needed)
      | _ :: stack => visit rest stack needed
    | instruction :: rest =>
      let rule ← atomic context instruction
      let (stack, needed) ← inferConsume stack needed rule.inputs.reverse
      visit rest (rule.outputs.reverse ++ stack) needed
  visit code [] []

def valueTypeExpr : ValueType → MetaM Lean.Expr
  | .i32 => pure (mkConst ``ValueType.i32)
  | .i64 => pure (mkConst ``ValueType.i64)
  | .f32 => pure (mkConst ``ValueType.f32)
  | .f64 => pure (mkConst ``ValueType.f64)
  | type => throwError "validity proof: unsupported value type {repr type}"

def typesExpr (types : List ValueType) : MetaM Lean.Expr := do
  let type := mkConst ``ValueType
  let values ← types.mapM valueTypeExpr
  return values.foldr (fun value tail => mkApp3 (mkConst ``List.cons [.zero]) type value tail)
    (mkApp (mkConst ``List.nil [.zero]) type)

private def numericProof (type : ValueType) : MetaM Lean.Expr := do
  mkDecideProof (← whnf (← mkAppM ``Numeric #[← valueTypeExpr type]))

private def typesProof (types : List ValueType) : MetaM Lean.Expr := do
  let mut proof := mkConst ``types_nil
  for type in types.reverse do
    proof ← mkAppM ``types_cons #[← numericProof type, proof]
  return proof

private def blockProof (types : List ValueType) : MetaM Lean.Expr := do
  match types with
  | [] => mkAppM ``BlockForm.empty #[]
  | [type] =>
    let expression ← valueTypeExpr type
    mkAppM ``BlockForm.value #[expression, ← numericProof type]
  | _ => throwError "validity proof: structured control has more than one result"

private def ensureType (proof expected : Lean.Expr) : MetaM Lean.Expr := do
  unless ← isDefEq (← inferType proof) expected do
    throwError "validity proof: constructed type{indentExpr (← inferType proof)}\n\
      differs from required type{indentExpr expected}"
  mkExpectedTypeHint (← instantiateMVars proof) expected

private def instructionType (context instruction : Lean.Expr) (inputs outputs : List ValueType) :
    MetaM Lean.Expr := do
  mkAppM ``Spec.Validity.Instruction #[context, instruction, ← typesExpr inputs, ← typesExpr outputs]

private def lookupProof (context : Lean.Expr) (field : Name) (index : Nat) (value : Lean.Expr) :
    MetaM Lean.Expr := do
  let values ← mkAppM field #[context]
  let found ← mkAppM ``GetElem?.getElem? #[values, mkNatLit index]
  mkDecideProof (← mkEq found (← mkAppM ``Option.some #[value]))

private def memoryProof (context : Lean.Expr) : MetaM Lean.Expr := do
  mkDecideProof (← mkEq (← mkAppM ``Spec.Validity.Context.hasMemory #[context]) (toExpr true))

private def labelContext (context : Lean.Expr) (label : List ValueType) : MetaM Lean.Expr := do
  let label ← typesExpr label
  let labels ← mkAppM ``Spec.Validity.Context.labels #[context]
  let labels ← mkAppM ``List.cons #[label, labels]
  mkAppM ``Spec.Validity.Context.mk #[
    ← mkAppM ``Spec.Validity.Context.functions #[context],
    ← mkAppM ``Spec.Validity.Context.locals #[context],
    ← mkAppM ``Spec.Validity.Context.globals #[context], labels,
    ← mkAppM ``Spec.Validity.Context.results #[context],
    ← mkAppM ``Spec.Validity.Context.hasMemory #[context]]

private def contextConstructor (name : Name) (context : Lean.Expr) (arguments : Array Lean.Expr) :
    MetaM Lean.Expr := do
  let constant ← mkConstWithFreshMVarLevels name
  forallTelescope (← inferType constant) fun parameters _ => do
    let mut position := 0
    let mut assigned := #[]
    for parameter in parameters do
      let declaration ← parameter.fvarId!.getDecl
      if declaration.userName == `context then
        assigned := assigned.push (some context)
      else if declaration.binderInfo.isExplicit then
        let some argument := arguments[position]?
          | throwError "validity proof: missing argument {position} of {name}"
        assigned := assigned.push (some argument)
        position := position + 1
      else
        assigned := assigned.push none
    unless position == arguments.size do
      throwError "validity proof: excess arguments to {name}"
    mkAppOptM name assigned

private def atomicProof (contextValue : Spec.Validity.Context) (context instruction : Lean.Expr)
    (rule : Atomic) : MetaM Lean.Expr := do
  let instruction ← whnf instruction
  let arguments := instruction.getAppArgs
  let proof ← match rule.rule with
    | .fixed constructor => contextConstructor constructor context #[]
    | .immediate constructor => contextConstructor constructor context #[arguments[0]!]
    | .unary constructor => contextConstructor ``Spec.Validity.Instruction.unary context #[mkConst constructor]
    | .binary constructor => contextConstructor ``Spec.Validity.Instruction.binary context #[mkConst constructor]
    | .localOp constructor index type =>
      contextConstructor constructor context #[mkNatLit index,
        ← lookupProof context ``Spec.Validity.Context.locals index (← valueTypeExpr type)]
    | .globalOp constructor index type mutable => do
      let value ← mkAppM ``Prod.mk #[← valueTypeExpr type, toExpr mutable]
      contextConstructor constructor context #[mkNatLit index,
        ← lookupProof context ``Spec.Validity.Context.globals index value]
    | .call index type => do
      let type ← mkAppM ``FuncType.mk #[← typesExpr type.params, ← typesExpr type.results]
      contextConstructor ``Spec.Validity.Instruction.call context #[mkNatLit index, type,
        ← lookupProof context ``Spec.Validity.Context.functions index type]
    | .memory constructor => do
      unless contextValue.hasMemory do throwError "validity proof: memory instruction without memory"
      contextConstructor constructor context #[← memoryProof context]
    | .load constructor => do
      unless contextValue.hasMemory do throwError "validity proof: load instruction without memory"
      contextConstructor ``Spec.Validity.Instruction.load context
        #[mkConst constructor, arguments[0]!, ← memoryProof context]
    | .store constructor => do
      unless contextValue.hasMemory do throwError "validity proof: store instruction without memory"
      contextConstructor ``Spec.Validity.Instruction.store context
        #[mkConst constructor, arguments[0]!, ← memoryProof context]
    | .branchIf index results =>
      contextConstructor ``Spec.Validity.Instruction.brIf context #[mkNatLit index,
        ← lookupProof context ``Spec.Validity.Context.labels index (← typesExpr results)]
    | .control => throwError "validity proof: structured control requires its body proof"
  ensureType proof (← instructionType context instruction rule.inputs rule.outputs)

private def frameProof (context instruction proof : Lean.Expr) (stackPrefix inputs outputs : List ValueType) :
    MetaM Lean.Expr := do
  let proof ← if stackPrefix.isEmpty then pure proof
    else contextConstructor ``Spec.Validity.Instruction.frame context #[proof, ← typesProof stackPrefix]
  ensureType proof (← instructionType context instruction (stackPrefix ++ inputs) (stackPrefix ++ outputs))

private def fromExcept (value : Except String α) : MetaM α :=
  match value with
  | .ok result => pure result
  | .error message => throwError "validity proof: {message}"

/-- Construct a typing derivation for concrete code.  Native values select rules, while the
kernel checks those rules against `context` and `expression`. -/
partial def program (contextValue : Spec.Validity.Context) (context : Lean.Expr)
    (code : Wasm.Program) (expression : Lean.Expr) (inputs outputs : List ValueType) :
    MetaM Lean.Expr := do
  let reduced ← whnf expression
  match code with
  | [] =>
    unless inputs == outputs do
      throwError "validity proof: final stack {repr inputs} differs from declared results {repr outputs}"
    let proof ← contextConstructor ``Spec.Validity.Program.nil context #[← typesProof outputs]
    ensureType proof (← mkAppM ``Spec.Validity.Program
      #[context, expression, ← typesExpr inputs, ← typesExpr outputs])
  | instruction :: rest =>
    let (``List.cons, #[_, head, tail]) := reduced.getAppFnArgs
      | throwError "validity proof: program does not reduce to the supplied instruction list"
    let head ← whnf head
    let arguments := head.getAppArgs
    let (next, first) ← match instruction with
      | .unreachable => do
        let next ← fromExcept (requiredInputs contextValue rest outputs)
        let proof ← contextConstructor ``Spec.Validity.Instruction.unreachable context
          #[← typesExpr inputs, ← typesExpr next, ← typesProof inputs, ← typesProof next]
        pure (next, ← ensureType proof (← instructionType context head inputs next))
      | .br index => do
        let results ← fromExcept (lookup "label" contextValue.labels index)
        let stackPrefix ← fromExcept (consume inputs results)
        let next ← fromExcept (requiredInputs contextValue rest outputs)
        let proof ← contextConstructor ``Spec.Validity.Instruction.br context
          #[mkNatLit index, ← lookupProof context ``Spec.Validity.Context.labels index (← typesExpr results),
            ← typesProof stackPrefix, ← typesProof next]
        pure (next, ← ensureType proof (← instructionType context head inputs next))
      | .ret => do
        let stackPrefix ← fromExcept (consume inputs contextValue.results)
        let next ← fromExcept (requiredInputs contextValue rest outputs)
        let proof ← contextConstructor ``Spec.Validity.Instruction.ret context
          #[← typesProof stackPrefix, ← typesProof next]
        pure (next, ← ensureType proof (← instructionType context head inputs next))
      | .drop => do
        let some type := inputs.getLast?
          | throwError "validity proof: drop has no operand"
        let stackPrefix := inputs.dropLast
        let proof ← contextConstructor ``Spec.Validity.Instruction.drop context
          #[← numericProof type]
        let proof ← ensureType proof (← instructionType context head [type] [])
        pure (stackPrefix, ← frameProof context head proof stackPrefix [type] [])
      | .block parameters results body parameterTypes resultTypes => do
        let resultTypes ← fromExcept (controlResults parameters results parameterTypes resultTypes)
        let nested := { contextValue with labels := resultTypes :: contextValue.labels }
        let bodyProof ← program nested (← labelContext context resultTypes) body arguments[2]! [] resultTypes
        let proof ← contextConstructor ``Spec.Validity.Instruction.block context
          #[← blockProof resultTypes, bodyProof]
        let proof ← ensureType proof (← instructionType context head [] resultTypes)
        pure (inputs ++ resultTypes, ← frameProof context head proof inputs [] resultTypes)
      | .loop parameters results body parameterTypes resultTypes => do
        let resultTypes ← fromExcept (controlResults parameters results parameterTypes resultTypes)
        let nested := { contextValue with labels := [] :: contextValue.labels }
        let bodyProof ← program nested (← labelContext context []) body arguments[2]! [] resultTypes
        let proof ← contextConstructor ``Spec.Validity.Instruction.loop context
          #[← blockProof resultTypes, bodyProof]
        let proof ← ensureType proof (← instructionType context head [] resultTypes)
        pure (inputs ++ resultTypes, ← frameProof context head proof inputs [] resultTypes)
      | .iff parameters results yes no parameterTypes resultTypes => do
        let resultTypes ← fromExcept (controlResults parameters results parameterTypes resultTypes)
        let stackPrefix ← fromExcept (consume inputs [.i32])
        let nested := { contextValue with labels := resultTypes :: contextValue.labels }
        let nestedContext ← labelContext context resultTypes
        let yesProof ← program nested nestedContext yes arguments[2]! [] resultTypes
        let noProof ← program nested nestedContext no arguments[3]! [] resultTypes
        let proof ← contextConstructor ``Spec.Validity.Instruction.iff context
          #[← blockProof resultTypes, yesProof, noProof]
        let proof ← ensureType proof (← instructionType context head [.i32] resultTypes)
        pure (stackPrefix ++ resultTypes, ← frameProof context head proof stackPrefix [.i32] resultTypes)
      | _ => do
        let rule ← fromExcept (atomic contextValue instruction)
        let stackPrefix ← fromExcept (consume inputs rule.inputs)
        let proof ← atomicProof contextValue context head rule
        pure (stackPrefix ++ rule.outputs,
          ← frameProof context head proof stackPrefix rule.inputs rule.outputs)
    let remaining ← program contextValue context rest tail next outputs
    let proof ← contextConstructor ``Spec.Validity.Program.cons context #[first, remaining]
    ensureType proof (← mkAppM ``Spec.Validity.Program
      #[context, expression, ← typesExpr inputs, ← typesExpr outputs])

end Wasm.Encoding.ValidityProof
